#!/usr/bin/env python3
"""Radar de Licitações - CONSOL (coletor).

Consulta o PNCP, filtra o que interessa e grava licitacoes.json.
Roda sozinho no GitHub Actions (veja .github/workflows/coletar.yml).
Só usa a biblioteca padrão do Python: não precisa instalar nada.
"""
import json
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone

API_PROPOSTAS = "https://pncp.gov.br/api/consulta/v1/contratacoes/proposta"
ARQUIVO_SAIDA = os.environ.get("RADAR_SAIDA", "licitacoes.json")
FUSO = timezone(timedelta(hours=-3))  # Brasília

# ---------------------------------------------------------------- configuração
UFS = ("AC AL AP AM BA CE DF ES GO MA MT MS MG PA PB PR PE PI RJ RN RS RO RR SC SP SE TO").split()
MODALIDADES = [3, 4, 5, 6, 7, 12]  # concurso, concorrência (eletr./presencial), pregão (eletr./presencial), credenciamento
DIAS_A_FRENTE = 180        # consulta propostas que encerram em até N dias
DIAS_GUARDAR_ENCERRADAS = 30
TAMANHO_PAGINA = 50
PAGINAS_MAX = 200
PARALELO = 6               # consultas ao mesmo tempo (educado com o PNCP)
LIMITE_MINUTOS = 70        # passou disso, para de consultar e salva o que já tem
PRAZO_FINAL = time.time() + LIMITE_MINUTOS * 60

PALAVRAS_CHAVE = (
    "projeto,anteprojeto,supervis,gerenciamento,fiscaliza,estudo,topograf,geotecn,sondagem,"
    "rodovi,estrada,pavimen,ponte,obra de arte,oae,drenagem,ambiental,licenciamento,consultoria,"
    "levantamento,aerolevantamento,sinaliza,restaura,conserva,recupera,melhoramento,duplica,"
    "terraplen,contencao,desapropria,engenharia,viabilidade,geoprocessamento,cadastro,bim$"
).split(",")
PALAVRAS_EXCLUIR = (
    "medicamento,merenda,alimenticio,material de limpeza,material de expediente,uniforme,"
    "aquisicao de veiculo"
).split(",")

RX_ORGAO_RODOVIARIO = re.compile(
    r"\b(der|deer|dnit|daer|derba|goinfra|agesul|ageto|sinfra|seinfra|sie|deinfra|dertins|"
    r"departamento de estradas|departamento nacional de infraestrutura|infraestrutura|"
    r"transportes|rodagem)\b"
)


# ------------------------------------------------------------------ utilidades
def normalizar(texto):
    texto = unicodedata.normalize("NFD", str(texto or ""))
    return "".join(c for c in texto if not unicodedata.combining(c)).lower()


def montar_regex(lista):
    partes = []
    for kw in lista:
        kw = normalizar(kw).strip()
        if not kw:
            continue
        fim = ""
        if kw.endswith("$"):  # termina com $ = só vale a palavra inteira
            kw, fim = kw[:-1], r"\b"
        partes.append(r"\b" + re.escape(kw) + fim)
    return re.compile("|".join(partes)) if partes else None


def agora():
    return datetime.now(FUSO)


def iso(dt):
    return dt.strftime("%Y-%m-%dT%H:%M:%S")


# ------------------------------------------------------------------- consultas
def pedir(url, tentativas=3):
    """GET com repetição em caso de limite (429) ou erro do servidor (5xx)."""
    ultimo = "sem resposta"
    for t in range(tentativas):
        if t:
            time.sleep(2 * t)
        req = urllib.request.Request(url, headers={"Accept": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                corpo = resp.read().decode("utf-8") if resp.status != 204 else ""
                if not corpo:
                    return {"ok": True, "json": {"data": [], "totalPaginas": 0}}
                try:
                    return {"ok": True, "json": json.loads(corpo)}
                except ValueError:
                    return {"ok": False, "code": resp.status, "erro": "resposta inválida"}
        except urllib.error.HTTPError as e:
            ultimo = "HTTP %d" % e.code
            if e.code == 429 or e.code >= 500:
                continue
            return {"ok": False, "code": e.code, "erro": ultimo}
        except Exception as e:  # rede, tempo esgotado etc.
            ultimo = str(e)[:120]
    return {"ok": False, "code": 0, "erro": ultimo}


def url_pagina(uf, mod, data_final, pagina, tamanho):
    qs = urllib.parse.urlencode({
        "dataFinal": data_final,
        "codigoModalidadeContratacao": mod,
        "uf": uf,
        "pagina": pagina,
        "tamanhoPagina": tamanho,
    })
    return API_PROPOSTAS + "?" + qs


def coletar_par(args):
    """Todas as páginas de um par estado x modalidade."""
    uf, mod, data_final = args
    if time.time() > PRAZO_FINAL:
        return {"uf": uf, "mod": mod, "regs": [], "erro": "tempo esgotado"}
    tamanho = TAMANHO_PAGINA
    r = pedir(url_pagina(uf, mod, data_final, 1, tamanho))
    if not r["ok"] and r.get("code") == 400 and tamanho > 10:
        tamanho = 10  # o PNCP às vezes recusa páginas grandes
        r = pedir(url_pagina(uf, mod, data_final, 1, tamanho))
    if not r["ok"]:
        return {"uf": uf, "mod": mod, "regs": [], "erro": r["erro"]}
    regs = list(r["json"].get("data") or [])
    erro = None
    total = min(int(r["json"].get("totalPaginas") or 0), PAGINAS_MAX)
    for p in range(2, total + 1):
        if time.time() > PRAZO_FINAL:
            erro = erro or "tempo esgotado"
            break
        rp = pedir(url_pagina(uf, mod, data_final, p, tamanho))
        if rp["ok"]:
            regs.extend(rp["json"].get("data") or [])
        else:
            erro = erro or rp["erro"]
    return {"uf": uf, "mod": mod, "regs": regs, "erro": erro}


# ----------------------------------------------------------------- registros
def normalizar_registro(r):
    org = r.get("orgaoEntidade") or {}
    un = r.get("unidadeOrgao") or {}
    cnpj = org.get("cnpj") or ""
    ano, seq = r.get("anoCompra"), r.get("sequencialCompra")
    link = "https://pncp.gov.br/app/editais/%s/%s/%s" % (cnpj, ano, seq) if (cnpj and ano and seq) else ""
    valor = r.get("valorTotalEstimado")
    return {
        "id": r.get("numeroControlePNCP") or "%s-%s-%s" % (cnpj, ano, seq),
        "orgao": str(org.get("razaoSocial") or "").strip(),
        "unidade": str(un.get("nomeUnidade") or "").strip(),
        "uf": un.get("ufSigla") or "",
        "municipio": un.get("municipioNome") or "",
        "objeto": str(r.get("objetoCompra") or "").strip(),
        "modalidade": r.get("modalidadeNome") or "",
        "situacao": r.get("situacaoCompraNome") or "",
        "numero": r.get("numeroCompra") or "",
        "ano": ano,
        "abertura": r.get("dataAberturaProposta"),
        "encerramento": r.get("dataEncerramentoProposta"),
        "valor": valor if isinstance(valor, (int, float)) and not isinstance(valor, bool) else None,
        "link_pncp": link,
        "link_origem": r.get("linkSistemaOrigem") or "",
    }


def filtrar(regs, rx_inc, rx_exc, limite_encerradas, coletados):
    for r in regs:
        rec = normalizar_registro(r)
        if rec["encerramento"] and rec["encerramento"] < limite_encerradas:
            continue
        texto = normalizar(rec["objeto"] + " " + rec["orgao"])
        rec["relevante"] = bool(rx_inc and rx_inc.search(texto)) and not (rx_exc and rx_exc.search(texto))
        rec["rodoviario"] = bool(RX_ORGAO_RODOVIARIO.search(normalizar(rec["orgao"])))
        if rec["relevante"] or rec["rodoviario"]:
            coletados[rec["id"]] = rec


def carregar_anterior():
    try:
        with open(ARQUIVO_SAIDA, encoding="utf-8") as f:
            return {i["id"]: i for i in json.load(f).get("itens", [])}
    except (OSError, ValueError, KeyError):
        return {}


def mesclar(coletados, anteriores, ts, limite_encerradas):
    """Mantém 'primeira_vez' de quem já era conhecido e guarda encerradas recentes."""
    saida = {}
    for id_, rec in coletados.items():
        ant = anteriores.get(id_)
        rec["primeira_vez"] = (ant or {}).get("primeira_vez") or ts
        rec["ultima_vez"] = ts
        saida[id_] = rec
    for id_, ant in anteriores.items():
        if id_ in saida:
            continue
        enc = ant.get("encerramento")
        if enc and enc >= limite_encerradas:  # sumiu da consulta mas ainda é recente: guarda
            saida[id_] = ant
    return list(saida.values())


# ------------------------------------------------------------------------ main
def main():
    inicio = agora()
    ts = iso(inicio)
    data_final = (inicio + timedelta(days=DIAS_A_FRENTE)).strftime("%Y%m%d")
    limite_encerradas = iso(inicio - timedelta(days=DIAS_GUARDAR_ENCERRADAS))
    rx_inc, rx_exc = montar_regex(PALAVRAS_CHAVE), montar_regex(PALAVRAS_EXCLUIR)

    pares = [(uf, mod, data_final) for uf in UFS for mod in MODALIDADES]
    print("Consultando %d combinações estado x modalidade..." % len(pares), flush=True)
    coletados, erros, ok = {}, [], 0
    with ThreadPoolExecutor(max_workers=PARALELO) as pool:
        for res in pool.map(coletar_par, pares):
            if res["erro"]:
                erros.append("%s/%s: %s" % (res["uf"], res["mod"], res["erro"]))
            if not res["erro"] or res["regs"]:
                ok += 1
            filtrar(res["regs"], rx_inc, rx_exc, limite_encerradas, coletados)

    # Se quase tudo falhou, NÃO sobrescreve: o site continua mostrando o último resultado bom.
    if ok < len(pares) * 0.5:
        print("Muitas consultas falharam (%d de %d). Mantendo o arquivo anterior." % (len(pares) - ok, len(pares)))
        for e in erros[:10]:
            print(" -", e)
        sys.exit(1)

    itens = mesclar(coletados, carregar_anterior(), ts, limite_encerradas)
    itens.sort(key=lambda i: i.get("encerramento") or "9999")
    saida = {
        "gerado_em": ts,
        "consultas": len(pares),
        "consultas_com_erro": len(pares) - ok,
        "itens": itens,
    }
    with open(ARQUIVO_SAIDA, "w", encoding="utf-8") as f:
        json.dump(saida, f, ensure_ascii=False, indent=0)
    print("Pronto: %d licitações gravadas (%d consultas com erro)." % (len(itens), len(pares) - ok))
    for e in erros[:10]:
        print(" -", e)


if __name__ == "__main__":
    main()
