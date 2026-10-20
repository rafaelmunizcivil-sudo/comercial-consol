#!/usr/bin/env python3
"""
Radar de Licitacoes - CONSOL
Coletor: consulta o PNCP (Portal Nacional de Contratacoes Publicas), filtra o que
interessa e grava licitacoes.json. Roda sozinho no GitHub Actions (veja
.github/workflows/coletar.yml). Usa so a biblioteca padrao do Python.

Para ajustar o que e "relevante", edite as listas PALAVRAS_CHAVE e PALAVRAS_EXCLUIR
logo abaixo (pode editar direto no site do GitHub, no lapis).

Modos:
  python coletar.py            coleta e grava licitacoes.json (+ novas.md se houver novas)
  python coletar.py --prazos   le licitacoes.json e grava prazos.md (o que encerra logo)
"""
import json
import os
import threading
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone

try:
    from zoneinfo import ZoneInfo
    FUSO = ZoneInfo("America/Sao_Paulo")
except Exception:  # sem base de fusos: o Brasil esta sem horario de verao (UTC-3)
    FUSO = timezone(timedelta(hours=-3))

# ----------------------------------------------------------------- configuracao

UFS = ["AC", "AL", "AP", "AM", "BA", "CE", "DF", "ES", "GO", "MA", "MT", "MS", "MG", "PA",
       "PB", "PR", "PE", "PI", "RJ", "RN", "RS", "RO", "RR", "SC", "SP", "SE", "TO"]

# Modalidades do PNCP: 3 concurso, 4 concorrencia eletronica, 5 concorrencia presencial,
# 6 pregao eletronico, 7 pregao presencial, 12 credenciamento.
MODALIDADES = [3, 4, 5, 6, 7, 12]

# Uma licitacao e "relevante" se o objeto ou o orgao tiver alguma destas palavras
# (sem acento, minusculas). Sem $ no fim: vale qualquer palavra que COMECE assim.
# Com $ no fim: so vale a palavra inteira.
PALAVRAS_CHAVE = [
    "projeto", "anteprojeto", "supervis", "gerenciamento", "fiscaliza", "estudo",
    "topograf", "geotecn", "sondagem", "rodovi", "estrada", "pavimen", "ponte",
    "obra de arte", "oae", "drenagem", "ambiental", "licenciamento", "consultoria",
    "levantamento", "aerolevantamento", "sinaliza", "restaura", "conserva",
    "recupera", "melhoramento", "duplica", "terraplen", "contencao", "desapropria",
    "engenharia", "viabilidade", "geoprocessamento", "cadastro", "bim$",
]

# Se aparecer qualquer uma destas, deixa de ser "relevante".
PALAVRAS_EXCLUIR = [
    "medicamento", "merenda", "alimenticio", "material de limpeza",
    "material de expediente", "uniforme", "aquisicao de veiculo",
]

DIAS_A_FRENTE = 180        # consulta propostas que encerram ate daqui a N dias
DIAS_GUARDAR = 30          # quanto tempo manter licitacoes ja encerradas
DIAS_ALERTA_PRAZO = 3      # o aviso diario de prazos olha ate N dias a frente
TAMANHO_PAGINA = 50        # a API aceita no minimo 10; se recusar 50, cai para 10
PARALELO = 2               # consultas ao mesmo tempo (o PNCP limita a velocidade: erro 429)
INTERVALO = 0.6            # segundos minimos entre duas requisicoes (somando todas as consultas)
TEMPO_MAXIMO_MIN = 70      # nunca passar disso (o GitHub corta em 90)
PAGINAS_MAXIMO = 200
MINIMO_DE_SUCESSO = 0.5    # com menos de 50% das consultas ok, nao sobrescreve a lista

API = "https://pncp.gov.br/api/consulta/v1/contratacoes/proposta"
RX_ORGAO_RODOVIARIO = re.compile(
    r"\b(der|deer|dnit|daer|derba|goinfra|agesul|ageto|sinfra|seinfra|sie|deinfra|dertins"
    r"|departamento de estradas|departamento nacional de infraestrutura|"
    r"infraestrutura|transportes|rodagem)\b"
)

ARQUIVO = os.environ.get("RADAR_SAIDA", "licitacoes.json")
ARQ_AVISAR = "avisar.txt"
ARQ_MOCK = os.environ.get("RADAR_MOCK")      # so para testes: lista de registros simulados


# -------------------------------------------------------------------- utilidades

def agora():
    return datetime.now(FUSO).replace(tzinfo=None)


def iso(d):
    return d.isoformat(timespec="seconds")


def sem_acento(s):
    s = unicodedata.normalize("NFKD", str(s or ""))
    return "".join(c for c in s if not unicodedata.combining(c)).lower()


def montar_regex(lista):
    partes = []
    for kw in lista:
        kw = sem_acento(kw).strip()
        if not kw:
            continue
        fim = ""
        if kw.endswith("$"):
            kw, fim = kw[:-1], r"\b"
        partes.append(r"\b" + re.escape(kw) + fim)
    return re.compile("|".join(partes)) if partes else None


def ler_json(caminho, padrao):
    try:
        with open(caminho, "r", encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return padrao


def gravar_json(caminho, obj):
    tmp = caminho + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, caminho)


def lista_de_itens(dados):
    itens = (dados or {}).get("itens") or []
    return list(itens.values()) if isinstance(itens, dict) else list(itens)


def usuarios_para_avisar():
    nomes = []
    try:
        with open(ARQ_AVISAR, "r", encoding="utf-8") as f:
            for linha in f:
                nome = linha.split("#")[0].strip().lstrip("@")
                if re.fullmatch(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})", nome):
                    nomes.append("@" + nome)
    except FileNotFoundError:
        pass
    return nomes


def limpar_md(texto, limite=260):
    t = re.sub(r"\s+", " ", str(texto or "")).strip()
    if len(t) > limite:
        t = t[:limite].rstrip() + "..."
    t = t.replace("@", "@​").replace("<", "&lt;").replace(">", "&gt;")
    return t.replace("[", "\\[").replace("]", "\\]")


def moeda(v):
    if not isinstance(v, (int, float)):
        return "valor nao informado"
    return "R$ " + format(v, ",.2f").replace(",", "X").replace(".", ",").replace("X", ".")


def data_br(s):
    m = re.match(r"(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2})", s or "")
    return "%s/%s/%s %sh%s" % (m.group(3), m.group(2), m.group(1), m.group(4), m.group(5)) if m else "sem prazo informado"


def linha_md(r):
    local = "/".join(x for x in (r.get("municipio"), r.get("uf")) if x)
    link = r.get("link_pncp") or ""
    final = " - [edital no PNCP](%s)" % link if link.startswith("https://") else ""
    return "- **%s** | %s (%s)  \n  %s  \n  %s%s\n" % (
        data_br(r.get("encerramento")), limpar_md(r.get("orgao"), 90), limpar_md(local, 60),
        limpar_md(r.get("objeto")), moeda(r.get("valor")), final)


# ------------------------------------------------------------------- PNCP

_trava = threading.Lock()
_proxima = [0.0]       # instante em que a proxima requisicao pode sair (vale para todas as consultas)


def _esperar_vez(extra=0.0):
    """Todas as consultas passam por aqui: mantem o ritmo e respeita pausas pedidas pelo PNCP."""
    with _trava:
        if extra:
            _proxima[0] = max(_proxima[0], time.time() + extra)
        agora_t = time.time()
        espera = max(0.0, _proxima[0] - agora_t)
        _proxima[0] = max(agora_t, _proxima[0]) + INTERVALO
    if espera:
        time.sleep(espera)


def pedir(url, tentativas=7):
    ultimo = None
    for i in range(tentativas):
        _esperar_vez()
        try:
            req = urllib.request.Request(url, headers={
                "Accept": "application/json", "User-Agent": "CONSOL-RadarLicitacoes/2.0"})
            with urllib.request.urlopen(req, timeout=60) as r:
                corpo = r.read()
            return json.loads(corpo) if corpo else {"data": [], "totalPaginas": 0}
        except urllib.error.HTTPError as e:
            ultimo = e
            if e.code == 400:
                raise
            if e.code == 429 and i < tentativas - 1:
                try:
                    pausa = float(e.headers.get("Retry-After") or 0)
                except (TypeError, ValueError):
                    pausa = 0
                _esperar_vez(extra=max(pausa, 20 * (i + 1)))   # todas as consultas param juntas
                continue
            if e.code in (500, 502, 503, 504) and i < tentativas - 1:
                time.sleep(3 * (i + 1))
                continue
            raise
        except (urllib.error.URLError, TimeoutError, ConnectionError, json.JSONDecodeError) as e:
            ultimo = e
            if i < tentativas - 1:
                time.sleep(3 * (i + 1))
                continue
            raise
    raise ultimo


def coletar_par(uf, modalidade, data_final, prazo_final):
    if ARQ_MOCK:
        with open(ARQ_MOCK, "r", encoding="utf-8") as f:
            todos = json.load(f)
        return [r for r in todos if (r.get("unidadeOrgao") or {}).get("ufSigla") == uf
                and str(r.get("modalidadeId")) == str(modalidade)]
    itens, tamanho, pagina = [], TAMANHO_PAGINA, 1
    while True:
        if time.time() > prazo_final:
            raise TimeoutError("tempo maximo da coleta")
        params = {"dataFinal": data_final, "codigoModalidadeContratacao": modalidade,
                  "uf": uf, "pagina": pagina, "tamanhoPagina": tamanho}
        try:
            dados = pedir(API + "?" + urllib.parse.urlencode(params))
        except urllib.error.HTTPError as e:
            if e.code == 400 and tamanho > 10:
                tamanho, pagina, itens = 10, 1, []
                continue
            raise
        lote = dados.get("data") or []
        itens.extend(lote)
        total = min(dados.get("totalPaginas") or 0, PAGINAS_MAXIMO)
        if not lote or pagina >= total:
            return itens
        pagina += 1


def normalizar(r):
    org = r.get("orgaoEntidade") or {}
    un = r.get("unidadeOrgao") or {}
    cnpj, ano, seq = org.get("cnpj") or "", r.get("anoCompra"), r.get("sequencialCompra")
    return {
        "id": r.get("numeroControlePNCP") or "%s-%s-%s" % (cnpj, ano, seq),
        "orgao": (org.get("razaoSocial") or "").strip(),
        "unidade": (un.get("nomeUnidade") or "").strip(),
        "uf": un.get("ufSigla") or "",
        "municipio": un.get("municipioNome") or "",
        "objeto": (r.get("objetoCompra") or "").strip(),
        "modalidade": r.get("modalidadeNome") or "",
        "situacao": r.get("situacaoCompraNome") or "",
        "numero": r.get("numeroCompra") or "",
        "ano": ano,
        "abertura": r.get("dataAberturaProposta"),
        "encerramento": r.get("dataEncerramentoProposta"),
        "valor": r.get("valorTotalEstimado"),
        "link_pncp": ("https://pncp.gov.br/app/editais/%s/%s/%s" % (cnpj, ano, seq)) if cnpj and ano and seq else "",
        "link_origem": r.get("linkSistemaOrigem") or "",
    }


# ------------------------------------------------------------------- modos

def coletar():
    inicio = time.time()
    prazo_final = inicio + TEMPO_MAXIMO_MIN * 60
    data_final = (agora() + timedelta(days=DIAS_A_FRENTE)).strftime("%Y%m%d")
    pares = [(u, m) for u in UFS for m in MODALIDADES]
    rx_inc, rx_exc = montar_regex(PALAVRAS_CHAVE), montar_regex(PALAVRAS_EXCLUIR)
    limite_encerradas = iso(agora() - timedelta(days=DIAS_GUARDAR))
    coletados, ok, erros = {}, 0, []

    def rodada(lista):
        nonlocal ok
        falhas = []
        with ThreadPoolExecutor(max_workers=PARALELO) as ex:
            futuros = {ex.submit(coletar_par, u, m, data_final, prazo_final): (u, m) for u, m in lista}
            for f in as_completed(futuros):
                u, m = futuros[f]
                try:
                    registros = f.result()
                except Exception as e:  # noqa: BLE001 - registrar e seguir
                    falhas.append((u, m, str(e)))
                    continue
                ok += 1
                for r in registros:
                    rec = normalizar(r)
                    enc = rec["encerramento"]
                    if isinstance(enc, str) and enc < limite_encerradas:
                        continue
                    texto = sem_acento(rec["objeto"] + " " + rec["orgao"])
                    rec["relevante"] = bool(rx_inc and rx_inc.search(texto)) and not (rx_exc and rx_exc.search(texto))
                    rec["rodoviario"] = bool(RX_ORGAO_RODOVIARIO.search(sem_acento(rec["orgao"])))
                    if rec["relevante"] or rec["rodoviario"]:
                        coletados[rec["id"]] = rec
        return falhas

    falhas = rodada(pares)
    if falhas and time.time() < prazo_final:      # uma segunda chance para o que falhou
        print("Repetindo %d consulta(s) que falharam..." % len(falhas))
        falhas = rodada([(u, m) for u, m, _ in falhas])
    erros = ["%s/%s: %s" % f for f in falhas]

    print("Consultas ok: %d de %d (%.0f s). Itens guardados desta coleta: %d"
          % (ok, len(pares), time.time() - inicio, len(coletados)))
    for e in erros[:15]:
        print("  erro:", e)
    if ok < len(pares) * MINIMO_DE_SUCESSO:
        print("Poucas consultas deram certo; a lista anterior foi mantida.")
        sys.exit(1)

    anterior = ler_json(ARQUIVO, {})
    antigos = {r["id"]: r for r in lista_de_itens(anterior) if r.get("id")}
    primeira = not antigos
    agora_s = iso(agora())
    novas = []
    for id_, rec in coletados.items():
        ant = antigos.get(id_)
        rec["primeira_vez"] = ant["primeira_vez"] if ant and ant.get("primeira_vez") else agora_s
        rec["ultima_vez"] = agora_s
        if not ant and rec["relevante"]:
            novas.append(rec)
        antigos[id_] = rec
    itens = [r for r in antigos.values()
             if not isinstance(r.get("encerramento"), str) or r["encerramento"] >= limite_encerradas]
    itens.sort(key=lambda r: r.get("encerramento") or "9999")
    gravar_json(ARQUIVO, {"gerado_em": agora_s, "consultas": len(pares),
                          "consultas_com_erro": len(pares) - ok, "itens": itens})
    print("Lista gravada: %d licitacoes (%d novas relevantes)" % (len(itens), len(novas)))

    # Aviso de novas (vira uma Issue no GitHub, que manda e-mail). Nao avisa na primeira coleta.
    if os.path.exists("novas.md"):
        os.remove("novas.md")
    novas = [r for r in novas if not r.get("encerramento") or r["encerramento"] >= agora_s]
    if novas and not primeira:
        novas.sort(key=lambda r: r.get("encerramento") or "9999")
        corpo = " ".join(usuarios_para_avisar()) + "\n\n" if usuarios_para_avisar() else ""
        corpo += "%d nova(s) licitacao(oes) relevante(s):\n\n" % len(novas)
        corpo += "\n".join(linha_md(r) for r in novas[:30])
        if len(novas) > 30:
            corpo += "\n... e mais %d. Veja todas no site.\n" % (len(novas) - 30)
        with open("novas.md", "w", encoding="utf-8") as f:
            f.write(corpo)


def prazos():
    if os.path.exists("prazos.md"):
        os.remove("prazos.md")
    dados = ler_json(ARQUIVO, {})
    ini, fim = iso(agora()), iso(agora() + timedelta(days=DIAS_ALERTA_PRAZO))
    lista = [r for r in lista_de_itens(dados)
             if r.get("relevante") and r.get("encerramento") and ini <= r["encerramento"] <= fim]
    lista.sort(key=lambda r: r["encerramento"])
    print("Encerram em ate %d dias: %d" % (DIAS_ALERTA_PRAZO, len(lista)))
    if not lista:
        return
    corpo = " ".join(usuarios_para_avisar()) + "\n\n" if usuarios_para_avisar() else ""
    corpo += "%d licitacao(oes) relevante(s) encerram em ate %d dias:\n\n" % (len(lista), DIAS_ALERTA_PRAZO)
    corpo += "\n".join(linha_md(r) for r in lista[:40])
    with open("prazos.md", "w", encoding="utf-8") as f:
        f.write(corpo)


if __name__ == "__main__":
    if "--prazos" in sys.argv:
        prazos()
    else:
        coletar()
