"""TiendaTrack · aplicación del negocio (productos, inventario, punto de venta, caja, clientes).
Es una app aparte de PROCSIS. El acceso llega desde PROCSIS con un token firmado (SSO) y la vigencia
de la cuenta (demo / plan activo / vencido) se consulta a la API de PROCSIS.
Variables de entorno: SECRET_KEY, DATABASE_URL, PROCSIS_URL, TIENDATRACK_API_KEY, RESEND_API_KEY, RESEND_FROM. Ver README.md."""
import base64
import calendar
import csv
import hashlib
import hmac
import io
import json
import os
import re
import secrets
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

from jinja2 import ChoiceLoader, DictLoader, FileSystemLoader
from flask import (Flask, Response, abort, flash, jsonify, redirect, render_template, request,
                   session, url_for)

from werkzeug.security import check_password_hash, generate_password_hash

import db

BASE = os.path.dirname(os.path.abspath(__file__))
try:  # plantillas y estilos copiados dentro de un .py (ver dev/embeber.py): sirven de respaldo si faltan las carpetas
    from _embebidos import STATIC as _STATIC_EMB, TEMPLATES as _TEMPLATES_EMB
except ImportError:
    _STATIC_EMB, _TEMPLATES_EMB = {}, {}

app = Flask(__name__, static_folder=None, template_folder=None)
app.jinja_loader = ChoiceLoader([FileSystemLoader(os.path.join(BASE, "templates")), DictLoader(_TEMPLATES_EMB)])
app.secret_key = os.environ.get("SECRET_KEY") or "cambia-esta-clave-en-produccion"
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax",
                  SESSION_COOKIE_SECURE=os.environ.get("TT_COOKIE_SECURE", "1") == "1",
                  PERMANENT_SESSION_LIFETIME=timedelta(hours=12), MAX_CONTENT_LENGTH=1024 * 1024)
app.teardown_appcontext(db.cerrar)

PROCSIS_URL = (os.environ.get("PROCSIS_URL") or "").rstrip("/")
API_KEY = (os.environ.get("TIENDATRACK_API_KEY") or "").strip()
TZ = ZoneInfo("America/Bogota")
METODOS = (("efectivo", "Efectivo"), ("tarjeta", "Tarjeta"), ("transferencia", "Transferencia"), ("nequi", "Nequi / Daviplata"))
METODOS_D = dict(METODOS)
REVALIDAR_S = 600          # cada cuánto se vuelve a preguntar a PROCSIS si la cuenta sigue vigente
GRACIA_S = 24 * 3600       # si PROCSIS no responde, se conserva el último acceso conocido por este tiempo

_TABLAS = {"ok": False}
_HASH_FALSO = generate_password_hash("no-es-una-clave", method="pbkdf2:sha256")
MAX_FALLOS_CORREO, MAX_FALLOS_IP, VENTANA_FALLOS_MIN = 5, 20, 10


# ───────────────────────── utilidades ─────────────────────────
def ahora():
    return datetime.now(TZ).replace(tzinfo=None)


def ahora_s():
    return ahora().strftime("%Y-%m-%d %H:%M:%S")


def hoy_s():
    return ahora().strftime("%Y-%m-%d")


def entero(v, defecto=0, minimo=0, maximo=10 ** 10):
    try:
        n = int(re.sub(r"[^\d-]", "", str(v or "")) or defecto)
    except Exception:
        n = defecto
    return max(minimo, min(maximo, n))


def limpio(v, largo=160):
    return re.sub(r"\s+", " ", str(v or "")).strip()[:largo]


@app.template_filter("cop")
def f_cop(v):
    try:
        return "$" + "{:,.0f}".format(int(v or 0)).replace(",", ".")
    except Exception:
        return "$0"


@app.template_filter("fecha")
def f_fecha(s):
    meses = ("ene", "feb", "mar", "abr", "may", "jun", "jul", "ago", "sep", "oct", "nov", "dic")
    try:
        d = datetime.strptime((s or "")[:19], "%Y-%m-%d %H:%M:%S")
        h = d.hour % 12 or 12
        return "%d %s %s, %d:%02d %s" % (d.day, meses[d.month - 1], d.year, h, d.minute, "a. m." if d.hour < 12 else "p. m.")
    except Exception:
        return s or "—"


@app.template_filter("dia")
def f_dia(s):
    meses = ("ene", "feb", "mar", "abr", "may", "jun", "jul", "ago", "sep", "oct", "nov", "dic")
    try:
        a, m, d = (s or "")[:10].split("-")
        return "%d %s" % (int(d), meses[int(m) - 1])
    except Exception:
        return s or "—"


def _migrar_registro():
    """Tabla de PINs y columnas extra del negocio. Es idempotente: si la columna ya existe, el ALTER falla y se ignora."""
    for ddl in (
        "CREATE TABLE IF NOT EXISTS registro_pins (email VARCHAR(160) PRIMARY KEY, pin_hash VARCHAR(80), intentos INTEGER DEFAULT 0, "
        "vence VARCHAR(20), enviado_en VARCHAR(20))",
        "ALTER TABLE negocios ADD COLUMN nit VARCHAR(30) DEFAULT ''",
        "ALTER TABLE negocios ADD COLUMN titular VARCHAR(160) DEFAULT ''",
        "ALTER TABLE negocios ADD COLUMN usuarios_est INTEGER DEFAULT 0",
    ):
        try:
            db.x(ddl)
            db.commit()
        except Exception:
            try:
                db.rollback()
            except Exception:
                pass


def _asegurar_tablas():
    if not _TABLAS["ok"]:
        db.crear_tablas()
        _migrar_registro()
        _TABLAS["ok"] = True


# ───────────────────────── SSO desde PROCSIS ─────────────────────────
def _firmar(datos):
    cuerpo = base64.urlsafe_b64encode(json.dumps(datos, separators=(",", ":")).encode()).decode().rstrip("=")
    firma = hmac.new(API_KEY.encode(), cuerpo.encode(), hashlib.sha256).hexdigest()
    return cuerpo + "." + firma


def _leer_token(token):
    """Devuelve el correo si el token es válido y no ha vencido; si no, None."""
    if not API_KEY or "." not in (token or ""):
        return None
    cuerpo, firma = token.rsplit(".", 1)
    esperada = hmac.new(API_KEY.encode(), cuerpo.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(esperada, firma):
        return None
    try:
        datos = json.loads(base64.urlsafe_b64decode(cuerpo + "=" * (-len(cuerpo) % 4)))
        if int(datos.get("x", 0)) < time.time():
            return None
        return str(datos.get("e") or "").strip().lower() or None
    except Exception:
        return None


def _consultar_procsis(email):
    """Pregunta a PROCSIS el estado de la cuenta. Devuelve dict o None si no se pudo consultar."""
    if not (PROCSIS_URL and API_KEY):
        return None
    url = PROCSIS_URL + "/api/v1/tiendatrack/cuenta?" + urllib.parse.urlencode({"email": email})
    req = urllib.request.Request(url, headers={"X-API-Key": API_KEY, "User-Agent": "tiendatrack-app"})
    try:
        with urllib.request.urlopen(req, timeout=6) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return {"ok": False, "acceso": False, "estado": "sin_cuenta"}
        return None
    except Exception:
        return None


def _guardar_acceso(info):
    plan = info.get("plan") or {}
    session["acc"] = bool(info.get("acceso"))
    session["estado"] = info.get("estado") or ""
    session["vence"] = info.get("vence") or ""
    session["dias"] = int(info.get("dias_restantes") or 0)
    session["plan"] = {"nombre": plan.get("nombre") or "", "max_productos": int(plan.get("max_productos") or 0),
                       "max_usuarios": int(plan.get("max_usuarios") or 0), "max_sucursales": int(plan.get("max_sucursales") or 0)}
    session["acc_ts"] = int(time.time())


def _negocio_de(email, info):
    _asegurar_tablas()
    n = db.uno("SELECT id FROM negocios WHERE email=?", email)
    if n:
        db.x("UPDATE negocios SET nombre=?, segmento=? WHERE id=?", limpio(info.get("negocio")) or email, limpio(info.get("segmento"), 20) or "tienda", n["id"])
        db.commit()
        _guardar_extra(n["id"], info)
        return n["id"]
    nid = db.x("INSERT INTO negocios (email, nombre, segmento, creado_en) VALUES (?,?,?,?) RETURNING id",
               email, limpio(info.get("negocio")) or email, limpio(info.get("segmento"), 20) or "tienda", ahora_s())
    db.commit()
    _guardar_extra(nid, info)
    return nid


def _guardar_extra(negocio_id, info):
    """NIT, titular y número de usuarios que PROCSIS tiene de la cuenta (si los hay). Nunca debe tumbar el inicio de sesión."""
    nit, titular, usu = limpio(info.get("nit"), 30), limpio(info.get("titular")), entero(info.get("usuarios_est"), 0, 0, 1000)
    if not (nit or titular or usu):
        return
    try:
        db.x("UPDATE negocios SET nit=?, titular=?, usuarios_est=? WHERE id=?", nit, titular, usu, negocio_id)
        db.commit()
    except Exception:
        try:
            db.rollback()
        except Exception:
            pass


@app.route("/sso")
def sso():
    email = _leer_token(request.args.get("t", ""))
    if not email:
        return render_template("bloqueado.html", titulo="Enlace no válido", detalle="El enlace de acceso venció o no es válido. Vuelve a entrar desde tu cuenta de PROCSIS.", procsis=PROCSIS_URL), 401
    info = _consultar_procsis(email)
    if info is None:
        return render_template("bloqueado.html", titulo="No pudimos verificar tu cuenta", detalle="PROCSIS no respondió. Intenta de nuevo en un minuto.", procsis=PROCSIS_URL), 503
    if not info.get("ok"):
        return render_template("bloqueado.html", titulo="Cuenta no encontrada", detalle="No encontramos una cuenta de TiendaTrack con ese correo.", procsis=PROCSIS_URL), 403
    return _iniciar_sesion(email, info)


def _iniciar_sesion(email, info):
    """Abre la sesión del negocio a partir de lo que respondió PROCSIS."""
    session.clear()
    session.permanent = True
    session["email"] = email
    _guardar_acceso(info)
    session["neg_id"] = _negocio_de(email, info)
    session["negocio"] = limpio(info.get("negocio")) or email
    session["segmento"] = limpio(info.get("segmento"), 20) or "tienda"
    session["csrf"] = secrets.token_urlsafe(24)
    return redirect(url_for("inicio") if session["acc"] else url_for("bloqueado"))


# ───────────────────────── login (Google vía PROCSIS, o correo y clave) ─────────────────────────
def _ip():
    return (request.headers.get("X-Forwarded-For", "").split(",")[0].strip() or request.remote_addr or "?")[:60]


def _fallos(clave):
    desde = (ahora() - timedelta(minutes=VENTANA_FALLOS_MIN)).strftime("%Y-%m-%d %H:%M:%S")
    return int(db.uno("SELECT COUNT(*) AS c FROM login_fallos WHERE clave=? AND creado_en>=?", clave, desde)["c"])


def _login_bloqueado(email):
    return _fallos("e:" + email) >= MAX_FALLOS_CORREO or _fallos("i:" + _ip()) >= MAX_FALLOS_IP


def _registrar_fallo(email):
    ts = ahora_s()
    db.x("INSERT INTO login_fallos (clave, creado_en) VALUES (?,?)", "e:" + email, ts)
    db.x("INSERT INTO login_fallos (clave, creado_en) VALUES (?,?)", "i:" + _ip(), ts)
    db.x("DELETE FROM login_fallos WHERE creado_en<?", (ahora() - timedelta(days=1)).strftime("%Y-%m-%d %H:%M:%S"))
    db.commit()


@app.route("/login", methods=["GET", "POST"])
def login():
    if session.get("neg_id") and session.get("acc"):
        return redirect(url_for("inicio"))
    error = ""
    email = ""
    aviso = "Ese correo ya tiene una cuenta. Ingresa con tu clave o continúa con Google." if request.args.get("ya") else ""
    if request.method == "POST":
        email = limpio(request.form.get("email"), 160).lower()
        clave = request.form.get("clave") or ""
        if _login_bloqueado(email):
            error = "Demasiados intentos. Espera %d minutos e inténtalo de nuevo." % VENTANA_FALLOS_MIN
        else:
            n = db.uno("SELECT clave_hash FROM negocios WHERE email=?", email)
            hash_ = (n or {}).get("clave_hash") or _HASH_FALSO
            valida = check_password_hash(hash_, clave) and bool(n and n["clave_hash"])
            if not valida:
                _registrar_fallo(email)
                error = "Correo o clave incorrectos. Si aún no tienes clave, entra con Google y créala en Configuración."
            else:
                info = _consultar_procsis(email)
                if info is None:
                    error = "No pudimos verificar tu cuenta con PROCSIS. Intenta de nuevo en un minuto."
                elif not info.get("ok"):
                    error = "No encontramos una cuenta activa con ese correo."
                else:
                    return _iniciar_sesion(email, info)
    return render_template("login.html", error=error, aviso=aviso, email=email, google=bool(PROCSIS_URL), google_url=_google_url(),
                           registro_url=url_for("registro"), planes_url=(PROCSIS_URL + "/tt") if PROCSIS_URL else "", dias_demo=DIAS_DEMO), (401 if error else 200)


@app.route("/salir")
def salir():
    session.clear()
    return redirect(url_for("login"))


# ───────────────────────── registro propio: correo → PIN (Resend) → datos del negocio ─────────────────────────
# Flujo: 1) el correo recibe un PIN de 6 dígitos por Resend, 2) se verifica el PIN (vence, máx. intentos),
# 3) el formulario del negocio (nombre, NIT, usuarios...) crea la cuenta en PROCSIS con la demo gratis y abre la sesión.
# Con Google no hace falta PIN: Google ya verificó el correo; ese camino lo atiende PROCSIS (/tt/google/inicio).
DIAS_DEMO = 15
PIN_VIDA_MIN, PIN_MAX_INTENTOS, PIN_ESPERA_S = 10, 5, 60
PIN_ENVIOS_CORREO_H, PIN_ENVIOS_IP_H = 5, 15
REG_VIDA_S = 30 * 60        # tiempo para terminar el formulario después de verificar el PIN
SEGMENTOS = (("tienda", "Tienda"), ("ropa", "Tienda de ropa"), ("restaurante", "Restaurante"), ("otro", "Otro negocio"))
_CORREO_RE = re.compile(r"^[^@\s]{1,64}@[^@\s]{1,120}\.[^@\s.]{2,}$")


def _google_url():
    return (PROCSIS_URL + "/tt/google/inicio") if PROCSIS_URL else ""


def _csrf_reg():
    t = session.get("rcsrf")
    if not t:
        t = secrets.token_urlsafe(24)
        session["rcsrf"] = t
    return t


def _csrf_reg_ok():
    return hmac.compare_digest(str(request.form.get("csrf") or ""), str(session.get("rcsrf") or "x"))


def _pin_hash(email, pin):
    return hmac.new(str(app.secret_key).encode(), ("pin|%s|%s" % (email, pin)).encode(), hashlib.sha256).hexdigest()


def _conteo(clave, minutos):
    desde = (ahora() - timedelta(minutes=minutos)).strftime("%Y-%m-%d %H:%M:%S")
    return int(db.uno("SELECT COUNT(*) AS c FROM login_fallos WHERE clave=? AND creado_en>=?", clave, desde)["c"])


def _anotar(*claves):
    ts = ahora_s()
    for k in claves:
        db.x("INSERT INTO login_fallos (clave, creado_en) VALUES (?,?)", k, ts)
    db.commit()


def _oculto(email):
    u, _, d = email.partition("@")
    return u[:2] + "•" * max(1, len(u) - 2) + "@" + d


def nit_normalizado(valor):
    """NIT colombiano con o sin dígito de verificación. Devuelve (nit, error). Si trae DV, se valida."""
    s = re.sub(r"[^0-9-]", "", str(valor or ""))
    base, _, dv = s.partition("-")
    if not base.isdigit() or not (5 <= len(base) <= 12):
        return "", "Escribe un NIT o documento válido (solo números)."
    pesos = (3, 7, 13, 17, 19, 23, 29, 37, 41, 43, 47, 53, 59, 67, 71)
    r = sum(int(d) * p for d, p in zip(reversed(base), pesos)) % 11
    calc = str(r if r < 2 else 11 - r)
    if dv and dv != calc:
        return "", "El dígito de verificación del NIT no coincide. Revísalo."
    return base + "-" + calc, ""


def _enviar_resend(para, asunto, html, texto):
    """Envía un correo con Resend (HTTPS). Devuelve True si Resend lo aceptó."""
    llave = (os.environ.get("RESEND_API_KEY") or "").strip()
    if not llave:
        if os.environ.get("TT_DEV_PIN") == "1":  # solo para pruebas locales: el PIN sale por el log
            app.logger.warning("TT_DEV_PIN correo a %s: %s", para, texto)
            return True
        app.logger.error("Falta RESEND_API_KEY: no se puede enviar el PIN de registro.")
        return False
    de = (os.environ.get("RESEND_FROM") or "").strip() or "TiendaTrack <onboarding@resend.dev>"
    cuerpo = json.dumps({"from": de, "to": [para], "subject": asunto, "html": html, "text": texto}).encode("utf-8")
    req = urllib.request.Request("https://api.resend.com/emails", data=cuerpo, method="POST",
                                 headers={"Authorization": "Bearer " + llave, "Content-Type": "application/json", "User-Agent": "tiendatrack-app/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=10) as r:
            return 200 <= r.status < 300
    except urllib.error.HTTPError as e:
        app.logger.error("Resend rechazó el envío (%s): %s", e.code, e.read()[:300])
    except Exception:
        app.logger.exception("Resend falló")
    return False


def _correo_pin(email, pin):
    texto = ("Tu código de TiendaTrack es %s. Vence en %d minutos. "
             "Si no lo pediste, ignora este correo." % (pin, PIN_VIDA_MIN))
    html = (
        '<div style="background:#eaf1ff;padding:28px 12px;font-family:-apple-system,Segoe UI,Roboto,Arial,sans-serif">'
        '<div style="max-width:440px;margin:0 auto;background:#ffffff;border-radius:20px;overflow:hidden;'
        'box-shadow:0 12px 36px rgba(10,42,143,.16)">'
        '<div style="height:6px;background:linear-gradient(90deg,#0a2a8f,#12b5ff,#1fdc6a)"></div>'
        '<div style="padding:28px 28px 24px">'
        '<div style="font-size:22px;font-weight:800;color:#0a2a8f;letter-spacing:-.02em">Tienda<span style="color:#1fb85a">Track</span></div>'
        '<p style="color:#0b1437;font-size:16px;margin:18px 0 6px">Tu código para crear tu cuenta:</p>'
        '<div style="font-size:38px;font-weight:800;letter-spacing:.35em;color:#0a2a8f;background:#eef3ff;border-radius:14px;'
        'padding:16px 8px 16px 20px;text-align:center;margin:10px 0 16px">%s</div>'
        '<p style="color:#4b5b86;font-size:14px;line-height:1.5;margin:0">Vence en %d minutos. Si no lo pediste, ignora este correo: '
        'nadie podrá crear una cuenta con tu correo sin este código.</p>'
        '</div></div>'
        '<p style="text-align:center;color:#6b7aa3;font-size:12px;margin:14px 0 0">TiendaTrack · un producto de PROCSIS</p></div>'
    ) % (pin, PIN_VIDA_MIN)
    return _enviar_resend(email, "Tu código de TiendaTrack: " + pin, html, texto)


def _emitir_pin(email):
    """Genera, guarda y envía un PIN. Devuelve (ok, mensaje_de_error)."""
    if _conteo("pin:e:" + email, 60) >= PIN_ENVIOS_CORREO_H or _conteo("pin:i:" + _ip(), 60) >= PIN_ENVIOS_IP_H:
        return False, "Pediste demasiados códigos. Espera un rato e inténtalo de nuevo."
    pin = "%06d" % secrets.randbelow(10 ** 6)
    ts = ahora_s()
    vence = (ahora() + timedelta(minutes=PIN_VIDA_MIN)).strftime("%Y-%m-%d %H:%M:%S")
    db.x("DELETE FROM registro_pins WHERE email=?", email)
    db.x("INSERT INTO registro_pins (email, pin_hash, intentos, vence, enviado_en) VALUES (?,?,0,?,?)", email, _pin_hash(email, pin), vence, ts)
    _anotar("pin:e:" + email, "pin:i:" + _ip())
    if not _correo_pin(email, pin):
        db.x("DELETE FROM registro_pins WHERE email=?", email)
        db.commit()
        return False, "No pudimos enviar el código. Revisa el correo e inténtalo de nuevo en un minuto."
    return True, ""


def _espera_reenvio(email):
    f = db.uno("SELECT enviado_en FROM registro_pins WHERE email=?", email)
    if not f:
        return 0
    try:
        t = datetime.strptime(f["enviado_en"], "%Y-%m-%d %H:%M:%S")
    except Exception:
        return 0
    return max(0, PIN_ESPERA_S - int((ahora() - t).total_seconds()))


def _ctx_registro(paso, **extra):
    base = dict(paso=paso, rcsrf=_csrf_reg(), google_url=_google_url(), dias_demo=DIAS_DEMO, vida_min=PIN_VIDA_MIN, procsis=PROCSIS_URL,
                email=session.get("reg_email", ""), email_oculto=_oculto(session["reg_email"]) if session.get("reg_email") else "",
                segmentos=SEGMENTOS, error="", aviso="", f={})
    base.update(extra)
    return base


@app.route("/registro", methods=["GET", "POST"])
def registro():
    if session.get("neg_id") and session.get("acc"):
        return redirect(url_for("inicio"))
    if request.args.get("cambiar"):
        session.pop("reg_email", None)
        session.pop("reg_ok", None)
    error, email = "", limpio(request.form.get("email"), 160).lower() if request.method == "POST" else session.get("reg_email", "")
    if request.method == "POST":
        if not _csrf_reg_ok():
            error = "La página venció. Recárgala e inténtalo de nuevo."
        elif not _CORREO_RE.match(email):
            error = "Escribe un correo válido."
        else:
            # mismo trato exista o no la cuenta: así no se puede averiguar qué correos están registrados
            if session.get("reg_email") == email and _espera_reenvio(email) > 0:
                return redirect(url_for("registro_pin"))  # ya se envió hace poco: no se manda otro
            ok, msg = _emitir_pin(email)
            if ok:
                session["reg_email"] = email
                session.pop("reg_ok", None)
                return redirect(url_for("registro_pin"))
            error = msg
    return render_template("registro.html", **_ctx_registro(1, error=error, email=email)), (400 if error else 200)


@app.route("/registro/pin", methods=["GET", "POST"])
def registro_pin():
    email = session.get("reg_email")
    if not email:
        return redirect(url_for("registro"))
    error = aviso = ""
    if request.method == "POST":
        accion = request.form.get("accion")
        if not _csrf_reg_ok():
            error = "La página venció. Recárgala e inténtalo de nuevo."
        elif accion == "reenviar":
            espera = _espera_reenvio(email)
            if espera > 0:
                error = "Espera %d segundos para pedir otro código." % espera
            else:
                ok, msg = _emitir_pin(email)
                aviso, error = ("Te enviamos un código nuevo.", "") if ok else ("", msg)
        else:
            pin = re.sub(r"\D", "", request.form.get("pin") or "")[:6]
            fila = db.uno("SELECT pin_hash, intentos, vence FROM registro_pins WHERE email=?", email)
            if not fila or fila["vence"] < ahora_s():
                error = "El código venció. Pide uno nuevo."
            elif int(fila["intentos"]) >= PIN_MAX_INTENTOS:
                db.x("DELETE FROM registro_pins WHERE email=?", email)
                db.commit()
                error = "Demasiados intentos. Pide un código nuevo."
            elif len(pin) != 6 or not hmac.compare_digest(_pin_hash(email, pin), fila["pin_hash"]):
                db.x("UPDATE registro_pins SET intentos=intentos+1 WHERE email=?", email)
                db.commit()
                quedan = PIN_MAX_INTENTOS - int(fila["intentos"]) - 1
                error = "Código incorrecto. Te quedan %d intento%s." % (max(0, quedan), "" if quedan == 1 else "s")
            else:
                db.x("DELETE FROM registro_pins WHERE email=?", email)
                db.commit()
                session["reg_ok"] = int(time.time())
                return redirect(url_for("registro_datos"))
    return render_template("registro.html", **_ctx_registro(2, error=error, aviso=aviso)), (400 if error else 200)


def _crear_cuenta_procsis(datos):
    """Crea la cuenta (con su demo) en PROCSIS. Devuelve (código_http, json). Código 0 = no hubo respuesta."""
    if not (PROCSIS_URL and API_KEY):
        return 503, {}
    req = urllib.request.Request(PROCSIS_URL + "/api/v1/tiendatrack/registro", data=json.dumps(datos).encode("utf-8"), method="POST",
                                 headers={"X-API-Key": API_KEY, "Content-Type": "application/json", "User-Agent": "tiendatrack-app"})
    try:
        with urllib.request.urlopen(req, timeout=12) as r:
            return r.status, json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        try:
            return e.code, json.loads(e.read().decode("utf-8"))
        except Exception:
            return e.code, {}
    except Exception:
        return 0, {}


@app.route("/registro/datos", methods=["GET", "POST"])
def registro_datos():
    email = session.get("reg_email")
    if not email or int(time.time()) - int(session.get("reg_ok") or 0) > REG_VIDA_S:
        session.pop("reg_ok", None)
        return redirect(url_for("registro"))
    error, f = "", {}
    if request.method == "GET":
        info = _consultar_procsis(email)   # el correo ya está probado con el PIN, así que aquí sí se puede decir si existe
        if info and info.get("ok"):
            session.pop("reg_email", None)
            session.pop("reg_ok", None)
            return redirect(url_for("login", ya=1))
    else:
        f = {"nombre": limpio(request.form.get("nombre")), "negocio": limpio(request.form.get("negocio")), "nit": limpio(request.form.get("nit"), 20),
             "usuarios": entero(request.form.get("usuarios"), 1, 0, 1000), "segmento": request.form.get("segmento") or "tienda",
             "telefono": re.sub(r"[^0-9+]", "", request.form.get("telefono") or "")[:20], "acepto": bool(request.form.get("acepto"))}
        clave, repite = request.form.get("clave") or "", request.form.get("repite") or ""
        nit, err_nit = nit_normalizado(f["nit"])
        if not _csrf_reg_ok():
            error = "La página venció. Recárgala e inténtalo de nuevo."
        elif len(f["nombre"]) < 2:
            error = "Escribe tu nombre."
        elif len(f["negocio"]) < 2:
            error = "Escribe el nombre de tu negocio."
        elif err_nit:
            error = err_nit
        elif not 1 <= f["usuarios"] <= 50:
            error = "Indica cuántas personas usarán el sistema (de 1 a 50)."
        elif f["segmento"] not in dict(SEGMENTOS):
            error = "Elige el tipo de negocio."
        elif f["telefono"] and not 7 <= len(f["telefono"].lstrip("+")) <= 15:
            error = "El WhatsApp no parece válido. Déjalo vacío si prefieres no darlo."
        elif len(clave) < 8 or not re.search(r"[A-Za-z]", clave) or not re.search(r"\d", clave):
            error = "La clave debe tener mínimo 8 caracteres, con letras y números."
        elif clave != repite:
            error = "Las dos claves no coinciden."
        elif not f["acepto"]:
            error = "Debes aceptar los términos y el tratamiento de datos para continuar."
        elif _conteo("reg:i:" + _ip(), 60) >= 10:
            error = "Demasiados intentos desde tu conexión. Espera un rato."
        else:
            _anotar("reg:i:" + _ip())
            codigo, resp = _crear_cuenta_procsis({"email": email, "titular": f["nombre"], "negocio": f["negocio"], "nit": nit, "usuarios_est": f["usuarios"],
                                                  "segmento": f["segmento"], "telefono": f["telefono"], "acepto": True, "email_verificado": True})
            if codigo in (200, 201) and resp.get("ok"):
                nuevo_id_info = dict(resp, nit=nit, titular=f["nombre"], usuarios_est=f["usuarios"])
                neg = _negocio_de(email, nuevo_id_info)
                db.x("UPDATE negocios SET clave_hash=? WHERE id=?", generate_password_hash(clave, method="pbkdf2:sha256"), neg)
                db.commit()
                salida = _iniciar_sesion(email, nuevo_id_info)
                flash("¡Bienvenido a TiendaTrack! Tu demo de %d días ya está activa." % int(resp.get("dias_restantes") or DIAS_DEMO), "ok")
                return salida
            if codigo == 409:
                session.pop("reg_email", None)
                session.pop("reg_ok", None)
                return redirect(url_for("login", ya=1))
            if codigo == 403:
                error = "El registro aún no está abierto. Vuelve pronto."
            elif codigo == 400 and resp.get("error"):
                error = str(resp["error"])[:200]
            else:
                error = "No pudimos crear tu cuenta ahora. Intenta de nuevo en un minuto."
    return render_template("registro.html", **_ctx_registro(3, error=error, f=f)), (400 if error else 200)


@app.route("/bloqueado")
def bloqueado():
    est = session.get("estado")
    if session.get("acc"):
        return redirect(url_for("inicio"))
    if est == "suspendido":
        t, d = "Cuenta suspendida", "Tu cuenta está suspendida. Comunícate con soporte de PROCSIS."
    elif est in ("vencido",):
        t, d = "Tu periodo terminó", "Tu demo o plan venció. Elige un plan y paga en PROCSIS para seguir. Tus datos se conservan."
    else:
        return redirect(url_for("login"))
    return render_template("bloqueado.html", titulo=t, detalle=d, procsis=PROCSIS_URL), 403


_MIME = {".css": "text/css; charset=utf-8", ".js": "application/javascript; charset=utf-8", ".png": "image/png", ".webp": "image/webp",
         ".svg": "image/svg+xml", ".ico": "image/x-icon", ".jpg": "image/jpeg", ".jpeg": "image/jpeg"}


@app.route("/static/<path:filename>", endpoint="static")
def estatico(filename):
    ext = os.path.splitext(filename)[1].lower()
    ruta = os.path.join(BASE, "static", filename)
    if ext in _MIME and ".." not in filename and os.path.isfile(ruta):
        with open(ruta, "rb") as f:
            cuerpo = f.read()
    elif filename in _STATIC_EMB:
        cuerpo = _STATIC_EMB[filename].encode("utf-8")
    else:
        abort(404)
    r = Response(cuerpo, mimetype=_MIME.get(ext, "application/octet-stream").split(";")[0])
    r.headers["Content-Type"] = _MIME.get(ext, "application/octet-stream")
    r.headers["Cache-Control"] = "public, max-age=300"
    return r


@app.route("/salud")
def salud():
    return {"ok": True}


# ───────────────────────── guardia global ─────────────────────────
_LIBRES = {"sso", "login", "salir", "bloqueado", "salud", "static", "registro", "registro_pin", "registro_datos"}


@app.before_request
def guardia():
    if request.endpoint == "static" or request.endpoint is None:
        return None
    _asegurar_tablas()
    if request.endpoint in _LIBRES:
        return None
    if not session.get("neg_id"):
        return redirect(url_for("login"))
    # Revalidar vigencia con PROCSIS cada cierto tiempo
    edad = int(time.time()) - int(session.get("acc_ts") or 0)
    if edad > REVALIDAR_S:
        info = _consultar_procsis(session.get("email", ""))
        if info and info.get("ok"):
            _guardar_acceso(info)
        elif info is None and edad > GRACIA_S:
            session["acc"] = False
            session["estado"] = "sin_verificar"
    if not session.get("acc"):
        return redirect(url_for("bloqueado"))
    if request.method == "POST":
        enviado = request.form.get("csrf") or request.headers.get("X-CSRF") or ""
        if not hmac.compare_digest(str(enviado), str(session.get("csrf") or "x")):
            abort(400, "Sesión expirada. Recarga la página.")
    return None


@app.context_processor
def contexto():
    return {"csrf": session.get("csrf", ""), "negocio": session.get("negocio", ""), "plan": session.get("plan") or {},
            "estado": session.get("estado", ""), "dias": session.get("dias", 0), "vence": session.get("vence", ""),
            "segmento": session.get("segmento", ""), "procsis": PROCSIS_URL, "METODOS": METODOS}


@app.after_request
def cabeceras(r):
    r.headers["X-Content-Type-Options"] = "nosniff"
    r.headers["X-Frame-Options"] = "DENY"
    r.headers["Referrer-Policy"] = "same-origin"
    if request.endpoint != "static":
        r.headers["Cache-Control"] = "no-store"
    return r


def nid():
    return int(session["neg_id"])


# ───────────────────────── inicio ─────────────────────────
def _delta(actual, anterior):
    """Variación porcentual contra el periodo anterior; None si no hay con qué comparar."""
    if not anterior:
        return None
    return int(round((actual - anterior) * 100.0 / anterior))


def _total(n, desde, hasta):
    r = db.uno("SELECT COUNT(*) AS c, COALESCE(SUM(total),0) AS t FROM ventas WHERE negocio_id=? AND estado='pagada' AND substr(creado_en,1,10)>=? AND substr(creado_en,1,10)<=?", n, desde, hasta)
    return int(r["c"]), int(r["t"])


@app.route("/")
def inicio():
    n = nid()
    hoy = ahora()
    hoy_d = hoy.strftime("%Y-%m-%d")
    ayer_d = (hoy - timedelta(days=1)).strftime("%Y-%m-%d")
    mes_ini = hoy.replace(day=1)
    prev_fin = mes_ini - timedelta(days=1)
    prev_ini = prev_fin.replace(day=1)
    prev_mismo = prev_ini.replace(day=min(hoy.day, calendar.monthrange(prev_ini.year, prev_ini.month)[1]))
    n_hoy, t_hoy = _total(n, hoy_d, hoy_d)
    _na, t_ayer = _total(n, ayer_d, ayer_d)
    n_mes, t_mes = _total(n, mes_ini.strftime("%Y-%m-%d"), hoy_d)
    _np, t_prev = _total(n, prev_ini.strftime("%Y-%m-%d"), prev_mismo.strftime("%Y-%m-%d"))
    util = db.uno("SELECT COALESCE(SUM(i.total - i.costo * i.cantidad),0) AS u FROM venta_items i JOIN ventas v ON v.id=i.venta_id "
                  "WHERE v.negocio_id=? AND v.estado='pagada' AND substr(v.creado_en,1,10)>=?", n, mes_ini.strftime("%Y-%m-%d"))["u"]
    util = int(util)
    meta = int((db.uno("SELECT meta_mensual FROM negocios WHERE id=?", n) or {}).get("meta_mensual") or 0)
    avance = min(100, int(t_mes * 100 / meta)) if meta else 0
    ticket = t_hoy // n_hoy if n_hoy else 0
    bajo = db.q("SELECT id, nombre, stock, stock_minimo FROM productos WHERE negocio_id=? AND activo=1 AND controla_stock=1 AND stock<=stock_minimo ORDER BY stock ASC LIMIT 6", n)
    n_bajo = db.uno("SELECT COUNT(*) AS c FROM productos WHERE negocio_id=? AND activo=1 AND controla_stock=1 AND stock<=stock_minimo", n)["c"]
    desde = (hoy - timedelta(days=13)).strftime("%Y-%m-%d")
    por_dia = {f["d"]: int(f["t"]) for f in db.q(
        "SELECT substr(creado_en,1,10) AS d, SUM(total) AS t FROM ventas WHERE negocio_id=? AND estado='pagada' AND substr(creado_en,1,10)>=? GROUP BY substr(creado_en,1,10)", n, desde)}
    serie = [{"d": (hoy - timedelta(days=13 - i)).strftime("%Y-%m-%d")} for i in range(14)]
    for sdt in serie:
        sdt["t"] = por_dia.get(sdt["d"], 0)
    mx = max([sdt["t"] for sdt in serie] + [1])
    for sdt in serie:
        sdt["h"] = max(3, int(sdt["t"] * 100 / mx)) if sdt["t"] else 3
    top = db.q("SELECT i.nombre AS nombre, SUM(i.cantidad) AS u, SUM(i.total) AS t FROM venta_items i JOIN ventas v ON v.id=i.venta_id "
               "WHERE v.negocio_id=? AND v.estado='pagada' AND substr(v.creado_en,1,10)>=? GROUP BY i.nombre ORDER BY SUM(i.total) DESC LIMIT 5", n, mes_ini.strftime("%Y-%m-%d"))
    por_metodo = db.q("SELECT metodo, SUM(total) AS t FROM ventas WHERE negocio_id=? AND estado='pagada' AND substr(creado_en,1,10)>=? GROUP BY metodo ORDER BY SUM(total) DESC", n, mes_ini.strftime("%Y-%m-%d"))
    tot_m = sum(int(m["t"]) for m in por_metodo) or 1
    for m in por_metodo:
        m["nombre"] = METODOS_D.get(m["metodo"], m["metodo"])
        m["pct"] = int(round(int(m["t"]) * 100 / tot_m))
    caja = db.uno("SELECT * FROM cajas WHERE negocio_id=? AND estado='abierta' ORDER BY id DESC LIMIT 1", n)
    n_prod = db.uno("SELECT COUNT(*) AS c FROM productos WHERE negocio_id=? AND activo=1", n)["c"]
    return render_template("inicio.html", n_hoy=n_hoy, t_hoy=t_hoy, d_hoy=_delta(t_hoy, t_ayer), t_ayer=t_ayer, n_mes=n_mes, t_mes=t_mes, d_mes=_delta(t_mes, t_prev),
                           util=util, meta=meta, avance=avance, ticket=ticket, bajo=bajo, n_bajo=n_bajo, serie=serie, top=top, por_metodo=por_metodo,
                           caja=caja, n_prod=n_prod, mes_nombre=("enero febrero marzo abril mayo junio julio agosto septiembre octubre noviembre diciembre".split())[hoy.month - 1], pagina="inicio")


# ───────────────────────── configuración (clave y meta) ─────────────────────────
@app.route("/configuracion", methods=["GET", "POST"])
def configuracion():
    n = nid()
    neg = db.uno("SELECT email, clave_hash, meta_mensual FROM negocios WHERE id=?", n)
    if request.method == "POST":
        accion = request.form.get("accion")
        if accion == "meta":
            db.x("UPDATE negocios SET meta_mensual=? WHERE id=?", entero(request.form.get("meta")), n)
            db.commit()
            flash("Meta mensual guardada.", "ok")
        elif accion == "clave":
            nueva, repite, actual = request.form.get("nueva") or "", request.form.get("repite") or "", request.form.get("actual") or ""
            if neg["clave_hash"] and not check_password_hash(neg["clave_hash"], actual):
                flash("La clave actual no es correcta.", "err")
            elif len(nueva) < 8 or not re.search(r"[A-Za-z]", nueva) or not re.search(r"\d", nueva):
                flash("La clave debe tener mínimo 8 caracteres, con letras y números.", "err")
            elif nueva != repite:
                flash("Las dos claves no coinciden.", "err")
            else:
                db.x("UPDATE negocios SET clave_hash=? WHERE id=?", generate_password_hash(nueva, method="pbkdf2:sha256"), n)
                db.commit()
                flash("Clave guardada. Ya puedes entrar con tu correo y esta clave.", "ok")
        return redirect(url_for("configuracion"))
    return render_template("configuracion.html", email=neg["email"], tiene_clave=bool(neg["clave_hash"]), meta=neg["meta_mensual"], pagina="configuracion")


# ───────────────────────── productos ─────────────────────────
def _categoria(nombre):
    nombre = limpio(nombre, 80)
    if not nombre:
        return 0
    c = db.uno("SELECT id FROM categorias WHERE negocio_id=? AND lower(nombre)=lower(?)", nid(), nombre)
    if c:
        return c["id"]
    return db.x("INSERT INTO categorias (negocio_id, nombre) VALUES (?,?) RETURNING id", nid(), nombre)


@app.route("/productos")
def productos():
    n = nid()
    buscar = limpio(request.args.get("q"), 60)
    filtro = request.args.get("f", "")
    sql = ("SELECT p.*, COALESCE(c.nombre,'') AS categoria FROM productos p LEFT JOIN categorias c ON c.id=p.categoria_id "
           "WHERE p.negocio_id=? AND p.activo=?")
    par = [n, 0 if filtro == "inactivos" else 1]
    if buscar:
        sql += " AND (lower(p.nombre) LIKE ? OR lower(p.sku) LIKE ?)"
        par += ["%" + buscar.lower() + "%"] * 2
    if filtro == "bajo":
        sql += " AND p.controla_stock=1 AND p.stock<=p.stock_minimo"
    sql += " ORDER BY p.nombre LIMIT 500"
    filas = db.q(sql, *par)
    total = db.uno("SELECT COUNT(*) AS c FROM productos WHERE negocio_id=? AND activo=1", n)["c"]
    return render_template("productos.html", filas=filas, buscar=buscar, filtro=filtro, total=total, pagina="productos")


def _form_producto():
    return {"nombre": limpio(request.form.get("nombre")), "sku": limpio(request.form.get("sku"), 60),
            "precio": entero(request.form.get("precio")), "costo": entero(request.form.get("costo")),
            "stock": entero(request.form.get("stock"), 0, -10 ** 6, 10 ** 7), "stock_minimo": entero(request.form.get("stock_minimo")),
            "controla_stock": 1 if request.form.get("controla_stock") else 0, "categoria": limpio(request.form.get("categoria"), 80)}


@app.route("/productos/nuevo", methods=["GET", "POST"])
def producto_nuevo():
    n = nid()
    cats = [c["nombre"] for c in db.q("SELECT nombre FROM categorias WHERE negocio_id=? ORDER BY nombre", n)]
    if request.method == "POST":
        d = _form_producto()
        limite = int((session.get("plan") or {}).get("max_productos") or 0)
        activos = db.uno("SELECT COUNT(*) AS c FROM productos WHERE negocio_id=? AND activo=1", n)["c"]
        if not d["nombre"]:
            flash("Escribe el nombre del producto.", "err")
        elif d["precio"] <= 0:
            flash("El precio de venta debe ser mayor a cero.", "err")
        elif limite > 0 and activos >= limite:
            flash("Llegaste al límite de %d productos de tu plan. Cambia de plan en PROCSIS para agregar más." % limite, "err")
        elif d["sku"] and db.uno("SELECT id FROM productos WHERE negocio_id=? AND sku=? AND activo=1", n, d["sku"]):
            flash("Ya existe un producto con ese código.", "err")
        else:
            pid = db.x("INSERT INTO productos (negocio_id, categoria_id, nombre, sku, precio, costo, stock, stock_minimo, controla_stock, activo, creado_en) "
                       "VALUES (?,?,?,?,?,?,?,?,?,1,?) RETURNING id", n, _categoria(d["categoria"]), d["nombre"], d["sku"], d["precio"], d["costo"],
                       d["stock"] if d["controla_stock"] else 0, d["stock_minimo"], d["controla_stock"], ahora_s())
            if d["controla_stock"] and d["stock"]:
                db.x("INSERT INTO movimientos (negocio_id, producto_id, tipo, cantidad, nota, creado_en) VALUES (?,?,?,?,?,?)",
                     n, pid, "entrada", d["stock"], "Inventario inicial", ahora_s())
            db.commit()
            flash("Producto creado.", "ok")
            return redirect(url_for("productos"))
        return render_template("producto_form.html", p=d, cats=cats, nuevo=True, pagina="productos")
    return render_template("producto_form.html", p={"controla_stock": 1, "stock_minimo": 0, "stock": 0, "precio": "", "costo": 0}, cats=cats, nuevo=True, pagina="productos")


@app.route("/productos/<int:pid>/editar", methods=["GET", "POST"])
def producto_editar(pid):
    n = nid()
    p = db.uno("SELECT p.*, COALESCE(c.nombre,'') AS categoria FROM productos p LEFT JOIN categorias c ON c.id=p.categoria_id WHERE p.id=? AND p.negocio_id=?", pid, n)
    if not p:
        abort(404)
    cats = [c["nombre"] for c in db.q("SELECT nombre FROM categorias WHERE negocio_id=? ORDER BY nombre", n)]
    if request.method == "POST":
        d = _form_producto()
        if not d["nombre"] or d["precio"] <= 0:
            flash("Revisa el nombre y el precio.", "err")
        elif d["sku"] and db.uno("SELECT id FROM productos WHERE negocio_id=? AND sku=? AND activo=1 AND id<>?", n, d["sku"], pid):
            flash("Ya existe otro producto con ese código.", "err")
        else:
            # el stock solo se cambia desde Inventario, para que quede historial
            db.x("UPDATE productos SET nombre=?, sku=?, precio=?, costo=?, stock_minimo=?, controla_stock=?, categoria_id=? WHERE id=? AND negocio_id=?",
                 d["nombre"], d["sku"], d["precio"], d["costo"], d["stock_minimo"], d["controla_stock"], _categoria(d["categoria"]), pid, n)
            db.commit()
            flash("Cambios guardados.", "ok")
            return redirect(url_for("productos"))
        d.update({"id": pid, "stock": p["stock"], "activo": p["activo"]})
        return render_template("producto_form.html", p=d, cats=cats, nuevo=False, pagina="productos")
    return render_template("producto_form.html", p=p, cats=cats, nuevo=False, pagina="productos")


@app.route("/productos/<int:pid>/estado", methods=["POST"])
def producto_estado(pid):
    n = nid()
    p = db.uno("SELECT activo FROM productos WHERE id=? AND negocio_id=?", pid, n)
    if not p:
        abort(404)
    nuevo = 0 if p["activo"] else 1
    if nuevo:
        limite = int((session.get("plan") or {}).get("max_productos") or 0)
        activos = db.uno("SELECT COUNT(*) AS c FROM productos WHERE negocio_id=? AND activo=1", n)["c"]
        if limite > 0 and activos >= limite:
            flash("Llegaste al límite de productos de tu plan.", "err")
            return redirect(url_for("productos", f="inactivos"))
    db.x("UPDATE productos SET activo=? WHERE id=? AND negocio_id=?", nuevo, pid, n)
    db.commit()
    flash("Producto reactivado." if nuevo else "Producto desactivado. Las ventas anteriores se conservan.", "ok")
    return redirect(url_for("productos"))


# ───────────────────────── inventario ─────────────────────────
@app.route("/inventario")
def inventario():
    n = nid()
    buscar = limpio(request.args.get("q"), 60)
    sql = "SELECT id, nombre, sku, stock, stock_minimo FROM productos WHERE negocio_id=? AND activo=1 AND controla_stock=1"
    par = [n]
    if buscar:
        sql += " AND (lower(nombre) LIKE ? OR lower(sku) LIKE ?)"
        par += ["%" + buscar.lower() + "%"] * 2
    filas = db.q(sql + " ORDER BY (CASE WHEN stock<=stock_minimo THEN 0 ELSE 1 END), nombre LIMIT 300", *par)
    movs = db.q("SELECT m.*, p.nombre AS producto FROM movimientos m JOIN productos p ON p.id=m.producto_id WHERE m.negocio_id=? ORDER BY m.id DESC LIMIT 30", n)
    return render_template("inventario.html", filas=filas, movs=movs, buscar=buscar, pagina="inventario")


@app.route("/inventario/mover", methods=["POST"])
def inventario_mover():
    n = nid()
    pid = entero(request.form.get("producto_id"))
    tipo = request.form.get("tipo")
    cant = entero(request.form.get("cantidad"), 0, 0, 10 ** 6)
    nota = limpio(request.form.get("nota"), 200)
    db.inicio_transaccion()
    p = db.uno("SELECT id, stock, controla_stock FROM productos WHERE id=? AND negocio_id=?" + db.FOR_UPDATE, pid, n)
    if not p or not p["controla_stock"] or tipo not in ("entrada", "salida", "ajuste"):
        db.rollback()
        abort(400)
    if tipo == "ajuste":
        delta, nuevo = cant - p["stock"], cant
    elif tipo == "entrada":
        delta, nuevo = cant, p["stock"] + cant
    else:
        delta, nuevo = -cant, p["stock"] - cant
    if cant == 0 and tipo != "ajuste" or (tipo == "ajuste" and delta == 0):
        db.rollback()
        flash("No hay nada que cambiar.", "err")
    elif nuevo < 0:
        db.rollback()
        flash("No puedes dejar el stock en negativo.", "err")
    else:
        db.x("UPDATE productos SET stock=? WHERE id=? AND negocio_id=?", nuevo, pid, n)
        db.x("INSERT INTO movimientos (negocio_id, producto_id, tipo, cantidad, nota, creado_en) VALUES (?,?,?,?,?,?)", n, pid, tipo, delta, nota, ahora_s())
        db.commit()
        flash("Inventario actualizado.", "ok")
    return redirect(url_for("inventario", q=request.form.get("q", "")))


# ───────────────────────── clientes ─────────────────────────
@app.route("/clientes", methods=["GET", "POST"])
def clientes():
    n = nid()
    if request.method == "POST":
        cid = entero(request.form.get("id"))
        nombre = limpio(request.form.get("nombre"))
        doc, tel, mail = limpio(request.form.get("documento"), 30), limpio(request.form.get("telefono"), 30), limpio(request.form.get("email")).lower()
        if not nombre:
            flash("Escribe el nombre del cliente.", "err")
        elif cid:
            db.x("UPDATE clientes SET nombre=?, documento=?, telefono=?, email=? WHERE id=? AND negocio_id=?", nombre, doc, tel, mail, cid, n)
            db.commit()
            flash("Cliente actualizado.", "ok")
        else:
            db.x("INSERT INTO clientes (negocio_id, nombre, documento, telefono, email, creado_en) VALUES (?,?,?,?,?,?)", n, nombre, doc, tel, mail, ahora_s())
            db.commit()
            flash("Cliente agregado.", "ok")
        return redirect(url_for("clientes"))
    buscar = limpio(request.args.get("q"), 60)
    sql = ("SELECT c.*, (SELECT COUNT(*) FROM ventas v WHERE v.cliente_id=c.id AND v.estado='pagada') AS compras, "
           "(SELECT COALESCE(SUM(total),0) FROM ventas v WHERE v.cliente_id=c.id AND v.estado='pagada') AS gastado FROM clientes c WHERE c.negocio_id=?")
    par = [n]
    if buscar:
        sql += " AND (lower(c.nombre) LIKE ? OR c.documento LIKE ? OR c.telefono LIKE ?)"
        par += ["%" + buscar.lower() + "%", "%" + buscar + "%", "%" + buscar + "%"]
    filas = db.q(sql + " ORDER BY c.nombre LIMIT 300", *par)
    editar = None
    if request.args.get("editar"):
        editar = db.uno("SELECT * FROM clientes WHERE id=? AND negocio_id=?", entero(request.args.get("editar")), n)
    return render_template("clientes.html", filas=filas, buscar=buscar, editar=editar, pagina="clientes")


# ───────────────────────── caja ─────────────────────────
def _caja_abierta():
    return db.uno("SELECT * FROM cajas WHERE negocio_id=? AND estado='abierta' ORDER BY id DESC LIMIT 1", nid())


def _resumen_caja(caja):
    por = {f["metodo"]: f for f in db.q("SELECT metodo, COUNT(*) AS c, SUM(total) AS t FROM ventas WHERE negocio_id=? AND caja_id=? AND estado='pagada' GROUP BY metodo", nid(), caja["id"])}
    efectivo = int((por.get("efectivo") or {}).get("t") or 0)
    total = sum(int(f["t"] or 0) for f in por.values())
    nventas = sum(int(f["c"] or 0) for f in por.values())
    return por, efectivo, total, nventas, int(caja["base"]) + efectivo


@app.route("/caja", methods=["GET", "POST"])
def caja():
    n = nid()
    abierta = _caja_abierta()
    if request.method == "POST":
        accion = request.form.get("accion")
        if accion == "abrir":
            if abierta:
                flash("Ya hay una caja abierta.", "err")
            else:
                db.x("INSERT INTO cajas (negocio_id, abierta_en, base, estado) VALUES (?,?,?,'abierta')", n, ahora_s(), entero(request.form.get("base")))
                db.commit()
                flash("Caja abierta. Ya puedes vender.", "ok")
        elif accion == "cerrar" and abierta:
            _p, _e, _t, _n, esperado = _resumen_caja(abierta)
            contado = entero(request.form.get("contado"))
            db.x("UPDATE cajas SET estado='cerrada', cerrada_en=?, esperado=?, contado=?, nota=? WHERE id=? AND negocio_id=?",
                 ahora_s(), esperado, contado, limpio(request.form.get("nota"), 200), abierta["id"], n)
            db.commit()
            flash("Caja cerrada.", "ok")
            return redirect(url_for("caja_detalle", cid=abierta["id"]))
        return redirect(url_for("caja"))
    resumen = _resumen_caja(abierta) if abierta else None
    historial = db.q("SELECT * FROM cajas WHERE negocio_id=? AND estado='cerrada' ORDER BY id DESC LIMIT 15", n)
    return render_template("caja.html", abierta=abierta, resumen=resumen, historial=historial, pagina="caja")


@app.route("/caja/<int:cid>")
def caja_detalle(cid):
    c = db.uno("SELECT * FROM cajas WHERE id=? AND negocio_id=?", cid, nid())
    if not c:
        abort(404)
    por, efectivo, total, nventas, esperado = _resumen_caja(c)
    return render_template("caja_detalle.html", c=c, por=por, efectivo=efectivo, total=total, nventas=nventas, esperado=esperado, pagina="caja")


# ───────────────────────── punto de venta ─────────────────────────
@app.route("/pos")
def pos():
    n = nid()
    abierta = _caja_abierta()
    if not abierta:
        flash("Abre la caja para empezar a vender.", "err")
        return redirect(url_for("caja"))
    prods = db.q("SELECT p.id, p.nombre, p.sku, p.precio, p.stock, p.controla_stock, COALESCE(c.nombre,'') AS cat FROM productos p "
                 "LEFT JOIN categorias c ON c.id=p.categoria_id WHERE p.negocio_id=? AND p.activo=1 ORDER BY p.nombre LIMIT 3000", n)
    clis = db.q("SELECT id, nombre, documento FROM clientes WHERE negocio_id=? ORDER BY nombre LIMIT 1000", n)
    return render_template("pos.html", prods=prods, clis=clis, pagina="pos")


@app.route("/pos/cobrar", methods=["POST"])
def pos_cobrar():
    n = nid()
    datos = request.get_json(silent=True) or {}
    metodo = datos.get("metodo")
    if metodo not in METODOS_D:
        return jsonify(ok=False, error="Elige un método de pago."), 400
    pedido = {}
    for it in (datos.get("items") or [])[:200]:
        if not isinstance(it, dict):
            continue
        pid, cant = entero(it.get("id")), entero(it.get("cant"), 0, 0, 9999)
        if pid and cant:
            pedido[pid] = pedido.get(pid, 0) + cant
    if not pedido:
        return jsonify(ok=False, error="El carrito está vacío."), 400
    db.inicio_transaccion()
    try:
        caja = _caja_abierta()
        if not caja:
            db.rollback()
            return jsonify(ok=False, error="No hay caja abierta."), 409
        lineas, subtotal = [], 0
        for pid, cant in pedido.items():
            p = db.uno("SELECT id, nombre, precio, costo, stock, controla_stock FROM productos WHERE id=? AND negocio_id=? AND activo=1" + db.FOR_UPDATE, pid, n)
            if not p:
                db.rollback()
                return jsonify(ok=False, error="Un producto del carrito ya no está disponible."), 409
            if p["controla_stock"] and p["stock"] < cant:
                db.rollback()
                return jsonify(ok=False, error="Stock insuficiente de «%s» (quedan %d)." % (p["nombre"], p["stock"])), 409
            lineas.append((p, cant))
            subtotal += int(p["precio"]) * cant
        descuento = entero(datos.get("descuento"), 0, 0, subtotal)
        total = subtotal - descuento
        recibido, cambio = total, 0
        if metodo == "efectivo":
            recibido = entero(datos.get("recibido"), total) or total
            if recibido < total:
                db.rollback()
                return jsonify(ok=False, error="El efectivo recibido es menor al total."), 400
            cambio = recibido - total
        cliente = entero(datos.get("cliente_id"))
        if cliente and not db.uno("SELECT id FROM clientes WHERE id=? AND negocio_id=?", cliente, n):
            cliente = 0
        numero = int(db.uno("SELECT COALESCE(MAX(numero),0)+1 AS s FROM ventas WHERE negocio_id=?", n)["s"])
        ts = ahora_s()
        vid = db.x("INSERT INTO ventas (negocio_id, numero, cliente_id, caja_id, subtotal, descuento, total, metodo, recibido, cambio, estado, creado_en) "
                   "VALUES (?,?,?,?,?,?,?,?,?,?,'pagada',?) RETURNING id", n, numero, cliente, caja["id"], subtotal, descuento, total, metodo, recibido, cambio, ts)
        for p, cant in lineas:
            db.x("INSERT INTO venta_items (venta_id, producto_id, nombre, cantidad, precio, total, costo) VALUES (?,?,?,?,?,?,?)", vid, p["id"], p["nombre"], cant, p["precio"], int(p["precio"]) * cant, int(p["costo"] or 0))
            if p["controla_stock"]:
                db.x("UPDATE productos SET stock=stock-? WHERE id=? AND negocio_id=?", cant, p["id"], n)
                db.x("INSERT INTO movimientos (negocio_id, producto_id, tipo, cantidad, nota, venta_id, creado_en) VALUES (?,?,?,?,?,?,?)",
                     n, p["id"], "venta", -cant, "Venta #%d" % numero, vid, ts)
        db.commit()
        return jsonify(ok=True, id=vid, numero=numero, cambio=cambio)
    except Exception:
        db.rollback()
        app.logger.exception("error al cobrar")
        return jsonify(ok=False, error="No se pudo registrar la venta. Intenta de nuevo."), 500


# ───────────────────────── ventas ─────────────────────────
def _filtros_ventas():
    hasta = request.args.get("hasta") or hoy_s()
    desde = request.args.get("desde") or (ahora() - timedelta(days=29)).strftime("%Y-%m-%d")
    for v in (desde, hasta):
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", v):
            desde, hasta = (ahora() - timedelta(days=29)).strftime("%Y-%m-%d"), hoy_s()
    metodo = request.args.get("metodo", "")
    return desde, hasta, metodo if metodo in METODOS_D else ""


def _consulta_ventas(limite):
    desde, hasta, metodo = _filtros_ventas()
    sql = ("SELECT v.*, COALESCE(c.nombre,'') AS cliente FROM ventas v LEFT JOIN clientes c ON c.id=v.cliente_id "
           "WHERE v.negocio_id=? AND substr(v.creado_en,1,10)>=? AND substr(v.creado_en,1,10)<=?")
    par = [nid(), desde, hasta]
    if metodo:
        sql += " AND v.metodo=?"
        par.append(metodo)
    return db.q(sql + " ORDER BY v.id DESC LIMIT %d" % limite, *par), desde, hasta, metodo


@app.route("/ventas")
def ventas():
    filas, desde, hasta, metodo = _consulta_ventas(300)
    total = sum(int(f["total"]) for f in filas if f["estado"] == "pagada")
    return render_template("ventas.html", filas=filas, desde=desde, hasta=hasta, metodo=metodo, total=total, pagina="ventas")


def _celda(v):
    s = str(v if v is not None else "")
    return "'" + s if s[:1] in ("=", "+", "-", "@") else s  # evita inyección de fórmulas en Excel


@app.route("/ventas/exportar.csv")
def ventas_csv():
    filas, desde, hasta, _m = _consulta_ventas(20000)
    out = io.StringIO()
    w = csv.writer(out, delimiter=";")
    w.writerow(["Número", "Fecha", "Cliente", "Método", "Subtotal", "Descuento", "Total", "Estado"])
    for f in filas:
        w.writerow([f["numero"], f["creado_en"], _celda(f["cliente"]), METODOS_D.get(f["metodo"], f["metodo"]), f["subtotal"], f["descuento"], f["total"], f["estado"]])
    return Response("﻿" + out.getvalue(), mimetype="text/csv; charset=utf-8",
                    headers={"Content-Disposition": "attachment; filename=ventas_%s_a_%s.csv" % (desde, hasta)})


def _venta(vid):
    v = db.uno("SELECT v.*, COALESCE(c.nombre,'') AS cliente, COALESCE(c.documento,'') AS cliente_doc FROM ventas v LEFT JOIN clientes c ON c.id=v.cliente_id WHERE v.id=? AND v.negocio_id=?", vid, nid())
    if not v:
        abort(404)
    return v, db.q("SELECT * FROM venta_items WHERE venta_id=? ORDER BY id", vid)


@app.route("/ventas/<int:vid>")
def venta_detalle(vid):
    v, items = _venta(vid)
    return render_template("venta_detalle.html", v=v, items=items, pagina="ventas")


@app.route("/ventas/<int:vid>/recibo")
def venta_recibo(vid):
    v, items = _venta(vid)
    return render_template("recibo.html", v=v, items=items, nuevo=bool(request.args.get("nuevo")))


@app.route("/ventas/<int:vid>/anular", methods=["POST"])
def venta_anular(vid):
    n = nid()
    db.inicio_transaccion()
    v = db.uno("SELECT id, numero, estado FROM ventas WHERE id=? AND negocio_id=?" + db.FOR_UPDATE, vid, n)
    if not v:
        db.rollback()
        abort(404)
    if v["estado"] != "pagada":
        db.rollback()
        flash("Esa venta ya estaba anulada.", "err")
        return redirect(url_for("venta_detalle", vid=vid))
    ts = ahora_s()
    for it in db.q("SELECT i.producto_id, i.cantidad, p.controla_stock FROM venta_items i JOIN productos p ON p.id=i.producto_id WHERE i.venta_id=?", vid):
        if it["controla_stock"]:
            db.x("UPDATE productos SET stock=stock+? WHERE id=? AND negocio_id=?", it["cantidad"], it["producto_id"], n)
            db.x("INSERT INTO movimientos (negocio_id, producto_id, tipo, cantidad, nota, venta_id, creado_en) VALUES (?,?,?,?,?,?,?)",
                 n, it["producto_id"], "anulacion", it["cantidad"], "Anulación venta #%d" % v["numero"], vid, ts)
    db.x("UPDATE ventas SET estado='anulada', anulada_en=? WHERE id=? AND negocio_id=?", ts, vid, n)
    db.commit()
    flash("Venta anulada y stock devuelto al inventario.", "ok")
    return redirect(url_for("venta_detalle", vid=vid))


@app.errorhandler(400)
@app.errorhandler(404)
def error_pagina(e):
    return render_template("bloqueado.html", titulo="No se pudo completar", detalle=getattr(e, "description", "Página no encontrada."), procsis=PROCSIS_URL, volver=True), e.code


if __name__ == "__main__":
    app.run(debug=os.environ.get("FLASK_DEBUG") == "1", port=int(os.environ.get("PORT", 5001)))