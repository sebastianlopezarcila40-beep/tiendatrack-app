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
            "segmento": session.get("segmento", ""), "procsis": PROCSIS_URL, "METODOS": METODOS,
            "marco": _marco_procsis()}


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


# ───────────────────────── menú y pie de página (diseño EduTrack, administrados desde PROCSIS) ─────────────────────────
# El contenido (menú superior, columnas del pie, textos legales) lo edita PROCSIS desde su zona administrativa
# (Comunicaciones y Mercadeo, TI, Ventas y Legal, Soporte). Esta app lo consulta en GET {PROCSIS_URL}/api/v1/tiendatrack/marco
# con la misma X-API-Key de siempre, lo guarda en memoria unos minutos y, si PROCSIS no responde, usa el contenido de respaldo.
MARCO_TTL_S = 300          # cada cuánto se vuelve a pedir a PROCSIS
MARCO_REINTENTO_S = 60     # si PROCSIS no respondió, cuánto esperar antes de reintentar
_MARCO = {"ts": 0.0, "ttl": 0, "datos": None}


def _marco_respaldo():
    return {
        "menu": [
            {"titulo": "Procsis", "etiqueta": "Explorar Procsis", "sub": [
                {"titulo": "¿Qué es Procsis?", "url": "/procsis"},
                {"titulo": "Infraestructura en la Nube", "url": "/procsis"},
                {"titulo": "Sello de Auditoría Digital", "url": "/procsis"},
                {"titulo": "Seguridad Jurídica y Ciberseguridad", "url": "/procsis"}]},
            {"titulo": "Soluciones", "url": "/procsis"},
            {"titulo": "Planes", "url": "/tt"},
            {"titulo": "Ayuda", "url": "/contacto"},
            {"titulo": "Sedes y Puntos de Atención", "url": "/contacto"},
            {"titulo": "Support", "url": "/contacto"},
        ],
        "marca": {"titulo": "PROCSIS", "texto": "Soluciones digitales para tu negocio. Un producto de PROCSIS.",
                  "enlaces": [{"titulo": "Soporte por correo", "url": "/contacto"}, {"titulo": "Línea de atención", "url": "/contacto"},
                              {"titulo": "Formulario de contacto", "url": "/contacto"}]},
        "columnas": [
            {"titulo": "Procsis y la Educación", "enlaces": [
                {"titulo": "Procsis y el sector educativo", "url": "/procsis"}, {"titulo": "EduTrack para directivos y rectores", "url": "/procsis"},
                {"titulo": "Gestión para la coordinación escolar", "url": "/procsis"}, {"titulo": "Plataforma para docentes", "url": "/procsis"},
                {"titulo": "Portal de seguimiento para padres", "url": "/procsis"}, {"titulo": "Socios y alianzas", "url": "/procsis"}]},
            {"titulo": "Infraestructura y Operación", "enlaces": [
                {"titulo": "Operador de infraestructura", "url": "/procsis"}, {"titulo": "Trust Center", "url": "/procsis"},
                {"titulo": "Política de privacidad", "url": "/tratamiento-datos"}, {"titulo": "Integridad y conformidad", "url": "/procsis"},
                {"titulo": "Sustentabilidad", "url": "/procsis"}]},
            {"titulo": "Corporativo e Institucional", "enlaces": [
                {"titulo": "Equipo Directivo", "url": "/procsis"}, {"titulo": "Prensa y Medios", "url": "/procsis"},
                {"titulo": "Eventos y capacitaciones docentes", "url": "/procsis"}, {"titulo": "Canal oficial de PQRSD", "url": "/contacto"}]},
            {"titulo": "Procsis Ventas y Legal", "enlaces": [
                {"titulo": "Condiciones de venta", "url": "/legal"}, {"titulo": "Política de entrega", "url": "/legal"},
                {"titulo": "Política de devoluciones", "url": "/legal"}, {"titulo": "Preguntas frecuentes", "url": "/contacto"},
                {"titulo": "Superintendencia de Industria y Comercio", "url": "https://www.sic.gov.co"}]},
        ],
        "legal": [{"titulo": "Términos", "url": "/legal"}, {"titulo": "Cookies", "url": "/legal"},
                  {"titulo": "Habeas data", "url": "/tratamiento-datos"}, {"titulo": "Sedes y Puntos de Atención", "url": "/contacto"}],
        "notas": [],
        "tagline": "Un producto de PROCSIS · Innovación que gestiona",
        "aviso": "Entrega comprobantes de venta; no emite factura electrónica DIAN.",
        "version": "",
    }


def _marco_url(u):
    u = str(u or "").strip()
    if u.startswith("/") and not u.startswith("//"):
        return (PROCSIS_URL + u) if PROCSIS_URL else "#"
    if re.match(r"^(https?://|mailto:|tel:)", u, re.I):
        return u
    return "#"


def _marco_enlaces(lista, tope=12):
    sal = []
    for e in (lista if isinstance(lista, list) else [])[:tope]:
        if isinstance(e, dict) and str(e.get("titulo") or "").strip():
            sal.append({"titulo": str(e["titulo"]).strip()[:90], "url": _marco_url(e.get("url"))})
    return sal


def _marco_normalizar(b):
    """Deja el contenido en la forma que usan las plantillas, descartando lo que venga mal formado."""
    b = b if isinstance(b, dict) else {}
    t = lambda v, n: str(v or "").strip()[:n]
    menu = []
    for it in (b.get("menu") if isinstance(b.get("menu"), list) else [])[:8]:
        if isinstance(it, dict) and t(it.get("titulo"), 40):
            sub = _marco_enlaces(it.get("sub"), 10)
            menu.append({"titulo": t(it.get("titulo"), 40), "etiqueta": t(it.get("etiqueta"), 40), "sub": sub, "url": _marco_url(it.get("url"))})
    marca = b.get("marca") if isinstance(b.get("marca"), dict) else {}
    cols = []
    for c in (b.get("columnas") if isinstance(b.get("columnas"), list) else [])[:4]:
        if isinstance(c, dict) and t(c.get("titulo"), 60):
            cols.append({"titulo": t(c.get("titulo"), 60), "enlaces": _marco_enlaces(c.get("enlaces"), 10)})
    notas = []
    for n in (b.get("notas") if isinstance(b.get("notas"), list) else [])[:6]:
        if isinstance(n, dict) and t(n.get("texto"), 600):
            notas.append({"texto": t(n.get("texto"), 600), "enlace": t(n.get("enlace"), 80), "url": _marco_url(n.get("url")) if n.get("url") else ""})
    return {"menu": menu,
            "marca": {"titulo": t(marca.get("titulo"), 40), "texto": t(marca.get("texto"), 200), "enlaces": _marco_enlaces(marca.get("enlaces"), 6)} if t(marca.get("titulo"), 40) else None,
            "columnas": cols, "legal": _marco_enlaces(b.get("legal"), 6), "notas": notas,
            "copyright": t(b.get("copyright"), 200), "tagline": t(b.get("tagline"), 200), "aviso": t(b.get("aviso"), 300), "version": t(b.get("version"), 20)}


def _marco_limpiar(bruto):
    res = _marco_normalizar(_marco_respaldo())
    if isinstance(bruto, dict):
        for k, v in _marco_normalizar(bruto.get("marco") if isinstance(bruto.get("marco"), dict) else bruto).items():
            if v:
                res[k] = v
    if not res.get("copyright"):
        res["copyright"] = "© %d PROCSIS · Soluciones digitales. Todos los derechos reservados." % ahora().year
    res["anio"] = ahora().year
    return res


def _marco_procsis():
    """Menú y pie vigentes: lo último que dijo PROCSIS, o el respaldo si no responde. Nunca debe tumbar una página."""
    c, ahora_t = _MARCO, time.time()
    if c["datos"] is not None and ahora_t - c["ts"] < c["ttl"]:
        return c["datos"]
    bruto = None
    if PROCSIS_URL and API_KEY:
        req = urllib.request.Request(PROCSIS_URL + "/api/v1/tiendatrack/marco", headers={"X-API-Key": API_KEY, "User-Agent": "tiendatrack-app"})
        try:
            with urllib.request.urlopen(req, timeout=3) as r:
                bruto = json.loads(r.read().decode("utf-8"))
        except Exception:
            bruto = None
    try:
        if isinstance(bruto, dict):
            c["datos"], c["ttl"] = _marco_limpiar(bruto), MARCO_TTL_S
        else:
            if c["datos"] is None:
                c["datos"] = _marco_limpiar({})
            c["ttl"] = MARCO_REINTENTO_S
    except Exception:
        c["datos"], c["ttl"] = _marco_limpiar({}), MARCO_REINTENTO_S
    c["ts"] = ahora_t
    return c["datos"]


# ───────────────────────── plantillas incluidas en este archivo ─────────────────────────
# Login, registro, PIN y páginas de aviso (con el logo adentro). Tienen prioridad sobre las carpetas templates/ y _embebidos,
# así que basta con subir este archivo: no hace falta copiar plantillas ni imágenes.
PLANTILLAS_INCLUIDAS = {
    'publico_base.html': r'''<!doctype html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="robots" content="noindex">
<meta name="theme-color" content="#0a2a8f">
<title>{% block titulo %}TiendaTrack{% endblock %} · TiendaTrack</title>
<link rel="icon" type="image/webp" href="data:image/webp;base64,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">
<style>
/* TiendaTrack · estilo del logo (azul rey → cian → verde) con 55 % de vidrio tipo Apple.
   Todo está dentro de esta página: no depende de archivos estáticos. */
:root{
  --azul:#0a2a8f; --azul2:#1747d6; --cian:#12b5ff; --verde:#1fdc6a;
  --tinta:#0b1437; --suave:#4b5b86; --error:#b42318; --ok:#067647;
  --vidrio:.55;                                   /* opacidad del vidrio: 55 % */
  --v-fondo:rgba(255,255,255,var(--vidrio));
  --v-borde:rgba(255,255,255,.72);
  --v-blur:blur(26px) saturate(180%);
  --grad:linear-gradient(135deg,#0a2a8f 0%,#1747d6 50%,#12b5ff 100%);
  --grad-vivo:linear-gradient(90deg,#12b5ff,#1fdc6a);
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;min-height:100vh;display:flex;flex-direction:column;color:var(--tinta);background:#e8f0ff;
  font-family:Inter,-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif;-webkit-font-smoothing:antialiased}
body::before{content:"";position:fixed;inset:-15%;z-index:-1;pointer-events:none;
  background:
   radial-gradient(38% 40% at 10% 16%,rgba(18,181,255,.60),transparent 70%),
   radial-gradient(34% 38% at 90% 10%,rgba(31,220,106,.46),transparent 70%),
   radial-gradient(44% 46% at 80% 92%,rgba(23,71,214,.55),transparent 70%),
   radial-gradient(32% 34% at 6% 92%,rgba(31,220,106,.34),transparent 70%)}
a{color:var(--azul2);text-underline-offset:3px}
.cab{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:18px clamp(16px,4vw,44px)}
.cab img{height:38px;width:auto;display:block}
.cab nav{display:flex;gap:10px;align-items:center;font-size:14px}
.cab nav a{padding:9px 16px;border-radius:999px;font-weight:600;text-decoration:none;color:var(--azul)}
.vidrio{background:var(--v-fondo);-webkit-backdrop-filter:var(--v-blur);backdrop-filter:var(--v-blur);
  border:1px solid var(--v-borde);border-radius:24px;
  box-shadow:0 22px 60px rgba(10,42,143,.20),0 2px 6px rgba(10,42,143,.06),inset 0 1px 0 rgba(255,255,255,.85)}
@supports not ((backdrop-filter:blur(1px)) or (-webkit-backdrop-filter:blur(1px))){.vidrio{background:rgba(255,255,255,.93)}}
.cab nav a.vidrio{border-radius:999px;box-shadow:0 6px 18px rgba(10,42,143,.12),inset 0 1px 0 rgba(255,255,255,.85)}
main{flex:1;display:grid;grid-template-columns:minmax(0,1.05fr) minmax(0,.95fr);gap:clamp(20px,5vw,72px);
  align-items:center;width:100%;max-width:1120px;margin:0 auto;padding:clamp(8px,3vw,28px) clamp(16px,4vw,44px) 44px}
.hero h1{font-size:clamp(34px,5.4vw,58px);line-height:1.02;letter-spacing:-.035em;margin:0 0 16px;color:var(--azul)}
.hero h1 span{background:var(--grad-vivo);-webkit-background-clip:text;background-clip:text;color:transparent;-webkit-text-fill-color:transparent}
.hero p{font-size:clamp(16px,1.9vw,19px);line-height:1.55;color:var(--suave);max-width:520px;margin:0 0 22px}
.chips{display:flex;flex-wrap:wrap;gap:10px;margin:0 0 18px;padding:0;list-style:none}
.chips li{padding:9px 16px;border-radius:999px;font-size:14px;font-weight:600;color:var(--azul)}
.hero small{display:block;color:var(--suave);font-size:13.5px}
.tarjeta{padding:clamp(22px,3.4vw,34px);width:100%;max-width:470px;justify-self:center}
.tarjeta h2{margin:0 0 4px;font-size:clamp(22px,3vw,27px);letter-spacing:-.02em;color:var(--tinta)}
.tarjeta .sub{margin:0 0 20px;color:var(--suave);font-size:15px;line-height:1.5}
label{display:block;font-size:13px;font-weight:600;color:#26345e;margin:14px 0 6px}
.campo{width:100%;padding:13px 14px;font:inherit;font-size:16px;color:var(--tinta);background:rgba(255,255,255,.72);
  border:1px solid rgba(10,42,143,.16);border-radius:14px;outline:none;transition:border-color .15s,box-shadow .15s,background .15s}
.campo::placeholder{color:#8a97b8}
.campo:focus{border-color:var(--cian);background:#fff;box-shadow:0 0 0 4px rgba(18,181,255,.22)}
select.campo{appearance:none;-webkit-appearance:none;background-image:linear-gradient(45deg,transparent 50%,#4b5b86 50%),linear-gradient(135deg,#4b5b86 50%,transparent 50%);
  background-position:calc(100% - 20px) 50%,calc(100% - 14px) 50%;background-size:6px 6px;background-repeat:no-repeat;padding-right:38px}
.fila2{display:grid;grid-template-columns:1fr 1fr;gap:12px}
.ayuda{font-size:12.5px;color:var(--suave);margin:6px 2px 0;line-height:1.45}
.clave{position:relative}.clave .campo{padding-right:74px}
.clave button{position:absolute;right:8px;top:50%;transform:translateY(-50%);background:none;border:0;color:var(--azul2);font:inherit;font-size:13px;font-weight:700;cursor:pointer;padding:8px}
.btn{display:flex;align-items:center;justify-content:center;gap:10px;width:100%;margin-top:18px;padding:14px 18px;border:0;border-radius:14px;
  font:inherit;font-size:16px;font-weight:700;color:#fff;background:var(--grad);cursor:pointer;text-decoration:none;
  box-shadow:0 10px 24px rgba(23,71,214,.35),inset 0 1px 0 rgba(255,255,255,.35);transition:transform .12s,box-shadow .12s,filter .12s}
.btn:hover{filter:brightness(1.07);transform:translateY(-1px)}.btn:active{transform:translateY(0)}
.btn.google{background:rgba(255,255,255,.85);color:var(--tinta);border:1px solid rgba(10,42,143,.14);box-shadow:0 6px 16px rgba(10,42,143,.10);margin-top:0}
.btn.verde{background:linear-gradient(135deg,#12b5ff,#1fdc6a);color:#04204f;box-shadow:0 10px 24px rgba(31,220,106,.35),inset 0 1px 0 rgba(255,255,255,.5)}
.btn.suave{background:rgba(255,255,255,.7);color:var(--azul);border:1px solid rgba(10,42,143,.16);box-shadow:none;margin-top:12px}
.btn.chico{width:auto;display:inline-flex;margin-top:0;padding:10px 16px;font-size:14px}
.btn[disabled]{opacity:.55;cursor:not-allowed;transform:none}
.sep{display:flex;align-items:center;gap:12px;color:var(--suave);font-size:13px;margin:18px 0 2px}
.sep::before,.sep::after{content:"";flex:1;height:1px;background:rgba(10,42,143,.14)}
.aviso{border-radius:14px;padding:12px 14px;font-size:14px;line-height:1.45;margin:0 0 14px}
.aviso.err{background:rgba(254,228,226,.85);color:var(--error);border:1px solid rgba(217,45,32,.28)}
.aviso.ok{background:rgba(220,250,230,.85);color:var(--ok);border:1px solid rgba(7,148,85,.3)}
.aviso.info{background:rgba(224,242,255,.85);color:#0b4a8f;border:1px solid rgba(18,181,255,.35)}
.pie-t{margin:18px 0 0;text-align:center;font-size:14px;color:var(--suave)}
.pasos{display:flex;gap:8px;margin:0 0 18px;padding:0;list-style:none}
.pasos li{flex:1;height:6px;border-radius:99px;background:rgba(10,42,143,.14)}
.pasos li.on{background:var(--grad-vivo)}
.pin{text-align:center;font-size:34px;letter-spacing:.5em;padding-left:.5em;font-weight:700;font-variant-numeric:tabular-nums}
.chk{display:flex;gap:10px;align-items:flex-start;font-size:13.5px;color:#334170;line-height:1.5;margin:16px 0 0;font-weight:500}
.chk input{margin-top:3px;width:18px;height:18px;accent-color:var(--azul2);flex:none}
.pie{text-align:center;color:var(--suave);font-size:12.5px;line-height:1.7;padding:6px 16px 26px}
.pie b{color:var(--azul)}
@media (max-width:860px){
  main{grid-template-columns:1fr;gap:22px}
  .hero{text-align:center}.hero p{margin-left:auto;margin-right:auto}.chips{justify-content:center}
  .hero.oculta-movil{display:none}
  .cab img{height:32px}
}
@media (max-width:420px){.fila2{grid-template-columns:1fr}.pin{font-size:28px}}
@media (prefers-reduced-motion:reduce){*{transition:none!important}}
</style>
</head>
<body>
<header class="cab">
  <a href="{{ url_for('login') }}" aria-label="TiendaTrack"><img src="data:image/webp;base64,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" alt="TiendaTrack"></a>
  <nav>{% block nav %}{% endblock %}</nav>
</header>
{% include 'marco_menu.html' %}
<main>
  {% block hero %}
  <section class="hero oculta-movil">
    <h1>Vende más.<br><span>Controla todo.</span></h1>
    <p>Un panel ejecutivo con lo que importa: ventas del día y del mes, utilidad, meta mensual y productos por reponer, para decidir en segundos.</p>
    <ul class="chips">
      <li class="vidrio">Punto de venta</li><li class="vidrio">Inventario</li><li class="vidrio">Caja y cierres</li><li class="vidrio">Clientes</li><li class="vidrio">Reportes</li>
    </ul>
    <small>Para tiendas, tiendas de ropa y restaurantes</small>
  </section>
  {% endblock %}
  <section class="tarjeta vidrio">
    {% block tarjeta %}{% endblock %}
  </section>
</main>
{% include 'marco_pie.html' %}
{% block scripts %}{% endblock %}
</body>
</html>
''',
    'marco_menu.html': r'''<style>
.mp-menu{position:relative;z-index:20;background:rgba(255,255,255,.92);-webkit-backdrop-filter:blur(18px) saturate(180%);backdrop-filter:blur(18px) saturate(180%);
  border-top:1px solid rgba(10,42,143,.08);border-bottom:1px solid rgba(10,42,143,.10);font-family:inherit}
.mp-menu *{box-sizing:border-box}
.mp-menu-in{max-width:1240px;margin:0 auto;padding:0 clamp(16px,4vw,44px)}
.mp-lista{list-style:none;margin:0;padding:0;display:flex;flex-wrap:wrap;gap:clamp(14px,2.6vw,34px);align-items:center}
.mp-top{display:block;padding:15px 2px;font:inherit;font-size:15px;font-weight:500;color:#1d1d1f;background:none;border:0;border-bottom:2px solid transparent;cursor:pointer;text-decoration:none;letter-spacing:-.005em}
.mp-top:hover,.mp-it.abierto>.mp-top{color:#0a6fb5}
.mp-sub>.mp-top{color:#0a6fb5}
.mp-panel{display:none;position:absolute;left:0;right:0;top:100%;background:rgba(255,255,255,.97);border-bottom:1px solid rgba(10,42,143,.10);
  box-shadow:0 18px 40px rgba(10,42,143,.10);padding:22px clamp(16px,4vw,44px) 26px calc(clamp(16px,4vw,44px) + clamp(0px,14vw,190px))}
.mp-panel ul{list-style:none;margin:0;padding:0}
.mp-eti{margin:0 0 12px;font-size:12px;letter-spacing:.08em;text-transform:uppercase;color:#6e6e73;font-weight:500}
.mp-panel a{display:block;padding:7px 0;font-size:16px;color:#1d1d1f;text-decoration:none}
.mp-panel a:hover{color:#0a6fb5}
.mp-it.abierto>.mp-panel{display:block}
@media (hover:hover) and (min-width:861px){.mp-sub:hover>.mp-panel{display:block}}
.mp-burger{display:none;width:100%;text-align:left;padding:13px 0;font:inherit;font-size:15px;font-weight:600;color:#0a2a8f;background:none;border:0;cursor:pointer}
@media (max-width:860px){
  .mp-burger{display:block}
  .mp-lista{display:none;flex-direction:column;align-items:stretch;gap:0;padding-bottom:10px}
  .mp-menu.abierto .mp-lista{display:flex}
  .mp-top{width:100%;text-align:left;padding:12px 2px;border-bottom:1px solid rgba(10,42,143,.08)}
  .mp-panel{position:static;box-shadow:none;border:0;padding:4px 0 10px 14px;background:transparent}
}
</style>
{% if marco.menu %}
<nav class="mp-menu" aria-label="Menú PROCSIS">
  <div class="mp-menu-in">
    <button class="mp-burger" type="button" aria-expanded="false" aria-controls="mp-lista">☰ Menú</button>
    <ul class="mp-lista" id="mp-lista">
    {% for it in marco.menu %}
      {% if it.sub %}
      <li class="mp-it mp-sub">
        <button class="mp-top" type="button" aria-expanded="false" aria-haspopup="true">{{ it.titulo }}</button>
        <div class="mp-panel">
          {% if it.etiqueta %}<p class="mp-eti">{{ it.etiqueta }}</p>{% endif %}
          <ul>{% for s in it.sub %}<li><a href="{{ s.url }}" target="_blank" rel="noopener">{{ s.titulo }}</a></li>{% endfor %}</ul>
        </div>
      </li>
      {% else %}
      <li class="mp-it"><a class="mp-top" href="{{ it.url }}" target="_blank" rel="noopener">{{ it.titulo }}</a></li>
      {% endif %}
    {% endfor %}
    </ul>
  </div>
</nav>
<script>
(function(){
  var nav=document.querySelector('.mp-menu');if(!nav)return;
  var bur=nav.querySelector('.mp-burger');
  bur.addEventListener('click',function(){var o=nav.classList.toggle('abierto');bur.setAttribute('aria-expanded',o);});
  nav.querySelectorAll('.mp-sub>.mp-top').forEach(function(b){
    b.addEventListener('click',function(e){
      e.stopPropagation();var li=b.parentNode,o=!li.classList.contains('abierto');
      nav.querySelectorAll('.mp-it.abierto').forEach(function(x){x.classList.remove('abierto');x.firstElementChild.setAttribute('aria-expanded','false');});
      if(o){li.classList.add('abierto');b.setAttribute('aria-expanded','true');}
    });
  });
  document.addEventListener('click',function(){nav.querySelectorAll('.mp-it.abierto').forEach(function(x){x.classList.remove('abierto');x.firstElementChild.setAttribute('aria-expanded','false');});});
  document.addEventListener('keydown',function(e){if(e.key==='Escape'){nav.querySelectorAll('.mp-it.abierto').forEach(function(x){x.classList.remove('abierto');});}});
})();
</script>
{% endif %}
''',
    'marco_pie.html': r'''<style>
.mp-pie{margin-top:auto;font-family:inherit;color:#fff;-webkit-text-size-adjust:100%}
.mp-pie *{box-sizing:border-box}
.mp-in{max-width:1240px;margin:0 auto;padding:0 clamp(16px,4vw,44px)}
.mp-notas{background:#fff;padding:30px 0 28px}
.mp-notas p{margin:0 0 12px;font-size:13.5px;line-height:1.65;color:#5b5b63;max-width:1080px}
.mp-notas a{color:#0a84d6;font-weight:700;text-decoration:none}
.mp-azul{background:linear-gradient(180deg,#0021b8 0%,#00137f 100%);padding:46px 0 26px}
.mp-cols{display:grid;grid-template-columns:1.15fr repeat(4,1fr);gap:clamp(18px,3vw,40px)}
.mp-col h3{margin:0 0 14px;font-size:15px;font-weight:700;letter-spacing:-.005em;color:#fff}
.mp-col p{margin:0 0 14px;font-size:14px;line-height:1.55;color:rgba(255,255,255,.85)}
.mp-col ul{list-style:none;margin:0;padding:0}
.mp-col li{margin:0 0 11px}
.mp-col a{font-size:13.5px;line-height:1.4;color:rgba(255,255,255,.88);text-decoration:none}
.mp-col a:hover{color:#fff;text-decoration:underline;text-underline-offset:3px}
.mp-legal{display:flex;flex-wrap:wrap;gap:10px 24px;justify-content:space-between;align-items:center;margin-top:34px;padding-top:18px;border-top:1px solid rgba(255,255,255,.22);font-size:12.5px;color:rgba(255,255,255,.82)}
.mp-legal ul{list-style:none;margin:0;padding:0;display:flex;flex-wrap:wrap;gap:8px 22px}
.mp-legal a{color:rgba(255,255,255,.92);text-decoration:none}.mp-legal a:hover{text-decoration:underline}
.mp-negro{background:#222;padding:18px 16px 20px;text-align:center;font-size:13px;line-height:1.7;color:#b9bcc6}
.mp-negro b{color:#7aa2ff;font-weight:600}
@media (max-width:1000px){.mp-cols{grid-template-columns:repeat(2,1fr)}.mp-marca{grid-column:1/-1}}
@media (max-width:560px){.mp-cols{grid-template-columns:1fr}.mp-azul{padding:34px 0 22px}.mp-legal{flex-direction:column;align-items:flex-start}}
</style>
<footer class="mp-pie" aria-label="Pie de página">
  {% if marco.notas %}
  <div class="mp-notas"><div class="mp-in">
    {% for n in marco.notas %}<p>{{ n.texto }}{% if n.url and n.url != '#' %} <a href="{{ n.url }}" target="_blank" rel="noopener">{{ n.enlace or n.url }}</a>{% endif %}</p>{% endfor %}
  </div></div>
  {% endif %}
  <div class="mp-azul"><div class="mp-in">
    <div class="mp-cols">
      {% if marco.marca %}
      <div class="mp-col mp-marca">
        <h3>{{ marco.marca.titulo }}</h3>
        {% if marco.marca.texto %}<p>{{ marco.marca.texto }}</p>{% endif %}
        <ul>{% for e in marco.marca.enlaces %}<li><a href="{{ e.url }}" target="_blank" rel="noopener">{{ e.titulo }}</a></li>{% endfor %}</ul>
      </div>
      {% endif %}
      {% for c in marco.columnas %}
      <div class="mp-col">
        <h3>{{ c.titulo }}</h3>
        <ul>{% for e in c.enlaces %}<li><a href="{{ e.url }}" target="_blank" rel="noopener">{{ e.titulo }}</a></li>{% endfor %}</ul>
      </div>
      {% endfor %}
    </div>
    <div class="mp-legal">
      <span>{{ marco.copyright }}</span>
      <ul>{% for e in marco.legal %}<li><a href="{{ e.url }}" target="_blank" rel="noopener">{{ e.titulo }}</a></li>{% endfor %}</ul>
    </div>
  </div></div>
  <div class="mp-negro">
    <b>TiendaTrack</b> © {{ marco.anio }}{% if marco.tagline %} · {{ marco.tagline }}{% endif %}<br>
    Desarrollado por <b>Procsis</b>{% if marco.version %} · Versión {{ marco.version }}{% endif %}
    {% if marco.aviso %}<br>{{ marco.aviso }}{% endif %}
  </div>
</footer>
''',
    'login.html': r'''{% extends "publico_base.html" %}
{% block titulo %}Ingresar{% endblock %}
{% block nav %}{% if planes_url %}<a class="vidrio" href="{{ planes_url }}">Planes y demo gratis</a>{% endif %}{% endblock %}
{% block tarjeta %}
<h2>Ingresa a tu negocio</h2>
<p class="sub">Ventas, inventario y caja en un solo lugar</p>

{% if error %}<div class="aviso err" role="alert">{{ error }}</div>{% endif %}
{% if aviso %}<div class="aviso info" role="status">{{ aviso }}</div>{% endif %}

{% if google and google_url %}
<a class="btn google" href="{{ google_url }}">
  <svg width="20" height="20" viewBox="0 0 48 48" aria-hidden="true"><path fill="#EA4335" d="M24 9.5c3.54 0 6.71 1.22 9.21 3.6l6.85-6.85C35.9 2.38 30.47 0 24 0 14.62 0 6.51 5.38 2.56 13.22l7.98 6.19C12.43 13.72 17.74 9.5 24 9.5z"/><path fill="#4285F4" d="M46.98 24.55c0-1.57-.15-3.09-.38-4.55H24v9.02h12.94c-.58 2.96-2.26 5.48-4.78 7.18l7.73 6c4.51-4.18 7.09-10.36 7.09-17.65z"/><path fill="#FBBC05" d="M10.53 28.59c-.48-1.45-.76-2.99-.76-4.59s.27-3.14.76-4.59l-7.98-6.19C.92 16.46 0 20.12 0 24c0 3.88.92 7.54 2.56 10.78l7.97-6.19z"/><path fill="#34A853" d="M24 48c6.48 0 11.93-2.13 15.89-5.81l-7.73-6c-2.15 1.45-4.92 2.3-8.16 2.3-6.26 0-11.57-4.22-13.47-9.91l-7.98 6.19C6.51 42.62 14.62 48 24 48z"/></svg>
  Continuar con Google
</a>
<div class="sep">o con tu correo y clave</div>
{% endif %}

<form method="post" autocomplete="on" novalidate>
  <label for="email">Correo</label>
  <input class="campo" id="email" name="email" type="email" value="{{ email }}" placeholder="tucorreo@negocio.com" autocomplete="username" inputmode="email" required>
  <label for="clave">Clave</label>
  <div class="clave">
    <input class="campo" id="clave" name="clave" type="password" placeholder="Tu clave" autocomplete="current-password" required>
    <button type="button" id="ver" aria-label="Mostrar u ocultar la clave">Ver</button>
  </div>
  <button class="btn" type="submit">Ingresar</button>
</form>
<p class="ayuda" style="text-align:center;margin-top:14px">¿Sin clave? Entra con Google y créala en <b>Configuración</b>.</p>

{% if registro_url %}
<a class="btn suave" href="{{ registro_url }}">Probar {{ dias_demo }} días gratis</a>
{% endif %}
{% endblock %}
{% block scripts %}
<script>
(function(){var b=document.getElementById('ver'),i=document.getElementById('clave');
if(b&&i)b.addEventListener('click',function(){var m=i.type==='password';i.type=m?'text':'password';b.textContent=m?'Ocultar':'Ver';});})();
</script>
{% endblock %}
''',
    'registro.html': r'''{% extends "publico_base.html" %}
{% block titulo %}Crear cuenta{% endblock %}
{% block nav %}<a class="vidrio" href="{{ url_for('login') }}">Ya tengo cuenta</a>{% endblock %}
{% block hero %}
<section class="hero oculta-movil">
  <h1>{{ dias_demo }} días<br><span>gratis.</span></h1>
  <p>Crea tu cuenta en un minuto y empieza a vender hoy: punto de venta, inventario, caja y clientes, sin tarjeta de crédito.</p>
  <ul class="chips">
    <li class="vidrio">Demo de {{ dias_demo }} días</li><li class="vidrio">Sin tarjeta</li><li class="vidrio">Tus datos se conservan</li>
  </ul>
  <small>Para tiendas, tiendas de ropa y restaurantes</small>
</section>
{% endblock %}

{% block tarjeta %}
<ol class="pasos" aria-label="Paso {{ paso }} de 3">
  <li class="on"></li><li class="{{ 'on' if paso >= 2 }}"></li><li class="{{ 'on' if paso >= 3 }}"></li>
</ol>
{% if error %}<div class="aviso err" role="alert">{{ error }}</div>{% endif %}
{% if aviso %}<div class="aviso ok" role="status">{{ aviso }}</div>{% endif %}

{% if paso == 1 %}
  <h2>Crea tu cuenta</h2>
  <p class="sub">Elige cómo quieres empezar tu demo de {{ dias_demo }} días.</p>
  {% if google_url %}
  <a class="btn google" href="{{ google_url }}">
    <svg width="20" height="20" viewBox="0 0 48 48" aria-hidden="true"><path fill="#EA4335" d="M24 9.5c3.54 0 6.71 1.22 9.21 3.6l6.85-6.85C35.9 2.38 30.47 0 24 0 14.62 0 6.51 5.38 2.56 13.22l7.98 6.19C12.43 13.72 17.74 9.5 24 9.5z"/><path fill="#4285F4" d="M46.98 24.55c0-1.57-.15-3.09-.38-4.55H24v9.02h12.94c-.58 2.96-2.26 5.48-4.78 7.18l7.73 6c4.51-4.18 7.09-10.36 7.09-17.65z"/><path fill="#FBBC05" d="M10.53 28.59c-.48-1.45-.76-2.99-.76-4.59s.27-3.14.76-4.59l-7.98-6.19C.92 16.46 0 20.12 0 24c0 3.88.92 7.54 2.56 10.78l7.97-6.19z"/><path fill="#34A853" d="M24 48c6.48 0 11.93-2.13 15.89-5.81l-7.73-6c-2.15 1.45-4.92 2.3-8.16 2.3-6.26 0-11.57-4.22-13.47-9.91l-7.98 6.19C6.51 42.62 14.62 48 24 48z"/></svg>
    Continuar con Google
  </a>
  <div class="sep">o con tu correo</div>
  {% endif %}
  <form method="post" action="{{ url_for('registro') }}" novalidate>
    <input type="hidden" name="csrf" value="{{ rcsrf }}">
    <label for="email">Correo</label>
    <input class="campo" id="email" name="email" type="email" value="{{ email }}" placeholder="tucorreo@negocio.com" autocomplete="email" inputmode="email" required>
    <p class="ayuda">Te enviaremos un código de 6 dígitos para confirmar que es tuyo.</p>
    <button class="btn" type="submit">Enviarme el código</button>
  </form>

{% elif paso == 2 %}
  <h2>Revisa tu correo</h2>
  <p class="sub">Enviamos un código de 6 dígitos a <b>{{ email_oculto }}</b>. Vence en {{ vida_min }} minutos.</p>
  <form method="post" action="{{ url_for('registro_pin') }}" novalidate>
    <input type="hidden" name="csrf" value="{{ rcsrf }}">
    <input type="hidden" name="accion" value="verificar">
    <label for="pin">Código de verificación</label>
    <input class="campo pin" id="pin" name="pin" type="text" inputmode="numeric" pattern="[0-9]*" maxlength="6" autocomplete="one-time-code" placeholder="••••••" autofocus required>
    <button class="btn" type="submit">Verificar</button>
  </form>
  <form method="post" action="{{ url_for('registro_pin') }}">
    <input type="hidden" name="csrf" value="{{ rcsrf }}">
    <input type="hidden" name="accion" value="reenviar">
    <button class="btn suave" type="submit">Reenviar código</button>
  </form>
  <p class="pie-t">¿Te equivocaste de correo? <a href="{{ url_for('registro', cambiar=1) }}">Cambiarlo</a></p>
  <p class="ayuda" style="text-align:center">Si no lo ves, revisa la carpeta de spam o correo no deseado.</p>

{% else %}
  <h2>Cuéntanos de tu negocio</h2>
  <p class="sub">Correo confirmado: <b>{{ email }}</b></p>
  <form method="post" action="{{ url_for('registro_datos') }}" novalidate>
    <input type="hidden" name="csrf" value="{{ rcsrf }}">
    <label for="nombre">Tu nombre completo</label>
    <input class="campo" id="nombre" name="nombre" type="text" maxlength="160" value="{{ f.nombre }}" autocomplete="name" required>
    <label for="negocio">Nombre del negocio</label>
    <input class="campo" id="negocio" name="negocio" type="text" maxlength="160" value="{{ f.negocio }}" autocomplete="organization" required>
    <div class="fila2">
      <div>
        <label for="nit">NIT</label>
        <input class="campo" id="nit" name="nit" type="text" maxlength="20" value="{{ f.nit }}" placeholder="900123456-7" inputmode="numeric" required>
      </div>
      <div>
        <label for="usuarios">Usuarios</label>
        <input class="campo" id="usuarios" name="usuarios" type="number" min="1" max="50" value="{{ f.usuarios or 1 }}" required>
      </div>
    </div>
    <p class="ayuda">NIT con o sin dígito de verificación (si no tienes NIT, usa tu cédula). Usuarios: cuántas personas usarán el sistema.</p>
    <div class="fila2">
      <div>
        <label for="segmento">Tipo de negocio</label>
        <select class="campo" id="segmento" name="segmento">
          {% for v, n in segmentos %}<option value="{{ v }}" {{ 'selected' if f.segmento == v }}>{{ n }}</option>{% endfor %}
        </select>
      </div>
      <div>
        <label for="telefono">WhatsApp (opcional)</label>
        <input class="campo" id="telefono" name="telefono" type="tel" maxlength="20" value="{{ f.telefono }}" autocomplete="tel" inputmode="tel">
      </div>
    </div>
    <label for="clave">Crea tu clave</label>
    <div class="clave">
      <input class="campo" id="clave" name="clave" type="password" autocomplete="new-password" minlength="8" required>
      <button type="button" data-ver="clave">Ver</button>
    </div>
    <p class="ayuda">Mínimo 8 caracteres, con letras y números.</p>
    <label for="repite">Repite la clave</label>
    <input class="campo" id="repite" name="repite" type="password" autocomplete="new-password" required>
    <label class="chk"><input type="checkbox" name="acepto" value="1" {{ 'checked' if f.acepto }}>
      <span>Acepto los <a href="{{ procsis }}/legal" target="_blank" rel="noopener">términos</a> y la <a href="{{ procsis }}/tratamiento-datos" target="_blank" rel="noopener">política de tratamiento de datos personales</a> de PROCSIS.</span></label>
    <button class="btn verde" type="submit">Empezar mi demo de {{ dias_demo }} días</button>
  </form>
{% endif %}
{% endblock %}
{% block scripts %}
<script>
(function(){
  document.querySelectorAll('[data-ver]').forEach(function(b){
    b.addEventListener('click',function(){var i=document.getElementById(b.dataset.ver),m=i.type==='password';i.type=m?'text':'password';b.textContent=m?'Ocultar':'Ver';});
  });
  var p=document.getElementById('pin');
  if(p)p.addEventListener('input',function(){p.value=p.value.replace(/\D/g,'').slice(0,6);});
})();
</script>
{% endblock %}
''',
    'bloqueado.html': r'''{% extends "publico_base.html" %}
{% block titulo %}{{ titulo }}{% endblock %}
{% block hero %}<section class="hero oculta-movil"></section>{% endblock %}
{% block tarjeta %}
<h2>{{ titulo }}</h2>
<p class="sub" style="margin-bottom:6px">{{ detalle }}</p>
{% if procsis %}<a class="btn" href="{{ procsis }}/tt">Ir a PROCSIS</a>{% endif %}
<a class="btn suave" href="{{ url_for('login') if not volver else 'javascript:history.back()' }}">{% if volver %}Volver{% else %}Ir al inicio de sesión{% endif %}</a>
{% endblock %}
''',
}
app.jinja_loader = ChoiceLoader([DictLoader(PLANTILLAS_INCLUIDAS), FileSystemLoader(os.path.join(BASE, "templates")), DictLoader(_TEMPLATES_EMB)])


if __name__ == "__main__":
    app.run(debug=os.environ.get("FLASK_DEBUG") == "1", port=int(os.environ.get("PORT", 5001)))