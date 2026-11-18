"""TiendaTrack · aplicación del negocio (productos, inventario, punto de venta, caja, clientes).
Es una app aparte de PROCSIS. El acceso llega desde PROCSIS con un token firmado (SSO) y la vigencia
de la cuenta (demo / plan activo / vencido) se consulta a la API de PROCSIS.
Variables de entorno: SECRET_KEY, DATABASE_URL, PROCSIS_URL, TIENDATRACK_API_KEY. Ver README.md."""
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

from flask import (Flask, Response, abort, flash, jsonify, redirect, render_template, request,
                   session, url_for)

from werkzeug.security import check_password_hash, generate_password_hash

import db

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
app = Flask(
    __name__,
    template_folder=os.path.join(BASE_DIR, "templates"),
    static_folder=os.path.join(BASE_DIR, "static"),
)
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


def _asegurar_tablas():
    if not _TABLAS["ok"]:
        db.crear_tablas()
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
        return n["id"]
    nid = db.x("INSERT INTO negocios (email, nombre, segmento, creado_en) VALUES (?,?,?,?) RETURNING id",
               email, limpio(info.get("negocio")) or email, limpio(info.get("segmento"), 20) or "tienda", ahora_s())
    db.commit()
    return nid


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
Usa el código con precaución.
return _iniciar_sesion(email, info)
return render_template("login.html", error=error, email=email, google=bool(PROCSIS_URL)), (401 if error else 200)
@app.route("/salir")
def salir():
session.clear()
return redirect(url_for("login"))
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
@app.route("/salud")
def salud():
return {"ok": True}

───────────────────────── guardia global ─────────────────────────

_LIBRES = {"sso", "login", "salir", "bloqueado", "salud", "static"}
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

───────────────────────── inicio ─────────────────────────

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
n_bajo = db.uno("SELECT COUNT() AS c FROM productos WHERE negocio_id=? AND activo=1 AND controla_stock=1 AND stock<=stock_minimo", n)["c"]
desde = (hoy - timedelta(days=13)).strftime("%Y-%m-%d")
por_dia = {f["d"]: int(f["t"]) for f in db.q(
"SELECT substr(creado_en,1,10) AS d, SUM(total) AS t FROM ventas WHERE negocio_id=? AND estado='pagada' AND substr(creado_en,1,10)>=? GROUP BY substr(creado_en,1,10)", n, desde)}
serie = [{"d": (hoy - timedelta(days=13 - i)).strftime("%Y-%m-%d")} for i in range(14)]
for sdt in serie:
sdt["t"] = por_dia.get(sdt["d"], 0)
mx = max([sdt["t"] for sdt in serie] +)
for sdt in serie:
sdt["h"] = max(3, int(sdt["t"] * 100 / mx)) if sdt["t"] else 3
top = db.q("SELECT i.nombre AS nombre, SUM(i.cantidad) AS u, SUM(i.total) AS t FROM venta_items i JOIN ventas v ON v.id=i.venta_id "
"WHERE v.negocio_id=? AND v.estado='pagada' AND substr(v.creado_en,1,10)>=? GROUP BY i.nombre ORDER BY SUM(i.total) DESC LIMIT 5", n, mes_ini.strftime("%Y-%m-%d"))
por_metodo = db.q("SELECT metodo, SUM(total) AS t FROM ventas WHERE negocio_id=? AND estado='pagada' AND substr(v.creado_en,1,10)>=? GROUP BY metodo ORDER BY SUM(total) DESC", n, mes_ini.strftime("%Y-%m-%d"))
tot_m = sum(int(m["t"]) for m in por_metodo) or 1
for m in por_metodo:
m["nombre"] = METODOS_D.get(m["metodo"], m["metodo"])
m["pct"] = int(round(int(m["t"]) * 100 / tot_m))
caja = db.uno("SELECT * FROM cajas WHERE negocio_id=? AND estado='abierta' ORDER BY id DESC LIMIT 1", n)
n_prod = db.uno("SELECT COUNT() AS c FROM productos WHERE negocio_id=? AND activo=1", n)["c"]
return render_template("inicio.html", n_hoy=n_hoy, t_hoy=t_hoy, d_hoy=_delta(t_hoy, t_ayer), t_ayer=t_ayer, n_mes=n_mes, t_mes=t_mes, d_mes=_delta(t_mes, t_prev),
util=util, meta=meta, avance=avance, ticket=ticket, bajo=bajo, n_bajo=n_bajo, serie=serie, top=top, por_metodo=por_metodo,
caja=caja, n_prod=n_prod, mes_nombre=("enero febrero marzo abril mayo junio julio agosto septiembre octubre noviembre diciembre".split())[hoy.month - 1], pagina="inicio")

───────────────────────── configuración (clave y meta) ─────────────────────────

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

───────────────────────── productos ─────────────────────────

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
filas = db.q(sql, par)
total = db.uno("SELECT COUNT() AS c FROM productos WHERE negocio_id=? AND activo=1", n)["c"]
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
@app.route("/productos/int:pid/editar", methods=["GET", "POST"])
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
@app.route("/productos/int:pid/estado", methods=["POST"])
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

───────────────────────── inventario ─────────────────────────

@app.route("/inventario")
def inventario():
n = nid()
buscar = limpio(request.args.get("q"), 60)
sql = "SELECT id, nombre, sku, stock, stock_minimo FROM productos WHERE negocio_id=? AND activo=1 AND controla_stock=1"
par = [n]
if buscar:
sql += " AND (lower(nombre) LIKE ? OR lower(sku) LIKE ?)"
par += ["%" + buscar.lower() + "%"] * 2
filas = db.q(sql + " ORDER BY (CASE WHEN stock<=stock_minimo THEN 0 ELSE 1 END), nombre LIMIT 300", par)
movs = db.q("SELECT m., p.nombre AS producto FROM movimientos m JOIN productos p ON p.id=m.producto_id WHERE m.negocio_id=? ORDER BY m.id DESC LIMIT 30", n)
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

───────────────────────── clientes ─────────────────────────

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
sql = ("SELECT c., (SELECT COUNT() FROM ventas v WHERE v.cliente_id=c.id AND v.estado='pagada') AS compras, "
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

───────────────────────── caja ─────────────────────────

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
@app.route("/caja/int:cid")
def caja_detalle(cid):
c = db.uno("SELECT * FROM cajas WHERE id=? AND negocio_id=?", cid, nid())
if not c:
abort(404)
por, efectivo, total, nventas, esperado = _resumen_caja(c)
return render_template("caja_detalle.html", c=c, por=por, efectivo=efectivo, total=total, nventas=nventas, esperado=esperado, pagina="caja")

───────────────────────── punto de venta ─────────────────────────

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

───────────────────────── ventas ─────────────────────────

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
filas, desde, hasta, _m = consulta_ventas(20000)
out = io.StringIO()
w = csv.writer(out, delimiter=";")
w.writerow(["Número", "Fecha", "Cliente", "Método", "Subtotal", "Descuento", "Total", "Estado"])
for f in filas:
w.writerow([f["numero"], f["creado_en"], celda(f["cliente"]), METODOS_D.get(f["metodo"], f["metodo"]), f["subtotal"], f["descuento"], f["total"], f["estado"]])
return Response("\ufeff" + out.getvalue(), mimetype="text/csv; charset=utf-8",
headers={"Content-Disposition": "attachment; filename=ventas%s_a%s.csv" % (desde, hasta)})
def _venta(vid):
v = db.uno("SELECT v.*, COALESCE(c.nombre,'') AS cliente, COALESCE(c.documento,'') AS cliente_doc FROM ventas v LEFT JOIN clientes c ON c.id=v.cliente_id WHERE v.id=? AND v.negocio_id=?", vid, nid())
if not v:
abort(404)
return v, db.q("SELECT * FROM venta_items WHERE venta_id=? ORDER BY id", vid)
@app.route("/ventas/int:vid")
def venta_detalle(vid):
v, items = _venta(vid)
return render_template("venta_detalle.html", v=v, items=items, pagina="ventas")
@app.route("/ventas/int:vid/recibo")
def venta_recibo(vid):
v, items = _venta(vid)
return render_template("recibo.html", v=v, items=items, nuevo=bool(request.args.get("nuevo")))
@app.route("/ventas/int:vid/anular", methods=["POST"])
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
if name == "main":
app.run(debug=os.environ.get("FLASK_DEBUG") == "1", port=int(os.environ.get("PORT", 5001)))