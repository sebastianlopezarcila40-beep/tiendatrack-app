import os, sys, time, json, threading, re
os.environ.update(TIENDATRACK_API_KEY="llave-de-prueba", PROCSIS_URL="http://127.0.0.1:5050", TT_DB_PATH="/tmp/tt_prueba.db", TT_COOKIE_SECURE="0", SECRET_KEY="x")
if os.path.exists("/tmp/tt_prueba.db"): os.remove("/tmp/tt_prueba.db")
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__)))); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mock_procsis
from http.server import HTTPServer
srv = HTTPServer(("127.0.0.1", 5050), mock_procsis.H); threading.Thread(target=srv.serve_forever, daemon=True).start()
import app as A

def ok(c, m):
    print(("OK   " if c else "FALLA"), m)
    if not c: ok.fail += 1
ok.fail = 0

c = A.app.test_client()
ok(c.get("/").status_code == 302, "sin sesión redirige a /bloqueado")
ok(c.get("/sso?t=basura").status_code == 401, "token inválido rechazado")
viejo = A._firmar({"e": "a@x.com", "x": int(time.time()) - 5})
ok(c.get("/sso?t=" + viejo).status_code == 401, "token vencido rechazado")
falso = A._firmar({"e": "a@x.com", "x": int(time.time()) + 60}); falso = falso[:-3] + "abc"
ok(c.get("/sso?t=" + falso).status_code == 401, "firma alterada rechazada")
tok = A._firmar({"e": "dueno@x.com", "x": int(time.time()) + 60})
r = c.get("/sso?t=" + tok); ok(r.status_code == 302 and r.location.endswith("/"), "SSO válido entra")
csrf = None
def tomar_csrf():
    with c.session_transaction() as s: return s["csrf"]
csrf = tomar_csrf()
ok(c.get("/").status_code == 200, "inicio carga")
ok(c.post("/productos/nuevo", data={"nombre": "x", "precio": "100"}).status_code == 400, "POST sin CSRF rechazado")
def post(u, **d): d["csrf"] = csrf; return c.post(u, data=d, follow_redirects=False)
r = post("/productos/nuevo", nombre="Gaseosa 400ml", sku="7701", precio="2.500", costo="1.500", stock="10", stock_minimo="3", controla_stock="1", categoria="Bebidas")
ok(r.status_code == 302, "crear producto")
r = post("/productos/nuevo", nombre="Gaseosa dup", sku="7701", precio="100", controla_stock="1"); ok(r.status_code == 200, "SKU duplicado rechazado")
post("/productos/nuevo", nombre="Servicio domicilio", precio="3000")  # sin control de stock
for p in ("/productos", "/inventario", "/clientes", "/caja", "/ventas", "/ventas/exportar.csv"): ok(c.get(p).status_code == 200, "carga " + p)
ok(c.get("/pos").status_code == 302, "POS exige caja abierta")
post("/caja", accion="abrir", base="50.000")
ok(c.get("/pos").status_code == 200, "POS carga con caja abierta")
db_ = lambda sql, *a: (lambda: None)
def cobrar(**j):
    return c.post("/pos/cobrar", json=j, headers={"X-CSRF": csrf})
with A.app.app_context():
    prods = {p["nombre"]: p["id"] for p in A.db.q("SELECT id, nombre FROM productos")}
g, s = prods["Gaseosa 400ml"], prods["Servicio domicilio"]
r = cobrar(items=[{"id": g, "cant": 11}], metodo="efectivo"); ok(r.status_code == 409 and "insuficiente" in r.json["error"], "stock insuficiente bloquea")
r = cobrar(items=[{"id": g, "cant": 2}, {"id": s, "cant": 1}], metodo="efectivo", descuento=500, recibido=20000)
ok(r.status_code == 200 and r.json["cambio"] == 20000 - (5000 + 3000 - 500), "venta efectivo con descuento y cambio: %s" % r.json)
vid = r.json["id"]
r = cobrar(items=[{"id": g, "cant": 1}], metodo="efectivo", recibido=1000); ok(r.status_code == 400, "efectivo insuficiente rechazado")
r = cobrar(items=[{"id": g, "cant": 1}], metodo="tarjeta", descuento=999999); ok(r.status_code == 200, "descuento limitado al subtotal")
r = cobrar(items=[{"id": 99999, "cant": 1}], metodo="tarjeta"); ok(r.status_code == 409, "producto ajeno/inexistente rechazado")
r = cobrar(items=["x", 5], metodo="tarjeta"); ok(r.status_code == 400, "items malformados no rompen")
with A.app.app_context():
    st = A.db.uno("SELECT stock FROM productos WHERE id=?", g)["stock"]
ok(st == 10 - 2 - 1, "stock descontado (queda %s)" % st)
ok(c.get("/ventas/%d" % vid).status_code == 200 and c.get("/ventas/%d/recibo" % vid).status_code == 200, "detalle y recibo")
post("/ventas/%d/anular" % vid)
with A.app.app_context():
    st = A.db.uno("SELECT stock FROM productos WHERE id=?", g)["stock"]
ok(st == 10 - 1, "anular devuelve stock (queda %s)" % st)
post("/ventas/%d/anular" % vid)
with A.app.app_context(): st2 = A.db.uno("SELECT stock FROM productos WHERE id=?", g)["stock"]
ok(st2 == st, "anular dos veces no duplica el stock")
post("/inventario/mover", producto_id=g, tipo="salida", cantidad="100"); 
with A.app.app_context(): ok(A.db.uno("SELECT stock FROM productos WHERE id=?", g)["stock"] == st, "salida mayor al stock rechazada")
post("/inventario/mover", producto_id=g, tipo="ajuste", cantidad="20", nota="conteo")
with A.app.app_context(): ok(A.db.uno("SELECT stock FROM productos WHERE id=?", g)["stock"] == 20, "ajuste a conteo real")
post("/clientes", nombre="=cmd|' /C calc'!A0", documento="123")
csv = c.get("/ventas/exportar.csv").data.decode(); ok("Número" in csv, "CSV exporta")
r = post("/caja", accion="cerrar", contado="55.000"); ok(r.status_code == 302 and "/caja/" in r.location, "cerrar caja")
with A.app.app_context():
    cj = A.db.uno("SELECT * FROM cajas ORDER BY id DESC LIMIT 1")
ok(cj["esperado"] == 50000, "efectivo esperado = base + ventas efectivo no anuladas (%s)" % cj["esperado"])
ok(c.get(r.location).status_code == 200, "detalle de cierre")
# aislamiento entre negocios
c2 = A.app.test_client(); c2.get("/sso?t=" + A._firmar({"e": "otro@x.com", "x": int(time.time()) + 60}))
ok(c2.get("/ventas/%d" % vid).status_code == 404, "otro negocio no ve ventas ajenas")
ok(c2.get("/productos/%d/editar" % g).status_code == 404, "otro negocio no edita productos ajenos")
# cuentas vencidas / suspendidas
for correo, esperado in (("vencido@x.com", 403), ("suspendido@x.com", 403)):
    c3 = A.app.test_client(); r = c3.get("/sso?t=" + A._firmar({"e": correo, "x": int(time.time()) + 60}), follow_redirects=True)
    ok(r.status_code == 403 and c3.get("/pos", follow_redirects=True).status_code == 403, "bloqueada: " + correo)
# límite de plan
A_lim = A.app.test_client(); A_lim.get("/sso?t=" + A._firmar({"e": "limite@x.com", "x": int(time.time()) + 60}))
with A_lim.session_transaction() as s: s["plan"]["max_productos"] = 1; csrf_l = s["csrf"]; s.modified = True
A_lim.post("/productos/nuevo", data={"nombre": "uno", "precio": "10", "csrf": csrf_l})
r = A_lim.post("/productos/nuevo", data={"nombre": "dos", "precio": "10", "csrf": csrf_l}); ok(r.status_code == 200 and "límite" in r.data.decode(), "límite de productos del plan")
print("\nFALLAS:", ok.fail); sys.exit(1 if ok.fail else 0)
