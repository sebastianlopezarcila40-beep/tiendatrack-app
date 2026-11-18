# -*- coding: utf-8 -*-
"""
aplicar_tiendatrack_fase2.py  ·  Parche para app.py de PROCSIS

Conecta /tt/cuenta con la aplicación TiendaTrack (que vive en un proyecto aparte):
  1) Agrega la ruta  /tt/abrir  que firma un token de acceso de 2 minutos y manda al cliente a TIENDATRACK_APP_URL/sso
  2) Cambia el texto "La aplicación TiendaTrack se habilitará aquí..." por el botón "Abrir TiendaTrack"

Variables de entorno nuevas en PROCSIS (Vercel):  TIENDATRACK_APP_URL   (ej. https://tiendatrack.vercel.app)
Ya existente y compartida con la app:            TIENDATRACK_API_KEY

Uso:   python aplicar_tiendatrack_fase2.py            (busca app.py en la carpeta actual)
       python aplicar_tiendatrack_fase2.py ruta\\app.py
Es seguro correrlo dos veces. Guarda copia en app.py.bak_tt_fase2.
"""
import sys
import shutil
from pathlib import Path

MARCA = "# [procsis-tiendatrack-fase2]"

VIEJO = ('"<p>La aplicación TiendaTrack se habilitará aquí cuando esté disponible. '
         'Tu cuenta y tu demo ya quedaron registradas.</p></div>")')
NUEVO = ('"<p>Abre tu punto de venta, inventario, clientes y caja.</p>" + _tt_boton_abrir() + "</div>")')

BLOQUE = '''
%s
# ═════════════ TIENDATRACK · FASE 2: acceso a la aplicación del negocio (SSO firmado hacia la app aparte) ═════════════
# La app usa la MISMA llave (TIENDATRACK_API_KEY) para verificar el token y para consultar /api/v1/tiendatrack/cuenta.

def _tt_app_url():
    return (os.environ.get("TIENDATRACK_APP_URL") or "").strip().rstrip("/")


def _tt_boton_abrir():
    est = ""
    try:
        est = _tt_estado(_tt_cuenta_sesion())
    except Exception:
        pass
    if not _tt_app_url() or not (os.environ.get("TIENDATRACK_API_KEY") or "").strip():
        return "<p class='tt-msg'>La aplicación aún no está conectada. Escríbenos y te avisamos cuando esté lista.</p>"
    if est not in ("demo", "activo"):
        return ""
    return "<p><a class='tt-btn' style='display:inline-block;padding:12px 22px;background:#0020C2;color:#fff;border-radius:10px;text-decoration:none;font-weight:700' href='/tt/abrir'>Abrir TiendaTrack</a></p>"


def _tt_token_app(email, segundos=120):
    cuerpo = _tt_b64.urlsafe_b64encode(json.dumps({"e": email, "x": int(__import__("time").time()) + segundos},
                                                    separators=(",", ":")).encode()).decode().rstrip("=")
    firma = _tt_hm.new((os.environ.get("TIENDATRACK_API_KEY") or "").strip().encode(), cuerpo.encode(), _tt_hl.sha256).hexdigest()
    return cuerpo + "." + firma


@app.route("/tt/abrir")
def tt_abrir_app():
    c = _tt_cuenta_sesion()
    if not c:
        return redirect("/tt")
    destino = _tt_app_url()
    if not destino or not (os.environ.get("TIENDATRACK_API_KEY") or "").strip():
        return _tt_html("Aplicación no disponible", "<div class='tt-box'><h2>La aplicación aún no está conectada</h2><p>Estamos terminando de configurarla. Vuelve en un momento.</p></div>", c, 503)
    if _tt_estado(c) not in ("demo", "activo"):
        return redirect("/tt/cuenta")
    try:
        registrar_auditoria("TiendaTrack abrir app", "cuenta=%%s" %% c["id"])
    except Exception:
        pass
    return redirect(destino + "/sso?t=" + _tt_up.quote(_tt_token_app(c["email"]), safe=""))

''' % MARCA


def main():
    ruta = Path(sys.argv[1] if len(sys.argv) > 1 else "app.py")
    if not ruta.exists():
        sys.exit("No encuentro %s. Corre el script en la carpeta donde está app.py o pásale la ruta." % ruta)
    src = ruta.read_text(encoding="utf-8", newline="")
    if MARCA in src:
        print("Ya estaba aplicado (fase 2). No se cambió nada.")
        return
    if "[procsis-tiendatrack-fase1]" not in src:
        sys.exit("Falta la fase 1 de TiendaTrack en este app.py. Aplica primero aplicar_tiendatrack_fase1.py.")
    if src.count(VIEJO) != 1:
        sys.exit("No encontré el texto del botón de la aplicación en /tt/cuenta (¿ya lo cambiaste a mano?). No se tocó nada.")
    corte = src.rfind('\nif __name__ == "__main__":')
    if corte < 0:
        sys.exit('No encontré el bloque  if __name__ == "__main__":  al final de app.py. No se tocó nada.')
    crlf = "\r\n" in src
    bloque = BLOQUE.replace("\n", "\r\n") if crlf else BLOQUE
    nuevo = src.replace(VIEJO, NUEVO)
    corte = nuevo.rfind('\nif __name__ == "__main__":')
    nuevo = nuevo[:corte] + bloque + nuevo[corte:]
    try:
        compile(nuevo, str(ruta), "exec")
    except SyntaxError as e:
        sys.exit("El resultado tendría un error de sintaxis (%s). No se tocó nada." % e)
    shutil.copy2(ruta, str(ruta) + ".bak_tt_fase2")
    ruta.write_text(nuevo, encoding="utf-8", newline="")
    print("Listo. Copia de seguridad: %s.bak_tt_fase2" % ruta)
    print("Ahora en Vercel (proyecto PROCSIS) agrega TIENDATRACK_APP_URL con la dirección de la app TiendaTrack y vuelve a desplegar.")


if __name__ == "__main__":
    main()
