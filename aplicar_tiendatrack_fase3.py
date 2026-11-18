# -*- coding: utf-8 -*-
"""
aplicar_tiendatrack_fase3.py  ·  Parche para app.py de PROCSIS (requiere haber aplicado la fase 2)

Permite el botón "Continuar con Google" del login de la app TiendaTrack:
  1) Ruta nueva  /tt/entrar : si el cliente ya tiene sesión lo manda directo a la app; si no, lo manda a Google
     y, al volver de Google, lo deja entrar a la app (no a /tt/cuenta).
  2) En /tt/google/callback: si venía de la app, redirige a /tt/abrir.

Uso:   python aplicar_tiendatrack_fase3.py            (busca app.py en la carpeta actual)
       python aplicar_tiendatrack_fase3.py ruta\\app.py
Es seguro correrlo dos veces. Guarda copia en app.py.bak_tt_fase3.
"""
import re
import sys
import shutil
from pathlib import Path

MARCA = "# [procsis-tiendatrack-fase3]"

PATRON = re.compile(r'(session\["tt_cuenta"\] = c\["id"\]\r?\n(\s+))return redirect\("/tt/cuenta"\)')

BLOQUE = '''
%s
# ═════════════ TIENDATRACK · FASE 3: entrada desde el login de la app (Google) ═════════════

@app.route("/tt/entrar")
def tt_entrar_app():
    """Botón 'Continuar con Google' del login de TiendaTrack."""
    c = _tt_cuenta_sesion()
    if c and _tt_estado(c) in ("demo", "activo"):
        return redirect("/tt/abrir")
    session["tt_volver"] = "app"
    return redirect("/tt/google/inicio")

''' % MARCA


def main():
    ruta = Path(sys.argv[1] if len(sys.argv) > 1 else "app.py")
    if not ruta.exists():
        sys.exit("No encuentro %s. Corre el script en la carpeta donde está app.py o pásale la ruta." % ruta)
    src = ruta.read_text(encoding="utf-8", newline="")
    if MARCA in src:
        print("Ya estaba aplicado (fase 3). No se cambió nada.")
        return
    if "[procsis-tiendatrack-fase2]" not in src:
        sys.exit("Falta la fase 2. Aplica primero aplicar_tiendatrack_fase2.py.")
    if len(PATRON.findall(src)) != 1:
        sys.exit("No encontré el punto exacto del callback de Google (¿ya lo cambiaste a mano?). No se tocó nada.")
    nuevo = PATRON.sub(lambda m: m.group(1) + 'return redirect("/tt/abrir" if session.pop("tt_volver", "") == "app" else "/tt/cuenta")', src, count=1)
    corte = nuevo.rfind('\nif __name__ == "__main__":')
    if corte < 0:
        sys.exit('No encontré el bloque  if __name__ == "__main__":  al final de app.py. No se tocó nada.')
    bloque = BLOQUE.replace("\n", "\r\n") if "\r\n" in src else BLOQUE
    nuevo = nuevo[:corte] + bloque + nuevo[corte:]
    try:
        compile(nuevo, str(ruta), "exec")
    except SyntaxError as e:
        sys.exit("El resultado tendría un error de sintaxis (%s). No se tocó nada." % e)
    shutil.copy2(ruta, str(ruta) + ".bak_tt_fase3")
    ruta.write_text(nuevo, encoding="utf-8", newline="")
    print("Listo. Copia de seguridad: %s.bak_tt_fase3" % ruta)


if __name__ == "__main__":
    main()
