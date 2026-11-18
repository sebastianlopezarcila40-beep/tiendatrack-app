"""Simula la API de PROCSIS para probar TiendaTrack en tu computador, sin tocar producción.
Uso:  python dev/mock_procsis.py        (escucha en http://127.0.0.1:5050)
Estados de prueba según el correo:  vencido@x.com -> demo vencida · suspendido@x.com -> suspendida · cualquier otro -> demo activa."""
import json, os
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse, parse_qs

LLAVE = os.environ.get("TIENDATRACK_API_KEY", "llave-de-prueba")


class H(BaseHTTPRequestHandler):
    def do_GET(self):
        u = urlparse(self.path)
        if u.path != "/api/v1/tiendatrack/cuenta":
            return self._r(404, {"ok": False})
        if self.headers.get("X-API-Key") != LLAVE:
            return self._r(401, {"ok": False, "error": "no autorizado"})
        email = (parse_qs(u.query).get("email") or [""])[0].lower()
        est = "vencido" if email.startswith("vencido") else "suspendido" if email.startswith("suspendido") else "demo"
        ok = est == "demo"
        self._r(200, {"ok": True, "email": email, "negocio": "Negocio de prueba", "segmento": "tienda", "estado": est, "acceso": ok,
                      "vence": "2026-12-31 23:59:59", "dias_restantes": 13 if ok else 0,
                      "plan": {"slug": "basico", "nombre": "Básico", "max_sucursales": 1, "max_usuarios": 2, "max_productos": 500, "incluye_dian": "No"}})

    def _r(self, code, obj):
        b = json.dumps(obj).encode()
        self.send_response(code); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)

    def log_message(self, *a):
        pass


if __name__ == "__main__":
    print("PROCSIS simulado en http://127.0.0.1:5050")
    HTTPServer(("127.0.0.1", 5050), H).serve_forever()
