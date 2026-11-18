# TiendaTrack · app del negocio

App aparte de PROCSIS. Incluye: Inicio (métricas), Productos, Inventario (entradas/salidas/conteo con historial), Clientes,
Punto de venta (efectivo, tarjeta, transferencia, Nequi; descuento; cambio; recibo imprimible), Caja (apertura/cierre con diferencia) y Ventas (filtros, CSV, anulación que devuelve stock).

## Cómo entra el cliente
PROCSIS (`/tt/cuenta` → botón "Abrir TiendaTrack" → `/tt/abrir`) firma un token de 2 minutos con `TIENDATRACK_API_KEY` y redirige a `TU_APP/sso?t=...`.
La app verifica la firma, consulta `PROCSIS_URL/api/v1/tiendatrack/cuenta` y respeta `demo` / `activo` / `vencido` / `suspendido` y los límites del plan (`max_productos`).
La vigencia se vuelve a consultar cada 10 minutos.

## Variables de entorno
| Variable | Qué es |
|---|---|
| `SECRET_KEY` | Cadena larga aleatoria para las cookies de sesión |
| `DATABASE_URL` | Postgres de Supabase (usa el "pooler", puerto 6543). Sin ella usa SQLite local |
| `PROCSIS_URL` | Dirección de tu PROCSIS, sin `/` final |
| `TIENDATRACK_API_KEY` | La misma que ya usa PROCSIS |

## Probar en tu computador
```
pip install -r requirements.txt
python dev/mock_procsis.py            # terminal 1: PROCSIS simulado (puerto 5050)
set TIENDATRACK_API_KEY=llave-de-prueba & set PROCSIS_URL=http://127.0.0.1:5050 & set TT_COOKIE_SECURE=0   # Windows (en Linux/Mac usa export)
python app.py                         # terminal 2: http://127.0.0.1:5001
python dev/prueba.py                  # pruebas automáticas (SQLite)
```
## Publicar en Vercel
Sube la carpeta como proyecto nuevo, agrega las 4 variables y despliega. Las tablas se crean solas la primera vez que alguien entra.
Después, en el proyecto PROCSIS agrega `TIENDATRACK_APP_URL` con la dirección de esta app.

## Pendiente para siguientes fases
Variantes talla/color (ropa), mesas y comandas (restaurante), varios usuarios por negocio (`max_usuarios`) y sucursales, factura electrónica DIAN.
