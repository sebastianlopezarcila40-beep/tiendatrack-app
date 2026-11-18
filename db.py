"""Capa mínima de base de datos: SQLite (desarrollo) o PostgreSQL/Supabase (producción, con DATABASE_URL).
El SQL se escribe con ? y se adapta solo. Fechas como texto 'YYYY-MM-DD HH:MM:SS' (hora de Colombia)."""
import os
import sqlite3
from flask import g

URL = (os.environ.get("DATABASE_URL") or "").strip()
PG = URL.startswith(("postgres://", "postgresql://"))
SQLITE_PATH = os.environ.get("TT_DB_PATH", "tiendatrack.db")

if PG:
    import psycopg2
    import psycopg2.extras
    if URL.startswith("postgres://"):
        URL = "postgresql://" + URL[len("postgres://"):]
    if "sslmode=" not in URL:
        URL += ("&" if "?" in URL else "?") + "sslmode=require"


def _conectar():
    if not PG and os.environ.get("VERCEL"):
        raise RuntimeError("Falta DATABASE_URL: en Vercel no se puede usar SQLite. Pega la cadena de conexión de Supabase en las variables de entorno.")
    if PG:
        return psycopg2.connect(URL, cursor_factory=psycopg2.extras.RealDictCursor, connect_timeout=8)
    c = sqlite3.connect(SQLITE_PATH, timeout=15)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA foreign_keys=ON")
    return c


def conn():
    if "db" not in g:
        g.db = _conectar()
    return g.db


def cerrar(_exc=None):
    c = g.pop("db", None)
    if c is not None:
        try:
            c.rollback()
        except Exception:
            pass
        c.close()


def _sql(sql):
    return sql.replace("?", "%s") if PG else sql


def q(sql, *params):
    """Devuelve lista de dicts."""
    cur = conn().cursor()
    cur.execute(_sql(sql), params)
    filas = cur.fetchall()
    cur.close()
    return [dict(f) for f in filas]


def uno(sql, *params):
    filas = q(sql, *params)
    return filas[0] if filas else None


def x(sql, *params):
    """Ejecuta INSERT/UPDATE/DELETE. Con INSERT ... RETURNING id devuelve el id. No hace commit."""
    cur = conn().cursor()
    cur.execute(_sql(sql), params)
    nuevo = None
    if " returning " in sql.lower():
        r = cur.fetchone()
        nuevo = (dict(r) or {}).get("id") if r else None
    cur.close()
    return nuevo


def commit():
    conn().commit()


def rollback():
    conn().rollback()


def inicio_transaccion():
    """Bloquea escritura concurrente en SQLite (en PostgreSQL se usa FOR UPDATE en las consultas)."""
    if not PG:
        conn().execute("BEGIN IMMEDIATE")


FOR_UPDATE = " FOR UPDATE" if PG else ""

_PK = "SERIAL PRIMARY KEY" if PG else "INTEGER PRIMARY KEY AUTOINCREMENT"

DDL = (
    "CREATE TABLE IF NOT EXISTS negocios (id %s, email VARCHAR(160) UNIQUE NOT NULL, nombre VARCHAR(160) DEFAULT '', segmento VARCHAR(20) DEFAULT 'tienda', creado_en VARCHAR(20) DEFAULT '', clave_hash VARCHAR(255) DEFAULT '', meta_mensual BIGINT DEFAULT 0)" % _PK,
    "CREATE TABLE IF NOT EXISTS categorias (id %s, negocio_id INTEGER NOT NULL, nombre VARCHAR(80) NOT NULL)" % _PK,
    "CREATE TABLE IF NOT EXISTS productos (id %s, negocio_id INTEGER NOT NULL, categoria_id INTEGER DEFAULT 0, nombre VARCHAR(160) NOT NULL, sku VARCHAR(60) DEFAULT '', "
    "precio BIGINT DEFAULT 0, costo BIGINT DEFAULT 0, stock INTEGER DEFAULT 0, stock_minimo INTEGER DEFAULT 0, controla_stock INTEGER DEFAULT 1, activo INTEGER DEFAULT 1, creado_en VARCHAR(20) DEFAULT '')" % _PK,
    "CREATE TABLE IF NOT EXISTS movimientos (id %s, negocio_id INTEGER NOT NULL, producto_id INTEGER NOT NULL, tipo VARCHAR(20) NOT NULL, cantidad INTEGER NOT NULL, nota VARCHAR(200) DEFAULT '', venta_id INTEGER DEFAULT 0, creado_en VARCHAR(20) DEFAULT '')" % _PK,
    "CREATE TABLE IF NOT EXISTS clientes (id %s, negocio_id INTEGER NOT NULL, nombre VARCHAR(160) NOT NULL, documento VARCHAR(30) DEFAULT '', telefono VARCHAR(30) DEFAULT '', email VARCHAR(160) DEFAULT '', creado_en VARCHAR(20) DEFAULT '')" % _PK,
    "CREATE TABLE IF NOT EXISTS cajas (id %s, negocio_id INTEGER NOT NULL, abierta_en VARCHAR(20) DEFAULT '', cerrada_en VARCHAR(20) DEFAULT '', base BIGINT DEFAULT 0, esperado BIGINT DEFAULT 0, contado BIGINT DEFAULT 0, estado VARCHAR(10) DEFAULT 'abierta', nota VARCHAR(200) DEFAULT '')" % _PK,
    "CREATE TABLE IF NOT EXISTS ventas (id %s, negocio_id INTEGER NOT NULL, numero INTEGER NOT NULL, cliente_id INTEGER DEFAULT 0, caja_id INTEGER DEFAULT 0, subtotal BIGINT DEFAULT 0, descuento BIGINT DEFAULT 0, total BIGINT DEFAULT 0, "
    "metodo VARCHAR(20) DEFAULT 'efectivo', recibido BIGINT DEFAULT 0, cambio BIGINT DEFAULT 0, estado VARCHAR(10) DEFAULT 'pagada', creado_en VARCHAR(20) DEFAULT '', anulada_en VARCHAR(20) DEFAULT '')" % _PK,
    "CREATE TABLE IF NOT EXISTS venta_items (id %s, venta_id INTEGER NOT NULL, producto_id INTEGER NOT NULL, nombre VARCHAR(160) DEFAULT '', cantidad INTEGER NOT NULL, precio BIGINT DEFAULT 0, total BIGINT DEFAULT 0, costo BIGINT DEFAULT 0)" % _PK,
    "CREATE TABLE IF NOT EXISTS login_fallos (id %s, clave VARCHAR(200) NOT NULL, creado_en VARCHAR(20) NOT NULL)" % _PK,
    "CREATE INDEX IF NOT EXISTS ix_fallos ON login_fallos (clave, creado_en)",
    "CREATE INDEX IF NOT EXISTS ix_prod_neg ON productos (negocio_id)",
    "CREATE INDEX IF NOT EXISTS ix_vent_neg ON ventas (negocio_id, creado_en)",
    "CREATE INDEX IF NOT EXISTS ix_mov_neg ON movimientos (negocio_id, producto_id)",
    "CREATE INDEX IF NOT EXISTS ix_item_venta ON venta_items (venta_id)",
)


_IF = "IF NOT EXISTS " if PG else ""
# Para bases creadas con la versión anterior: agrega las columnas nuevas si faltan.
MIGRA = (
    "ALTER TABLE negocios ADD COLUMN %sclave_hash VARCHAR(255) DEFAULT ''" % _IF,
    "ALTER TABLE negocios ADD COLUMN %smeta_mensual BIGINT DEFAULT 0" % _IF,
    "ALTER TABLE venta_items ADD COLUMN %scosto BIGINT DEFAULT 0" % _IF,
)


def crear_tablas():
    c = _conectar()
    cur = c.cursor()
    for d in DDL:
        cur.execute(d)
    c.commit()
    for m in MIGRA:
        try:
            cur.execute(m)
            c.commit()
        except Exception:
            c.rollback()  # la columna ya existe
    cur.close()
    c.close()
