#!/usr/bin/env python3
"""
ОБЪЕДИНЁННЫЙ Bybit-бот (3 файла: config.py + main.py + requirements.txt)
=========================================================================
Торговый движок "памп -> шорт" (обнаружение пампа, подтверждённый разворот,
защита прибыли, умный выход) + учёт закрытых сделок и отчётность
(статистика, баланс, комиссии, CSV-экспорт, риск-алерты) под ОДНИМ
Telegram-ботом и ОДНИМ REST-клиентом Bybit.

Установка:
    pip install -r requirements.txt --break-system-packages

Запуск:
    python main.py
"""

from __future__ import annotations

import concurrent.futures
import base64
import csv
import hashlib
import io
import json
import logging
import math
import os
import queue
import re
import signal
import sqlite3
import sys
import tempfile
import threading
import time
import traceback
import uuid
import zlib
from collections import deque
from datetime import datetime, timedelta, timezone
from decimal import Decimal, ROUND_DOWN, ROUND_CEILING, ROUND_HALF_UP
from logging.handlers import RotatingFileHandler
from typing import Deque, Dict, List, Optional, Tuple

import telebot
from telebot import types
from pybit.unified_trading import HTTP, WebSocket

import config as cfg

BASE_DIR = os.path.dirname(os.path.abspath(__file__))


def resolve_path(path: str) -> str:
    """Относительные пути из config.py (DB_PATH, LOG_FILE, STATE_FILE,
    TRADES_FILE) резолвятся относительно папки со скриптом, а не текущей
    рабочей директории процесса. Это защищает от типичной проблемы
    деплоя (Docker/systemd/supervisor), когда сервис запускается из
    другого cwd и бот в другом окружении "не видит" свою же старую базу
    или пишет лог не туда, откуда его потом ищут.

    Абсолютные пути (например, DB_PATH=/data/trades.db — точка монтирования
    постоянного диска на Railway и подобных платформах) возвращаются как
    есть. В обоих случаях папка назначения создаётся заранее, если её ещё
    нет — иначе первый же запуск на чистом Volume упадёт с FileNotFoundError."""
    full = path if os.path.isabs(path) else os.path.join(BASE_DIR, path)
    os.makedirs(os.path.dirname(full) or ".", exist_ok=True)
    return full


def _plain_num_str(value) -> str:
    """Число для параметров ордера БЕЗ экспоненты и лишних нулей.

    str(0.00001) даёт '1e-05', а API биржи ждёт обычную десятичную запись;
    у дешёвых монет (шаг цены/количества 1e-5 и меньше) ордер иначе мог бы
    отклоняться как некорректный. Decimal(str(x)) сохраняет кратчайшую
    запись числа, поэтому лишних знаков не появляется."""
    try:
        d = Decimal(str(value))
    except ArithmeticError:
        raise ValueError(f"недопустимое число для ордера: {value!r}") from None
    if not d.is_finite():
        raise ValueError(f"недопустимое число для ордера: {value!r}")
    if d == 0:
        return "0"
    return format(d.normalize(), "f")


# ============================================================================
# УЧЁТ СДЕЛОК: SQLite-база (trades / meta / settings / notification_log)
# ============================================================================

_db_lock = threading.RLock()
_conn: sqlite3.Connection = None


def init_db():
    global _conn
    with _db_lock:
        # Не оставляем прежнее соединение открытым при повторной инициализации.
        if _conn is not None:
            try:
                _conn.close()
            except Exception:
                logging.getLogger(__name__).exception("Не удалось закрыть прежнее SQLite-соединение")
            _conn = None
        db_path = resolve_path(cfg.DB_PATH)
        try:
            _conn = sqlite3.connect(db_path, timeout=30.0, check_same_thread=False)
        except Exception:
            _conn = None
            raise
        _conn.row_factory = sqlite3.Row
        # Настройка соединения выполняется в защищённом блоке: если WAL/PRAGMA
        # завершится ошибкой (readonly, диск заполнен, повреждённый файл),
        # соединение не останется открытым и частично инициализированным.
        try:
            _conn.execute("PRAGMA busy_timeout=30000")
            _conn.execute("PRAGMA foreign_keys=ON")
            journal_row = _conn.execute("PRAGMA journal_mode=WAL").fetchone()
            journal_mode = str(journal_row[0]).lower() if journal_row else ""
            if journal_mode != "wal":
                raise sqlite3.DatabaseError(
                    f"Не удалось включить WAL для {db_path}: получен режим {journal_mode or 'unknown'}"
                )
            _conn.execute("PRAGMA synchronous=FULL")
            _conn.execute("PRAGMA wal_autocheckpoint=1000")
            _conn.execute("BEGIN IMMEDIATE")
        except Exception:
            try:
                _conn.close()
            finally:
                _conn = None
            raise
        try:
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS trades (
                    id TEXT PRIMARY KEY,
                    symbol TEXT,
                    side TEXT,
                    qty REAL,
                    entry_price REAL,
                    exit_price REAL,
                    closed_pnl REAL,
                    created_time INTEGER,
                    updated_time INTEGER,
                    leverage REAL,
                    source TEXT
                )
                """
            )
            for ddl in (
                "ALTER TABLE trades ADD COLUMN leverage REAL",
                "ALTER TABLE trades ADD COLUMN source TEXT",
            ):
                try:
                    _conn.execute(ddl)
                except sqlite3.OperationalError as exc:
                    if "duplicate column name" not in str(exc).lower():
                        raise

            _conn.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT)")
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS notification_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    sent_at INTEGER,
                    text TEXT
                )
                """
            )
            # Реестр позиций, открытых ИМЕННО ботом (не вручную пользователем).
            # Строка появляется в момент открытия сделки ботом и удаляется, когда
            # бот сам обнаруживает её закрытие. Переживает рестарты — это
            # единственный надёжный способ отличить "свою" сделку от вручную
            # открытой пользователем на бирже: у Bybit в closed-pnl нет флага
            # "кто открыл позицию", поэтому единственный источник истины — то,
            # что бот сам запомнил в момент СВОЕГО открытия ордера.
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS bot_positions (
                    symbol TEXT PRIMARY KEY,
                    entry_price REAL,
                    qty REAL,
                    is_long INTEGER,
                    tp_price REAL,
                    sl_price REAL,
                    tick_size REAL,
                    margin_usdt REAL,
                    profit_locked INTEGER DEFAULT 0,
                    opened_at INTEGER
                )
                """
            )
            # Позиции, открытые из вручную присланного в чат поста-сигнала
            # (см. parse_signal_post) — два лимитных входа + стоп, без тейков
            # (тейки фиксирует вручную сам пользователь). Таблица нужна, чтобы
            # фоновый монитор (signal_positions_monitor_loop) знал, за какими
            # символами следить, и пережила рестарт бота.
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS signal_positions (
                    symbol TEXT PRIMARY KEY,
                    side TEXT,
                    entries_json TEXT,
                    targets_json TEXT,
                    stop_price REAL,
                    avg_entry_price REAL,
                    qty_total REAL,
                    opened_qty REAL,
                    last_known_qty REAL,
                    entry_order_ids_json TEXT,
                    breakeven_after_tp1 INTEGER DEFAULT 0,
                    breakeven_done INTEGER DEFAULT 0,
                    status TEXT DEFAULT 'pending',
                    created_at INTEGER
                )
                """
            )
            for ddl in (
                "ALTER TABLE bot_positions ADD COLUMN tp_targets_json TEXT DEFAULT '{}'",
                "ALTER TABLE bot_positions ADD COLUMN tp_close_pcts_json TEXT DEFAULT '[25,25,25,100]'",
                "ALTER TABLE bot_positions ADD COLUMN tp_order_ids_json TEXT DEFAULT '{}'",
                "ALTER TABLE bot_positions ADD COLUMN tp_initial_qty REAL DEFAULT 0",
                "ALTER TABLE bot_positions ADD COLUMN tp_done_json TEXT DEFAULT '{}'",
                "ALTER TABLE bot_positions ADD COLUMN tp_filled_qty_json TEXT DEFAULT '{}'",
                "ALTER TABLE bot_positions ADD COLUMN tp1_breakeven_done INTEGER DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN tp_hits_count INTEGER DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN tp2_partial_done INTEGER DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN tp_orders_set INTEGER DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN tp_orders_qty_basis REAL DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN stale_entries_cancelled INTEGER DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN single_target_is_partial INTEGER DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN tp2_limit_order_id TEXT",
                "ALTER TABLE signal_positions ADD COLUMN source TEXT DEFAULT 'post'",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_targets_json TEXT DEFAULT '[]'",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_close_pcts_json TEXT DEFAULT '[25,25,25,100]'",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_order_ids_json TEXT DEFAULT '{}'",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_initial_qty REAL DEFAULT 0",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_done_json TEXT DEFAULT '{}'",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_filled_qty_json TEXT DEFAULT '{}'",
                "ALTER TABLE signal_positions ADD COLUMN manual_tp_overrides_json TEXT DEFAULT '{}'",
                "ALTER TABLE signal_positions ADD COLUMN manual_sl_override INTEGER DEFAULT 0",
            ):
                try:
                    _conn.execute(ddl)
                except sqlite3.OperationalError as exc:
                    # Ignore only idempotent ALTER TABLE reruns. Disk, permission,
                    # corruption, locking and other schema errors must stop startup.
                    if "duplicate column name" not in str(exc).lower():
                        raise
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS okx_feed_seen_posts (
                    post_id TEXT PRIMARY KEY,
                    seen_at INTEGER
                )
                """
            )
            # Полный снимок оперативного состояния своей позиции. Это позволяет
            # пережить restart/redeploy без зависимости от Python-памяти.
            try:
                _conn.execute("ALTER TABLE bot_positions ADD COLUMN runtime_json TEXT DEFAULT '{}'")
            except sqlite3.OperationalError as exc:
                if "duplicate column name" not in str(exc).lower():
                    raise

            # Runtime-state хранит состояния, которые не относятся к одной
            # конкретной позиции: watched/guards/cooldowns.
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS runtime_state (
                    key TEXT PRIMARY KEY,
                    value_json TEXT NOT NULL,
                    updated_at INTEGER NOT NULL
                )
                """
            )
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS state_events (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at INTEGER NOT NULL,
                    scope TEXT NOT NULL,
                    symbol TEXT,
                    event_type TEXT NOT NULL,
                    payload_json TEXT NOT NULL DEFAULT '{}'
                )
                """
            )
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS engine_trade_history (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at INTEGER NOT NULL,
                    record_json TEXT NOT NULL
                )
                """
            )
            # Постоянная привязка двух изменяемых ручных LIMIT к конкретным orderId.
            # Слот не пересчитывается каждый проход по расстоянию до рынка: после
            # исполнения/отмены одной заявки её нельзя автоматически заменить
            # третьей, пока вторая ещё активна или позиция не завершена.
            _conn.execute(
                """
                CREATE TABLE IF NOT EXISTS manual_limit_slots (
                    symbol TEXT NOT NULL,
                    slot INTEGER NOT NULL CHECK(slot IN (1, 2)),
                    order_id TEXT NOT NULL,
                    side TEXT NOT NULL,
                    position_idx INTEGER,
                    price REAL NOT NULL DEFAULT 0,
                    qty REAL NOT NULL DEFAULT 0,
                    target_notional_usdt REAL NOT NULL DEFAULT 0,
                    status TEXT NOT NULL DEFAULT 'active',
                    terminal_reason TEXT,
                    assigned_at INTEGER NOT NULL,
                    updated_at INTEGER NOT NULL,
                    PRIMARY KEY(symbol, slot)
                )
                """
            )
            try:
                _conn.execute("ALTER TABLE manual_limit_slots ADD COLUMN position_idx INTEGER")
            except sqlite3.OperationalError as exc:
                if "duplicate column name" not in str(exc).lower():
                    raise
            _conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_manual_limit_slots_order_id ON manual_limit_slots(order_id)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_manual_limit_slots_status ON manual_limit_slots(status, updated_at)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_state_events_symbol_time ON state_events(symbol, created_at)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_state_events_type_time ON state_events(event_type, created_at)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_runtime_state_updated ON runtime_state(updated_at)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_bot_positions_opened_at ON bot_positions(opened_at)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_signal_positions_status ON signal_positions(status)")
            _conn.execute("CREATE INDEX IF NOT EXISTS idx_signal_positions_source ON signal_positions(source)")
            _conn.commit()
        except Exception:
            try:
                _conn.rollback()
            finally:
                try:
                    _conn.close()
                finally:
                    _conn = None
            raise
        try:
            check = _conn.execute("PRAGMA quick_check").fetchone()
            if not check or str(check[0]).lower() != "ok":
                problem = str(check[0]) if check else "quick_check returned no result"
                raise sqlite3.DatabaseError(f"SQLite quick_check failed: {problem}")
            fk_check = _conn.execute("PRAGMA foreign_key_check").fetchall()
            if fk_check:
                raise sqlite3.DatabaseError(
                    f"SQLite foreign_key_check failed: {len(fk_check)} violation(s)"
                )
        except Exception:
            try:
                _conn.close()
            finally:
                _conn = None
            raise
def _json_default_state(value):
    """Безопасная сериализация runtime-state. Торговые объекты здесь только
    примитивные/JSON-совместимые; fallback нужен для неожиданных значений."""
    if isinstance(value, set):
        return sorted(value)
    if isinstance(value, ReversalTracker):
        return value.to_dict()
    if isinstance(value, (datetime,)):
        return value.isoformat()
    return str(value)


def record_state_event(scope: str, event_type: str, symbol: Optional[str] = None, payload: Optional[Dict] = None):
    """Append-only журнал критических переходов состояния. Идентичные
    последовательные снимки не дублируются, поэтому 24/7 работа не превращает
    SQLite в бесконечный поток одинаковых записей."""
    try:
        payload_json = json.dumps(payload or {}, ensure_ascii=False, separators=(",", ":"), default=_json_default_state)
        with _db_lock:
            last = _conn.execute(
                "SELECT payload_json FROM state_events WHERE scope=? AND symbol IS ? AND event_type=? ORDER BY id DESC LIMIT 1",
                (str(scope), symbol, str(event_type)),
            ).fetchone()
            if last is not None and last["payload_json"] == payload_json:
                return
            _conn.execute(
                "INSERT INTO state_events(created_at, scope, symbol, event_type, payload_json) VALUES (?, ?, ?, ?, ?)",
                (int(time.time() * 1000), str(scope), symbol, str(event_type), payload_json),
            )
            _conn.commit()
    except Exception:
        # После ошибки INSERT/COMMIT соединение может остаться в незавершённой
        # транзакции. Откатываем её под тем же lock, иначе следующий поток
        # может случайно продолжить/зафиксировать чужую частичную запись.
        try:
            with _db_lock:
                if _conn is not None:
                    _conn.rollback()
        except Exception:
            logging.getLogger(__name__).exception(
                "Не удалось откатить транзакцию после ошибки state_events"
            )
        # Журнал событий не должен прерывать торговый поток, но исходная
        # ошибка обязательно остаётся в логе.
        logging.getLogger(__name__).exception(
            "Не удалось записать state_events: scope=%s event_type=%s symbol=%s",
            scope, event_type, symbol,
        )


def get_manual_limit_slot_rows(symbol: Optional[str] = None) -> List[Dict]:
    """Возвращает сохранённое сопоставление L1/L2 с реальными orderId."""
    with _db_lock:
        if symbol:
            rows = _conn.execute(
                "SELECT * FROM manual_limit_slots WHERE symbol=? ORDER BY slot",
                (str(symbol).upper(),),
            ).fetchall()
        else:
            rows = _conn.execute(
                "SELECT * FROM manual_limit_slots ORDER BY symbol, slot"
            ).fetchall()
    return [dict(r) for r in rows]


def _entry_order_ids_to_cancel_after_tp(entry_order_ids: List[str], source: str) -> List[str]:
    """Select only the tracked leftover entry for a manual position.

    Manual entry IDs are persisted in [L1, L2] order. After TP1, only L2 is
    eligible for cancellation; never discover additional user orders by symbol.
    """
    order_ids = list(dict.fromkeys(str(x) for x in (entry_order_ids or []) if x))
    if str(source or "").lower() == "manual":
        # The canonical pair is [L1, L2]. Even if legacy/corrupt state contains
        # more IDs, never cancel the last one (which could be L3/L4).
        return order_ids[1:2] if len(order_ids) >= 2 else []
    return order_ids


def _sort_recovered_entry_orders(entry_orders: Dict[str, float], side: str) -> Tuple[List[float], List[str]]:
    """Keep recovered entry prices paired with their exact exchange order IDs."""
    pairs = []
    for order_id, raw_price in (entry_orders or {}).items():
        oid = str(order_id or "").strip()
        try:
            price = float(raw_price)
        except (TypeError, ValueError, OverflowError):
            continue
        if not oid or not math.isfinite(price) or price <= 0:
            continue
        pairs.append((price, oid))
    pairs.sort(key=lambda item: (item[0], item[1]), reverse=str(side or "").upper() == "LONG")
    return [price for price, _ in pairs], [oid for _, oid in pairs]


def _recovery_take_profit_prices(
    conditional_orders: List[Dict], side: str, entry_price: float
) -> List[float]:
    """Extract confirmed, directionally valid TP prices during lost-DB recovery.

    A generic triggerPrice may belong to a stop-loss or a conditional entry.
    Only explicit TP order types or a dedicated takeProfit field are accepted.
    Targets on the wrong side of the actual average entry are rejected.
    """
    normalized_side = str(side or "").strip().upper()
    if normalized_side not in {"LONG", "SHORT"}:
        return []
    try:
        entry = float(entry_price)
    except (TypeError, ValueError, OverflowError):
        return []
    if not math.isfinite(entry) or entry <= 0:
        return []

    found = set()
    for order in conditional_orders or []:
        if not isinstance(order, dict):
            continue
        stop_type = str(order.get("stopOrderType") or "").replace("_", "").replace(" ", "").lower()
        explicitly_tp = stop_type in {"takeprofit", "partialtakeprofit"}
        raw_prices = []
        if explicitly_tp:
            raw_prices.append(order.get("triggerPrice"))
        # Some API responses expose a position TP field directly.
        raw_prices.append(order.get("takeProfit"))
        for raw in raw_prices:
            try:
                price = float(raw or 0)
            except (TypeError, ValueError, OverflowError):
                continue
            if not math.isfinite(price) or price <= 0:
                continue
            if normalized_side == "LONG" and price <= entry:
                continue
            if normalized_side == "SHORT" and price >= entry:
                continue
            found.add(price)
    return sorted(found, reverse=normalized_side == "SHORT")


def _tp_order_matches_position(order: Dict, symbol: str, side: str, live_position_idx: Optional[int]) -> bool:
    """Return True only for a reduce-only exit order belonging to this live leg.

    Exchange-wide open-order snapshots can contain orders for both hedge legs and
    unrelated/manual orders. A matching orderLinkId prefix alone is not enough
    evidence to adopt or cancel an order.
    """
    if not isinstance(order, dict) or str(order.get("symbol") or "") != str(symbol):
        return False
    expected_close_side = "Sell" if str(side or "").upper() == "LONG" else "Buy"
    if str(order.get("side") or "").strip().lower() != expected_close_side.lower():
        return False
    # TP limit orders must be reduce-only. If the API omits the field, do not
    # infer ownership from the link ID alone.
    reduce_only = order.get("reduceOnly")
    if not (reduce_only is True or str(reduce_only).strip().lower() in {"true", "1"}):
        return False
    return _manual_order_position_idx_matches(order, live_position_idx)


def _is_conditional_stop_type(value) -> bool:
    """True, только если stopOrderType реально означает условный/TP/SL ордер.

    В REST-ответах Bybit у ОБЫЧНЫХ лимиток поле бывает пустым ИЛИ равным
    "UNKNOWN" (в документации примеры именно с UNKNOWN). Проверка «поле не
    пустое» принимала бы такие обычные лимитки за условные и молча выкидывала
    их из L1/L2, из отчёта и из изменения стоимости."""
    text = str(value or "").replace("_", "").replace(" ", "").strip().lower()
    return text not in ("", "unknown", "none", "null")


def _manual_order_position_idx_matches(order: Dict, live_position_idx: Optional[int]) -> bool:
    """Do not match a hedge-mode entry order to an unrelated position.

    Missing positionIdx is treated as one-way index 0 only. If the live
    position index is unknown, hedge-indexed orders are rejected rather than
    guessed into the L1/L2 pair.
    """
    raw = order.get("positionIdx") if isinstance(order, dict) else None
    try:
        order_idx = int(raw) if raw is not None and str(raw).strip() != "" else 0
    except (TypeError, ValueError, OverflowError):
        return False
    if live_position_idx is None:
        return order_idx == 0
    try:
        live_idx = int(live_position_idx)
    except (TypeError, ValueError, OverflowError):
        return False
    if live_idx not in (0, 1, 2):
        return False
    return order_idx == live_idx


def _resolve_manual_stop_anchor_from_state(
    side: str, live_pos: Dict, signal_pos: Dict, slot_rows: List[Dict]
) -> Tuple[float, str]:
    """Возвращает цену именно закреплённой L2, не выбирая L3/L4 по рынку.

    Сначала проверяем DB-слот L2 по стороне, orderId текущей позиции и
    positionIdx. Если запись слота конфликтует с сохранённой парой сделки,
    её цена не используется; fallback берётся строго из entries[1], а не из
    повторной сортировки текущих лимиток.
    """
    entry_side = "Buy" if str(side).upper() == "LONG" else "Sell"
    entry_ids = signal_pos.get("entry_order_ids") or []
    expected_l2_id = str(entry_ids[1]) if len(entry_ids) >= 2 and entry_ids[1] else None

    live_idx = None
    try:
        if live_pos.get("positionIdx") is not None:
            live_idx = int(live_pos.get("positionIdx"))
    except (TypeError, ValueError, OverflowError):
        live_idx = None

    for row in slot_rows or []:
        try:
            if int(row.get("slot") or 0) != 2:
                continue
            if str(row.get("side") or "") != entry_side:
                continue
            order_id = str(row.get("order_id") or "")
            price = float(row.get("price") or 0)
            if not order_id or not math.isfinite(price) or price <= 0:
                continue
            # A slot without the persisted position's exact second entry ID is
            # not enough proof: an old/corrupt slot could still contain L3/L4.
            # Fall back to entries[1] below rather than trusting that slot.
            if not expected_l2_id or order_id != expected_l2_id:
                continue
            saved_idx = None
            try:
                if row.get("position_idx") is not None:
                    saved_idx = int(row.get("position_idx"))
            except (TypeError, ValueError, OverflowError):
                saved_idx = None
            if live_idx in (1, 2) and saved_idx != live_idx:
                continue
            if live_idx == 0 and saved_idx not in (None, 0):
                continue
            if live_idx is None and saved_idx not in (None, 0):
                # If the live position index is unknown, do not trust a hedge
                # slot that may belong to the opposite side.
                continue
            return price, "db_l2"
        except (TypeError, ValueError, OverflowError):
            # Повреждённая запись не должна прерывать поиск корректной L2.
            continue

    # Сохранённая пара создаётся в порядке [L1, L2]. Не фильтруем сначала
    # некорректные цены — это могло бы сдвинуть L3 на индекс второго элемента.
    entries = signal_pos.get("entries") or []
    if len(entries) >= 2:
        try:
            price = float(entries[1])
            if math.isfinite(price) and price > 0:
                return price, "signal_position_l2_fallback"
        except (TypeError, ValueError, OverflowError):
            pass

    try:
        avg_entry = float(live_pos.get("avgPrice") or signal_pos.get("avg_entry_price") or 0)
    except (TypeError, ValueError, OverflowError):
        avg_entry = 0.0
    if not math.isfinite(avg_entry) or avg_entry <= 0:
        return 0.0, "missing_l2_and_entry"
    return avg_entry, "avg_entry_emergency_fallback"


def save_manual_limit_slot(
    symbol: str, slot: int, order_id: str, side: str, price: float, qty: float,
    target_notional_usdt: float, status: str = "active", terminal_reason: Optional[str] = None,
    replace: bool = False, position_idx: Optional[int] = None,
) -> bool:
    """Retry transient SQLite failures without retrying business conflicts."""
    last_error = None
    for attempt in range(1, 4):
        try:
            return _save_manual_limit_slot_once(
                symbol, slot, order_id, side, price, qty, target_notional_usdt,
                status=status, terminal_reason=terminal_reason, replace=replace,
                position_idx=position_idx,
            )
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    _conn.rollback()
            except Exception:
                pass
            logging.getLogger(__name__).exception(
                "[%s] Не удалось сохранить слот L%s в SQLite (попытка %s/3)",
                str(symbol or "").upper(), slot, attempt,
            )
            if attempt < 3:
                time.sleep(0.2 * attempt)
    raise RuntimeError(f"Не удалось сохранить слот L{slot} для {symbol} после 3 попыток") from last_error


def _save_manual_limit_slot_once(
    symbol: str, slot: int, order_id: str, side: str, price: float, qty: float,
    target_notional_usdt: float, status: str = "active", terminal_reason: Optional[str] = None,
    replace: bool = False, position_idx: Optional[int] = None,
) -> bool:
    """Сохраняет идентичность конкретной ручной лимитки и её состояние в SQLite.

    Чужой orderId не может незаметно занять уже закреплённый слот: замена
    разрешена только явным вызовом после подтверждённого завершения всей пары.
    """
    symbol = str(symbol or "").upper()
    order_id = str(order_id or "")
    slot = int(slot)
    status = str(status or "unknown").lower()
    if not symbol or not order_id or slot not in (1, 2):
        return False
    # Как и в атомарных вариантах: NaN/inf/отрицательные цена, qty или номинал
    # не должны попадать в слот (из-за NaN сравнение «изменилось ли» всегда
    # ложно, и испорченное значение не обновлялось бы). Нулевая цена/qty
    # допустима для слотов со статусом unknown/terminal.
    try:
        _numeric_slot_values = [float(v or 0) for v in (price, qty, target_notional_usdt)]
    except (TypeError, ValueError, OverflowError):
        return False
    if any((not math.isfinite(v)) or v < 0 for v in _numeric_slot_values):
        return False
    now = int(time.time() * 1000)
    event_type = None
    event_payload = None
    with _db_lock:
        existing = _conn.execute(
            "SELECT * FROM manual_limit_slots WHERE symbol=? AND slot=?", (symbol, slot)
        ).fetchone()
        other_slot = _conn.execute(
            "SELECT symbol, slot FROM manual_limit_slots WHERE order_id=? AND NOT(symbol=? AND slot=?) LIMIT 1",
            (order_id, symbol, slot),
        ).fetchone()
        if other_slot:
            return False
        if existing and str(existing["order_id"]) != order_id and not replace:
            return False

        same_order = bool(existing and str(existing["order_id"]) == order_id)
        if position_idx is None and same_order:
            position_idx = existing["position_idx"] if "position_idx" in existing.keys() else None
        try:
            position_idx = int(position_idx) if position_idx is not None and str(position_idx).strip() != "" else None
        except (TypeError, ValueError):
            position_idx = None
        assigned_at = int(existing["assigned_at"] or now) if same_order else now
        changed = (not same_order)
        if same_order:
            compare_values = {
                "side": str(existing["side"] or ""),
                "position_idx": existing["position_idx"] if "position_idx" in existing.keys() else None,
                "price": float(existing["price"] or 0),
                "qty": float(existing["qty"] or 0),
                "target_notional_usdt": float(existing["target_notional_usdt"] or 0),
                "status": str(existing["status"] or ""),
                "terminal_reason": existing["terminal_reason"],
            }
            new_values = {
                "side": str(side or ""), "position_idx": position_idx, "price": float(price or 0),
                "qty": float(qty or 0), "target_notional_usdt": float(target_notional_usdt or 0),
                "status": status, "terminal_reason": terminal_reason,
            }
            changed = any(
                (abs(compare_values[k] - new_values[k]) > 1e-12 if k in {"price", "qty", "target_notional_usdt"}
                 else compare_values[k] != new_values[k])
                for k in compare_values
            )
        updated_at = now if changed else int(existing["updated_at"] or now)
        if existing and str(existing["order_id"]) != order_id:
            event_type = "SLOT_REPLACED"
            event_payload = {
                "slot": slot, "old_order_id": str(existing["order_id"]),
                "order_id": order_id, "side": side, "position_idx": position_idx, "price": price,
                "qty": qty, "target_notional_usdt": target_notional_usdt,
                "status": status,
            }
        elif not existing:
            event_type = "SLOT_ASSIGNED"
            event_payload = {
                "slot": slot, "order_id": order_id, "side": side, "position_idx": position_idx, "price": price,
                "qty": qty, "target_notional_usdt": target_notional_usdt, "status": status,
            }
        elif changed:
            event_type = "SLOT_STATE"
            event_payload = {
                "slot": slot, "order_id": order_id, "side": side, "position_idx": position_idx, "price": price,
                "qty": qty, "target_notional_usdt": target_notional_usdt,
                "status": status, "terminal_reason": terminal_reason,
            }
        _conn.execute(
            """INSERT INTO manual_limit_slots
               (symbol, slot, order_id, side, position_idx, price, qty, target_notional_usdt, status, terminal_reason, assigned_at, updated_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
               ON CONFLICT(symbol, slot) DO UPDATE SET
                 order_id=excluded.order_id, side=excluded.side, position_idx=excluded.position_idx, price=excluded.price,
                 qty=excluded.qty, target_notional_usdt=excluded.target_notional_usdt,
                 status=excluded.status, terminal_reason=excluded.terminal_reason,
                 assigned_at=excluded.assigned_at, updated_at=excluded.updated_at""",
            (symbol, slot, order_id, str(side or ""), position_idx, float(price or 0), float(qty or 0),
             float(target_notional_usdt or 0), status, terminal_reason, assigned_at, updated_at),
        )
        _conn.commit()
    if event_type:
        record_state_event("manual_limit", event_type, symbol, event_payload)
    return True



def save_manual_limit_slots_atomically(symbol: str, slots: List[Dict]) -> bool:
    """Retry transient SQLite errors while preserving atomic L1/L2 assignment."""
    last_error = None
    for attempt in range(1, 4):
        try:
            return _save_manual_limit_slots_atomically_once(symbol, slots)
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    _conn.rollback()
            except Exception:
                pass
            logging.getLogger(__name__).exception(
                "[%s] Ошибка атомарного сохранения L1/L2 (попытка %s/3)",
                str(symbol or "").upper(), attempt,
            )
            if attempt < 3:
                time.sleep(0.2 * attempt)
    raise RuntimeError(f"Не удалось атомарно сохранить L1/L2 для {symbol} после 3 попыток") from last_error


def _save_manual_limit_slots_atomically_once(symbol: str, slots: List[Dict]) -> bool:
    """Atomic initial assignment of a new L1/L2 pair.

    This helper is intentionally insert-only: if the symbol already has any
    slots or any order ID is already assigned elsewhere, it refuses the whole
    operation. It never leaves a half-written pair after a process crash.
    """
    symbol = str(symbol or "").upper()
    if not symbol or not isinstance(slots, list) or not slots or len(slots) > 2:
        return False

    normalized = []
    seen_slots = set()
    seen_ids = set()
    now = int(time.time() * 1000)
    for raw in slots:
        if not isinstance(raw, dict):
            return False
        try:
            slot = int(raw.get("slot"))
            order_id = str(raw.get("order_id") or "")
            side = str(raw.get("side") or "")
            price = float(raw.get("price") or 0)
            qty = float(raw.get("qty") or 0)
            target = float(raw.get("target_notional_usdt") or 0)
            position_idx_raw = raw.get("position_idx")
            position_idx = int(position_idx_raw) if position_idx_raw is not None and str(position_idx_raw).strip() != "" else None
        except (TypeError, ValueError, OverflowError):
            return False
        if slot not in (1, 2) or slot in seen_slots or not order_id or order_id in seen_ids:
            return False
        if side not in ("Buy", "Sell") or not all(math.isfinite(x) for x in (price, qty, target)):
            return False
        if price <= 0 or qty < 0 or target < 0:
            return False
        seen_slots.add(slot)
        seen_ids.add(order_id)
        normalized.append({
            "slot": slot, "order_id": order_id, "side": side,
            "position_idx": position_idx, "price": price, "qty": qty,
            "target_notional_usdt": target,
            "status": str(raw.get("status") or "active").lower(),
            "terminal_reason": raw.get("terminal_reason"),
        })
    # Первичное назначение всегда начинается с L1. Не создаём orphan L2 при
    # неполных/повреждённых исходных данных.
    if seen_slots != set(range(1, len(normalized) + 1)):
        return False

    events = []
    with _db_lock:
        _conn.execute("BEGIN IMMEDIATE")
        try:
            existing = _conn.execute(
                "SELECT 1 FROM manual_limit_slots WHERE symbol=? LIMIT 1", (symbol,)
            ).fetchone()
            if existing:
                _conn.rollback()
                return False
            placeholders = ",".join("?" for _ in seen_ids)
            conflict = _conn.execute(
                f"SELECT order_id, symbol, slot FROM manual_limit_slots WHERE order_id IN ({placeholders}) LIMIT 1",
                tuple(seen_ids),
            ).fetchone()
            if conflict:
                _conn.rollback()
                return False

            for item in normalized:
                _conn.execute(
                    """INSERT INTO manual_limit_slots
                       (symbol, slot, order_id, side, position_idx, price, qty,
                        target_notional_usdt, status, terminal_reason, assigned_at, updated_at)
                       VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                    (symbol, item["slot"], item["order_id"], item["side"], item["position_idx"],
                     item["price"], item["qty"], item["target_notional_usdt"], item["status"],
                     item["terminal_reason"], now, now),
                )
            _conn.commit()
            events = [dict(item) for item in normalized]
        except Exception:
            _conn.rollback()
            raise

    for item in events:
        record_state_event("manual_limit", "SLOT_ASSIGNED", symbol, item)
    return True



def replace_manual_limit_slots_atomically(
    symbol: str, slots: List[Dict], expected_order_ids: Optional[Dict[int, str]] = None,
) -> bool:
    """Атомарно исправляет уже существующую пару L1/L2 в SQLite.

    Нужна только для доказанного исправления старой ошибочной привязки. Проверяет,
    что исходная пара не изменилась с момента чтения, не позволяет забрать orderId
    другого символа и не оставляет половину пары при сбое/перестановке L1↔L2.
    """
    symbol = str(symbol or "").upper()
    if not symbol or not isinstance(slots, list) or len(slots) != 2:
        return False

    normalized = []
    seen_ids = set()
    by_slot = {}
    now = int(time.time() * 1000)
    for raw in slots:
        if not isinstance(raw, dict):
            return False
        try:
            slot = int(raw.get("slot"))
            order_id = str(raw.get("order_id") or "")
            side = str(raw.get("side") or "")
            price = float(raw.get("price") or 0)
            qty = float(raw.get("qty") or 0)
            target = float(raw.get("target_notional_usdt") or 0)
            idx_raw = raw.get("position_idx")
            position_idx = int(idx_raw) if idx_raw is not None and str(idx_raw).strip() != "" else None
        except (TypeError, ValueError, OverflowError):
            return False
        if slot not in (1, 2) or slot in by_slot or not order_id or order_id in seen_ids:
            return False
        if side not in ("Buy", "Sell") or not all(math.isfinite(v) for v in (price, qty, target)):
            return False
        if price <= 0 or qty < 0 or target < 0:
            return False
        by_slot[slot] = {
            "slot": slot, "order_id": order_id, "side": side,
            "position_idx": position_idx, "price": price, "qty": qty,
            "target_notional_usdt": target,
            "status": str(raw.get("status") or "active").lower(),
            "terminal_reason": raw.get("terminal_reason"),
        }
        seen_ids.add(order_id)
    if set(by_slot) != {1, 2}:
        return False

    events = []
    with _db_lock:
        _conn.execute("BEGIN IMMEDIATE")
        try:
            existing_rows = _conn.execute(
                "SELECT * FROM manual_limit_slots WHERE symbol=? ORDER BY slot", (symbol,)
            ).fetchall()
            existing = {int(r["slot"]): dict(r) for r in existing_rows}
            if set(existing) != {1, 2}:
                _conn.rollback()
                return False
            if expected_order_ids is not None:
                for slot in (1, 2):
                    expected = str(expected_order_ids.get(slot) or "")
                    if str(existing[slot].get("order_id") or "") != expected:
                        _conn.rollback()
                        return False
            placeholders = ",".join("?" for _ in seen_ids)
            conflict = _conn.execute(
                f"SELECT order_id, symbol, slot FROM manual_limit_slots WHERE order_id IN ({placeholders}) AND symbol<>? LIMIT 1",
                tuple(seen_ids) + (symbol,),
            ).fetchone()
            if conflict:
                _conn.rollback()
                return False

            # Удаляем пару внутри текущей транзакции до вставки новых строк:
            # это позволяет безопасно поменять L1/L2 местами при UNIQUE(order_id).
            _conn.execute("DELETE FROM manual_limit_slots WHERE symbol=? AND slot IN (1, 2)", (symbol,))
            # Сохраняем время назначения у ID, который остался в своём слоте;
            # для нового ID ставим время корректировки.
            for slot in (1, 2):
                item = by_slot[slot]
                old = existing[slot]
                assigned_at = int(old.get("assigned_at") or now) if old.get("order_id") == item["order_id"] else now
                _conn.execute(
                    """INSERT INTO manual_limit_slots
                       (symbol, slot, order_id, side, position_idx, price, qty,
                        target_notional_usdt, status, terminal_reason, assigned_at, updated_at)
                       VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                    (symbol, slot, item["order_id"], item["side"], item["position_idx"],
                     item["price"], item["qty"], item["target_notional_usdt"], item["status"],
                     item["terminal_reason"], assigned_at, now),
                )
                if old.get("order_id") != item["order_id"]:
                    events.append({
                        "slot": slot, "old_order_id": str(old.get("order_id") or ""),
                        "order_id": item["order_id"], "price": item["price"],
                        "side": item["side"], "position_idx": item["position_idx"],
                    })
            _conn.commit()
        except Exception:
            _conn.rollback()
            raise

    for event in events:
        record_state_event("manual_limit", "SLOT_REPAIRED", symbol, event)
    return True


def clear_manual_limit_slots(symbol: str, reason: str = "") -> None:
    symbol = str(symbol or "").upper()
    if not symbol:
        return
    last_error = None
    for attempt in range(1, 4):
        try:
            with _db_lock:
                rows = _conn.execute(
                    "SELECT slot, order_id, status FROM manual_limit_slots WHERE symbol=? ORDER BY slot",
                    (symbol,),
                ).fetchall()
                _conn.execute("DELETE FROM manual_limit_slots WHERE symbol=?", (symbol,))
                _conn.commit()
            if rows:
                record_state_event("manual_limit", "SLOTS_RESET", symbol, {
                    "reason": reason, "orders": [dict(r) for r in rows],
                })
            return
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    _conn.rollback()
            except Exception:
                pass
            logging.getLogger(__name__).exception(
                "[%s] Ошибка очистки L1/L2 слотов (попытка %s/3)", symbol, attempt,
            )
            if attempt < 3:
                time.sleep(0.2 * attempt)
    raise RuntimeError(f"Не удалось очистить слоты L1/L2 для {symbol} после 3 попыток") from last_error


def save_runtime_state(watched: Dict[str, ReversalTracker], positions_guard: Dict[str, ReversalTracker], cooldowns: Dict[str, float], logger):
    """Транзакционно сохраняет runtime-state с повторами при временной блокировке SQLite.

    JSON-файл остаётся только legacy-fallback. Если запись не удалась после
    повторных попыток, ошибка явно логируется и поднимается выше, чтобы главный
    цикл мог уведомить оператора, а не молча продолжить с несохранённым state.
    """
    data = {
        "watched": {s: t.to_dict() for s, t in watched.items()},
        "positions_guard": {s: t.to_dict() for s, t in positions_guard.items()},
        "cooldowns": {str(k): float(v) for k, v in cooldowns.items()},
    }
    encoded = {
        key: json.dumps(value, ensure_ascii=False, separators=(",", ":"), default=_json_default_state)
        for key, value in data.items()
    }
    last_error = None
    for attempt in range(1, 4):
        try:
            now = int(time.time() * 1000)
            # Один lock охватывает BEGIN/все UPSERT/COMMIT/ROLLBACK: никакой
            # другой поток не сможет случайно присоединиться к этой транзакции.
            with _db_lock:
                try:
                    _conn.execute("BEGIN IMMEDIATE")
                    for key, value_json in encoded.items():
                        _conn.execute(
                            "INSERT INTO runtime_state(key,value_json,updated_at) VALUES(?,?,?) "
                            "ON CONFLICT(key) DO UPDATE SET value_json=excluded.value_json, updated_at=excluded.updated_at",
                            (key, value_json, now),
                        )
                    _conn.commit()
                except Exception:
                    _conn.rollback()
                    raise
            return
        except Exception as e:
            last_error = e
            logger.exception(
                "Не удалось сохранить runtime-state в SQLite (попытка %s/3): %s",
                attempt, e,
            )
            if attempt < 3:
                time.sleep(0.25 * attempt)
    raise RuntimeError("Не удалось сохранить runtime-state в SQLite после 3 попыток") from last_error


def load_runtime_state(logger):
    """Загружает runtime-state из SQLite. Если это старая база без снимка,
    один раз читает legacy bot_state.json для безопасной миграции."""
    try:
        with _db_lock:
            rows = _conn.execute("SELECT key,value_json FROM runtime_state WHERE key IN ('watched','positions_guard','cooldowns')").fetchall()
        raw = {r["key"]: json.loads(r["value_json"] or "{}") for r in rows}
        if raw:
            watched = {s: ReversalTracker.from_dict(d) for s, d in raw.get("watched", {}).items()}
            guards = {s: ReversalTracker.from_dict(d) for s, d in raw.get("positions_guard", {}).items()}
            cooldowns = {str(s): float(v) for s, v in raw.get("cooldowns", {}).items()}
            logger.info(f"Runtime-state восстановлен из SQLite: {len(watched)} наблюдений, {len(guards)} guard-ов, {len(cooldowns)} cooldown-ов.")
            return watched, guards, cooldowns
    except Exception as e:
        logger.warning(f"Не удалось прочитать runtime-state из SQLite: {e}")

    # Миграция со старой версии, где состояние лежало в bot_state.json.
    if os.path.exists(STATE_PATH):
        try:
            with _state_file_lock:
                with open(STATE_PATH, "r", encoding="utf-8") as f:
                    data = json.load(f)
            watched = {s: ReversalTracker.from_dict(d) for s, d in data.get("watched", {}).items()}
            guards = {s: ReversalTracker.from_dict(d) for s, d in data.get("positions_guard", {}).items()}
            cooldowns = {str(s): float(v) for s, v in data.get("cooldowns", {}).items()}
        except Exception as e:
            logger.exception("Не удалось прочитать legacy bot_state.json; состояние не восстановлено: %s", e)
            return {}, {}, {}

        # Не теряем уже прочитанное состояние в памяти, если миграция в SQLite
        # временно не удалась. Следующий цикл/перезапуск сможет повторить запись.
        try:
            save_runtime_state(watched, guards, cooldowns, logger)
            record_state_event("runtime", "LEGACY_JSON_MIGRATED", payload={"state_file": STATE_PATH})
            logger.info(
                "Старый bot_state.json мигрирован в SQLite: %s наблюдений, %s guard-ов, %s cooldown-ов.",
                len(watched), len(guards), len(cooldowns),
            )
        except Exception:
            logger.exception("Не удалось сохранить legacy-state в SQLite; продолжаю с восстановленным состоянием в памяти")
        return watched, guards, cooldowns
    return {}, {}, {}


# ---------------------- реестр позиций, открытых ботом ----------------------

def mark_bot_position_open(symbol: str, meta: Dict):
    with _db_lock:
        _conn.execute(
            """
            INSERT INTO bot_positions (symbol, entry_price, qty, is_long, tp_price, sl_price, tick_size, margin_usdt, profit_locked, opened_at, tp_targets_json, tp_close_pcts_json, tp_order_ids_json, tp_initial_qty, tp_done_json, tp_filled_qty_json, tp1_breakeven_done, runtime_json)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(symbol) DO UPDATE SET
                entry_price=excluded.entry_price, qty=excluded.qty, is_long=excluded.is_long,
                tp_price=excluded.tp_price, sl_price=excluded.sl_price, tick_size=excluded.tick_size,
                margin_usdt=excluded.margin_usdt, profit_locked=excluded.profit_locked, opened_at=excluded.opened_at,
                tp_targets_json=excluded.tp_targets_json, tp_close_pcts_json=excluded.tp_close_pcts_json,
                tp_order_ids_json=excluded.tp_order_ids_json, tp_initial_qty=excluded.tp_initial_qty, tp_done_json=excluded.tp_done_json, tp_filled_qty_json=excluded.tp_filled_qty_json, tp1_breakeven_done=excluded.tp1_breakeven_done, runtime_json=excluded.runtime_json
            """,
            (
                symbol, meta.get("entry_price"), meta.get("qty"), int(bool(meta.get("is_long"))),
                meta.get("tp_price"), meta.get("sl_price"), meta.get("tick_size"), meta.get("margin_usdt"),
                int(bool(meta.get("profit_locked"))), int(meta.get("opened_at", time.time()) * 1000),
                json.dumps(meta.get("tp_targets") or [], separators=(",", ":")),
                json.dumps(meta.get("tp_close_pcts") or [25, 25, 25, 100], separators=(",", ":")),
                json.dumps(meta.get("tp_order_ids") or {}, separators=(",", ":")),
                float(meta.get("tp_initial_qty") or meta.get("qty") or 0),
                json.dumps(meta.get("tp_done") or {}, separators=(",", ":")),
                json.dumps(meta.get("tp_filled_qty") or {}, separators=(",", ":")),
                int(bool(meta.get("tp1_breakeven_done"))),
                json.dumps(meta, ensure_ascii=False, separators=(",", ":"), default=_json_default_state),
            ),
        )
        _conn.commit()
    record_state_event("bot_position", "UPSERT", symbol, {
        "entry_price": meta.get("entry_price"), "qty": meta.get("qty"),
        "tp_targets": meta.get("tp_targets") or [], "tp_order_ids": meta.get("tp_order_ids") or {},
        "tp_done": meta.get("tp_done") or {}, "tp_filled_qty": meta.get("tp_filled_qty") or {},
        "sl_price": meta.get("sl_price"), "profit_locked": bool(meta.get("profit_locked")),
    })


def persist_bot_position_with_retry(symbol: str, meta: Dict, logger=None, attempts: int = 3) -> bool:
    """Повторяет запись критически важного реестра позиции после временного
    сбоя SQLite. Ошибка не маскируется: False означает, что позиция всё ещё
    может быть не восстановлена после рестарта и оператору нужен alert."""
    attempts = max(1, int(attempts))
    for attempt in range(1, attempts + 1):
        try:
            mark_bot_position_open(symbol, meta)
            return True
        except Exception:
            try:
                _conn.rollback()
            except Exception:
                pass
            if logger:
                logger.exception(
                    "[%s] Ошибка сохранения bot_positions (попытка %s/%s)",
                    symbol, attempt, attempts,
                )
            else:
                logging.getLogger(__name__).exception(
                    "[%s] Ошибка сохранения bot_positions (попытка %s/%s)",
                    symbol, attempt, attempts,
                )
            if attempt < attempts:
                time.sleep(0.25 * attempt)
    return False


def _mark_bot_position_closed_once(symbol: str):
    with _db_lock:
        _conn.execute("DELETE FROM bot_positions WHERE symbol = ?", (symbol,))
        _conn.commit()
    record_state_event("bot_position", "CLOSED", symbol, {})


def mark_bot_position_closed(symbol: str):
    last_error = None
    for attempt in range(1, 4):
        try:
            _mark_bot_position_closed_once(symbol)
            return
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    _conn.rollback()
            except Exception:
                pass
            logging.getLogger(__name__).exception(
                "[%s] Ошибка удаления закрытой позиции из SQLite (попытка %s/3)",
                symbol, attempt,
            )
            if attempt < 3:
                time.sleep(0.2 * attempt)
    raise RuntimeError(f"Не удалось отметить закрытую позицию {symbol} в SQLite после 3 попыток") from last_error


def _row_to_bot_position(row) -> Dict:
    d = dict(row)
    try:
        d["runtime"] = json.loads(d.get("runtime_json") or "{}")
    except Exception:
        d["runtime"] = {}
    return d


def get_all_bot_positions() -> Dict[str, Dict]:
    """Все символы, по которым у бота СЕЙЧАС числится открытая своя позиция
    (переживает рестарты). Всё, чего здесь нет, — не бот открывал (открыто
    вручную пользователем, либо это старая позиция с давней версии бота,
    когда этого реестра ещё не было) и потому не должно управляться ботом:
    ни защитой прибыли/умным выходом, ни авто-восстановлением TP/SL, ни
    уведомлениями/cooldown при закрытии, ни статистикой сделок."""
    with _db_lock:
        rows = _conn.execute("SELECT * FROM bot_positions").fetchall()
    return {r["symbol"]: _row_to_bot_position(r) for r in rows}


# ---------------------- сигнальные позиции (посты в чате) ----------------------

def _pending_signal_has_live_or_uncertain_entries(
    tracked_order_ids: List[str], open_order_ids: Optional[set], order_states: Optional[List[Dict]]
) -> bool:
    """Fail closed: don't drop a pending signal while any entry may still execute."""
    ids = list(dict.fromkeys(str(x) for x in (tracked_order_ids or []) if x))
    if not ids or open_order_ids is None or order_states is None:
        return True
    open_ids = {str(x) for x in open_order_ids}
    if any(order_id in open_ids for order_id in ids):
        return True
    if len(order_states) != len(ids):
        return True
    terminal_unfilled = {"cancelled", "rejected", "deactivated"}
    for state in order_states:
        if not isinstance(state, dict):
            return True
        status = str(state.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
        if status not in terminal_unfilled:
            # Filled/partially-filled/unknown must not be treated as a clean
            # unfilled cancellation; exchange position data may be lagging.
            return True
    return False


def _active_signal_position_conflict(existing: Optional[Dict], incoming: Dict) -> bool:
    """Never let a new signal overwrite any active same-symbol tracker.

    Even when side/source match, the UPSERT resets TP progress, entry IDs and
    timestamps. A repeated or duplicate signal must be rejected while the
    existing record is pending/open; callers can update it only through the
    dedicated state-update functions.
    """
    if not existing:
        return False
    return str(existing.get("status") or "").lower() in {"pending", "open"}


def create_signal_position(data: Dict):
    with _db_lock:
        # signal_positions has a single row per symbol. In hedge mode, or when a
        # manual and signal trade overlap, blindly UPSERTing would replace the
        # existing side/source and erase its TP progress. Fail closed instead.
        with _db_lock:
            existing_row = _conn.execute(
                "SELECT symbol, side, source, status FROM signal_positions WHERE symbol=?",
                (str(data.get("symbol") or ""),),
            ).fetchone()
        existing = dict(existing_row) if existing_row else None
        if _active_signal_position_conflict(existing, data):
            raise RuntimeError(
                f"Отказ перезаписи активного состояния {data.get('symbol')}: "
                f"в БД уже side={existing.get('side')} source={existing.get('source')}, "
                f"новое side={data.get('side')} source={data.get('source') or 'post'}. "
                "Сначала нужно безопасно закрыть/сверить старое состояние."
            )

        with _db_lock:
            _conn.execute(
                """
                INSERT INTO signal_positions
                    (symbol, side, entries_json, targets_json, stop_price, avg_entry_price,
                     qty_total, opened_qty, last_known_qty, entry_order_ids_json,
                     breakeven_after_tp1, breakeven_done, tp_hits_count, tp2_partial_done,
                     tp_orders_set, tp_orders_qty_basis, stale_entries_cancelled, single_target_is_partial, source,
                     manual_tp_targets_json, manual_tp_close_pcts_json, manual_tp_order_ids_json, manual_tp_initial_qty, manual_tp_done_json, manual_tp_filled_qty_json, manual_tp_overrides_json,
                     status, created_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(symbol) DO UPDATE SET
                    side=excluded.side, entries_json=excluded.entries_json, targets_json=excluded.targets_json,
                    stop_price=excluded.stop_price, avg_entry_price=excluded.avg_entry_price,
                    qty_total=excluded.qty_total, opened_qty=excluded.opened_qty, last_known_qty=excluded.last_known_qty,
                    entry_order_ids_json=excluded.entry_order_ids_json,
                    breakeven_after_tp1=excluded.breakeven_after_tp1, breakeven_done=0, manual_sl_override=0, tp_hits_count=0, tp2_partial_done=0,
                    tp_orders_set=0, tp_orders_qty_basis=0, stale_entries_cancelled=0, single_target_is_partial=excluded.single_target_is_partial,
                    tp2_limit_order_id=NULL, source=excluded.source,
                    manual_tp_targets_json=excluded.manual_tp_targets_json, manual_tp_close_pcts_json=excluded.manual_tp_close_pcts_json,
                    manual_tp_order_ids_json=excluded.manual_tp_order_ids_json, manual_tp_initial_qty=excluded.manual_tp_initial_qty,
                    manual_tp_done_json=excluded.manual_tp_done_json, manual_tp_filled_qty_json=excluded.manual_tp_filled_qty_json,
                    manual_tp_overrides_json=excluded.manual_tp_overrides_json,
                    status=excluded.status, created_at=excluded.created_at
                """,
                (
                    data["symbol"], data["side"], json.dumps(data["entries"]), json.dumps(data["targets"]),
                    data["stop_price"], data["avg_entry_price"], data["qty_total"], 0.0, 0.0,
                    json.dumps(data["entry_order_ids"]), int(bool(data.get("breakeven_after_tp1"))), 0, 0, 0,
                    0, 0.0, 0, int(bool(data.get("single_target_is_partial"))), data.get("source") or "post",
                    json.dumps(data.get("manual_tp_targets") or []),
                    json.dumps(data.get("manual_tp_close_pcts") or [25, 25, 25, 100]),
                    json.dumps(data.get("manual_tp_order_ids") or {}),
                    float(data.get("manual_tp_initial_qty") or 0),
                    json.dumps(data.get("manual_tp_done") or {}),
                    json.dumps(data.get("manual_tp_filled_qty") or {}),
                    json.dumps(data.get("manual_tp_overrides") or {}),
                    data.get("status") or "pending", int(time.time() * 1000),
                ),
            )
            _conn.commit()
        record_state_event("signal_position", "UPSERT", data.get("symbol"), {
            "source": data.get("source") or "post", "side": data.get("side"),
            "status": data.get("status") or "pending", "entry_order_ids": data.get("entry_order_ids") or [],
        })


def get_signal_position(symbol: str) -> Optional[Dict]:
    with _db_lock:
        row = _conn.execute("SELECT * FROM signal_positions WHERE symbol = ?", (symbol,)).fetchone()
    return _row_to_signal_position(row) if row else None


def get_all_open_signal_positions() -> Dict[str, Dict]:
    with _db_lock:
        rows = _conn.execute("SELECT * FROM signal_positions WHERE status IN ('pending', 'open')").fetchall()
    return {r["symbol"]: _row_to_signal_position(r) for r in rows}


def _decode_db_json(row_dict: Dict, column: str, default, expected_type, symbol: str):
    """Decode persisted state without silently replacing corrupt trading state.

    Falling back to empty TP/SL/order-ID dictionaries can make the bot believe
    that no exits exist and create duplicates. Corrupt critical state therefore
    raises a clear error and fails closed; it must be repaired/reconciled rather
    than silently traded with defaults.
    """
    raw = row_dict.get(column)
    if raw in (None, ""):
        value = default
    else:
        try:
            value = json.loads(raw)
        except (TypeError, ValueError, json.JSONDecodeError) as exc:
            raise sqlite3.DatabaseError(
                f"Повреждён JSON в signal_positions.{column} для {symbol}; "
                "автоматическое восстановление остановлено во избежание потери TP/SL"
            ) from exc
    if not isinstance(value, expected_type):
        raise sqlite3.DatabaseError(
            f"Неверный тип JSON в signal_positions.{column} для {symbol}: "
            f"ожидался {expected_type.__name__}, получен {type(value).__name__}"
        )
    return value


def _row_to_signal_position(row) -> Dict:
    d = dict(row)
    symbol = str(d.get("symbol") or "<unknown>")
    d["entries"] = _decode_db_json(d, "entries_json", [], list, symbol)
    d["targets"] = _decode_db_json(d, "targets_json", [], list, symbol)
    d["entry_order_ids"] = _decode_db_json(d, "entry_order_ids_json", [], list, symbol)
    d["manual_tp_targets"] = _decode_db_json(d, "manual_tp_targets_json", [], list, symbol)
    d["manual_tp_close_pcts"] = _decode_db_json(d, "manual_tp_close_pcts_json", [25, 25, 25, 100], list, symbol)
    d["manual_tp_order_ids"] = _decode_db_json(d, "manual_tp_order_ids_json", {}, dict, symbol)
    d["manual_tp_done"] = _decode_db_json(d, "manual_tp_done_json", {}, dict, symbol)
    d["manual_tp_filled_qty"] = _decode_db_json(d, "manual_tp_filled_qty_json", {}, dict, symbol)
    d["manual_tp_overrides"] = _decode_db_json(d, "manual_tp_overrides_json", {}, dict, symbol)
    # Validate persisted TP close fractions and prices before exposing them to
    # order reconciliation. Invalid state must never be interpreted as defaults.
    for field in ("entries", "targets", "manual_tp_targets", "manual_tp_close_pcts"):
        normalized = []
        for value in d[field]:
            try:
                number = float(value)
            except (TypeError, ValueError, OverflowError) as exc:
                raise sqlite3.DatabaseError(f"Нечисловое значение в {field} для {symbol}") from exc
            if not math.isfinite(number) or number < 0 or (field != "manual_tp_close_pcts" and number == 0):
                raise sqlite3.DatabaseError(f"Некорректное значение в {field} для {symbol}: {value!r}")
            normalized.append(number)
        d[field] = normalized
    if len(d["manual_tp_close_pcts"]) > 4 or any(x > 100 for x in d["manual_tp_close_pcts"]):
        raise sqlite3.DatabaseError(f"Некорректные доли закрытия TP в БД для {symbol}")
    if len(d["entry_order_ids"]) > 0 and any(not str(x or "").strip() for x in d["entry_order_ids"]):
        raise sqlite3.DatabaseError(f"Пустой orderId во входных ордерах {symbol}")
    d["breakeven_after_tp1"] = bool(d["breakeven_after_tp1"])
    d["breakeven_done"] = bool(d["breakeven_done"])
    d["manual_sl_override"] = bool(d.get("manual_sl_override", 0))
    d["tp_hits_count"] = int(d.get("tp_hits_count") or 0)
    d["tp2_partial_done"] = bool(d.get("tp2_partial_done"))
    d["tp_orders_set"] = bool(d.get("tp_orders_set"))
    d["tp_orders_qty_basis"] = float(d.get("tp_orders_qty_basis") or 0)
    d["stale_entries_cancelled"] = bool(d.get("stale_entries_cancelled"))
    d["single_target_is_partial"] = bool(d.get("single_target_is_partial"))
    d["tp2_limit_order_id"] = d.get("tp2_limit_order_id")
    d["source"] = d.get("source") or "post"
    d["manual_tp_initial_qty"] = float(d.get("manual_tp_initial_qty") or 0)
    return d


def persist_signal_position_tp_state_with_retry(
    symbol: str, avg_entry: float, targets: List[float], stop_price: float,
    live_qty: float, closes: List[float], order_ids: Dict, initial_qty: float,
    done: Dict, filled_qty: Dict, manual_sl_override: bool, logger=None,
    attempts: int = 3, manual_tp_overrides: Optional[Dict] = None,
) -> bool:
    """Persist the complete TP/SL reconciliation snapshot with bounded retries."""
    params = (
        avg_entry, json.dumps(targets), stop_price, live_qty, live_qty,
        json.dumps(targets), json.dumps(closes), json.dumps(order_ids),
        initial_qty, json.dumps(done), json.dumps(filled_qty),
        json.dumps(manual_tp_overrides or {}), int(bool(manual_sl_override)), symbol,
    )
    last_error = None
    attempts = max(1, int(attempts))
    for attempt in range(1, attempts + 1):
        try:
            with _db_lock:
                cur = _conn.execute(
                    "UPDATE signal_positions SET avg_entry_price=?, targets_json=?, stop_price=?, last_known_qty=?, qty_total=?, manual_tp_targets_json=?, manual_tp_close_pcts_json=?, manual_tp_order_ids_json=?, manual_tp_initial_qty=?, manual_tp_done_json=?, manual_tp_filled_qty_json=?, manual_tp_overrides_json=?, manual_sl_override=?, status='open' WHERE symbol=?",
                    params,
                )
                if cur.rowcount != 1:
                    raise RuntimeError(
                        f"signal_positions row missing or ambiguous for {symbol}; TP/SL state was not persisted"
                    )
                _conn.commit()
            return True
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    _conn.rollback()
            except Exception:
                pass
            log = logger or logging.getLogger(__name__)
            log.exception(
                "[%s] Ошибка сохранения TP/SL состояния signal_positions (попытка %s/%s)",
                symbol, attempt, attempts,
            )
            if attempt < attempts:
                time.sleep(0.2 * attempt)
    raise RuntimeError(
        f"Не удалось сохранить TP/SL состояние signal_positions для {symbol} после {attempts} попыток"
    ) from last_error



def persist_manual_tp1_fill_observation(
    symbol: str,
    cumulative_qty: float,
    order_id: Optional[str] = None,
    done: bool = False,
    logger=None,
    attempts: int = 3,
) -> bool:
    """Immediately persist confirmed TP1 execution evidence for manual positions.

    This is deliberately a narrow update: it does not overwrite target prices,
    SL, other TP progress, or current order IDs. The caller uses it before
    applying the post-TP1 break-even stop so a failed later API call/restart
    cannot make the bot forget a confirmed TP1 fill.
    """
    try:
        qty = float(cumulative_qty)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"Некорректный cumExecQty TP1 для {symbol}") from exc
    if not math.isfinite(qty) or qty < 0:
        raise ValueError(f"Некорректный cumExecQty TP1 для {symbol}: {cumulative_qty!r}")
    if qty <= 0 and not done:
        return True

    log = logger or logging.getLogger(__name__)
    last_error = None
    attempts = max(1, int(attempts))
    for attempt in range(1, attempts + 1):
        try:
            with _db_lock:
                row = _conn.execute(
                    "SELECT source, manual_tp_filled_qty_json, manual_tp_done_json "
                    "FROM signal_positions WHERE symbol=?",
                    (str(symbol),),
                ).fetchone()
                if row is None:
                    raise RuntimeError(f"signal_positions row missing for TP1 fill {symbol}")
                row = dict(row)
                if str(row.get("source") or "post") != "manual":
                    raise RuntimeError(f"TP1 fill persistence refused: {symbol} is not a manual position")

                try:
                    fills = json.loads(row.get("manual_tp_filled_qty_json") or "{}")
                    done_map = json.loads(row.get("manual_tp_done_json") or "{}")
                except (TypeError, ValueError, json.JSONDecodeError) as exc:
                    raise sqlite3.DatabaseError(
                        f"Повреждён JSON исполнения TP1 для {symbol}; состояние не перезаписываю"
                    ) from exc
                if not isinstance(fills, dict) or not isinstance(done_map, dict):
                    raise sqlite3.DatabaseError(
                        f"Неверный тип JSON исполнения TP1 для {symbol}; состояние не перезаписываю"
                    )

                old_qty_raw = fills.get("1", 0)
                try:
                    old_qty = float(old_qty_raw or 0)
                except (TypeError, ValueError, OverflowError) as exc:
                    raise sqlite3.DatabaseError(
                        f"Некорректный сохранённый объём TP1 для {symbol}: {old_qty_raw!r}"
                    ) from exc
                if not math.isfinite(old_qty) or old_qty < 0:
                    raise sqlite3.DatabaseError(
                        f"Некорректный сохранённый объём TP1 для {symbol}: {old_qty_raw!r}"
                    )

                # The existing field is cumulative per TP stage (legacy schema).
                # max() is idempotent across repeated API snapshots of one order.
                fills["1"] = max(old_qty, qty)
                if done:
                    done_map["1"] = True
                cur = _conn.execute(
                    "UPDATE signal_positions SET manual_tp_filled_qty_json=?, manual_tp_done_json=? "
                    "WHERE symbol=? AND source='manual'",
                    (json.dumps(fills, ensure_ascii=False, separators=(",", ":")),
                     json.dumps(done_map, ensure_ascii=False, separators=(",", ":")),
                     str(symbol)),
                )
                if cur.rowcount != 1:
                    raise RuntimeError(f"TP1 fill update affected {cur.rowcount} rows for {symbol}")
                _conn.commit()
            # The audit event is intentionally best-effort; the authoritative TP1
            # state above is already committed and must not be rolled back because
            # the append-only event journal is unavailable.
            try:
                record_state_event(
                    "signal_position", "MANUAL_TP1_FILL_OBSERVED", str(symbol),
                    {"order_id": str(order_id or ""), "cum_exec_qty": qty, "done": bool(done)},
                )
            except Exception:
                log.exception("[%s] TP1 fill сохранён, но журнал события недоступен", symbol)
            return True
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    if _conn is not None:
                        _conn.rollback()
            except Exception:
                log.exception("[%s] Не удалось откатить транзакцию сохранения TP1", symbol)
            log.exception(
                "[%s] Ошибка немедленного сохранения исполнения TP1 (попытка %s/%s)",
                symbol, attempt, attempts,
            )
            if attempt < attempts:
                time.sleep(0.2 * attempt)
    raise RuntimeError(
        f"Не удалось сохранить подтверждённое исполнение TP1 для {symbol} после {attempts} попыток"
    ) from last_error


def _update_signal_position_checked(symbol: str, sql: str, params: tuple, operation: str, payload: Dict) -> None:
    """Persist a critical signal-position change with bounded retries.

    A missing row is treated as an error rather than silently reporting a
    successful save. This prevents in-memory state from getting ahead of DB.
    """
    last_error = None
    for attempt in range(1, 4):
        try:
            with _db_lock:
                cur = _conn.execute(sql, params)
                if cur.rowcount != 1:
                    raise RuntimeError(
                        f"signal_positions row missing or ambiguous for {symbol} ({operation})"
                    )
                _conn.commit()
            record_state_event("signal_position", operation, symbol, payload)
            return
        except Exception as exc:
            last_error = exc
            try:
                with _db_lock:
                    _conn.rollback()
            except Exception:
                pass
            logging.getLogger(__name__).exception(
                "[%s] Ошибка сохранения signal_positions (%s), попытка %s/3",
                symbol, operation, attempt,
            )
            if attempt < 3:
                time.sleep(0.2 * attempt)
    raise RuntimeError(
        f"Не удалось сохранить {operation} для {symbol} в SQLite после 3 попыток"
    ) from last_error


def update_signal_position_opened(symbol: str, qty: float):
    _update_signal_position_checked(
        symbol,
        "UPDATE signal_positions SET status='open', opened_qty=?, last_known_qty=? WHERE symbol=?",
        (qty, qty, symbol), "OPENED", {"qty": qty},
    )


def update_signal_position_qty(symbol: str, qty: float):
    _update_signal_position_checked(
        symbol, "UPDATE signal_positions SET last_known_qty=? WHERE symbol=?",
        (qty, symbol), "QTY_UPDATED", {"qty": qty},
    )



def update_manual_entry_pair(
    symbol: str, entries: List[float], order_ids: List[str],
    expected_order_ids: Optional[List[str]] = None,
    expected_entries: Optional[List[float]] = None,
) -> bool:
    """Атомарно обновляет пару L1/L2; optional expected values provide CAS protection.

    CAS checks prevent an older monitor snapshot from overwriting a newer pair
    written by another scanner thread between exchange lookup and DB update.
    """
    symbol = str(symbol or "").upper()
    if not symbol or not isinstance(entries, list) or not isinstance(order_ids, list):
        return False
    if len(entries) != 2 or len(order_ids) != 2 or not all(order_ids) or str(order_ids[0]) == str(order_ids[1]):
        return False
    try:
        prices = [float(x) for x in entries]
    except (TypeError, ValueError, OverflowError):
        return False
    if not all(math.isfinite(x) and x > 0 for x in prices):
        return False
    ids = [str(x) for x in order_ids]
    expected_ids = [str(x) for x in expected_order_ids] if expected_order_ids is not None else None
    try:
        expected_px = [float(x) for x in expected_entries] if expected_entries is not None else None
    except (TypeError, ValueError, OverflowError):
        return False
    if expected_ids is not None and (len(expected_ids) != 2 or not all(expected_ids)):
        return False
    if expected_px is not None and (len(expected_px) != 2 or not all(math.isfinite(x) and x > 0 for x in expected_px)):
        return False
    with _db_lock:
        row = _conn.execute(
            "SELECT source, status, entries_json, entry_order_ids_json FROM signal_positions WHERE symbol=?", (symbol,)
        ).fetchone()
        if not row or str(row["source"] or "") != "manual" or str(row["status"] or "") not in ("pending", "open"):
            return False
        if expected_ids is not None:
            try:
                current_ids_raw = json.loads(row["entry_order_ids_json"] or "[]")
                current_ids = [str(x) for x in current_ids_raw] if isinstance(current_ids_raw, list) else None
            except (TypeError, ValueError, json.JSONDecodeError):
                return False
            if current_ids != expected_ids:
                return False
        if expected_px is not None:
            try:
                current_px_raw = json.loads(row["entries_json"] or "[]")
                current_px = [float(x) for x in current_px_raw] if isinstance(current_px_raw, list) else None
            except (TypeError, ValueError, OverflowError, json.JSONDecodeError):
                return False
            if current_px is None or len(current_px) != 2 or any(
                not math.isfinite(v) or abs(v - exp) > max(abs(exp) * 1e-12, 1e-12)
                for v, exp in zip(current_px, expected_px)
            ):
                return False
        cur = _conn.execute(
            "UPDATE signal_positions SET entries_json=?, entry_order_ids_json=? WHERE symbol=? AND source='manual'",
            (json.dumps(prices), json.dumps(ids), symbol),
        )
        if cur.rowcount != 1:
            _conn.rollback()
            raise RuntimeError(f"Не удалось сохранить пару ручных лимиток для {symbol}: строка БД отсутствует")
        _conn.commit()
    record_state_event("signal_position", "MANUAL_ENTRY_PAIR_REPAIRED", symbol, {
        "entries": prices, "entry_order_ids": ids,
    })
    return True


def mark_signal_breakeven_done(symbol: str, stop_price: Optional[float] = None):
    # TP1's automatic break-even step takes precedence over a pre-TP1 manual
    # stop override. Clear the latch in the same SQLite transaction as the
    # breakeven state so restarts cannot restore the old behaviour.
    if stop_price is None:
        sql = "UPDATE signal_positions SET breakeven_done=1, manual_sl_override=0 WHERE symbol=?"
        params = (symbol,)
    else:
        sql = "UPDATE signal_positions SET breakeven_done=1, manual_sl_override=0, stop_price=? WHERE symbol=?"
        params = (float(stop_price), symbol)
    _update_signal_position_checked(
        symbol, sql, params, "BREAKEVEN_DONE", {"stop_price": stop_price},
    )


def set_signal_manual_sl_override(symbol: str, enabled: bool, stop_price: Optional[float] = None):
    """Persist the user's manual SL choice until TP1's existing break-even step."""
    if stop_price is None:
        sql = "UPDATE signal_positions SET manual_sl_override=? WHERE symbol=? AND source='manual'"
        params = (int(bool(enabled)), symbol)
    else:
        sql = "UPDATE signal_positions SET manual_sl_override=?, stop_price=? WHERE symbol=? AND source='manual'"
        params = (int(bool(enabled)), float(stop_price), symbol)
    _update_signal_position_checked(
        symbol, sql, params, "MANUAL_SL_OVERRIDE",
        {"enabled": bool(enabled), "stop_price": stop_price},
    )


def mark_signal_stale_entries_cancelled(symbol: str):
    _update_signal_position_checked(
        symbol, "UPDATE signal_positions SET stale_entries_cancelled=1 WHERE symbol=?",
        (symbol,), "STALE_ENTRIES_CANCELLED", {},
    )


def delete_signal_position(symbol: str):
    with _db_lock:
        _conn.execute("DELETE FROM signal_positions WHERE symbol = ?", (symbol,))
        _conn.commit()
    record_state_event("signal_position", "CLOSED", symbol, {})


# ---------------------- лента постов OKX-трейдера ----------------------

def is_okx_post_seen(post_id: str) -> bool:
    with _db_lock:
        row = _conn.execute("SELECT 1 FROM okx_feed_seen_posts WHERE post_id = ?", (post_id,)).fetchone()
    return row is not None


def mark_okx_post_seen(post_id: str):
    with _db_lock:
        _conn.execute(
            "INSERT OR IGNORE INTO okx_feed_seen_posts (post_id, seen_at) VALUES (?, ?)",
            (post_id, int(time.time())),
        )
        # храним только последние 500 id, чтобы таблица не росла бесконечно
        _conn.execute(
            "DELETE FROM okx_feed_seen_posts WHERE post_id NOT IN "
            "(SELECT post_id FROM okx_feed_seen_posts ORDER BY seen_at DESC LIMIT 500)"
        )
        _conn.commit()


# ---------------------- meta / settings ----------------------

def get_meta(key: str, default=None):
    with _db_lock:
        row = _conn.execute("SELECT value FROM meta WHERE key = ?", (key,)).fetchone()
    return row["value"] if row else default


def set_meta(key: str, value):
    with _db_lock:
        _conn.execute(
            "INSERT INTO meta (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
            (key, str(value)),
        )
        _conn.commit()


def _parse_bool_setting_value(value, default=None) -> Optional[bool]:
    """Разбирает bool из SQLite/JSON без ловушки bool("False") == True.

    None означает нераспознанное значение. Текстовые варианты нужны для
    восстановления старых снимков настроек; неизвестные значения нельзя
    молча трактовать как True.
    """
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        try:
            if math.isfinite(float(value)) and value in (0, 1):
                return bool(value)
        except (TypeError, ValueError, OverflowError):
            return default
    normalized = str(value).strip().lower()
    if normalized in {"1", "true", "yes", "on", "enabled", "вкл", "включен", "включён", "да"}:
        return True
    if normalized in {"0", "false", "no", "off", "disabled", "выкл", "выключен", "выключён", "нет", ""}:
        return False
    return default


def get_setting(name: str, default):
    val = get_meta(f"setting_{name}", None)
    if val is None:
        return default
    if isinstance(default, bool):
        parsed_bool = _parse_bool_setting_value(val, None)
        if parsed_bool is not None:
            return parsed_bool
        # Для автоизменения лимиток неизвестное/повреждённое значение должно
        # отключать автоматизацию, а не неожиданно включать её.
        if name == "manual_limit_value_changes_enabled":
            return False
        return default
    if isinstance(default, (int, float)):
        # ВАЖНО: некоторые настройки объявлены в config.py как int (например
        # PNL_TRADE_ALERT_PLUS = 0), но пользователь вполне может ввести
        # дробное значение вроде 42.5 USDT через кнопки/ручной ввод. Старая
        # версия этой функции для int-дефолтов всегда делала int(val),
        # что молча ОБРЕЗАЛО дробную часть (42.5 -> 42) при каждом чтении —
        # реальный баг. Теперь дробная часть сохраняется, если она есть;
        # целые значения по-прежнему возвращаются как int (важно для мест
        # вроде daily_report_hour, которые сравниваются с now.hour).
        try:
            parsed = float(val)
        except ValueError:
            return default
        if isinstance(default, int) and parsed.is_integer():
            return int(parsed)
        return parsed
    return val


def set_setting(name: str, value):
    set_meta(f"setting_{name}", value)


def _safe_json_list(value, default):
    try:
        data = json.loads(value) if isinstance(value, str) else value
        return data if isinstance(data, list) else list(default)
    except (TypeError, ValueError, json.JSONDecodeError):
        return list(default)

def _safe_json_dict(value, default):
    try:
        data = json.loads(value) if isinstance(value, str) else value
        return data if isinstance(data, dict) else dict(default)
    except (TypeError, ValueError, json.JSONDecodeError):
        return dict(default)


# ---------------------- избранные монеты (whitelist для торговли) ----------------------

def get_favorite_symbols() -> List[str]:
    raw = get_meta("favorite_symbols", None)
    if raw is None:
        return [str(s).upper() for s in (getattr(cfg, "FAVORITE_SYMBOLS", None) or [])]
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [str(s).upper() for s in data]
    except (ValueError, TypeError):
        pass
    return []


def set_favorite_symbols(symbols: List[str]):
    seen: List[str] = []
    for s in symbols:
        s = str(s).upper().strip()
        if s and s not in seen:
            seen.append(s)
    set_meta("favorite_symbols", json.dumps(seen))


def add_favorite_symbols(symbols: List[str]) -> List[str]:
    """Добавляет монеты в избранное (принимает и 'BTC', и 'BTCUSDT' — сама
    дописывает суффикс USDT). Возвращает реально добавленные (новые)."""
    current = get_favorite_symbols()
    added: List[str] = []
    for raw in symbols:
        s = str(raw).upper().strip()
        if not s:
            continue
        if not s.endswith(cfg.QUOTE_COIN):
            s = s + cfg.QUOTE_COIN
        if s not in current and s not in added:
            added.append(s)
    if added:
        set_favorite_symbols(current + added)
    return added


# ---------------------- монеты-исключения (бот их не трогает вообще) ------

def get_excluded_symbols() -> List[str]:
    """Монеты, которые бот НЕ должен трогать ни при каких условиях — ни
    тейки, ни стопы, ни взятие под управление ручных сделок, ни новые
    сделки по постам. Хранится в Telegram meta (переживает передеплой)."""
    raw = get_meta("excluded_symbols", None)
    if raw is None:
        return [str(s).upper() for s in (getattr(cfg, "EXCLUDED_SYMBOLS_DEFAULT", None) or [])]
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [str(s).upper() for s in data]
    except (ValueError, TypeError):
        pass
    return []


def set_excluded_symbols(symbols: List[str]):
    seen: List[str] = []
    for s in symbols:
        s = str(s).upper().strip()
        if s and s not in seen:
            seen.append(s)
    set_meta("excluded_symbols", json.dumps(seen))


def add_excluded_symbols(symbols: List[str]) -> List[str]:
    current = get_excluded_symbols()
    added: List[str] = []
    for raw in symbols:
        s = str(raw).upper().strip()
        if not s:
            continue
        if not s.endswith(cfg.QUOTE_COIN):
            s = s + cfg.QUOTE_COIN
        if s not in current and s not in added:
            added.append(s)
    if added:
        set_excluded_symbols(current + added)
    return added


def remove_excluded_symbols(symbols: List[str]) -> List[str]:
    current = get_excluded_symbols()
    to_remove = set()
    for raw in symbols:
        s = str(raw).upper().strip()
        if s and not s.endswith(cfg.QUOTE_COIN):
            s = s + cfg.QUOTE_COIN
        to_remove.add(s)
    removed = [s for s in current if s in to_remove]
    if removed:
        set_excluded_symbols([s for s in current if s not in to_remove])
    return removed


def remove_favorite_symbol(symbol: str) -> bool:
    current = get_favorite_symbols()
    symbol = symbol.upper().strip()
    if symbol in current:
        current.remove(symbol)
        set_favorite_symbols(current)
        return True
    return False


def is_favorites_mode_enabled() -> bool:
    return bool(get_setting("favorites_mode_enabled", getattr(cfg, "ENABLE_FAVORITES_MODE", False)))


def set_favorites_mode_enabled(value: bool):
    set_setting("favorites_mode_enabled", bool(value))


def get_last_sync_time() -> int:
    return int(get_meta("last_sync_ms", 0))


def set_last_sync_time(ts_ms: int):
    set_meta("last_sync_ms", ts_ms)


# ---------------------- trades ----------------------

def upsert_trades(trades: list, source: str = "sync") -> list:
    """Сохраняет пакет сделок атомарно.

    При ошибке хотя бы одной строки откатывается весь пакет и исключение
    передаётся вызывающему коду. Это принципиально: курсор синхронизации нельзя
    продвигать, если часть сделок не записалась.
    """
    if not trades:
        return []
    new_trades = []
    with _db_lock:
        try:
            # Recover only a stale transaction left by a previous failed DB
            # operation; the lock guarantees no other thread is using it now.
            if _conn.in_transaction:
                _conn.rollback()
            _conn.execute("BEGIN IMMEDIATE")
            for t in trades:
                if not isinstance(t, dict):
                    raise TypeError(f"Некорректная запись закрытой сделки: {type(t).__name__}")
                trade_id = t.get("orderId") or t.get("execId") or f"{t.get('symbol')}_{t.get('updatedTime')}"
                if not trade_id or not t.get("symbol"):
                    raise ValueError("У закрытой сделки отсутствует id или symbol")
                cur = _conn.execute(
                    """
                    INSERT INTO trades (id, symbol, side, qty, entry_price, exit_price, closed_pnl, created_time, updated_time, leverage, source)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(id) DO NOTHING
                    """,
                    (
                        str(trade_id), t.get("symbol"), t.get("side"),
                        float(t.get("qty", 0) or 0),
                        float(t.get("avgEntryPrice", 0) or 0),
                        float(t.get("avgExitPrice", 0) or 0),
                        float(t.get("closedPnl", 0) or 0),
                        int(t.get("createdTime", 0) or 0),
                        int(t.get("updatedTime", 0) or 0),
                        float(t.get("leverage", 0) or 0) or None, source,
                    ),
                )
                if cur.rowcount > 0:
                    new_trades.append(t)
            _conn.commit()
        except Exception:
            try:
                _conn.rollback()
            except Exception:
                pass
            logging.getLogger(__name__).exception(
                "Сбой пакетной записи trades: весь пакет отменён, курсор синхронизации не должен двигаться"
            )
            raise
    return new_trades


def query_trades(start_ms: int, end_ms: int, symbol: str = None) -> list:
    with _db_lock:
        if symbol:
            rows = _conn.execute(
                "SELECT * FROM trades WHERE updated_time BETWEEN ? AND ? AND symbol = ? ORDER BY updated_time ASC",
                (start_ms, end_ms, symbol),
            ).fetchall()
        else:
            rows = _conn.execute(
                "SELECT * FROM trades WHERE updated_time BETWEEN ? AND ? ORDER BY updated_time ASC",
                (start_ms, end_ms),
            ).fetchall()
    return [dict(r) for r in rows]


def total_trade_count() -> int:
    with _db_lock:
        row = _conn.execute("SELECT COUNT(*) AS c FROM trades").fetchone()
    return row["c"] if row else 0


def last_trade_row():
    with _db_lock:
        row = _conn.execute("SELECT * FROM trades ORDER BY updated_time DESC LIMIT 1").fetchone()
    return dict(row) if row else None


# ---------------------- notification log ----------------------

def log_notification(text: str):
    with _db_lock:
        _conn.execute(
            "INSERT INTO notification_log (sent_at, text) VALUES (?, ?)",
            (int(datetime.now(timezone.utc).timestamp() * 1000), text),
        )
        _conn.execute(
            "DELETE FROM notification_log WHERE id NOT IN "
            "(SELECT id FROM notification_log ORDER BY id DESC LIMIT 200)"
        )
        _conn.commit()


def get_notification_log(limit: int = 15) -> list:
    with _db_lock:
        rows = _conn.execute(
            "SELECT sent_at, text FROM notification_log ORDER BY id DESC LIMIT ?", (limit,)
        ).fetchall()
    return [dict(r) for r in rows]


# ============================================================================
# BYBIT REST-КЛИЕНТ: торговые операции + справочные/статистические запросы
# ============================================================================

def call_with_retry(logger, func, *args, description: str = "", **kwargs):
    last_exc = None
    for attempt in range(1, max(1, cfg.MAX_RETRIES) + 1):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            last_exc = e
            if attempt < cfg.MAX_RETRIES:
                delay = cfg.RETRY_BACKOFF_SEC * (2 ** (attempt - 1))
                logger.warning(f"Попытка {attempt}/{cfg.MAX_RETRIES} не удалась ({description or func.__name__}): {e}. Повтор через {delay:.1f} сек.")
                time.sleep(delay)
            else:
                logger.error(f"Все {cfg.MAX_RETRIES} попыток исчерпаны ({description or func.__name__}): {e}")
    raise last_exc if last_exc is not None else RuntimeError(f"call_with_retry: не удалось выполнить {description or func.__name__}")


# ============================================================================
# РАСПОЗНАВАНИЕ ПОСТА-СИГНАЛА, ПРИСЛАННОГО ВРУЧНУЮ В ЧАТ
# ============================================================================
#
# Ожидаемый формат (пример):
#
#   JUP | SHORT
#   Плечо: 50х
#
#   Вход двумя равными лимитными ордерами:
#   0.2361; 0.2457
#
#   Цели:
#   0.2338; 0.2292; 0.2150; 0.1981
#
#   Стоп:
#   0.2528
#
#   После первого тейка консервативный сценарий — перенос стопа на точку входа.
#
#   Максимальный убыток по сделке — до 2% от депозита.
#
# Тейки в этом формате бот НЕ выставляет сам — их фиксирует вручную сам
# автор сигнала/пользователь. Бот лишь открывает два лимитных входа со
# стопом и, если в посте есть фраза про "перенос стопа на точку входа",
# следит за объёмом позиции и переносит стоп в безубыток, как только видит,
# что объём уменьшился (значит, часть позиции кто-то закрыл вручную).

def _numbers_after_label(lines: List[str], label_pattern: str) -> List[float]:
    """Ищет строку, содержащую label_pattern, и возвращает числа СТРОГО
    ПОСЛЕ места, где нашлась сама метка (а не после первого попавшегося
    двоеточия в строке — если на одной строке несколько меток через запятую,
    типа "Плечо: 50, Вход: 100, 105", наивный поиск по ":" мог случайно
    захватить чужое число). Если чисел после метки нет — берёт их из
    следующей(-их) непустых строк (так оформлен исходный пример поста —
    заголовок и значения на разных строках). Числа находятся независимо от
    разделителя (';', ',', '-', пробел и т.п.) — findall просто выхватывает
    все числа подряд."""
    for i, line in enumerate(lines):
        m = re.search(label_pattern, line, re.IGNORECASE)
        if m:
            tail = line[m.end():]
            nums = re.findall(r"\d+(?:[.,]\d+)?", tail)
            j = i + 1
            while not nums and j < len(lines) and lines[j].strip() != "":
                nums = re.findall(r"\d+(?:[.,]\d+)?", lines[j])
                j += 1
            return [float(n.replace(",", ".")) for n in nums]
    return []


# Слова стороны сделки — и по-русски, и по-английски, в любом регистре.
_SHORT_RE = re.compile(r"\bshort\b|шорт|шортить|продаж|\bsell\b", re.IGNORECASE)
_LONG_RE = re.compile(r"\blong\b|лонг|лонговать|покупк|\bbuy\b", re.IGNORECASE)

# Слова, которые не могут быть тикером монеты, даже если выглядят как
# "слово из букв/цифр" — встречаются в заголовке поста рядом с тикером.
_SYMBOL_NOISE_WORDS = {
    cfg.QUOTE_COIN.lower(), "usdc", "perp", "perpetual", "фьючерс", "фьючерсы",
    "пара", "монета", "тикер", "symbol", "pair", "направление", "direction",
    "сигнал", "signal", "плечо", "leverage", "лонг", "long", "шорт", "short",
    "buy", "sell", "покупка", "продажа",
}


def _extract_symbol_candidates(line: str) -> List[str]:
    # Многие тикеры на бирже идут с числовым множителем впереди
    # (1000PEPE, 1000SHIB, 1000BONK, 10000SATS и т.п.) — если не учитывать
    # ведущие цифры, "1000SHIB" превратится в "SHIB", а это на Bybit
    # совсем другой (и чаще всего несуществующий) символ.
    words = re.findall(r"\b\d{0,6}[A-Za-zА-Яа-яЁё][A-Za-zА-Яа-я0-9Ёё]{1,14}\b", line)
    return [
        w for w in words
        if w.lower() not in _SYMBOL_NOISE_WORDS
        and not _SHORT_RE.search(w)
        and not _LONG_RE.search(w)
    ]


def _find_side_and_symbol(lines: List[str]) -> Tuple[Optional[str], Optional[str]]:
    """Ищет направление сделки (SHORT/LONG, по-русски или по-английски) и
    тикер монеты в первых нескольких строках поста — не требуя жёсткого
    формата "ТИКЕР | SHORT": работает и с "JUP SHORT", "Шорт по JUP",
    "#JUP шортим", отдельными строками "Пара: JUP" / "Направление: SHORT",
    а также когда тикер и слово-направление разнесены по всему заголовку
    (например, "🚀 Разбор монеты SOL" на одной строке и "Направление: Long"
    на другой)."""
    header_zone = lines[:8]

    side, side_line_idx = None, None
    for i, line in enumerate(header_zone):
        if not line.strip():
            continue
        if _SHORT_RE.search(line):
            side, side_line_idx = "SHORT", i
            break
        if _LONG_RE.search(line):
            side, side_line_idx = "LONG", i
            break
    if side is None:
        return None, None

    # Эвристика 1 (самая надёжная): тикер почти всегда пишут ЗАГЛАВНЫМИ
    # буквами, в отличие от обычных слов описания вокруг него. Если во всей
    # шапке поста находится ровно один такой короткий "капсовый" токен —
    # это он, независимо от того, на какой именно строке относительно слова
    # направления он оказался.
    all_caps_seen, all_caps_uniq = set(), []
    for line in header_zone:
        for w in _extract_symbol_candidates(line):
            if w.isupper() and 2 <= len(w) <= 10 and w not in all_caps_seen:
                all_caps_seen.add(w)
                all_caps_uniq.append(w)
    if len(all_caps_uniq) == 1:
        return side, all_caps_uniq[0].upper()

    # Эвристика 2: тикер в той же строке, что и слово направления, либо на
    # соседней строке, если та состоит ровно из одного слова.
    candidates = _extract_symbol_candidates(header_zone[side_line_idx])
    if candidates:
        return side, candidates[0].upper()
    for j in (side_line_idx - 1, side_line_idx + 1):
        if 0 <= j < len(header_zone) and header_zone[j].strip():
            cands = _extract_symbol_candidates(header_zone[j])
            if len(cands) == 1:
                return side, cands[0].upper()

    # Последний шанс: если капсовых кандидатов несколько — берём первый
    # (обычно тикер упоминают раньше прочих капсовых сокращений вроде TP/SL).
    if all_caps_uniq:
        return side, all_caps_uniq[0].upper()

    return side, None


def _find_symbol_only(lines: List[str]) -> Optional[str]:
    """Ищет тикер монеты, когда рядом может не быть явного слова направления
    (например, посты-обзоры вида "#BEAT\\n\\nформируем накопление у нижней
    границы..." — без слова SHORT/LONG вообще)."""
    header_zone = lines[:8]
    # приоритет — хэштег в начале поста, это почти всегда сам тикер
    for line in header_zone:
        m = re.search(r"#([A-Za-zА-Яа-я0-9]{2,15})\b", line)
        if m and m.group(1).lower() not in _SYMBOL_NOISE_WORDS:
            return m.group(1).upper()

    # иначе — единственный явно капсовый короткий токен во всей шапке
    all_caps_seen, all_caps_uniq = set(), []
    for line in header_zone:
        for w in _extract_symbol_candidates(line):
            if w.isupper() and 2 <= len(w) <= 10 and w not in all_caps_seen:
                all_caps_seen.add(w)
                all_caps_uniq.append(w)
    if len(all_caps_uniq) == 1:
        return all_caps_uniq[0].upper()
    return None


# Посты-обзоры без явного слова SHORT/LONG: направление угадываем по смыслу
# текста — разговор о накоплении/покупке у нижней границы диапазона это
# LONG (покупаем на дне), о распределении/продаже у верхней границы — SHORT.
_ACCUMULATION_RE = re.compile(r"накоплен|аккумул|нижн", re.IGNORECASE)
_DISTRIBUTION_RE = re.compile(r"распредел|верхн(?:ей|яя|их)?\s*границ|сверху", re.IGNORECASE)


def _infer_side_from_context(text: str) -> Optional[str]:
    acc = bool(_ACCUMULATION_RE.search(text))
    dist = bool(_DISTRIBUTION_RE.search(text))
    if acc and not dist:
        return "LONG"
    if dist and not acc:
        return "SHORT"
    return None


# Посты-разборы с ДВУМЯ зонами сразу в одном тексте: где-то выше по цене —
# зона на шорт, где-то ниже — зона на подбор в лонг (без общего явного
# SHORT/LONG на весь пост, т.к. это две разные, независимые идеи сразу).
_ZONE_SHORT_RE = re.compile(r"шорт\w*\s*зон|зон\w*\s*шорт", re.IGNORECASE)
_ZONE_LONG_RE = re.compile(r"подбор\w*\s*в\s*лонг|лонг\w*\s*(?:можно|рассмотр)|зон\w*\s*лонг", re.IGNORECASE)


def _extract_zone_entries(lines: List[str], label_re: re.Pattern) -> Optional[List[float]]:
    """Как _numbers_after_label, но берёт ровно первые 2 числа СТРОГО ПОСЛЕ
    места, где нашлась метка (не из всей строки целиком — иначе случайная
    цифра до метки, вроде нумерации "1. Шорт зона: 100-105", могла бы
    попасть в результат вместо реальной границы зоны), либо из следующей
    непустой строки — используется отдельно для шорт-зоны и лонг-зоны,
    когда обе описаны в одном посте."""
    for i, line in enumerate(lines):
        m = label_re.search(line)
        if m:
            tail = line[m.end():]
            nums = re.findall(r"\d+(?:[.,]\d+)?", tail)
            j = i + 1
            while not nums and j < len(lines) and lines[j].strip() != "":
                nums = re.findall(r"\d+(?:[.,]\d+)?", lines[j])
                j += 1
            if len(nums) >= 2:
                return [float(n.replace(",", ".")) for n in nums[:2]]
    return None


def parse_signal_post(text: str) -> Optional[Dict]:
    """Пытается распознать текст сообщения как пост-сигнал. Возвращает None,
    если текст не похож на сигнал (обычное сообщение/кнопка/команда), чтобы
    не мешать остальным обработчикам.

    Формат гибкий: жёстко требуются только тикер монеты и хотя бы одна цена
    входа. Направление (SHORT/LONG) можно не писать явно, если из текста
    понятен смысл (накопление у нижней границы диапазона -> LONG и т.п.).
    Цели необязательны (бот их всё равно не использует для ордеров, только
    для справки). Стоп тоже необязателен — если явно не указан, бот сам
    поставит его в SIGNAL_AUTO_STOP_PERCENT % от первой цены входа."""
    if not text:
        return None
    lines = text.splitlines()
    non_empty = [l for l in lines if l.strip()]
    if not non_empty:
        return None

    # Строгий явный формат "ТИКЕР | SHORT/LONG" первой строкой — самый
    # надёжный сигнал, проверяем его ПЕРВЫМ и, если он совпал, дальше уже
    # ничего не угадываем (в частности, не даём эвристике "две зоны сразу"
    # ниже случайно переопределить явно указанное направление).
    header = re.match(r"^\s*([A-Za-z0-9]{2,20})\s*\|\s*(SHORT|LONG)\s*$", non_empty[0], re.IGNORECASE)

    # Пост с ДВУМЯ независимыми зонами сразу (шорт-зона выше по цене, зона
    # на подбор в лонг ниже — без общего явного SHORT/LONG на весь пост,
    # т.к. это буквально две разные идеи в одном тексте). В отличие от
    # остального разбора, тут бот не может сам выбрать направление — цена
    # ещё не в ЛЮБОЙ из зон, и без выбора пользователя гадать нельзя.
    if not header:
        short_zone = _extract_zone_entries(lines, _ZONE_SHORT_RE)
        long_zone = _extract_zone_entries(lines, _ZONE_LONG_RE)
        if short_zone and long_zone:
            raw_symbol = _find_symbol_only(non_empty)
            if raw_symbol:
                symbol = raw_symbol if raw_symbol.endswith(cfg.QUOTE_COIN) else raw_symbol + cfg.QUOTE_COIN
                return {
                    "symbol": symbol,
                    "dual_zone": True,
                    "long_entries": long_zone,
                    "short_entries": short_zone,
                    "leverage": None,
                    "targets": [],
                    "stop_auto": True,
                    "breakeven_after_tp1": False,
                }

    # Быстрый путь: строгий формат уже проверен выше (переменная header).
    side_explicit = True
    if header:
        raw_symbol, side = header.group(1).upper(), header.group(2).upper()
    else:
        side, raw_symbol = _find_side_and_symbol(non_empty)
        if raw_symbol is None:
            raw_symbol = _find_symbol_only(non_empty)
        if side is None:
            side = _infer_side_from_context(text)
            side_explicit = False
        if side is None:
            # Ни явного SHORT/LONG, ни узнаваемого контекста (накопление/
            # распределение) — но если при этом нашлась зона входа с ценами
            # (например, "Зона интереса 96.94-95.46" без единого слова про
            # направление), не сдаёмся: отдаём как зону с неизвестным
            # направлением, а выбор — кнопкой у пользователя (как и для
            # постов с двумя зонами сразу).
            if raw_symbol is not None:
                zone_entries = _numbers_after_label(lines, r"вход|entr(?:y|ies)|buy\s*zone|диапазон\s*интерес|зона\s*интерес")
                if len(zone_entries) >= 1:
                    symbol = raw_symbol if raw_symbol.endswith(cfg.QUOTE_COIN) else raw_symbol + cfg.QUOTE_COIN
                    return {
                        "symbol": symbol,
                        "unknown_zone": True,
                        "zone_entries": zone_entries,
                        "leverage": None,
                        "targets": [],
                        "stop_auto": True,
                        "breakeven_after_tp1": False,
                    }
            return None
        if raw_symbol is None:
            return None

    symbol = raw_symbol if raw_symbol.endswith(cfg.QUOTE_COIN) else raw_symbol + cfg.QUOTE_COIN

    leverage_nums = _numbers_after_label(lines, r"плеч|leverage|\blev\b")
    leverage = leverage_nums[0] if leverage_nums else None

    entries = _numbers_after_label(lines, r"вход|entr(?:y|ies)|buy\s*zone|диапазон\s*интерес|зона\s*интерес")
    targets = _numbers_after_label(lines, r"цел|тейк|target|\btp\b")
    stop_nums = _numbers_after_label(lines, r"стоп|\bstop\b|\bsl\b")
    stop = stop_nums[0] if stop_nums else None

    breakeven_after_tp1 = bool(re.search(r"точку входа|безубыток|в\s*бу\b|break\s*even", text, re.IGNORECASE))

    if len(entries) < 1:
        return None

    # Правило «лимиток больше двух — работаем с ПЕРВЫМИ двумя». Раньше бот
    # выставлял лимитки на ВСЕ числа после слова «Вход» (и мог зацепить лишнее
    # число из строки). Остальные цены не теряются: они уходят в entries_dropped,
    # чтобы это было видно в подтверждении. Лимит задаётся SIGNAL_MAX_ENTRIES в config.py.
    entries_dropped: List[float] = []
    try:
        max_entries = max(1, int(getattr(cfg, "SIGNAL_MAX_ENTRIES", 2)))
    except (TypeError, ValueError):
        max_entries = 2
    if len(entries) > max_entries:
        entries_dropped = entries[max_entries:]
        entries = entries[:max_entries]

    stop_auto = False
    if stop is None:
        auto_pct = getattr(cfg, "SIGNAL_AUTO_STOP_PERCENT", 12) / 100.0
        stop = entries[0] * (1 - auto_pct) if side == "LONG" else entries[0] * (1 + auto_pct)
        stop_auto = True

    single_target_is_partial = False
    if not targets:
        # В посте вообще нет секции "Цели" (например, обычное "накопление"
        # без своих целей) — придумывать полноценный тейк не из чего, но
        # частичное закрытие + перенос в безубыток всё равно нужны каждой
        # сделке, поэтому считаем ту же синтетическую цель, что и для зон:
        # SIGNAL_ZONE_TP_PERCENT % от первой цены входа.
        zone_tp_pct = getattr(cfg, "SIGNAL_ZONE_TP_PERCENT", 3) / 100.0
        synthetic_tp = entries[0] * (1 + zone_tp_pct) if side == "LONG" else entries[0] * (1 - zone_tp_pct)
        targets = [synthetic_tp]
        single_target_is_partial = True
        breakeven_after_tp1 = True  # без явного текста тоже переносим — иначе стоп никогда не сдвинется

    return {
        "symbol": symbol,
        "side": side,
        "side_explicit": side_explicit,
        "leverage": leverage,
        "entries": entries,
        "entries_dropped": entries_dropped,
        "targets": targets,
        "single_target_is_partial": single_target_is_partial,
        "stop": stop,
        "stop_auto": stop_auto,
        "breakeven_after_tp1": breakeven_after_tp1,
    }


# ---------------------------------------------------------------------------
# Мониторинг ленты постов трейдера в OKX (Insights/Moments) и пересылка новых
# постов в Telegram с переводом на русский и картинками.
#
# ВАЖНО: okx.com закрыт для автоматического обращения по robots.txt, а сама
# лента отрисовывается через JS (SPA) — точную HTML-разметку страницы
# заранее увидеть было нельзя. Поэтому ниже используется headless-браузер
# (Playwright, а не голый requests — без него JS-контент просто не появится
# в HTML), а селекторы вынесены в OKX_FEED_SELECTORS одним блоком, чтобы их
# было легко поправить под реальную вёрстку страницы, если после первого
# запуска бот скачает 0 постов или явно не те данные.
# ---------------------------------------------------------------------------

OKX_FEED_SELECTORS = {
    # Контейнер одного поста в ленте.
    "post_container": "[class*='post'], [class*='feed-item'], [class*='moment'], article",
    # Текст поста внутри контейнера.
    "post_text": "[class*='content'], [class*='text'], p",
    # Картинки поста внутри контейнера.
    "post_images": "img",
    # Атрибут с уникальным id поста на контейнере, если он есть в вёрстке.
    "post_id_attr": "data-post-id",
}


def _fetch_okx_feed_posts() -> List[Dict]:
    """Рендерит страницу ленты постов трейдера в headless-браузере и
    возвращает список постов [{id, text, images}], от старых к новым.
    Требует `pip install playwright` + `playwright install chromium`."""
    from playwright.sync_api import sync_playwright

    posts = []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        page = browser.new_page(user_agent=(
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
        ))
        try:
            page.goto(cfg.OKX_FEED_URL, wait_until="networkidle", timeout=30000)
            page.wait_for_timeout(2000)  # доотрисовка контента после сети

            containers = page.query_selector_all(OKX_FEED_SELECTORS["post_container"])
            for c in containers:
                text_el = c.query_selector(OKX_FEED_SELECTORS["post_text"])
                text = (text_el.inner_text() if text_el else c.inner_text()).strip()
                if not text:
                    continue
                img_urls = [img.get_attribute("src") for img in c.query_selector_all(OKX_FEED_SELECTORS["post_images"])]
                img_urls = [u for u in img_urls if u and u.startswith("http")]

                post_id = c.get_attribute(OKX_FEED_SELECTORS["post_id_attr"])
                if not post_id:
                    # нет отдельного id в вёрстке — используем хэш текста поста
                    post_id = hashlib.sha1(text.encode("utf-8")).hexdigest()[:16]

                posts.append({"id": post_id, "text": text, "images": img_urls})
        finally:
            browser.close()
    return posts


def _translate_to_russian(text: str) -> str:
    """Переводит текст поста на русский через Google Translate (без ключа,
    библиотека deep-translator). Если перевод не удался — возвращает
    оригинал, чтобы пост всё равно дошёл до пользователя."""
    try:
        from deep_translator import GoogleTranslator
        chunk_size = 4500  # у Google Translate есть лимит на длину запроса
        chunks = [text[i:i + chunk_size] for i in range(0, len(text), chunk_size)] or [text]
        translated_chunks = [GoogleTranslator(source="auto", target="ru").translate(c) for c in chunks]
        return "\n".join(translated_chunks)
    except Exception:
        return text


def _is_position_mode_error(exc) -> bool:
    """Bybit возвращает ErrCode 10001 "position idx not match position mode",
    когда для символа аккаунт находится в режиме хеджирования (Buy/Sell —
    раздельные позиции), а запрос отправлен с positionIdx=0 (режим one-way),
    или наоборот. Определяем это по тексту ошибки, чтобы автоматически
    подставить верный positionIdx и не проваливать размещение ордера."""
    msg = str(exc).lower()
    return "position idx not match position mode" in msg or "errcode: 10001" in msg or '"retcode":10001' in msg


class OrderPlacementUnknown(RuntimeError):
    """Запрос создания ордера мог быть принят биржей, но его состояние
    невозможно надёжно подтвердить из-за сбоя чтения API. В таком состоянии
    нельзя создавать второй ордер с новым orderLinkId — это может раздвоить
    позицию/тейк. Следующий фоновый цикл должен повторить reconciliation."""


class BybitClient:
    def __init__(self, logger):
        self.log = logger
        self.session = HTTP(
            testnet=cfg.TESTNET,
            api_key=cfg.API_KEY,
            api_secret=cfg.API_SECRET,
            timeout=cfg.REQUEST_TIMEOUT_SEC,
            recv_window=20000,
        )
        if getattr(cfg, "PROXY_URL", ""):
            self.session.client.proxies = {"http": cfg.PROXY_URL, "https": cfg.PROXY_URL}
            self.log.info("Использую прокси для запросов к Bybit")

        self._leverage_set: set = set()
        self._instrument_cache: Dict[str, Dict] = {}
        self._instrument_cache_lock = threading.Lock()
        self._hedge_mode_symbols: set = set()  # символы, для которых аккаунт оказался в hedge-режиме

    # ------------------------------------------------------------------
    # Справочные данные
    # ------------------------------------------------------------------

    def get_linear_usdt_symbols(self) -> List[str]:
        symbols = []
        cursor = None
        while True:
            # ВАЖНО: get_instruments_info пагинируется (лимит по умолчанию
            # 500 на страницу, максимум 1000) — без явного прохода по всем
            # страницам через nextPageCursor часть бессрочных пар могла бы
            # просто не попасть в список, если их больше лимита одной
            # страницы. Явно запрашиваем максимум (1000) и идём по курсору
            # до конца, чтобы гарантированно отслеживать ВСЕ пары.
            params = dict(category=cfg.CATEGORY, limit=1000)
            if cursor:
                params["cursor"] = cursor
            result = call_with_retry(self.log, self.session.get_instruments_info, description="get_instruments_info (все символы)", **params)
            for item in result["result"]["list"]:
                if item.get("status") != "Trading":
                    continue
                if not item["symbol"].endswith(cfg.QUOTE_COIN):
                    continue
                if item.get("contractType") != "LinearPerpetual":
                    continue
                symbols.append(item["symbol"])
            cursor = result["result"].get("nextPageCursor")
            if not cursor:
                break

        if cfg.SYMBOL_WHITELIST:
            symbols = [s for s in symbols if s in cfg.SYMBOL_WHITELIST]
        if cfg.SYMBOL_BLACKLIST:
            symbols = [s for s in symbols if s not in cfg.SYMBOL_BLACKLIST]
        return symbols

    # Фильтры инструмента (шаг цены/количества, minNotional, максимальное
    # плечо) биржа может менять; без срока годности процесс, работающий
    # неделями, считал бы объёмы по устаревшим правилам.
    _INSTRUMENT_CACHE_TTL_SEC = 6 * 3600

    def get_instrument_filters(self, symbol: str) -> Dict:
        with self._instrument_cache_lock:
            cached_entry = self._instrument_cache.get(symbol)
        if cached_entry is not None and time.time() - cached_entry[0] < self._INSTRUMENT_CACHE_TTL_SEC:
            return cached_entry[1]

        try:
            resp = call_with_retry(self.log, self.session.get_instruments_info, category=cfg.CATEGORY, symbol=symbol, description=f"get_instruments_info({symbol})")
        except Exception as e:
            if cached_entry is not None:
                # Сетевой сбой при обновлении: лучше прежние фильтры, чем отказ.
                self.log.warning(f"[{symbol}] Не удалось обновить фильтры инструмента ({e}); использую сохранённые.")
                return cached_entry[1]
            raise
        lst = resp["result"]["list"]
        if not lst:
            # Bybit для несуществующего символа иногда отвечает retCode=0 с
            # пустым списком вместо ошибки — ловим это явно, чтобы выше по
            # стеку (resolve_symbol) можно было спокойно перебрать варианты.
            raise ValueError(f"символ {symbol} не найден на бирже")
        info = lst[0]
        with self._instrument_cache_lock:
            self._instrument_cache[symbol] = (time.time(), info)
        return info

    def get_qty_step(self, symbol: str) -> float:
        return float(self.get_instrument_filters(symbol)["lotSizeFilter"]["qtyStep"])

    def get_open_order_ids(self, symbol: str) -> Optional[set]:
        """Возвращает set orderId открытых (ещё не исполненных) ордеров по
        символу — одним запросом на весь символ, а не по каждому ордеру
        отдельно. Возвращает None при сбое запроса (а не пустой set!), чтобы
        вызывающий код не спутал 'не смогли узнать' с 'ничего не осталось
        открытым' — это разные вещи и последствия разные."""
        try:
            resp = call_with_retry(self.log, self.session.get_open_orders, category=cfg.CATEGORY, symbol=symbol, description=f"get_open_orders({symbol})")
            return {o["orderId"] for o in resp.get("result", {}).get("list", [])}
        except Exception:
            self.log.exception(f"Не удалось получить открытые ордера {symbol}")
            return None

    # Числовые множители, с которыми на Bybit торгуются мелкие по цене
    # монеты: 1000PEPEUSDT, 1000SHIBUSDT, 1000BONKUSDT, 10000SATSUSDT и т.п.
    # Длинные множители — раньше, чтобы не спутать вложенные варианты.
    _SIZE_MULTIPLIERS = ("1000000", "100000", "10000", "1000")

    def resolve_symbol(self, symbol: str) -> str:
        """Проверяет, существует ли символ на бирже, и если нет — перебирает
        типичные числовые множители в начале тикера, пока не найдёт реально
        торгуемый контракт (например, пост про "SHIB" на деле означает
        1000SHIBUSDT, а пост уже с "1000SHIB" должен сработать сразу же).
        Бросает понятную ошибку, если ни один вариант не нашёлся."""
        quote = cfg.QUOTE_COIN
        base = symbol[:-len(quote)] if symbol.endswith(quote) else symbol

        candidates = [base]
        matched_multiplier = next((m for m in self._SIZE_MULTIPLIERS if base.startswith(m)), None)
        if matched_multiplier:
            candidates.append(base[len(matched_multiplier):])  # вариант без множителя
        for m in self._SIZE_MULTIPLIERS:
            if m != matched_multiplier:
                candidates.append(m + (base[len(matched_multiplier):] if matched_multiplier else base))

        seen = set()
        uniq_candidates = [c for c in candidates if c and not (c in seen or seen.add(c))]

        tried_symbols = []
        for cand in uniq_candidates:
            cand_symbol = cand if cand.endswith(quote) else cand + quote
            tried_symbols.append(cand_symbol)
            try:
                self.get_instrument_filters(cand_symbol)
                return cand_symbol
            except Exception:
                continue

        raise ValueError(f"не нашёл на бирже ни одного варианта символа: {', '.join(tried_symbols)}. Проверь тикер в посте.")

    # ---- REST-фолбэк для расчёта % изменения (пока WS не накопил историю) --

    def get_hourly_change_pct_rest(self, symbol: str) -> Optional[float]:
        limit = max(2, cfg.LOOKBACK_MINUTES // int(cfg.KLINE_INTERVAL) + 1)
        try:
            resp = call_with_retry(self.log, self.session.get_kline, category=cfg.CATEGORY, symbol=symbol, interval=cfg.KLINE_INTERVAL, limit=limit, description=f"get_kline({symbol})")
        except Exception as e:
            self.log.debug(f"[{symbol}] REST-фолбэк не удался: {e}")
            return None

        klines = resp["result"]["list"]
        if len(klines) < 2:
            return None
        oldest_close = float(klines[-1][4])
        latest_close = float(klines[0][4])
        if oldest_close <= 0:
            return None
        return (latest_close - oldest_close) / oldest_close * 100.0

    def scan_rest_fallback(self, symbols: List[str]) -> Dict[str, float]:
        results: Dict[str, float] = {}
        if not symbols:
            return results
        with concurrent.futures.ThreadPoolExecutor(max_workers=cfg.MAX_WORKERS, thread_name_prefix="rest-scan") as pool:
            future_to_symbol = {pool.submit(self.get_hourly_change_pct_rest, s): s for s in symbols}
            for future in concurrent.futures.as_completed(future_to_symbol):
                symbol = future_to_symbol[future]
                try:
                    change_pct = future.result()
                except Exception:
                    continue
                if change_pct is not None:
                    results[symbol] = change_pct
        return results

    def get_last_price_rest(self, symbol: str) -> Optional[float]:
        resp = call_with_retry(self.log, self.session.get_tickers, category=cfg.CATEGORY, symbol=symbol, description=f"get_tickers({symbol})")
        lst = resp["result"]["list"]
        return float(lst[0]["lastPrice"]) if lst else None

    def get_recent_candles(self, symbol: str, interval: str = "1", limit: int = 60) -> List[Dict]:
        """Возвращает последние свечи в порядке от СТАРОЙ к НОВОЙ (удобно для
        индикаторов вроде EMA). Каждая свеча: {open, high, low, close, volume,
        start_ms}. Используется фильтрами входа (тренд, объём, пробой,
        вертикальная свеча) — все они работают по одним и тем же данным,
        поэтому кэшируются на уровне вызывающего кода на секунды, а не здесь.
        """
        resp = call_with_retry(self.log, self.session.get_kline, category=cfg.CATEGORY, symbol=symbol, interval=interval, limit=limit, description=f"get_kline_candles({symbol})")
        raw = resp["result"]["list"]  # Bybit отдаёт от новой к старой
        candles = []
        for row in reversed(raw):  # переворачиваем -> от старой к новой
            candles.append({
                "start_ms": int(row[0]),
                "open": float(row[1]),
                "high": float(row[2]),
                "low": float(row[3]),
                "close": float(row[4]),
                "volume": float(row[5]),
            })
        return candles

    # ------------------------------------------------------------------
    # Позиции и баланс
    # ------------------------------------------------------------------

    def get_equity_usdt(self) -> float:
        resp = call_with_retry(self.log, self.session.get_wallet_balance, accountType="UNIFIED", coin=cfg.QUOTE_COIN, description="get_wallet_balance")
        coins = resp["result"]["list"][0]["coin"]
        for c in coins:
            if c["coin"] == cfg.QUOTE_COIN:
                return float(c["walletBalance"] or 0)
        return 0.0

    def _get_positions_all_pages(self, description: str) -> List[Dict]:
        """Все позиции аккаунта по settleCoin со ВСЕМИ страницами. Без limit/cursor
        Bybit отдаёт только первую страницу (по умолчанию 20 записей): позиции
        сверх неё были бы невидимы — бот не взял бы их под управление, а уже
        отслеживаемые принял бы за закрытые."""
        positions: List[Dict] = []
        cursor = None
        for _ in range(50):  # защита от бесконечной пагинации
            params = dict(category=cfg.CATEGORY, settleCoin=cfg.QUOTE_COIN, limit=200)
            if cursor:
                params["cursor"] = cursor
            resp = call_with_retry(self.log, self.session.get_positions, description=description, **params)
            result = resp.get("result", {}) or {}
            positions.extend(result.get("list", []) or [])
            cursor = result.get("nextPageCursor")
            if not cursor:
                break
        return [p for p in positions if float(p.get("size") or 0) > 0]

    def get_open_positions(self) -> List[Dict]:
        return self._get_positions_all_pages("get_positions")

    def get_position(self, symbol: str, side: Optional[str] = None) -> Optional[Dict]:
        """side — опциональный фильтр "Buy"/"Sell": в hedge-режиме по одному
        символу может быть сразу 2 открытые позиции (long и short), и без
        фильтра можно случайно взять не ту. В one-way режиме по символу
        всегда максимум одна позиция, фильтр не мешает.

        ВНИМАНИЕ: при сбое запроса возвращает None — то же самое значение,
        что и при "позиции реально нет". Для кода, где это разграничение
        критично (например, мониторинг сигнальных позиций — спутать сбой
        сети с реальным закрытием позиции значит по ошибке удалить её из
        отслеживания, хотя она всё ещё жива), используй get_position_strict,
        который при сбое поднимает исключение вместо молчаливого None."""
        try:
            resp = call_with_retry(self.log, self.session.get_positions, category=cfg.CATEGORY, symbol=symbol, description=f"get_positions({symbol})")
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось получить данные позиции: {e}")
            return None
        lst = [p for p in resp["result"]["list"] if float(p.get("size") or 0) > 0 and (side is None or p.get("side") == side)]
        return lst[0] if lst else None

    def get_position_strict(self, symbol: str, side: Optional[str] = None) -> Optional[Dict]:
        """Как get_position, но при сбое запроса ПОДНИМАЕТ исключение вместо
        молчаливого None — используется там, где нельзя перепутать 'не
        удалось узнать' с 'позиции точно нет'."""
        resp = call_with_retry(self.log, self.session.get_positions, category=cfg.CATEGORY, symbol=symbol, description=f"get_positions({symbol})")
        lst = [p for p in resp["result"]["list"] if float(p.get("size") or 0) > 0 and (side is None or p.get("side") == side)]
        return lst[0] if lst else None

    def get_closed_pnl(self, symbol: str) -> Optional[Dict]:
        lst = self.get_recent_closed_pnl(symbol, limit=1)
        return lst[0] if lst else None

    def get_recent_closed_pnl(self, symbol: str, limit: int = 5) -> List[Dict]:
        """Последние N записей closed-pnl по символу (не обязательно только
        одна) — нужно, чтобы можно было сопоставить нужную запись с только
        что закрытой позицией, а не слепо брать «самую свежую», которая
        из-за задержки индексации на бирже иногда оказывается предыдущей
        сделкой по этому же символу."""
        try:
            resp = call_with_retry(self.log, self.session.get_closed_pnl, category=cfg.CATEGORY, symbol=symbol, limit=limit, description=f"get_closed_pnl({symbol})")
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось получить Closed PnL: {e}")
            return []
        return resp.get("result", {}).get("list", [])

    def fetch_closed_pnl_range(self, start_ms: int, end_ms: int) -> List[Dict]:
        """Вся история закрытых сделок за диапазон времени (для фоновой сверки
        и построения статистики) — с пагинацией по 7-дневным окнам, как того
        требует Bybit API.

        ВАЖНО: без symbol в запросе category="linear" отдаёт закрытые сделки
        по ВСЕМ линейным контрактам аккаунта, включая USDC-перпетуалы вида
        "AAVEPERP" (не то же самое, что USDT-пара "AAVEUSDT"!) — если
        случайно/вручную была сделка на таком контракте, бот присылал бы
        уведомление о ней, как будто это его собственная сделка. Явно
        отсекаем settleCoin=USDT, чтобы учитывались только те же
        USDT-перпетуалы, которыми бот и торгует."""
        all_trades = []
        window = 7 * 24 * 60 * 60 * 1000
        cur_start = start_ms
        while cur_start < end_ms:
            cur_end = min(cur_start + window, end_ms)
            cursor = None
            while True:
                params = dict(category=cfg.CATEGORY, settleCoin=cfg.QUOTE_COIN, startTime=cur_start, endTime=cur_end, limit=100)
                if cursor:
                    params["cursor"] = cursor
                resp = call_with_retry(self.log, self.session.get_closed_pnl, description="get_closed_pnl(range)", **params)
                result = resp.get("result", {})
                all_trades.extend(result.get("list", []))
                cursor = result.get("nextPageCursor")
                if not cursor:
                    break
                time.sleep(0.1)
            cur_start = cur_end
        return all_trades

    def get_open_orders_all(self) -> List[Dict]:
        """Все открытые ордера по всему аккаунту (USDT-перпетуалы), с
        пагинацией. Используется для восстановления состояния бота после
        рестарта/редеплоя — если локальная база потерялась, это единственный
        способ узнать, какие лимитки бот когда-то выставил и они всё ещё
        висят неисполненными."""
        orders = []
        cursor = None
        while True:
            params = dict(category=cfg.CATEGORY, settleCoin=cfg.QUOTE_COIN, limit=50)
            if cursor:
                params["cursor"] = cursor
            resp = call_with_retry(self.log, self.session.get_open_orders, description="get_open_orders(all)", **params)
            result = resp.get("result", {})
            orders.extend(result.get("list", []))
            cursor = result.get("nextPageCursor")
            if not cursor:
                break
            time.sleep(0.1)
        return orders

    def get_order_state(self, symbol: str, order_id: str) -> Optional[Dict]:
        """Возвращает состояние конкретного ордера, включая уже исполненный.

        ВАЖНО: get_open_orders не является надёжным источником финальной
        истории. После исполнения Bybit может убрать ордер из списка активных.
        Поэтому сначала проверяем активные ордера, затем order history по
        конкретному orderId. Если оба запроса не смогли дать ответ, исключение
        поднимается наружу: вызывающий код не имеет права создавать новый TP
        при неизвестном состоянии старого.
        """
        last_exc = None
        try:
            resp = call_with_retry(
                self.log, self.session.get_open_orders,
                category=cfg.CATEGORY, symbol=symbol, orderId=order_id, openOnly=0,
                description=f"get_order_state({symbol},{order_id})",
            )
            for order in resp.get("result", {}).get("list", []):
                if str(order.get("orderId") or "") == str(order_id):
                    return order
        except Exception as e:
            last_exc = e

        # Финальный статус ищем в истории ордеров. Ограничиваем запрос самим
        # orderId, чтобы не сканировать историю всей монеты.
        try:
            resp = call_with_retry(
                self.log, self.session.get_order_history,
                category=cfg.CATEGORY, symbol=symbol, orderId=order_id, limit=1,
                description=f"get_order_history_by_id({symbol},{order_id})",
            )
            for order in resp.get("result", {}).get("list", []):
                if str(order.get("orderId") or "") == str(order_id):
                    return order
        except Exception as e:
            last_exc = e

        if last_exc is not None:
            raise last_exc
        return None

    def get_order_state_by_link(self, symbol: str, order_link_id: str) -> Optional[Dict]:
        """Возвращает состояние ордера по orderLinkId, включая финальные статусы.

        Используется как защита от потерянного ACK: если create-order реально
        создал TP, но ответ не дошёл до бота, повторный create не должен создавать
        второй ордер. Активное состояние ищем через open orders, финальное —
        через order history.
        """
        last_exc = None
        try:
            resp = call_with_retry(
                self.log, self.session.get_open_orders,
                category=cfg.CATEGORY, symbol=symbol, orderLinkId=order_link_id, openOnly=0,
                description=f"get_order_state_by_link({symbol},{order_link_id})",
            )
            for order in resp.get("result", {}).get("list", []):
                if str(order.get("orderLinkId") or "") == str(order_link_id):
                    return order
        except Exception as e:
            last_exc = e

        try:
            resp = call_with_retry(
                self.log, self.session.get_order_history,
                category=cfg.CATEGORY, symbol=symbol, orderLinkId=order_link_id, limit=1,
                description=f"get_order_history_by_link({symbol},{order_link_id})",
            )
            for order in resp.get("result", {}).get("list", []):
                if str(order.get("orderLinkId") or "") == str(order_link_id):
                    return order
        except Exception as e:
            last_exc = e

        if last_exc is not None:
            raise last_exc
        return None

    def get_symbol_order_history(self, symbol: str, days: int = 30) -> List[Dict]:
        """История ордеров (включая исполненные) ПО ОДНОМУ символу — дешевле
        и быстрее, чем сканировать весь аккаунт, когда нужно проверить
        конкретную монету (например, ставился ли уже частичный тейк)."""
        end_ms = int(time.time() * 1000)
        start_ms = end_ms - days * 24 * 60 * 60 * 1000
        orders = []
        window = 7 * 24 * 60 * 60 * 1000
        cur_start = start_ms
        while cur_start < end_ms:
            cur_end = min(cur_start + window, end_ms)
            cursor = None
            while True:
                params = dict(category=cfg.CATEGORY, symbol=symbol, startTime=cur_start, endTime=cur_end, limit=50)
                if cursor:
                    params["cursor"] = cursor
                resp = call_with_retry(self.log, self.session.get_order_history, description=f"get_order_history({symbol})", **params)
                result = resp.get("result", {})
                orders.extend(result.get("list", []))
                cursor = result.get("nextPageCursor")
                if not cursor:
                    break
                time.sleep(0.1)
            cur_start = cur_end
        return orders

    def get_all_open_positions(self) -> List[Dict]:
        """Все открытые позиции по всему аккаунту (USDT-перпетуалы), одним
        запросом без фильтра по символу — нужно, чтобы найти позиции,
        открытые ПОЛЬЗОВАТЕЛЕМ ВРУЧНУЮ на бирже (не через посты в чате и не
        через памп-шорт стратегию), и взять их под управление ботом."""
        return self._get_positions_all_pages("get_positions(all)")

    def get_recent_order_history_all(self, days: int = 14) -> List[Dict]:
        """История ордеров (включая уже исполненные) за последние N дней по
        всему аккаунту — нужна, чтобы найти входы, которые бот уже открыл
        (и они пропали из 'открытых ордеров', т.к. исполнились), но
        локальная база о них уже не помнит (например, после редеплоя)."""
        end_ms = int(time.time() * 1000)
        start_ms = end_ms - days * 24 * 60 * 60 * 1000
        orders = []
        window = 7 * 24 * 60 * 60 * 1000
        cur_start = start_ms
        while cur_start < end_ms:
            cur_end = min(cur_start + window, end_ms)
            cursor = None
            while True:
                params = dict(category=cfg.CATEGORY, settleCoin=cfg.QUOTE_COIN, startTime=cur_start, endTime=cur_end, limit=50)
                if cursor:
                    params["cursor"] = cursor
                resp = call_with_retry(self.log, self.session.get_order_history, description="get_order_history(all)", **params)
                result = resp.get("result", {})
                orders.extend(result.get("list", []))
                cursor = result.get("nextPageCursor")
                if not cursor:
                    break
                time.sleep(0.1)
            cur_start = cur_end
        return orders

    def get_symbol_conditional_orders_strict(self, symbol: str) -> List[Dict]:
        """Strict recovery lookup: propagate API failures so recovery never
        mistakes an unavailable order list for a confirmed empty list."""
        resp = call_with_retry(
            self.log, self.session.get_open_orders,
            category=cfg.CATEGORY, symbol=symbol, openOnly=0,
            orderFilter="StopOrder",
            description=f"get_open_orders(StopOrder,{symbol})",
        )
        return resp.get("result", {}).get("list", [])

    def fetch_fees_sum(self, start_ms: int, end_ms: int) -> Tuple[float, int]:
        """Суммарная комиссия по исполнениям за период. Как и в
        fetch_closed_pnl_range, отсекаем settleCoin=USDT, чтобы не приплюсовать
        комиссии по несвязанным USDC-перпетуалам."""
        total_fee = 0.0
        count = 0
        cursor = None
        while True:
            params = dict(category=cfg.CATEGORY, settleCoin=cfg.QUOTE_COIN, startTime=start_ms, endTime=end_ms, limit=100)
            if cursor:
                params["cursor"] = cursor
            resp = call_with_retry(self.log, self.session.get_executions, description="get_executions(fees)", **params)
            result = resp.get("result", {})
            for ex in result.get("list", []):
                total_fee += float(ex.get("execFee", 0) or 0)
                count += 1
            cursor = result.get("nextPageCursor")
            if not cursor:
                break
            time.sleep(0.1)
        return total_fee, count

    # ------------------------------------------------------------------
    # Торговые действия
    # ------------------------------------------------------------------

    @staticmethod
    def _new_order_link_id(prefix: str) -> str:
        return f"{prefix}{uuid.uuid4().hex[:28]}"

    def ensure_leverage(self, symbol: str, leverage: Optional[float] = None, strict: bool = False):
        """strict=True — используется там, где объём ордера СЧИТАЕТСЯ от
        этого плеча (сигнальные позиции): если биржа не подтвердит именно
        запрошенное плечо, лучше явно провалить операцию с понятной
        ошибкой, чем молча открыть позицию, объём которой был посчитан под
        одно плечо, а реально применится другое (несовпадение риска и
        размера маржи на сделке)."""
        lev = leverage if leverage is not None else cfg.LEVERAGE
        cache_key = (symbol, lev)
        if cache_key in self._leverage_set:
            return
        try:
            call_with_retry(self.log, self.session.set_leverage, category=cfg.CATEGORY, symbol=symbol, buyLeverage=str(lev), sellLeverage=str(lev), description=f"set_leverage({symbol})")
            self._remember_leverage(symbol, cache_key)
        except Exception as e:
            if "not modified" in str(e).lower():
                self._remember_leverage(symbol, cache_key)
            elif strict:
                raise RuntimeError(f"не удалось выставить плечо {lev:g}x для {symbol}: {e}")
            else:
                self.log.warning(f"[{symbol}] Не удалось выставить плечо {lev}x, повторю попытку при следующем входе: {e}")

    def _remember_leverage(self, symbol: str, cache_key) -> None:
        """Запоминает, что для символа выставлено плечо cache_key[1], и забывает
        прежние значения этого символа: иначе возврат к ранее использованному
        плечу считался бы «уже выставленным», хотя на бирже стоит другое."""
        for k in list(self._leverage_set):
            if k[0] == symbol and k != cache_key:
                self._leverage_set.discard(k)
        self._leverage_set.add(cache_key)

    def ensure_leverage_verified(self, symbol: str, leverage: float) -> Optional[float]:
        """Выставляет плечо и подтверждает его чтением с биржи. Возвращает
        фактическое плечо (None, если прочитать не удалось).

        Кэш ensure_leverage мог устареть (плечо изменили вручную в приложении
        Bybit): при расхождении сбрасываем кэш и выставляем плечо заново один
        раз, иначе расчёт маржи шёл бы от плеча, которого на бирже уже нет."""
        self.ensure_leverage(symbol, leverage=leverage, strict=True)
        actual = self.get_symbol_leverage(symbol)
        if actual and abs(actual - leverage) > 0.01:
            self._leverage_set.discard((symbol, leverage))
            self.ensure_leverage(symbol, leverage=leverage, strict=True)
            actual = self.get_symbol_leverage(symbol)
        return actual

    def get_symbol_leverage(self, symbol: str) -> Optional[float]:
        """Реальное текущее плечо, выставленное на аккаунте для символа.
        В отличие от get_position() не требует открытой позиции (объём >0)
        — плечо привязано к символу и возвращается биржей всегда, даже
        когда позиции ещё нет. Используется, чтобы после ensure_leverage
        подтвердить, что плечо и правда применилось именно то, от которого
        считается объём ордера."""
        try:
            resp = call_with_retry(self.log, self.session.get_positions, category=cfg.CATEGORY, symbol=symbol, description=f"get_positions/leverage({symbol})")
            lst = resp["result"]["list"]
            if lst:
                return float(lst[0].get("leverage") or 0)
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось проверить текущее плечо: {e}")
        return None

    def get_max_leverage(self, symbol: str) -> float:
        """Максимальное плечо, разрешённое биржей именно для этой монеты
        (у разных пар разный потолок — у топовых обычно выше, у мелких
        альтов заметно ниже). Используется настройкой «Плечо для сигналов:
        максимальное для монеты»."""
        filters = self.get_instrument_filters(symbol)
        return float(filters["leverageFilter"]["maxLeverage"])

    def _place_order_resilient(self, description: str, **params) -> Dict:
        """Безопасно создаёт ордер с защитой от потерянного ACK.

        Bybit подтверждает создание ордера асинхронно. Если HTTP-ответ потерян
        после фактического создания, повторная отправка create с новым
        orderLinkId может создать дубль. Поэтому для запросов с orderLinkId
        сначала проверяем судьбу ИМЕННО этого id; только если биржа подтверждает,
        что такого ордера нет, допускаем повторную попытку с тем же id.
        Если состояние API само неопределённо — безопаснее вернуть
        OrderPlacementUnknown и дождаться следующего цикла, чем рисковать
        дублированием сделки."""
        symbol = params.get("symbol")
        side = params.get("side")
        link_id = params.get("orderLinkId")

        if params.get("positionIdx") == 0 and symbol in self._hedge_mode_symbols:
            params = dict(params, positionIdx=(1 if side == "Buy" else 2))

        last_exc = None
        max_attempts = max(1, int(getattr(cfg, "MAX_RETRIES", 3)))
        for attempt in range(1, max_attempts + 1):
            try:
                return self.session.place_order(**params)
            except Exception as e:
                last_exc = e

                if params.get("positionIdx") == 0 and _is_position_mode_error(e):
                    self._hedge_mode_symbols.add(symbol)
                    hedge_idx = 1 if side == "Buy" else 2
                    params = dict(params, positionIdx=hedge_idx)
                    # С этой же уникальной ссылкой можно безопасно проверить,
                    # не был ли ордер уже принят до ошибки режима.
                if link_id:
                    try:
                        state = self.get_order_state_by_link(symbol, link_id)
                    except Exception as lookup_exc:
                        raise OrderPlacementUnknown(
                            f"{description}: после ошибки создания состояние orderLinkId={link_id} "
                            f"не удалось подтвердить: {lookup_exc}"
                        ) from e
                    if state:
                        status = str(state.get("orderStatus") or "").lower()
                        if status in ("new", "partiallyfilled", "untriggered", "created"):
                            return {"result": {"orderId": state.get("orderId"), "orderLinkId": link_id}}
                        if status == "filled":
                            return {"result": {"orderId": state.get("orderId"), "orderLinkId": link_id}, "_already_filled": True}
                        # Rejected/cancelled/deactivated: допускаем повтор того же
                        # уникального linkId, если биржа действительно говорит,
                        # что прежний запрос не жив.

                if attempt < max_attempts:
                    delay = float(getattr(cfg, "RETRY_BACKOFF_SEC", 1.5)) * (2 ** (attempt - 1))
                    self.log.warning(
                        f"Попытка {attempt}/{max_attempts} не удалась ({description}): {e}. "
                        f"Повтор через {delay:.1f} сек."
                    )
                    time.sleep(delay)

        raise last_exc if last_exc is not None else RuntimeError(f"Не удалось выполнить {description}")

    def _resolve_live_position_idx(self, symbol: str, fallback_side: Optional[str] = None) -> int:
        """Resolve positionIdx only from a confirmed live position.

        Never infer one-way mode (idx=0) from a missing position response:
        a stale/empty response must not cause protective orders to be attached
        to the wrong leg or leave reduce-only TP orders for a future position.
        """
        if fallback_side not in (None, "Buy", "Sell"):
            raise ValueError(f"Invalid fallback_side: {fallback_side!r}")
        try:
            # In hedge mode, querying by symbol alone can return the opposite
            # leg. Always resolve the exact side when the caller knows it.
            pos = (
                self.get_position_strict(symbol, side=fallback_side)
                if fallback_side
                else self.get_position_strict(symbol)
            )
        except Exception as e:
            if symbol in self._hedge_mode_symbols and fallback_side:
                # Cached hedge mode plus a known leg gives an unambiguous idx
                # even when the position endpoint is temporarily unavailable.
                return 1 if fallback_side == "Buy" else 2
            raise RuntimeError(
                f"[{symbol}] Cannot safely resolve positionIdx while position lookup is unavailable"
            ) from e
        if not pos:
            raise RuntimeError(
                f"[{symbol}] Cannot safely resolve positionIdx: no confirmed live position"
            )
        raw_idx = pos.get("positionIdx")
        if raw_idx is None or str(raw_idx).strip() == "":
            raise RuntimeError(
                f"[{symbol}] Live position response has no positionIdx; refusing to guess"
            )
        try:
            idx = int(raw_idx)
        except (TypeError, ValueError, OverflowError) as e:
            raise RuntimeError(
                f"[{symbol}] Live position has invalid positionIdx={raw_idx!r}"
            ) from e
        if idx not in (0, 1, 2):
            raise RuntimeError(f"[{symbol}] Live position has unsupported positionIdx={idx}")
        actual_side = pos.get("side")
        if fallback_side and actual_side and actual_side != fallback_side:
            raise RuntimeError(
                f"[{symbol}] Position side mismatch: expected {fallback_side}, got {actual_side!r}"
            )
        # If side is present, validate the hedge mapping directly. Some
        # compatible/test responses omit side after a side-filtered query;
        # the requested side then remains the source of truth.
        if idx == 1 and (actual_side or fallback_side) == "Sell":
            raise RuntimeError(f"[{symbol}] Hedge positionIdx=1 conflicts with Sell side")
        if idx == 2 and (actual_side or fallback_side) == "Buy":
            raise RuntimeError(f"[{symbol}] Hedge positionIdx=2 conflicts with Buy side")
        return idx

    def _compute_entry_plan(self, symbol: str, equity: float, price: float) -> Optional[Dict]:
        """Общий расчёт объёма/TP/SL для входа — используется и рыночным, и
        post-only лимитным путём входа, чтобы не дублировать логику
        округления и защитных уровней. Направление (шорт/лонг) берётся из
        ENABLE_LONG_MODE — сам сигнал входа (памп -> разворот) не меняется,
        меняется только сторона сделки и то, в какую сторону от цены входа
        считаются TP/SL."""
        filters = self.get_instrument_filters(symbol)
        qty_step = float(filters["lotSizeFilter"]["qtyStep"])
        min_qty = float(filters["lotSizeFilter"]["minOrderQty"])
        tick_size = float(filters["priceFilter"]["tickSize"])

        margin_usdt = equity * (cfg.POSITION_PCT_OF_EQUITY / 100.0)
        notional = margin_usdt * cfg.LEVERAGE
        qty = self.qty_for_notional(notional, price, qty_step)

        if qty < min_qty:
            self.log.warning(f"[{symbol}] Расчётный объём {qty} меньше минимального {min_qty}, пропуск сделки.")
            return None
        # minNotionalValue: биржа всё равно отклонит такой ордер — отказываемся
        # заранее, до отправки и без цепочки повторов/fallback.
        try:
            min_notional = float(filters["lotSizeFilter"].get("minNotionalValue") or 0)
        except (TypeError, ValueError):
            min_notional = 0.0
        if min_notional > 0 and Decimal(str(qty)) * Decimal(str(price)) < Decimal(str(min_notional)):
            self.log.warning(
                f"[{symbol}] Номинал {qty} × {price} меньше minNotional {min_notional:g} USDT, пропуск сделки."
            )
            return None

        long_mode = getattr(cfg, "ENABLE_LONG_MODE", False)

        tp_moves, _tp_closes = get_bot_tp_config()
        tp4_move_pct = float(tp_moves[3])

        if long_mode:
            # Лонг: TP4 ВЫШЕ входа, обычный стоп-лосс НИЖЕ входа.
            # Сразу ставим именно TP4 из общего 4-TP плана, чтобы старая
            # одиночная цель из cfg не могла закрыть позицию раньше новой схемы.
            tp_pct = tp4_move_pct
            tp_price = self.round_step(price * (1 + tp4_move_pct / 100.0), tick_size)
            sl_price = None
            if getattr(cfg, "ENABLE_FIXED_STOP_LOSS", False) and getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) > 0:
                sl_price = self.round_step(price * (1 - cfg.LONG_FIXED_STOP_LOSS_PCT / 100.0), tick_size)
        else:
            # Шорт: TP4 НИЖЕ входа.
            tp_pct = tp4_move_pct
            tp_price = self.round_step(price * (1 - tp4_move_pct / 100.0), tick_size)
            # Обычный стоп-лосс в % от цены входа (как и тейк-профит): для шорта
            # цена стоп-лосса выше входа на FIXED_STOP_LOSS_PCT процентов.
            sl_price = None
            if getattr(cfg, "ENABLE_FIXED_STOP_LOSS", False) and getattr(cfg, "FIXED_STOP_LOSS_PCT", 0) > 0:
                sl_price = self.round_step(price * (1 + cfg.FIXED_STOP_LOSS_PCT / 100.0), tick_size)

        return {"qty": qty, "tp_price": tp_price, "sl_price": sl_price, "tick_size": tick_size, "margin_usdt": margin_usdt}

    def order_info_from_live_position(self, symbol: str, live_pos: Dict, long_mode: bool) -> Dict:
        """Те же поля (_entry_price/_qty/_tp_price/_sl_price/…), что возвращает
        вход бота, но по ФАКТИЧЕСКОЙ позиции на бирже — для позиции, чей вход
        остался «неопределённым» и был найден позже."""
        entry = float(live_pos.get("avgPrice") or 0)
        qty = float(live_pos.get("size") or 0)
        if not math.isfinite(entry) or not math.isfinite(qty) or entry <= 0 or qty <= 0:
            raise ValueError(f"{symbol}: некорректные avgPrice/size позиции ({entry!r}/{qty!r})")
        filters = self.get_instrument_filters(symbol)
        tick_size = float(filters["priceFilter"]["tickSize"])
        tp4_move_pct = float(get_bot_tp_config()[0][3])
        tp_price = self.round_step(entry * (1 + tp4_move_pct / 100.0) if long_mode else entry * (1 - tp4_move_pct / 100.0), tick_size)
        sl_price = None
        sl_pct = getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) if long_mode else getattr(cfg, "FIXED_STOP_LOSS_PCT", 0)
        if getattr(cfg, "ENABLE_FIXED_STOP_LOSS", False) and sl_pct > 0:
            sl_price = self.round_step(entry * (1 - sl_pct / 100.0) if long_mode else entry * (1 + sl_pct / 100.0), tick_size)
        leverage = getattr(cfg, "LEVERAGE", 0) or 0
        margin_usdt = (entry * qty / leverage) if leverage else entry * qty
        return {
            "_entry_price": entry, "_qty": qty, "_margin_usdt": margin_usdt,
            "_tp_price": tp_price, "_sl_price": sl_price, "_tick_size": tick_size,
        }

    def _ensure_initial_4tp_protection(self, symbol: str, order: Dict, attempts: int = 5) -> bool:
        """Сразу после фактического входа ставит и подтверждает ВСЮ защиту.

        TP4 и SL проверяются как position-level protection, TP1-TP3 — как
        отдельные reduce-only LIMIT. Функция идемпотентна: перед созданием
        нового TP ищет уже существующий наш ордер по префиксу и истории,
        поэтому потерянный ACK не приводит к дублю.
        """
        try:
            long_mode = getattr(cfg, "ENABLE_LONG_MODE", False)
            side = "LONG" if long_mode else "SHORT"
            pos_side = "Buy" if long_mode else "Sell"
            entry = float(order.get("_entry_price") or 0)
            qty = float(order.get("_qty") or 0)
            tick = float(order.get("_tick_size") or 0)
            if entry <= 0 or qty <= 0:
                return False

            moves, closes = get_bot_tp_config()
            enabled = get_bot_tp_enabled()
            if _bot_tp_validate_moves(moves, enabled) or _bot_tp_validate_closes(closes, enabled):
                self.log.error(f"[{symbol}] Неверная конфигурация 4 TP — защиту не считаю установленной.")
                return False

            targets = [self.round_step(entry * (1 + m / 100.0) if long_mode else entry * (1 - m / 100.0), tick) for m in moves]
            qty_step = float(self.get_qty_step(symbol))
            ready = False
            protection_started_ms = int(time.time() * 1000)
            own_tp_ids = {}

            for attempt in range(max(1, int(attempts))):
                try:
                    live = self.get_position_strict(symbol, side=pos_side)
                except Exception as e:
                    self.log.warning(f"[{symbol}] Защита после входа: не удалось прочитать позицию ({attempt+1}/{attempts}): {e}")
                    live = None
                if not live or float(live.get("size") or 0) <= 0:
                    time.sleep(0.2)
                    continue

                entry = float(live.get("avgPrice") or entry)
                qty = float(live.get("size") or qty)
                targets = [self.round_step(entry * (1 + m / 100.0) if long_mode else entry * (1 - m / 100.0), tick) for m in moves]

                # Сначала position-level SL/TP4. Это главный аварийный
                # барьер, поэтому каждый из них не просто отправляется, а
                # подтверждается чтением реальной позиции.
                sl_expected = order.get("_sl_price")
                sl_pct = getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) if long_mode else getattr(cfg, "FIXED_STOP_LOSS_PCT", 0)
                if sl_expected is not None and sl_pct > 0:
                    sl_expected = self.round_step(entry * (1 - sl_pct / 100.0) if long_mode else entry * (1 + sl_pct / 100.0), tick)
                    sl_ok = self.update_stop_loss_verified(symbol, sl_expected, side, attempts=2)
                else:
                    sl_ok = True

                # TP4 уже мог быть вручную передвинут после фактического входа,
                # но до завершения первичной установки TP1-TP3. Не возвращаем
                # его к расчётной цене. Цена в order['_tp_price'] — последний
                # уровень, который выставлял сам входной код; если биржа всё ещё
                # показывает именно его, разрешаем уточнить уровень по свежему avg.
                try:
                    current_tp4 = float(live.get("takeProfit") or 0)
                except (TypeError, ValueError, OverflowError):
                    current_tp4 = 0.0
                tp4_tol = max(tick * 0.5, abs(targets[3]) * 1e-8, 1e-12)
                try:
                    last_bot_tp4 = float(order.get("_tp_price") or 0)
                except (TypeError, ValueError, OverflowError):
                    last_bot_tp4 = 0.0
                if math.isfinite(current_tp4) and current_tp4 > 0 and abs(current_tp4 - targets[3]) > tp4_tol:
                    last_bot_tol = max(tick * 0.5, abs(last_bot_tp4) * 1e-8, 1e-12)
                    if last_bot_tp4 > 0 and abs(current_tp4 - last_bot_tp4) <= last_bot_tol:
                        tp4_ok = self.update_take_profit_verified(symbol, targets[3], side, attempts=2)
                    else:
                        targets[3] = self.round_step(current_tp4, tick)
                        tp4_ok = True
                        self.log.info(
                            f"[{symbol}] Первичная защита: обнаружен ручной перенос TP4 на {targets[3]}; "
                            "сохраняю биржевую цену."
                        )
                elif math.isfinite(current_tp4) and current_tp4 > 0:
                    tp4_ok = True
                else:
                    tp4_ok = self.update_take_profit_verified(symbol, targets[3], side, attempts=2)

                # Затем TP1-TP3. Перед каждым create сначала восстанавливаем
                # уже существующий наш ордер, чтобы после timeout/потери ACK
                # никогда не создать второй reduce-only TP.
                active = None
                try:
                    active = self.get_open_orders_all()
                except Exception as e:
                    self.log.warning(f"[{symbol}] Не удалось прочитать активные TP при первичной защите: {e}")

                all_partial_ok = True
                initial_qty = qty
                for i in range(1, 4):
                    if not enabled[i-1]:
                        continue
                    desired = self.round_step(initial_qty * closes[i-1] / 100.0, qty_step)
                    if desired <= 0:
                        all_partial_ok = False
                        continue
                    prefix = f"btp{i}-"
                    existing = None
                    if active is not None:
                        candidates = [o for o in active
                                      if str(o.get("orderLinkId") or "").startswith(prefix)
                                      and _tp_order_matches_position(o, symbol, side, live.get("positionIdx"))
                                      and (str(o.get("orderId") or "") in set(own_tp_ids.values())
                                           or int(o.get("createdTime") or o.get("updatedTime") or 0) >= protection_started_ms - 10000)]
                        if len(candidates) > 1:
                            # A timed-out create or an earlier restart may have
                            # left multiple active orders for this stage. Never
                            # add a third order; let the normal reconciliation
                            # resolve the duplicates with full state checks.
                            all_partial_ok = False
                            self.log.error(f"[{symbol}] Первичная защита: найдено несколько активных btp{i}- для одной позиции; новый TP не создаю до сверки.")
                            continue
                        if candidates:
                            existing = candidates[0]
                    if existing is None:
                        try:
                            hist = self.get_symbol_order_history(symbol, days=1)
                            candidates = [o for o in hist
                                          if str(o.get("orderLinkId") or "").startswith(prefix)
                                          and _tp_order_matches_position(o, symbol, side, live.get("positionIdx"))
                                          and int(o.get("createdTime") or o.get("updatedTime") or 0) >= protection_started_ms - 10000]
                            candidates.sort(key=lambda x: int(x.get("updatedTime") or x.get("createdTime") or 0), reverse=True)
                            if candidates:
                                existing = candidates[0]
                        except Exception:
                            pass
                    if existing is not None:
                        st = str(existing.get("orderStatus") or "").lower()
                        if st in ("new", "partiallyfilled", "untriggered", "created", "filled"):
                            continue

                    oid = self.place_bot_tp_limit(symbol, side, targets[i-1], desired, i)
                    if oid:
                        own_tp_ids[str(i)] = str(oid)
                    else:
                        all_partial_ok = False

                if sl_ok and tp4_ok and all_partial_ok:
                    # Финальная сверка: убеждаемся, что position-level TP4 и
                    # SL действительно видны на бирже после всех запросов.
                    try:
                        check = self.get_position_strict(symbol, side=pos_side)
                        sl_check = float(check.get("stopLoss") or 0) if check else 0
                        tp_check = float(check.get("takeProfit") or 0) if check else 0
                        sl_final = (sl_expected is None) or (sl_check > 0 and abs(sl_check - float(sl_expected)) <= max(tick * 0.5, abs(float(sl_expected))*1e-8, 1e-12))
                        tp_final = tp_check > 0 and abs(tp_check-targets[3]) <= max(tick * 0.5, abs(targets[3])*1e-8, 1e-12)
                        if sl_final and tp_final:
                            ready = True
                            order["_sl_price"] = sl_expected
                            order["_tp_price"] = targets[3]
                            order["_protection_ready"] = True
                            return True
                    except Exception as e:
                        self.log.warning(f"[{symbol}] Финальная проверка защиты не прошла: {e}")
                time.sleep(0.25 * (attempt + 1))

            order["_protection_ready"] = False
            self.log.error(f"[{symbol}] После открытия не удалось подтвердить всю 4-TP/SL защиту. Позиция остаётся под отдельной reconciliation-проверкой.")
            return ready
        except Exception as e:
            order["_protection_ready"] = False
            self.log.exception(f"[{symbol}] Критическая ошибка первичной установки 4-TP/SL: {e}")
            return False

    def open_short(self, symbol: str, equity: float, entry_price_hint: Optional[float] = None) -> Optional[Dict]:
        price = entry_price_hint or self.get_last_price_rest(symbol)
        if price is None:
            self.log.warning(f"[{symbol}] Не удалось получить цену, пропуск.")
            return None

        plan = self._compute_entry_plan(symbol, equity, price)
        if plan is None:
            return None

        self.ensure_leverage(symbol)

        if getattr(cfg, "ENABLE_POST_ONLY_ENTRY", False):
            order = self._open_short_post_only(symbol, price, plan)
            if order is not None:
                if order.get("_post_only_unresolved"):
                    self.log.error(f"[{symbol}] Состояние post-only входа не подтверждено — рыночный fallback запрещён, чтобы не открыть дубль.")
                    # Не None: вызывающий код обязан взять вход под наблюдение
                    # (ордер может остаться активным или исполниться позже).
                    return order
                self._ensure_initial_4tp_protection(symbol, order)
                return order
            self.log.info(f"[{symbol}] Post-only лимитный вход не исполнился вовремя — перехожу на рыночный ордер.")

        order = self._open_short_market(symbol, price, plan)
        if order is not None and not order.get("_entry_unresolved"):
            self._ensure_initial_4tp_protection(symbol, order)
        return order

    def _open_short_market(self, symbol: str, price: float, plan: Dict) -> Optional[Dict]:
        qty, tp_price, sl_price, tick_size, margin_usdt = plan["qty"], plan["tp_price"], plan["sl_price"], plan["tick_size"], plan["margin_usdt"]

        long_mode = getattr(cfg, "ENABLE_LONG_MODE", False)
        entry_side = "Buy" if long_mode else "Sell"
        side_label = "ЛОНГ" if long_mode else "ШОРТ"
        tp_pct = getattr(cfg, "LONG_TAKE_PROFIT_PCT", cfg.TAKE_PROFIT_PCT) if long_mode else cfg.TAKE_PROFIT_PCT
        sl_pct = getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) if long_mode else getattr(cfg, "FIXED_STOP_LOSS_PCT", 0)
        tp_sign = "+" if long_mode else "-"
        sl_sign = "-" if long_mode else "+"

        order = None
        entry_link_id = self._new_order_link_id("op1-")
        try:
            params = dict(
                category=cfg.CATEGORY, symbol=symbol, side=entry_side,
                orderType="Market", qty=_plain_num_str(qty), reduceOnly=False, positionIdx=0,
                takeProfit=_plain_num_str(tp_price), tpTriggerBy="LastPrice", tpslMode="Full", orderLinkId=entry_link_id,
            )
            if sl_price is not None:
                params["stopLoss"] = _plain_num_str(sl_price)
                params["slTriggerBy"] = "LastPrice"
            order = self._place_order_resilient(f"place_order({symbol})", **params)
            sl_log = f", SL={sl_price} ({sl_sign}{sl_pct}% от входа)" if sl_price is not None else ""
            self.log.info(f"[{symbol}] {side_label} открыт (market): qty={qty}, цена входа~{price}, margin={margin_usdt:.2f} USDT, TP={tp_price} ({tp_sign}{tp_pct}%){sl_log}")
        except OrderPlacementUnknown as e:
            self.log.error(f"[{symbol}] Создание {side_label.lower()}а осталось в неизвестном состоянии — второй market-ордер НЕ отправляю: {e}")
            return {"_entry_unresolved": True, "_link_id": entry_link_id, "_order_id": None, "_side": entry_side}
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось открыть {side_label.lower()} с TP/SL одним запросом ({e}), проверяю, не открылась ли позиция перед fallback...")
            try:
                # Do not send a second market entry unless the exchange has
                # positively confirmed that the first request did not open a
                # position. get_position() converts API errors to None, which
                # is indistinguishable from "no position" and can double-entry.
                existing_pos = self.get_position_strict(symbol, side=entry_side)
            except Exception as check_error:
                self.log.error(
                    f"[{symbol}] Нельзя безопасно проверить результат первого market-ордера "
                    f"({check_error}); повторный вход отменён во избежание дубля."
                )
                return {"_entry_unresolved": True, "_link_id": entry_link_id, "_order_id": None, "_side": entry_side}
            if existing_pos and float(existing_pos.get("size") or 0) > 0:
                order = {"result": {"orderId": None}}
            else:
                fallback_link_id = self._new_order_link_id("op2-")
                try:
                    order = self._place_order_resilient(f"place_order({symbol})", category=cfg.CATEGORY, symbol=symbol, side=entry_side, orderType="Market", qty=_plain_num_str(qty), reduceOnly=False, positionIdx=0, orderLinkId=fallback_link_id)
                except OrderPlacementUnknown as e2:
                    self.log.error(f"[{symbol}] Второй market-ордер запрещён из-за неизвестного состояния первого: {e2}")
                    return {"_entry_unresolved": True, "_link_id": fallback_link_id, "_order_id": None, "_side": entry_side}
                except Exception as e2:
                    self.log.error(f"[{symbol}] Ошибка открытия {side_label.lower()}а после всех попыток: {e2}")
                    return None

            self.log.info(f"[{symbol}] {side_label} открыт (market): qty={qty}, цена входа~{price}, margin={margin_usdt:.2f} USDT")

        # После фактического исполнения всегда уточняем avgPrice/qty. Для TP
        # важнее реальный fill, а не цена до отправки market-ордера. Затем
        # повторно задаём и проверяем защитные уровни — embedded TP/SL в create
        # считается только предварительной попыткой.
        actual_entry = price
        actual_qty = qty
        for _ in range(5):
            try:
                live = self.get_position_strict(symbol, side=entry_side)
            except Exception:
                live = None
            if live and float(live.get("avgPrice") or 0) > 0 and float(live.get("size") or 0) > 0:
                actual_entry = float(live["avgPrice"])
                actual_qty = float(live.get("size") or qty)
                break
            time.sleep(0.15)

        if actual_entry > 0:
            tp4_move_pct = float(get_bot_tp_config()[0][3])
            tp_actual = self.round_step(actual_entry * (1 + tp4_move_pct / 100.0) if long_mode else actual_entry * (1 - tp4_move_pct / 100.0), tick_size)
            tp_pct = tp4_move_pct
            sl_actual = None
            if sl_price is not None:
                sl_actual = self.round_step(actual_entry * (1 - sl_pct / 100.0) if long_mode else actual_entry * (1 + sl_pct / 100.0), tick_size)
            try:
                if not self.update_take_profit_verified(symbol, tp_actual, "LONG" if long_mode else "SHORT"):
                    self.log.error(f"[{symbol}] TP после market-исполнения не подтверждён на бирже: {tp_actual}. Фоновая reconciliation повторит попытку.")
                else:
                    tp_price = tp_actual
            except Exception as e:
                self.log.error(f"[{symbol}] Ошибка проверки TP после market-исполнения: {e}")
            if sl_actual is not None:
                try:
                    if not self.update_stop_loss_verified(symbol, sl_actual, "LONG" if long_mode else "SHORT"):
                        self.log.error(f"[{symbol}] SL после market-исполнения не подтверждён на бирже: {sl_actual}. Фоновая reconciliation повторит попытку.")
                    else:
                        sl_price = sl_actual
                except Exception as e:
                    self.log.error(f"[{symbol}] Ошибка проверки SL после market-исполнения: {e}")
        qty = actual_qty
        price = actual_entry

        order["_entry_price"] = price
        order["_qty"] = qty
        order["_margin_usdt"] = margin_usdt
        order["_tp_price"] = tp_price
        order["_sl_price"] = sl_price
        order["_tick_size"] = tick_size
        return order

    def _open_short_post_only(self, symbol: str, price: float, plan: Dict) -> Optional[Dict]:
        """Пытается войти лимитным post-only ордером (гарантированно как
        мейкер — обычно ниже комиссия и часто более выгодная цена входа,
        ровно на пике, а не после проскальзывания рыночного ордера).
        Если ордер не исполнился за POST_ONLY_TIMEOUT_SEC — отменяет его и
        возвращает None, тогда open_short() переходит на рыночный вход, чтобы
        не упустить сигнал совсем."""
        qty, tp_price, sl_price, tick_size, margin_usdt = plan["qty"], plan["tp_price"], plan["sl_price"], plan["tick_size"], plan["margin_usdt"]

        long_mode = getattr(cfg, "ENABLE_LONG_MODE", False)
        entry_side = "Buy" if long_mode else "Sell"
        side_label = "ЛОНГ" if long_mode else "ШОРТ"
        tp_pct = getattr(cfg, "LONG_TAKE_PROFIT_PCT", cfg.TAKE_PROFIT_PCT) if long_mode else cfg.TAKE_PROFIT_PCT
        sl_pct = getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) if long_mode else getattr(cfg, "FIXED_STOP_LOSS_PCT", 0)
        tp_sign = "+" if long_mode else "-"
        offset_pct = getattr(cfg, "POST_ONLY_OFFSET_PCT", 0.02)
        # Шорт: лимит чуть ВЫШЕ рынка (ловим мейкером верхушку пампа перед падением).
        # Лонг: лимит чуть НИЖЕ рынка (ловим мейкером небольшой откат перед входом),
        # иначе лимит на покупку выше рынка сразу пересёк бы спред и не был бы post-only.
        # Округляем ОТ рынка, чтобы отступ post-only не съедался шагом цены:
        # лонг (лимит ниже рынка) — вниз, шорт (лимит выше рынка) — вверх.
        # Прежнее округление вниз для шорта сдвигало цену к рынку и на монетах
        # с крупным тиком могло пересечь стакан (PostOnly тогда отклоняется).
        limit_price = (
            self.round_step(price * (1 - offset_pct / 100.0), tick_size) if long_mode
            else _round_stop_price_for_side(price * (1 + offset_pct / 100.0), tick_size, "SHORT")  # SHORT => округление вверх
        )
        timeout_sec = max(0.5, getattr(cfg, "POST_ONLY_TIMEOUT_SEC", 3.0))

        link_id = self._new_order_link_id("po1-")
        order_id = None

        def _unresolved() -> Dict:
            # Неопределённый вход нельзя просто «забыть»: ордер мог остаться
            # активным или исполниться позже. Возвращаем всё, что нужно, чтобы
            # бот нашёл ордер/позицию и взял их под управление.
            return {"_post_only_unresolved": True, "_link_id": link_id, "_order_id": order_id, "_side": entry_side}

        params = dict(
            category=cfg.CATEGORY, symbol=symbol, side=entry_side,
            orderType="Limit", price=_plain_num_str(limit_price), qty=_plain_num_str(qty),
            timeInForce="PostOnly", reduceOnly=False, positionIdx=0,
            takeProfit=_plain_num_str(tp_price), tpTriggerBy="LastPrice", tpslMode="Full", orderLinkId=link_id,
        )
        if sl_price is not None:
            params["stopLoss"] = _plain_num_str(sl_price)
            params["slTriggerBy"] = "LastPrice"

        try:
            # Один первичный запрос без искусственного ret​​ry: для PostOnly
            # отклонение из-за пересечения спреда действительно не имеет смысла
            # повторять. Но если HTTP-ответ потерялся, сначала восстанавливаем
            # состояние по тому же уникальному orderLinkId — иначе market fallback
            # мог бы задвоить уже принятый лимитный вход.
            resp = self.session.place_order(**params)
        except Exception as e:
            if params.get("positionIdx") == 0 and _is_position_mode_error(e):
                self._hedge_mode_symbols.add(symbol)
                hedge_idx = 1 if entry_side == "Buy" else 2
                params = dict(params, positionIdx=hedge_idx)
                try:
                    resp = self.session.place_order(**params)
                except Exception as e2:
                    try:
                        state = self.get_order_state_by_link(symbol, link_id)
                    except Exception:
                        state = None
                    if state and state.get("orderId"):
                        resp = {"result": {"orderId": state.get("orderId")}}
                    else:
                        # The retry raised and orderLinkId lookup did not
                        # conclusively recover the request. It may have been
                        # accepted despite the lost response; do not market-enter.
                        self.log.error(
                            f"[{symbol}] Не удалось подтвердить результат PostOnly после ошибки ({e2}); "
                            "вход оставлен неопределённым, market fallback запрещён."
                        )
                        return _unresolved()
            else:
                try:
                    state = self.get_order_state_by_link(symbol, link_id)
                except Exception:
                    state = None
                if state and state.get("orderId"):
                    resp = {"result": {"orderId": state.get("orderId")}}
                else:
                    # A failed lookup is not proof that the exchange rejected
                    # the order; order acceptance may be delayed or the reply lost.
                    self.log.error(
                        f"[{symbol}] Не удалось подтвердить результат PostOnly после ошибки ({e}); "
                        "вход оставлен неопределённым, market fallback запрещён."
                    )
                    return _unresolved()

        order_id = resp.get("result", {}).get("orderId")
        if not order_id:
            # Нет orderId после успешного ACK — пробуем восстановить именно
            # этот orderLinkId и не создаём другой вход.
            try:
                state = self.get_order_state_by_link(symbol, link_id)
            except Exception as e:
                self.log.error(f"[{symbol}] Не удалось восстановить orderId PostOnly после ACK: {e}")
                return _unresolved()
            if state and state.get("orderId"):
                order_id = state.get("orderId")
            else:
                return _unresolved()

        self.log.info(f"[{symbol}] Post-only лимитный ордер на {limit_price} выставлен, жду исполнения до {timeout_sec:.1f} сек...")

        deadline = time.time() + timeout_sec
        filled = False
        while time.time() < deadline:
            time.sleep(0.15)  # частый опрос — вход должен быть максимально быстрым
            try:
                state = self.get_order_state(symbol, order_id)
            except Exception:
                continue
            if not state:
                continue  # неизвестное состояние — НЕ считаем исполненным
            status = str(state.get("orderStatus") or "").lower()
            if status == "filled":
                filled = True
                break
            if status in ("new", "partiallyfilled", "untriggered"):
                continue
            if status in ("cancelled", "rejected", "deactivated"):
                try:
                    live_pos = self.get_position_strict(symbol, side=entry_side)
                except Exception as e:
                    self.log.warning(
                        f"[{symbol}] Состояние позиции после терминального статуса PostOnly неизвестно: {e}; "
                        "вход оставляю неразрешённым, market fallback запрещён."
                    )
                    return _unresolved()
                cum_exec_qty = float(state.get("cumExecQty") or 0)
                if live_pos and float(live_pos.get("size") or 0) > 0:
                    filled = True
                elif cum_exec_qty > 0:
                    # The entry partially filled before cancellation. Position
                    # data may lag, so do not treat this as a clean no-fill.
                    self.log.warning(
                        f"[{symbol}] PostOnly терминальный статус {status}, но cumExecQty={cum_exec_qty}; "
                        "рыночный fallback запрещён до восстановления позиции."
                    )
                    return _unresolved()
                else:
                    return None
                break

        if not filled:
            try:
                call_with_retry(self.log, self.session.cancel_order, category=cfg.CATEGORY, symbol=symbol, orderId=order_id, description=f"cancel_order({symbol})")
            except Exception as e:
                self.log.debug(f"[{symbol}] Отмена post-only ордера не удалась: {e}")

            # После cancel нельзя переходить на market, пока не доказано, что
            # post-only либо исполнен, либо действительно больше не активен.
            try:
                state = self.get_order_state(symbol, order_id)
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось подтвердить состояние post-only после timeout: {e}")
                return _unresolved()

            status = str((state or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
            if status == "filled":
                filled = True
            elif status in ("new", "partiallyfilled", "untriggered"):
                self.log.warning(f"[{symbol}] Post-only order {order_id} всё ещё активен после timeout — market fallback НЕ выполняю, чтобы не задвоить позицию.")
                return _unresolved()
            elif status in ("cancelled", "rejected", "deactivated"):
                try:
                    live_pos = self.get_position_strict(symbol, side=entry_side)
                except Exception as e:
                    self.log.warning(
                        f"[{symbol}] Не удалось проверить позицию после подтверждённого терминального статуса PostOnly: {e}; "
                        "market fallback запрещён."
                    )
                    return _unresolved()
                cum_exec_qty = float((state or {}).get("cumExecQty") or 0)
                if live_pos and float(live_pos.get("size") or 0) > 0:
                    filled = True
                elif cum_exec_qty > 0:
                    self.log.warning(
                        f"[{symbol}] PostOnly отменён/отклонён после частичного исполнения "
                        f"(cumExecQty={cum_exec_qty}), но позиция ещё не видна; market fallback запрещён."
                    )
                    return _unresolved()
                else:
                    self.log.info(f"[{symbol}] Post-only ордер не исполнился за {timeout_sec:.1f} сек и подтверждённо закрыт.")
                    return None
            else:
                # Empty/unknown status is not evidence of cancellation. The
                # exchange may still have an active order or a delayed update.
                self.log.warning(
                    f"[{symbol}] Статус PostOnly после timeout неизвестен ({status or 'empty'}); "
                    "market fallback запрещён до следующей сверки."
                )
                return _unresolved()

        entry_price = limit_price
        actual_qty = qty
        live_pos = None
        for _attempt in range(5):
            try:
                live_pos = self.get_position_strict(symbol, side=entry_side)
            except Exception as e:
                live_pos = None
                self.log.debug(f"[{symbol}] PostOnly: не удалось прочитать позицию после fill (попытка {_attempt + 1}/5): {e}")
            if live_pos and float(live_pos.get("avgPrice") or 0) > 0 and float(live_pos.get("size") or 0) > 0:
                entry_price = float(live_pos["avgPrice"])
                actual_qty = float(live_pos.get("size") or qty)
                break
            time.sleep(0.15)

        # Критично: embedded TP/SL у PostOnly рассчитывался по цене ДО
        # исполнения. После реального fill сразу заменяем его на уровни от
        # фактического avgPrice, чтобы до первого фонового цикла не существовал
        # старый одиночный TP/SL. Если подтверждение не прошло, сделку не
        # объявляем полностью защищённой — следующий цикл продолжит retry.
        if entry_price > 0 and live_pos and float(live_pos.get("size") or 0) > 0:
            try:
                tp4_move = float(get_bot_tp_config()[0][3])
                tp_actual = self.round_step(entry_price * (1 + tp4_move / 100.0) if long_mode else entry_price * (1 - tp4_move / 100.0), tick_size)
                if not self.update_take_profit_verified(symbol, tp_actual, "LONG" if long_mode else "SHORT"):
                    self.log.error(f"[{symbol}] PostOnly: TP4 после фактического fill не подтверждён на {tp_actual}; reconciliation продолжит попытки.")
                else:
                    tp_price = tp_actual
                if sl_price is not None:
                    sl_actual = self.round_step(entry_price * (1 - sl_pct / 100.0) if long_mode else entry_price * (1 + sl_pct / 100.0), tick_size)
                    if not self.update_stop_loss_verified(symbol, sl_actual, "LONG" if long_mode else "SHORT"):
                        self.log.error(f"[{symbol}] PostOnly: SL после фактического fill не подтверждён на {sl_actual}; reconciliation продолжит попытки.")
                    else:
                        sl_price = sl_actual
            except Exception as e:
                self.log.error(f"[{symbol}] Ошибка установки фактических TP4/SL после PostOnly fill: {e}")

        self.log.info(f"[{symbol}] {side_label} открыт (post-only maker): qty={actual_qty}, цена входа~{entry_price}, margin={margin_usdt:.2f} USDT, TP={tp_price} ({'+' if long_mode else '-'}{tp_pct}%){f', SL={sl_price}' if sl_price is not None else ''}")
        return {
            "_entry_price": entry_price, "_qty": actual_qty, "_margin_usdt": margin_usdt,
            "_tp_price": tp_price, "_sl_price": sl_price, "_tick_size": tick_size,
        }

    def update_stop_loss(self, symbol: str, sl_price: float, side: Optional[str] = None) -> bool:
        try:
            fallback_side = "Buy" if side == "LONG" else "Sell" if side == "SHORT" else None
            idx = self._resolve_live_position_idx(symbol, fallback_side=fallback_side)
            call_with_retry(self.log, self.session.set_trading_stop, category=cfg.CATEGORY, symbol=symbol, stopLoss=_plain_num_str(sl_price), slTriggerBy="LastPrice", positionIdx=idx, description=f"set_trading_stop/SL({symbol})")
            return True
        except Exception as e:
            self.log.error(f"[{symbol}] Не удалось обновить стоп-лосс: {e}")
            return False

    def update_stop_loss_verified(self, symbol: str, sl_price: float, side: str, attempts: int = 3) -> bool:
        """Устанавливает SL и подтверждает его фактическое наличие на бирже.

        Для ручных сделок защитный стоп нельзя считать установленным только
        по ACK set_trading_stop: Bybit указывает, что торговые изменения
        обрабатываются асинхронно. Поэтому после записи ждём и перечитываем
        реальную позицию. side здесь — LONG/SHORT, чтобы в hedge-режиме
        однозначно выбрать positionIdx.
        """
        if side not in {"LONG", "SHORT"}:
            self.log.error(f"[{symbol}] Отказ от установки SL: неизвестная сторона {side!r}")
            return False
        expected_side = "Buy" if side == "LONG" else "Sell"
        try:
            tick_size = float(self.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
        except Exception:
            tick_size = 0.0
        if not math.isfinite(tick_size) or tick_size <= 0:
            self.log.error(f"[{symbol}] Отказ от установки SL: некорректный tickSize {tick_size!r}")
            return False
        try:
            sl_price = float(sl_price)
        except (TypeError, ValueError, OverflowError):
            return False
        if not math.isfinite(sl_price) or sl_price <= 0:
            self.log.error(f"[{symbol}] Отказ от установки SL: некорректная цена {sl_price!r}")
            return False
        try:
            expected = _round_stop_price_for_side(sl_price, tick_size, side)
        except (TypeError, ValueError, OverflowError) as rounding_error:
            self.log.error(f"[{symbol}] Отказ от установки SL: ошибка округления для {side}: {rounding_error}")
            return False
        if not math.isfinite(expected) or expected <= 0:
            return False

        for attempt in range(max(1, int(attempts))):
            try:
                pos = self.get_position_strict(symbol, side=expected_side)
                if not pos:
                    return False
                raw_idx = pos.get("positionIdx")
                if raw_idx is None or str(raw_idx).strip() == "":
                    self.log.error(f"[{symbol}] Отказ от установки SL: Bybit не вернул positionIdx для стороны {expected_side}")
                    return False
                idx = int(raw_idx)
                if idx not in (0, 1, 2) or (idx == 1 and expected_side != "Buy") or (idx == 2 and expected_side != "Sell"):
                    self.log.error(f"[{symbol}] Отказ от установки SL: конфликт side={expected_side}, positionIdx={idx}")
                    return False
                call_with_retry(
                    self.log, self.session.set_trading_stop,
                    category=cfg.CATEGORY, symbol=symbol,
                    stopLoss=_plain_num_str(expected), slTriggerBy="LastPrice",
                    positionIdx=idx,
                    description=f"set_trading_stop/verified-SL({symbol})",
                )
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось выставить/обновить проверяемый SL на {expected}: {e}")
                if attempt + 1 < max(1, int(attempts)):
                    time.sleep(0.2 * (attempt + 1))
                continue

            # ACK асинхронный — даём бирже немного времени и проверяем именно
            # фактическое поле stopLoss открытой позиции.
            for verify_attempt in range(3):
                try:
                    time.sleep(0.15)
                    check = self.get_position_strict(symbol, side=expected_side)
                    if not check:
                        return False
                    actual = float(check.get("stopLoss") or 0)
                    if actual > 0:
                        tolerance = max(tick_size * 0.5, abs(expected) * 1e-8, 1e-12)
                        if abs(actual - expected) <= tolerance:
                            return True
                except Exception as e:
                    self.log.debug(f"[{symbol}] Проверка установленного SL ещё не готова: {e}")
        return False

    def update_take_profit_verified(self, symbol: str, tp_price: float, side: str, attempts: int = 3) -> bool:
        """Устанавливает TP и подтверждает фактическое поле takeProfit позиции."""
        if side not in {"LONG", "SHORT"}:
            self.log.error(f"[{symbol}] Отказ от установки TP: неизвестная сторона {side!r}")
            return False
        expected_side = "Buy" if side == "LONG" else "Sell"
        try:
            tick_size = float(self.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
        except Exception:
            tick_size = 0.0
        if not math.isfinite(tick_size) or tick_size <= 0:
            self.log.error(f"[{symbol}] Отказ от установки TP: некорректный tickSize {tick_size!r}")
            return False
        try:
            tp_price = float(tp_price)
        except (TypeError, ValueError, OverflowError):
            return False
        if not math.isfinite(tp_price) or tp_price <= 0:
            self.log.error(f"[{symbol}] Отказ от установки TP: некорректная цена {tp_price!r}")
            return False
        expected = self.round_step(tp_price, tick_size)
        if not math.isfinite(expected) or expected <= 0:
            return False

        for attempt in range(max(1, int(attempts))):
            try:
                pos = self.get_position_strict(symbol, side=expected_side)
                if not pos:
                    return False
                raw_idx = pos.get("positionIdx")
                if raw_idx is None or str(raw_idx).strip() == "":
                    self.log.error(f"[{symbol}] Отказ от установки TP: Bybit не вернул positionIdx для стороны {expected_side}")
                    return False
                idx = int(raw_idx)
                if idx not in (0, 1, 2) or (idx == 1 and expected_side != "Buy") or (idx == 2 and expected_side != "Sell"):
                    self.log.error(f"[{symbol}] Отказ от установки TP: конфликт side={expected_side}, positionIdx={idx}")
                    return False
                call_with_retry(
                    self.log, self.session.set_trading_stop,
                    category=cfg.CATEGORY, symbol=symbol,
                    takeProfit=_plain_num_str(expected), tpTriggerBy="LastPrice",
                    positionIdx=idx,
                    description=f"set_trading_stop/verified-TP({symbol})",
                )
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось выставить/обновить проверяемый TP на {expected}: {e}")
                if attempt + 1 < max(1, int(attempts)):
                    time.sleep(0.2 * (attempt + 1))
                continue

            for _ in range(3):
                try:
                    time.sleep(0.15)
                    check = self.get_position_strict(symbol, side=expected_side)
                    if not check:
                        return False
                    actual = float(check.get("takeProfit") or 0)
                    if actual > 0:
                        tolerance = max(tick_size * 0.5, abs(expected) * 1e-8, 1e-12)
                        if abs(actual - expected) <= tolerance:
                            return True
                except Exception as e:
                    self.log.debug(f"[{symbol}] Проверка установленного TP ещё не готова: {e}")
        return False

    def update_take_profit(self, symbol: str, tp_price: float, side: Optional[str] = None) -> bool:
        try:
            fallback_side = "Buy" if side == "LONG" else "Sell" if side == "SHORT" else None
            idx = self._resolve_live_position_idx(symbol, fallback_side=fallback_side)
            call_with_retry(self.log, self.session.set_trading_stop, category=cfg.CATEGORY, symbol=symbol, takeProfit=_plain_num_str(tp_price), tpTriggerBy="LastPrice", positionIdx=idx, description=f"set_trading_stop/TP({symbol})")
            return True
        except Exception as e:
            self.log.error(f"[{symbol}] Не удалось (пере)выставить take-profit: {e}")
            return False

    def close_position_market(self, symbol: str, qty: float, side: Optional[str] = None) -> bool:
        # Сторона закрытия — обратная стороне открытой позиции. Определяем по
        # реальной позиции на бирже (а не по текущему значению ENABLE_LONG_MODE),
        # чтобы закрытие оставалось верным, даже если режим переключили уже
        # после того, как сделка была открыта. Если позицию узнать не удалось
        # (например, её уже закрыл TP прямо перед вызовом) — резервный вариант
        # берём из текущего режима, а не всегда "Buy" (иначе в режиме лонга
        # ошибочно пытались бы закрыть шортовой стороной).
        fallback_side = "Buy" if side == "LONG" else "Sell" if side == "SHORT" else None
        close_side = (
            "Sell" if fallback_side == "Buy" else "Buy"
            if fallback_side == "Sell"
            else ("Sell" if getattr(cfg, "ENABLE_LONG_MODE", False) else "Buy")
        )
        idx = (
            (1 if fallback_side == "Buy" else 2)
            if symbol in self._hedge_mode_symbols and fallback_side
            else 0
        )
        try:
            live_pos = self.get_position_strict(symbol, side=fallback_side) if fallback_side else self.get_position_strict(symbol)
            if live_pos:
                close_side = "Sell" if live_pos.get("side") == "Buy" else "Buy"
                idx = int(live_pos.get("positionIdx", idx))
            elif symbol in self._hedge_mode_symbols and not fallback_side:
                self.log.error(f"[{symbol}] Нельзя безопасно закрыть позицию в hedge-режиме без известной стороны.")
                return False
        except Exception as e:
            # Without a successful lookup, absence from the hedge cache does
            # not prove one-way mode. Do not submit a close with guessed idx=0.
            if symbol in self._hedge_mode_symbols and fallback_side:
                idx = 1 if fallback_side == "Buy" else 2
            else:
                self.log.error(f"[{symbol}] Не удалось безопасно определить позицию перед закрытием: {e}")
                return False
            self.log.warning(f"[{symbol}] Использую подтверждённый hedge positionIdx={idx} по известной стороне после ошибки чтения позиции.")
        try:
            link_id = self._new_order_link_id("cl-")
            self._place_order_resilient(
                f"close_position({symbol})",
                category=cfg.CATEGORY, symbol=symbol, side=close_side,
                orderType="Market", qty=_plain_num_str(qty), reduceOnly=True,
                positionIdx=idx, orderLinkId=link_id,
            )
            return True
        except OrderPlacementUnknown as e:
            # Для reduce-only закрытия неизвестное состояние безопаснее считать
            # НЕуспешным и ждать следующего цикла, чем повторно отправлять новый
            # market close и потенциально закрыть лишний объём.
            self.log.warning(f"[{symbol}] Состояние market-close неизвестно, повторный ордер не отправляю: {e}")
            return False
        except Exception as e:
            self.log.error(f"[{symbol}] Не удалось закрыть позицию рыночным ордером: {e}")
            return False

    def place_bot_tp_limit(self, symbol: str, side: str, price: float, qty: float, tp_no: int) -> Optional[str]:
        """Ставит независимый reduce-only TP1/TP2/TP3 с уникальным
        orderLinkId. При потерянном HTTP-ответе пытается восстановить
        именно этот ордер по linkId и не создаёт второй ордер вслепую."""
        close_side = "Sell" if side == "LONG" else "Buy"
        idx = self._resolve_live_position_idx(symbol, fallback_side=("Buy" if side == "LONG" else "Sell"))
        tick_size = float(self.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
        qty_step = float(self.get_qty_step(symbol))
        price_r = self.round_step(price, tick_size)
        qty_r = self.round_step(qty, qty_step)
        if price_r <= 0 or qty_r <= 0:
            return None
        link_id = self._new_order_link_id(f"btp{int(tp_no)}-")
        try:
            resp = self._place_order_resilient(
                f"place_bot_tp{tp_no}({symbol})",
                category=cfg.CATEGORY, symbol=symbol, side=close_side,
                orderType="Limit", price=_plain_num_str(price_r), qty=_plain_num_str(qty_r),
                reduceOnly=True, positionIdx=idx, orderLinkId=link_id,
            )
            return resp.get("result", {}).get("orderId")
        except OrderPlacementUnknown as e:
            # Даже если первый lookup был неуспешен, повторно проверяем тот же
            # linkId. Если ордер уже принят/исполнен, возвращаем его orderId;
            # новый create с другим linkId никогда не делаем вслепую.
            try:
                state = self.get_order_state_by_link(symbol, link_id)
                if state and state.get("orderId"):
                    self.log.warning(f"[{symbol}] TP{tp_no}: восстановил ордер после неизвестного ACK по linkId={link_id}")
                    return state.get("orderId")
            except Exception as lookup_exc:
                self.log.warning(f"[{symbol}] TP{tp_no}: состояние после неизвестного ACK всё ещё не подтверждено: {lookup_exc}")
            self.log.warning(f"[{symbol}] TP{tp_no}: состояние создания неизвестно, повторную постановку сейчас не выполняю: {e}")
            return None
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось поставить TP{tp_no} на {price_r}: {e}")
            return None

    def amend_manual_entry_limit(self, symbol: str, order_id: str, qty: float) -> bool:
        """Безопасно изменяет только qty существующей свободной LIMIT-заявки.

        Цена, сторона и остальные параметры не меняются. После amend обязательно
        перечитываем состояние ордера с биржи: успешный HTTP-ответ сам по себе
        не считается достаточным подтверждением изменения. Если ордер уже
        исполнился/отменён во время операции, возвращаем ошибку вместо того,
        чтобы считать изменение применённым.
        """
        amend = getattr(self.session, "amend_order", None)
        if not callable(amend):
            raise RuntimeError("Текущая версия pybit не поддерживает amend_order")
        qty_step = float(self.get_qty_step(symbol))
        qty_r = self.round_step(qty, qty_step)
        if qty_r <= 0:
            raise ValueError(f"Некорректный новый qty для {symbol}: {qty_r}")
        call_with_retry(
            self.log, amend,
            category=cfg.CATEGORY, symbol=symbol, orderId=order_id,
            qty=_plain_num_str(qty_r),
            description=f"amend_manual_entry_limit({symbol})",
        )

        state = self.get_order_state(symbol, order_id)
        if not state:
            raise RuntimeError(f"{symbol}: после изменения не удалось подтвердить состояние ордера {order_id}")
        status = str(state.get("orderStatus") or "").strip().lower()
        if status not in {"new", "partiallyfilled", "partially_filled"}:
            raise RuntimeError(f"{symbol}: ордер {order_id} уже не активен после amend (status={state.get('orderStatus')})")
        try:
            actual_qty = float(state.get("qty") or 0)
        except (TypeError, ValueError):
            actual_qty = 0.0
        if abs(actual_qty - qty_r) > max(qty_step / 2.0, 1e-12):
            raise RuntimeError(f"{symbol}: биржа не подтвердила новый qty для {order_id} (ожидалось {qty_r:g}, получено {actual_qty:g})")
        return True

    def compute_signal_entry_sizing(self, symbol: str, side: str, entries: List[float], stop: float, order_usdt: float) -> Dict:
        """Единый расчёт размера входов по сигналу. Им пользуются и предпросмотр
        в Telegram, и реальная постановка ордеров, поэтому пользователь
        подтверждает ровно те числа, которые потом уйдут на биржу.

        order_usdt — суммарный номинал всех входов. Входы делятся поровну по
        КОЛИЧЕСТВУ, цены у них разные, поэтому количество на вход считается
        от суммы округлённых цен входов и округляется вниз за одно деление
        (раньше было два последовательных округления от средней цены).
        Проверяются minOrderQty, minNotionalValue для КАЖДОГО входа (по
        самой низкой цене это самое жёсткое условие) и maxOrderQty.
        Бросает ValueError с понятным текстом, если ордера выставить нельзя."""
        side = str(side).upper()
        if side not in ("SHORT", "LONG"):
            raise ValueError(f"Неизвестное направление «{side}» — ожидался SHORT или LONG.")
        if not entries:
            raise ValueError("В сигнале нет цен входа.")
        try:
            order_dec = Decimal(str(order_usdt))
        except Exception:
            raise ValueError("Сумма сделки должна быть числом.")
        if not order_dec.is_finite() or order_dec <= 0:
            raise ValueError("Сумма сделки должна быть конечным числом больше 0 USDT.")

        filters = self.get_instrument_filters(symbol)
        lot = filters["lotSizeFilter"]
        qty_step = float(lot["qtyStep"])
        min_qty = float(lot["minOrderQty"])
        tick_size = float(filters["priceFilter"]["tickSize"])
        min_notional = float(lot.get("minNotionalValue") or 0)
        max_qty = float(lot.get("maxOrderQty") or 0)
        if (not math.isfinite(qty_step) or qty_step <= 0 or not math.isfinite(min_qty) or min_qty <= 0
                or not math.isfinite(tick_size) or tick_size <= 0
                or not math.isfinite(min_notional) or min_notional < 0 or not math.isfinite(max_qty) or max_qty < 0):
            raise RuntimeError(f"{symbol}: биржа вернула некорректные фильтры цены/количества")

        prices = [self.round_price_nearest(float(p), tick_size) for p in entries]
        if any((not math.isfinite(p)) or p <= 0 for p in prices):
            raise ValueError("Цена входа после округления к шагу цены некорректна — проверь пост.")
        stop_price = _round_stop_price_for_side(stop, tick_size, side)
        # Направление стопа проверяем и ПОСЛЕ округления: на очень близких
        # уровнях стоп мог бы совпасть с ценой входа и сработать сразу.
        if side == "SHORT" and stop_price <= max(prices):
            raise ValueError(f"После округления к шагу цены {tick_size:g} стоп {stop_price:g} не выше цены входа {max(prices):g} — проверь пост.")
        if side == "LONG" and stop_price >= min(prices):
            raise ValueError(f"После округления к шагу цены {tick_size:g} стоп {stop_price:g} не ниже цены входа {min(prices):g} — проверь пост.")

        step_dec = Decimal(str(qty_step))
        price_sum = sum((Decimal(str(p)) for p in prices), Decimal(0))
        qty_each_dec = (order_dec / (price_sum * step_dec)).to_integral_value(rounding=ROUND_DOWN) * step_dec

        # Минимальный объём на вход и соответствующая ему минимальная сумма.
        need_qty = Decimal(str(min_qty))
        if min_notional > 0:
            by_notional = (Decimal(str(min_notional)) / (Decimal(str(min(prices))) * step_dec)).to_integral_value(rounding=ROUND_CEILING) * step_dec
            need_qty = max(need_qty, by_notional)
        need_qty = (need_qty / step_dec).to_integral_value(rounding=ROUND_CEILING) * step_dec
        min_usdt = float((need_qty * price_sum).quantize(Decimal("0.01"), rounding=ROUND_CEILING))

        qty_each = float(qty_each_dec)
        if qty_each_dec < Decimal(str(min_qty)):
            raise ValueError(
                f"Расчётный объём на один вход ({qty_each:g}) меньше минимального ({min_qty:g}) для {symbol} — "
                f"сумма {float(order_dec):g} USDT слишком мала для этой пары (нужно не меньше ≈{min_usdt:g} USDT)."
            )
        low_price = min(prices)
        if min_notional > 0 and qty_each_dec * Decimal(str(low_price)) < Decimal(str(min_notional)):
            raise ValueError(
                f"Номинал одного входа ({qty_each:g} × {low_price:g} = {float(qty_each_dec * Decimal(str(low_price))):g} USDT) "
                f"меньше минимального {min_notional:g} USDT для {symbol} — нужно не меньше ≈{min_usdt:g} USDT суммарно."
            )
        if max_qty > 0 and qty_each > max_qty:
            raise ValueError(f"Объём на один вход ({qty_each:g}) превышает максимум биржи ({max_qty:g}) для {symbol} — уменьши сумму.")

        qty_total = float(qty_each_dec * len(prices))
        notional_total = float(qty_each_dec * price_sum)
        return {
            "qty_each": qty_each,
            "qty_total": qty_total,
            "notional_total": notional_total,
            "entry_prices": prices,
            "avg_entry": float(price_sum / len(prices)),
            "stop_price": stop_price,
            "qty_step": qty_step,
            "tick_size": tick_size,
            "min_order_usdt": min_usdt,
        }

    def open_signal_position(self, symbol: str, side: str, entries: List[float], stop: float, order_usdt: float, targets: Optional[List[float]] = None, single_target_is_partial: bool = False) -> Dict:
        """Открывает позицию по вручную присланному в чат посту-сигналу:
        равными лимитными ордерами на каждую из цен входа (обычно двумя),
        каждый со встроенным стоп-лоссом. Старый TP из сигнала здесь НЕ
        встраивается: после фактического исполнения входа монитор ставит
        единую систему TP1-TP4 от реальной средней цены позиции.
        TP1-TP3 — независимые reduce-only LIMIT, TP4 — Full TP оставшегося
        объёма.

        order_usdt — это ИТОГОВЫЙ размер позиции в USDT (суммарный объём
        всех входов), а НЕ маржа для умножения на плечо: если пользователь
        пишет "20", суммарный объём входов будет ≈20 USDT. Максимальное
        плечо монеты используется только для того, чтобы под эту сумму
        требовалось как можно меньше залоговой маржи — саму сумму ордеров
        оно не увеличивает."""
        side = side.upper()
        if side not in ("SHORT", "LONG"):
            raise ValueError(f"Неизвестное направление «{side}» — ожидался SHORT или LONG.")

        symbol = self.resolve_symbol(symbol)

        avg_entry_raw = sum(entries) / len(entries)

        # Сверяем направление стопа со стороной сделки, чтобы не отправить
        # на биржу заведомо некорректный запрос (для шорта стоп обязан быть
        # выше входа, для лонга — ниже).
        if side == "SHORT" and stop <= avg_entry_raw:
            raise ValueError(f"Для SHORT стоп ({stop}) должен быть выше средней цены входа ({avg_entry_raw:g}) — проверь пост.")
        if side == "LONG" and stop >= avg_entry_raw:
            raise ValueError(f"Для LONG стоп ({stop}) должен быть ниже средней цены входа ({avg_entry_raw:g}) — проверь пост.")

        # Размер считаем ДО смены плеча: если ордера всё равно нельзя выставить
        # (мало денег/minNotional), на аккаунте ничего не меняем.
        sizing = self.compute_signal_entry_sizing(symbol, side, entries, stop, order_usdt)
        qty_each = sizing["qty_each"]
        stop_price = sizing["stop_price"]
        entry_prices = sizing["entry_prices"]
        avg_entry = sizing["avg_entry"]
        notional_total = sizing["notional_total"]

        leverage = self.get_max_leverage(symbol)
        # Подтверждаем у биржи, что плечо реально стало запрошенным (с
        # однократным повтором при устаревшем кэше). Иначе под ордер на ту же
        # сумму потребовалась бы другая маржа, чем рассчитал пользователь.
        actual_leverage = self.ensure_leverage_verified(symbol, leverage)
        if actual_leverage and abs(actual_leverage - leverage) > 0.01:
            self.log.warning(f"[{symbol}] Запрошено плечо {leverage:g}x, но на аккаунте фактически {actual_leverage:g}x — маржа под ордер будет отличаться от расчётной.")
            leverage = actual_leverage

        # Маржа считается от ФАКТИЧЕСКОГО номинала ордеров (после округления
        # количества), а не от суммы, которую ввёл пользователь.
        required_margin = notional_total / leverage if leverage else notional_total

        entry_side = "Sell" if side == "SHORT" else "Buy"

        # Старый TP из сигнала больше НЕ встраиваем во входной ордер.
        # После фактического исполнения входа монитор сразу ставит единый TP1-TP4
        # от реальной средней цены позиции.
        order_ids = []
        errors = []
        for price_r in entry_prices:
            link_id = self._new_order_link_id("sg1-")
            params = dict(
                category=cfg.CATEGORY, symbol=symbol, side=entry_side,
                orderType="Limit", price=_plain_num_str(price_r), qty=_plain_num_str(qty_each),
                timeInForce="GTC", reduceOnly=False, positionIdx=0,
                stopLoss=_plain_num_str(stop_price), slTriggerBy="LastPrice",
                orderLinkId=link_id,
            )
            try:
                resp = self._place_order_resilient(f"place_order(signal,{symbol})", **params)
                order_id = resp.get("result", {}).get("orderId")
                if order_id:
                    order_ids.append(order_id)
                self.log.info(f"[{symbol}] Сигнальный вход: лимитный {entry_side} {qty_each} по {price_r}, плечо {leverage}x, стоп {stop_price}")
            except Exception as e:
                # Не роняем всю операцию из-за одного неудачного входа —
                # если хотя бы один ордер уже встал, вызывающий код должен
                # узнать о нём и поставить позицию под наблюдение, иначе
                # уже выставленный ордер останется без отслеживания вообще.
                self.log.error(f"[{symbol}] Не удалось разместить лимитный вход по {price_r}: {e}")
                errors.append(f"{price_r}: {e}")

        if not order_ids:
            raise RuntimeError("Не удалось разместить ни одного входного ордера. " + "; ".join(errors))

        return {
            "qty_each": qty_each,
            # Decimal: float-умножение (0.7 * 3 = 2.0999999999999996) писало в БД шум.
            "qty_total": float(Decimal(str(qty_each)) * len(order_ids)),
            "avg_entry": avg_entry,
            "order_ids": order_ids,
            "leverage": leverage,
            "order_usdt": order_usdt,
            "notional_total": notional_total,
            "required_margin": required_margin,
            "stop_price": stop_price,
            "entry_prices": entry_prices,
            # Старого одиночного TP здесь больше нет. TP1-TP4 рассчитываются
            # только после фактического исполнения входа от реальной средней цены.
            "take_profit": None,
            "tp_system": "TP1-TP4",
            "errors": errors,
        }

    def place_manual_tp_limit(self, symbol: str, side: str, price: float, qty: float, tp_no: int, prefix: str = "mtp") -> Optional[str]:
        """Независимый reduce-only TP1/TP2/TP3. prefix=mtp для ручных сделок, stp для сигнальных постов."""
        close_side = "Sell" if side == "LONG" else "Buy"
        idx = self._resolve_live_position_idx(symbol, fallback_side=("Buy" if side == "LONG" else "Sell"))
        tick_size = float(self.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
        qty_step = float(self.get_qty_step(symbol))
        price_r = self.round_step(price, tick_size)
        qty_r = self.round_step(qty, qty_step)
        if price_r <= 0 or qty_r <= 0:
            return None
        link_id = self._new_order_link_id(f"{prefix}{int(tp_no)}-")
        try:
            resp = self._place_order_resilient(
                f"place_{prefix}_tp{tp_no}({symbol})", category=cfg.CATEGORY, symbol=symbol,
                side=close_side, orderType="Limit", price=_plain_num_str(price_r), qty=_plain_num_str(qty_r),
                reduceOnly=True, positionIdx=idx, orderLinkId=link_id,
            )
            return resp.get("result", {}).get("orderId")
        except OrderPlacementUnknown as e:
            try:
                state = self.get_order_state_by_link(symbol, link_id)
                if state and state.get("orderId"):
                    self.log.warning(f"[{symbol}] {prefix.upper()} TP{tp_no}: восстановил ордер после неизвестного ACK по linkId={link_id}")
                    return state.get("orderId")
            except Exception as lookup_exc:
                self.log.warning(f"[{symbol}] {prefix.upper()} TP{tp_no}: состояние после неизвестного ACK всё ещё не подтверждено: {lookup_exc}")
            self.log.warning(f"[{symbol}] {prefix.upper()} TP{tp_no}: состояние создания неизвестно: {e}")
            return None
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось поставить ручной TP{tp_no} на {price_r}: {e}")
            return None

    @staticmethod
    def round_step(value: float, step: float) -> float:
        """Округляет value вниз до ближайшего шага step (публичный метод —
        используется и внутри клиента, и торговым движком для расчёта
        стоп-лосса/тейк-профита по правилам биржи)."""
        if step <= 0:
            return value
        d_value = Decimal(str(value))
        d_step = Decimal(str(step))
        steps = (d_value / d_step).to_integral_value(rounding=ROUND_DOWN)
        return float(steps * d_step)

    # Совместимость: старое приватное имя указывает на тот же метод.
    _round_step = round_step

    @staticmethod
    def qty_for_notional(notional: float, price: float, qty_step: float) -> float:
        """Максимальное количество (кратное qty_step), которое укладывается в
        notional USDT по цене price. Считается целиком в Decimal за ОДНО
        деление: частное float notional/price заранее теряет точность и на
        точных кратных (например 5 USDT / 0.00001 = 500000) могло дать
        499999.99999… и после округления вниз лишний шаг терялся.
        При некорректных входных данных возвращает 0.0."""
        try:
            n = Decimal(str(notional))
            p = Decimal(str(price))
            s = Decimal(str(qty_step))
        except Exception:
            return 0.0
        if not (n.is_finite() and p.is_finite() and s.is_finite()) or n <= 0 or p <= 0 or s <= 0:
            return 0.0
        steps = (n / (p * s)).to_integral_value(rounding=ROUND_DOWN)
        return float(steps * s)

    @staticmethod
    def round_price_nearest(price: float, tick: float) -> float:
        """Округляет цену лимитного входа к ближайшему тику (а не всегда вниз:
        round_step сдвигал бы цену на тик не в ту сторону для половины входов)."""
        if tick <= 0:
            return price
        t = Decimal(str(tick))
        steps = (Decimal(str(price)) / t).to_integral_value(rounding=ROUND_HALF_UP)
        return float(steps * t)


# ============================================================================
# ПУБЛИЧНЫЙ WS-ФИД ЦЕН + ТРЕКЕР РАЗВОРОТА (ядро стратегии обнаружения пампа)
# ============================================================================

class PriceFeed:
    def __init__(self, logger):
        self.log = logger
        self._lock = threading.Lock()
        self._last_price: Dict[str, float] = {}
        self._last_update_ts: Dict[str, float] = {}
        self._history: Dict[str, Deque[Tuple[float, float]]] = {}
        self._subscribed: set = set()
        self._subscribed_lock = threading.Lock()
        self._last_message_at = 0.0
        self._ws: Optional[WebSocket] = None
        self._running = True
        self._supervisor_thread: Optional[threading.Thread] = None
        self._min_sample_interval = 5.0

    def get_price(self, symbol: str) -> Optional[float]:
        with self._lock:
            return self._last_price.get(symbol)

    def get_price_and_ts(self, symbol: str) -> Optional[Tuple[float, float]]:
        with self._lock:
            price = self._last_price.get(symbol)
            ts = self._last_update_ts.get(symbol)
            if price is None or ts is None:
                return None
            return price, ts

    def get_change_pct(self, symbol: str, lookback_seconds: float) -> Optional[float]:
        with self._lock:
            hist = self._history.get(symbol)
            if not hist or len(hist) < 2:
                return None
            oldest_ts, oldest_price = hist[0]
            newest_ts, newest_price = hist[-1]

        if newest_ts - oldest_ts < lookback_seconds * 0.5:
            return None
        if oldest_price <= 0:
            return None

        return (newest_price - oldest_price) / oldest_price * 100.0

    def has_recent_data(self, symbol: str, max_age_sec: float = 30.0) -> bool:
        with self._lock:
            hist = self._history.get(symbol)
            if not hist:
                return False
            return (time.time() - hist[-1][0]) <= max_age_sec

    def seconds_since_last_message(self) -> float:
        if self._last_message_at == 0.0:
            return float("inf")
        return time.time() - self._last_message_at

    def start(self, symbols: List[str]):
        # ВАЖНО: PriceFeed переиспользуется на одном и том же объекте между
        # перезапусками торгового движка (watchdog, автовосстановление после
        # сбоя и т.п.) — start()/stop() могут вызываться много раз за время
        # жизни процесса. Без явного сброса этих полей _running остался бы
        # False навсегда после первого stop(), и supervisor-поток (авто-
        # переподключение WS) сразу же завершался бы на каждом следующем
        # перезапуске, тихо оставляя бота без реконнекта до конца работы.
        self._running = True
        self._last_message_at = 0.0
        with self._subscribed_lock:
            self._subscribed.clear()

        self._connect()
        self._subscribe(symbols)
        self._supervisor_thread = threading.Thread(target=self._supervisor_loop, daemon=True, name="ws-supervisor")
        self._supervisor_thread.start()

    def stop(self):
        self._running = False
        try:
            if self._ws is not None:
                self._ws.exit()
        except Exception:
            pass

    def ensure_subscribed(self, symbols: List[str]):
        if self._ws is None:
            # Фид ещё не запущен (start() не вызывался) — сохранять эти символы
            # некуда и незачем: start() и так подпишется на весь актуальный
            # список при запуске. Просто не пытаемся дергать несуществующий WS.
            self.log.debug("ensure_subscribed вызван до start() — пропускаю, WS ещё не создан.")
            return
        with self._subscribed_lock:
            missing = [s for s in symbols if s not in self._subscribed]
        if missing:
            self._subscribe(missing)

    def _connect(self):
        self._ws = WebSocket(testnet=cfg.TESTNET, channel_type=cfg.CATEGORY)
        self.log.info("Публичный WebSocket (цены) установлен.")

    def _subscribe(self, symbols: List[str]):
        if self._ws is None:
            self.log.warning("Попытка подписаться на WS-тикеры без активного соединения — пропускаю.")
            return
        for i, symbol in enumerate(symbols):
            try:
                self._ws.ticker_stream(symbol=symbol, callback=self._on_ticker)
                with self._subscribed_lock:
                    self._subscribed.add(symbol)
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось подписаться на WS-тикер: {e}")
            if cfg.WS_SUBSCRIBE_STAGGER_SEC:
                time.sleep(cfg.WS_SUBSCRIBE_STAGGER_SEC)
            if (i + 1) % 50 == 0:
                self.log.info(f"WS: подписано {i + 1}/{len(symbols)} символов...")
        with self._subscribed_lock:
            total_subscribed = len(self._subscribed)
        self.log.info(f"WS: подписка завершена, всего символов: {total_subscribed}.")

    def _on_ticker(self, message: dict):
        try:
            data = message.get("data") or {}
            symbol = data.get("symbol")
            price_raw = data.get("lastPrice")
            if not symbol or price_raw is None:
                return
            price = float(price_raw)
            now = time.time()

            with self._lock:
                self._last_price[symbol] = price
                self._last_update_ts[symbol] = now
                self._last_message_at = now

                hist = self._history.setdefault(symbol, deque())
                if not hist or (now - hist[-1][0]) >= self._min_sample_interval:
                    hist.append((now, price))

                max_age = max(cfg.LOOKBACK_MINUTES * 60 * 1.5, 3600)
                while hist and (now - hist[0][0]) > max_age:
                    hist.popleft()
        except Exception as e:
            self.log.debug(f"Ошибка обработки WS-сообщения: {e}")

    def _supervisor_loop(self):
        while self._running:
            time.sleep(15)
            if not self._running:
                break
            silence = self.seconds_since_last_message()
            if silence > cfg.WS_STALE_TIMEOUT_SEC:
                self.log.warning(f"WS молчит {silence:.0f} сек, переподключаюсь...")
                try:
                    if self._ws is not None:
                        self._ws.exit()
                except Exception:
                    pass
                try:
                    with self._subscribed_lock:
                        symbols = list(self._subscribed)
                        self._subscribed.clear()
                    self._connect()
                    self._subscribe(symbols)
                except Exception as e:
                    self.log.error(f"Не удалось переподключить WS: {e}")


class ReversalTracker:
    """direction="up" — следим за пиком (вход в шорт).
    direction="down" — следим за дном (умный выход)."""

    __slots__ = ("symbol", "direction", "extreme_price", "added_at", "stall_ticks", "meta", "last_seen_ts", "extreme_set_at", "recent_gains")

    def __init__(self, symbol: str, price: float, direction: str, meta: Optional[Dict] = None,
                 last_seen_ts: Optional[float] = None, extreme_set_at: Optional[float] = None,
                 recent_gains: Optional[List[float]] = None):
        self.symbol = symbol
        self.direction = direction
        self.extreme_price = price
        self.added_at = time.time()
        self.stall_ticks = 0
        self.meta = meta or {}
        self.last_seen_ts = last_seen_ts if last_seen_ts is not None else self.added_at
        self.extreme_set_at = extreme_set_at if extreme_set_at is not None else self.last_seen_ts
        # "Микро-анализ": размеры последних приростов к новому максимуму/минимуму,
        # используется чтобы отличить настоящее замедление роста от случайной
        # паузы посреди ещё ускоряющегося движения (см. _is_decelerating).
        self.recent_gains: Deque[float] = deque(recent_gains or [], maxlen=6)

    def _is_decelerating(self) -> bool:
        """True, если темп последних приростов к экстремуму уже замедляется
        (средний размер недавних приростов меньше среднего более ранних) —
        признак того, что движение реально выдыхается, а не просто сделало
        случайную паузу посреди ускорения."""
        gains = list(self.recent_gains)
        if len(gains) < 4:
            # недостаточно истории для суждения о замедлении — не блокируем
            # разворот из-за нехватки данных, просто пропускаем эту проверку
            return True
        half = len(gains) // 2
        older_avg = sum(gains[:half]) / half
        recent_avg = sum(gains[half:]) / (len(gains) - half)
        if older_avg <= 0:
            return True
        return recent_avg < older_avg

    def update(self, price: float, tick_ts: Optional[float], stall_ticks_needed: int, reversal_pct: float) -> bool:
        if tick_ts is not None and tick_ts <= self.last_seen_ts:
            return False
        if tick_ts is not None:
            self.last_seen_ts = tick_ts

        is_new_extreme = price > self.extreme_price if self.direction == "up" else price < self.extreme_price

        if is_new_extreme:
            gain = abs(price - self.extreme_price)
            if gain > 0:
                self.recent_gains.append(gain)
            self.extreme_price = price
            self.extreme_set_at = tick_ts if tick_ts is not None else time.time()
            self.stall_ticks = 0
            return False

        self.stall_ticks += 1
        if self.extreme_price <= 0:
            move_pct = 0.0
        elif self.direction == "up":
            move_pct = (self.extreme_price - price) / self.extreme_price * 100
        else:
            move_pct = (price - self.extreme_price) / self.extreme_price * 100

        is_entry_tracker = self.direction == "up" and self.meta.get("purpose") != "exit"

        required_pct = reversal_pct
        if is_entry_tracker and cfg.STALL_DROP_ADAPTIVE_FACTOR > 0:
            ref = self.meta.get("reference_price")
            if ref and ref > 0:
                total_move_pct = max(0.0, (self.extreme_price - ref) / ref * 100)
                adaptive_pct = total_move_pct * cfg.STALL_DROP_ADAPTIVE_FACTOR
                required_pct = max(reversal_pct, min(adaptive_pct, cfg.STALL_DROP_MAX_PCT))

        now_ts = tick_ts if tick_ts is not None else time.time()
        elapsed_since_peak = now_ts - self.extreme_set_at
        # purpose="exit" отмечает трекеры умного выхода лонга (direction="up",
        # но семантика — "жду пик перед выходом", как и обычный "down" для
        # шорта) — им нужны SMART_EXIT_* тайминги, а не тайминги входа.
        min_seconds = cfg.STALL_MIN_SECONDS if is_entry_tracker else cfg.SMART_EXIT_MIN_SECONDS

        basic_conditions = (
            self.stall_ticks >= stall_ticks_needed
            and move_pct >= required_pct
            and elapsed_since_peak >= min_seconds
        )
        if not basic_conditions:
            return False

        if getattr(cfg, "ENABLE_MICRO_ANALYSIS", False):
            return self._is_decelerating()
        return True

    def is_timed_out(self, max_minutes: float) -> bool:
        return (time.time() - self.added_at) > max_minutes * 60

    def to_dict(self) -> Dict:
        return {"symbol": self.symbol, "direction": self.direction, "extreme_price": self.extreme_price,
                "added_at": self.added_at, "stall_ticks": self.stall_ticks, "meta": self.meta,
                "last_seen_ts": self.last_seen_ts, "extreme_set_at": self.extreme_set_at,
                "recent_gains": list(self.recent_gains)}

    @classmethod
    def from_dict(cls, d: Dict) -> "ReversalTracker":
        t = cls(d["symbol"], d["extreme_price"], d["direction"], d.get("meta", {}), d.get("last_seen_ts"), d.get("extreme_set_at"), d.get("recent_gains"))
        t.added_at = d["added_at"]
        t.stall_ticks = d["stall_ticks"]
        return t


# ============================================================================
# ТОРГОВЫЙ ДВИЖОК: памп -> подтверждённый разворот -> шорт; защита прибыли;
# умный выход; восстановление состояния между рестартами
# ============================================================================

STATE_PATH = resolve_path(getattr(cfg, "STATE_FILE", "bot_state.json"))
TRADES_PATH = resolve_path(getattr(cfg, "TRADES_FILE", "trades.json"))

_state_file_lock = threading.Lock()
_trades_file_lock = threading.Lock()


def save_state(watched: Dict[str, ReversalTracker], positions_guard: Dict[str, ReversalTracker], cooldowns: Dict[str, float], logger):
    """Совместимый фасад: теперь состояние сохраняется только в SQLite."""
    save_runtime_state(watched, positions_guard, cooldowns, logger)


def load_state(logger):
    """Совместимый фасад для старого кода; фактически читает SQLite."""
    return load_runtime_state(logger)


def append_trade_record(record: Dict, logger):
    """Persist one engine history record atomically and surface failures.

    A warning-only failure made the UI appear successful while the trade was
    permanently absent from history. The caller now receives an exception and
    can alert/log the failed persistence explicitly.
    """
    encoded = json.dumps(record, ensure_ascii=False, separators=(",", ":"), default=_json_default_state)
    try:
        with _db_lock:
            try:
                _conn.execute("BEGIN IMMEDIATE")
                _conn.execute(
                    "INSERT INTO engine_trade_history(created_at, record_json) VALUES (?, ?)",
                    (int(time.time() * 1000), encoded),
                )
                _conn.commit()
            except Exception:
                _conn.rollback()
                raise
        # Event log is secondary: failure is logged by record_state_event and
        # must not make a successfully committed history row look uncommitted.
        record_state_event("trade_history", "TRADE_RECORDED", record.get("symbol"), record)
    except Exception as e:
        if logger:
            logger.exception("Не удалось записать сделку в SQLite history")
        raise RuntimeError("Не удалось надёжно сохранить запись истории сделки в SQLite") from e


def read_trade_history(limit: int = 10) -> List[Dict]:
    limit = int(limit)
    if limit <= 0:
        return []
    # Do not fall back to legacy JSON when the SQLite read itself fails: doing
    # so concealed DB corruption/locking and could trigger duplicate migration.
    with _db_lock:
        rows = _conn.execute(
            "SELECT record_json FROM engine_trade_history ORDER BY id DESC LIMIT ?",
            (limit,),
        ).fetchall()
        count_row = _conn.execute("SELECT COUNT(*) AS n FROM engine_trade_history").fetchone()
        history_count = int(count_row["n"] if count_row else 0)
    if rows:
        records = []
        for row in reversed(rows):
            try:
                record = json.loads(row["record_json"])
            except (TypeError, ValueError, json.JSONDecodeError) as exc:
                raise sqlite3.DatabaseError("Повреждена запись engine_trade_history.record_json") from exc
            if not isinstance(record, dict):
                raise sqlite3.DatabaseError("Запись engine_trade_history должна быть JSON-объектом")
            records.append(record)
        return records

    # One-time legacy migration is allowed only when SQLite history is truly
    # empty, and the entire import is transactional (never half-import records).
    if history_count == 0 and os.path.exists(TRADES_PATH):
        with _trades_file_lock:
            with open(TRADES_PATH, "r", encoding="utf-8") as f:
                legacy_records = json.load(f)
        if not isinstance(legacy_records, list):
            raise ValueError("Legacy trades.json должен содержать список записей")
        if legacy_records:
            encoded_records = []
            for rec in legacy_records:
                if not isinstance(rec, dict):
                    raise ValueError("Некорректная запись в legacy trades.json")
                closed_at = float(rec.get("closed_at") or time.time())
                if not math.isfinite(closed_at) or closed_at <= 0:
                    closed_at = time.time()
                encoded_records.append((int(closed_at * 1000), json.dumps(rec, ensure_ascii=False, separators=(",", ":"), default=_json_default_state)))
            with _db_lock:
                try:
                    _conn.execute("BEGIN IMMEDIATE")
                    # Another thread may have migrated it after our initial read.
                    existing = _conn.execute("SELECT COUNT(*) FROM engine_trade_history").fetchone()[0]
                    if int(existing) == 0:
                        _conn.executemany(
                            "INSERT INTO engine_trade_history(created_at, record_json) VALUES (?, ?)",
                            encoded_records,
                        )
                    _conn.commit()
                except Exception:
                    _conn.rollback()
                    raise
            record_state_event("trade_history", "LEGACY_JSON_MIGRATED", payload={"count": len(encoded_records), "path": TRADES_PATH})
            return legacy_records[-limit:]
    return []


def fmt_num(value) -> str:
    if isinstance(value, float):
        return f"{value:.4f}".rstrip("0").rstrip(".")
    return str(value)


class BoundedIdSet:
    """Потокобезопасное множество с ограниченным размером: используется для
    дедупликации уведомлений о сделках (движок помечает сделку как уже
    уведомлённую, фоновая REST-сверка это видит и не дублирует сообщение).
    При превышении maxlen самые старые id вытесняются — нет утечки памяти
    при непрерывной работе 24/7."""

    def __init__(self, maxlen: int = 500):
        self._order: Deque[str] = deque(maxlen=maxlen)
        self._set: set = set()
        self._lock = threading.Lock()

    def add(self, item: str):
        with self._lock:
            if item in self._set:
                return
            if len(self._order) == self._order.maxlen:
                oldest = self._order.popleft()
                self._set.discard(oldest)
            self._order.append(item)
            self._set.add(item)

    def __contains__(self, item) -> bool:
        with self._lock:
            return item in self._set

    def __len__(self) -> int:
        with self._lock:
            return len(self._set)


def calc_ema(values: List[float], period: int) -> Optional[float]:
    """Экспоненциальная скользящая средняя по последним `period` значениям
    (простая SMA как затравка + экспоненциальное сглаживание дальше).
    Возвращает None, если данных меньше периода."""
    if len(values) < period:
        return None
    k = 2.0 / (period + 1)
    ema = sum(values[:period]) / period
    for value in values[period:]:
        ema = value * k + ema * (1 - k)
    return ema


class ShortPumpBot:
    """Ядро стратегии. `controller` — любой объект с интерфейсом:
    .paused (bool), .running (bool), .notify(text: str)."""

    def __init__(self, logger, client: BybitClient, controller):
        self.log = logger
        self.client = client
        self.feed = PriceFeed(logger)
        self.tg = controller
        self._running = True

        self._symbols: List[str] = []
        self._last_symbol_refresh = 0.0

        self._known_open_symbols: set = set()
        self._known_lock = threading.Lock()
        # Входы, исход которых биржа не подтвердила (потерянный ответ, лаг
        # статуса). Ордер мог остаться активным или исполниться позже — такие
        # входы нельзя забывать, пока не выяснено, есть ли позиция.
        self._unresolved_entries: Dict[str, Dict] = {}
        self._unresolved_lock = threading.Lock()
        self._unresolved_last_check = 0.0

        self._watched: Dict[str, ReversalTracker] = {}
        self._watched_lock = threading.Lock()

        self._position_guards: Dict[str, ReversalTracker] = {}
        self._guards_lock = threading.Lock()

        self._cooldowns: Dict[str, float] = {}
        self._cooldown_lock = threading.Lock()

        self._trade_meta: Dict[str, Dict] = {}
        self._trade_meta_lock = threading.Lock()

        self._open_positions_cache: Dict[str, Dict] = {}
        self._open_positions_cache_lock = threading.Lock()

        self._last_heartbeat = time.time()
        self._last_state_save = 0.0

        # Watchdog круглосуточной работы: если основной торговый цикл или
        # WS-поток цен "тихо зависнут" (без исключения, просто перестанут
        # прогрессировать) — это единственный способ заметить и форсировать
        # полный перезапуск движка, а не остаться молча висеть навсегда.
        self._last_loop_tick = time.time()
        self._watchdog_stale = threading.Event()

        # id недавно закрытых ботом сделок — чтобы фоновая REST-сверка (db_sync)
        # не слала о них ВТОРОЕ уведомление, когда доберётся до них сама.
        # Ограничено по размеру (BoundedIdSet), чтобы не расти бесконечно при
        # круглосуточной работе.
        self.recently_closed_ids = BoundedIdSet(maxlen=500)

    def stop(self, *_):
        self.log.info("Получен сигнал остановки, завершаю работу...")
        self._running = False

    # ---- статус -------------------------------------------------------------

    def build_status_summary(self) -> str:
        with self._watched_lock:
            watched_count = len(self._watched)
        with self._guards_lock:
            guards_count = len(self._position_guards)
        ws_age = self.feed.seconds_since_last_message()
        ws_state = "🟢 живой" if ws_age < 30 else f"🟡 тишина {ws_age:.0f} сек"

        active_filters = []
        if getattr(cfg, "ENABLE_MICRO_ANALYSIS", False):
            active_filters.append("микро-анализ разворота")
        if getattr(cfg, "ENABLE_VERTICAL_CANDLE_FILTER", False):
            active_filters.append("не шортить вертикальную свечу")
        if getattr(cfg, "ENABLE_BREAKOUT_FILTER", False):
            active_filters.append("провал пробоя")
        if getattr(cfg, "ENABLE_TREND_FILTER", False):
            active_filters.append("не шортить сильный тренд")
        if getattr(cfg, "ENABLE_VOLUME_FILTER", False):
            active_filters.append("объёмный спайк")
        if getattr(cfg, "ENABLE_VOLUME_DECLINE_FILTER", False):
            active_filters.append("падение объёма после пампа")
        if getattr(cfg, "ENABLE_SHORT_LOW_BOUNCE_FILTER", False):
            active_filters.append(
                f"рост от лоя свечи (шорт, +{fmt_num(getattr(cfg, 'SHORT_LOW_BOUNCE_PCT', 1.0))}% "
                f"на {getattr(cfg, 'SHORT_LOW_BOUNCE_CANDLE_INTERVAL', '1')}м)"
            )
        if getattr(cfg, "ENABLE_LONG_LOW_BOUNCE_FILTER", False):
            active_filters.append(
                f"рост от лоя свечи (лонг, +{fmt_num(getattr(cfg, 'LONG_LOW_BOUNCE_PCT', 1.0))}% "
                f"на {getattr(cfg, 'LONG_LOW_BOUNCE_CANDLE_INTERVAL', '1')}м)"
            )
        filters_line = f"• Фильтры входа: <b>{', '.join(active_filters)}</b>\n" if active_filters else "• Фильтры входа: <b>все выключены</b> (чистый вход по цене)\n"
        entry_mode_line = f"• Тип входа: <b>{'post-only лимит (+ market фолбэк)' if getattr(cfg, 'ENABLE_POST_ONLY_ENTRY', False) else 'рыночный (market)'}</b>\n"

        favorites_on = is_favorites_mode_enabled()
        if favorites_on:
            fav_list = get_favorite_symbols()
            favorites_line = f"• ⭐ Избранное: <b>вкл</b> — торгуются только {len(fav_list)} монет(ы)\n" if fav_list else "• ⭐ Избранное: <b>вкл, но список пуст</b> — вход не сканируется вообще!\n"
        else:
            favorites_line = ""

        long_mode_status = getattr(cfg, "ENABLE_LONG_MODE", False)
        status_tp_pct = getattr(cfg, "LONG_TAKE_PROFIT_PCT", cfg.TAKE_PROFIT_PCT) if long_mode_status else cfg.TAKE_PROFIT_PCT
        status_sl_pct = getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) if long_mode_status else getattr(cfg, "FIXED_STOP_LOSS_PCT", 0)
        status_sl_sign = "-" if long_mode_status else "+"

        return (
            f"• Порог пампа: <b>{fmt_num(cfg.PUMP_THRESHOLD_PCT)}%</b> за {cfg.LOOKBACK_MINUTES} мин\n"
            f"• Направление входа: <b>{'ЛОНГ' if long_mode_status else 'ШОРТ'}</b>\n"
            f"• Плечо: <b>{cfg.LEVERAGE}x</b> · Размер: <b>{fmt_num(cfg.POSITION_PCT_OF_EQUITY)}%</b> от equity\n"
            f"• Тейки: <b>TP1 +{fmt_num(get_bot_tp_config()[0][0])}% / {fmt_num(get_bot_tp_config()[1][0])}% · TP2 +{fmt_num(get_bot_tp_config()[0][1])}% / {fmt_num(get_bot_tp_config()[1][1])}% · TP3 +{fmt_num(get_bot_tp_config()[0][2])}% / {fmt_num(get_bot_tp_config()[1][2])}% · TP4 +{fmt_num(get_bot_tp_config()[0][3])}% / 100% остатка</b> · Лимит позиций: <b>{cfg.MAX_OPEN_POSITIONS}</b>\n"
            f"• Стоп-лосс: <b>{'вкл' if getattr(cfg, 'ENABLE_FIXED_STOP_LOSS', False) else 'выкл'}</b>"
            + (f" ({status_sl_sign}{fmt_num(status_sl_pct)}% от входа)\n" if getattr(cfg, 'ENABLE_FIXED_STOP_LOSS', False) else "\n") +
            f"• Защита прибыли: <b>{'вкл' if cfg.ENABLE_PROFIT_LOCK else 'выкл'}</b> "
            f"(SL при движении +{fmt_num(cfg.PROFIT_LOCK_TRIGGER_PCT)}%, фиксирует ~{fmt_num(cfg.PROFIT_LOCK_MIN_USDT)} USDT)\n"
            f"• Умный выход: <b>{'вкл' if cfg.ENABLE_SMART_EXIT else 'выкл'}</b>\n"
            f"{entry_mode_line}"
            f"{favorites_line}"
            f"{filters_line}"
            f"• WebSocket цен: {ws_state} · Символов: <b>{len(self._symbols)}</b>\n"
            f"• Под наблюдением на вход: <b>{watched_count}</b> · На умном выходе: <b>{guards_count}</b>"
        )

    def _refresh_symbols_if_needed(self, force: bool = False):
        now = time.time()
        if force or not self._symbols or (now - self._last_symbol_refresh) > cfg.SYMBOL_REFRESH_MINUTES * 60:
            try:
                new_symbols = self.client.get_linear_usdt_symbols()
                added = [s for s in new_symbols if s not in self._symbols]
                self._symbols = new_symbols
                self._last_symbol_refresh = now
                self.log.info(f"Список символов обновлён: {len(self._symbols)} пар ({len(added)} новых).")
                if added:
                    self.feed.ensure_subscribed(added)
            except Exception as e:
                self.log.error(f"Не удалось обновить список символов: {e}")

    # ---- запуск --------------------------------------------------------------

    def run(self):
        self.log.info("Торговый движок запущен.")

        # Сброс watchdog-состояния: run() может вызываться повторно на ТОМ ЖЕ
        # экземпляре после перезапуска движка (см. main()) — если не сбросить,
        # флаг зависания от предыдущего запуска тут же форсировал бы ещё один
        # рестарт вникуда.
        self._watchdog_stale.clear()
        self._last_loop_tick = time.time()

        # ВАЖНО: сперва получаем начальный список символов НАПРЯМУЮ (без
        # _refresh_symbols_if_needed), а уже потом стартуем feed.start(...),
        # который создаёт WebSocket и сразу подписывается на этот список.
        # Если сделать наоборот (как было раньше) — _refresh_symbols_if_needed
        # увидит пустой self._symbols и попытается вызвать
        # feed.ensure_subscribed(...) ДО того, как WebSocket вообще создан,
        # что валит подписку на каждый символ с ошибкой
        # "'NoneType' object has no attribute 'ticker_stream'".
        try:
            self._symbols = self.client.get_linear_usdt_symbols()
            self._last_symbol_refresh = time.time()
            self.log.info(f"Стартовый список символов получен: {len(self._symbols)} пар.")
        except Exception as e:
            self.log.error(f"Не удалось получить стартовый список символов: {e}. Начинаю с пустого списка, обновлю на следующем цикле.")
            self._symbols = []

        watched, guards, cooldowns = load_state(self.log)
        record_state_event("runtime", "ENGINE_START", payload={"version": "db-state-v2"})
        with self._watched_lock:
            self._watched = watched
        with self._guards_lock:
            self._position_guards = guards
        with self._cooldown_lock:
            self._cooldowns = cooldowns

        self.feed.start(self._symbols)

        summary = self.build_status_summary()
        self.tg.notify(f"🚀 <b>Торговый движок запущен</b>\n━━━━━━━━━━━━━━━\n{summary}")

        try:
            open_positions = self.client.get_open_positions()
            self._rebuild_trade_meta_from_exchange(open_positions)
            with self._trade_meta_lock:
                bot_tracked = set(self._trade_meta.keys())
            live_symbols = {p["symbol"] for p in open_positions}
            with self._known_lock:
                # Только позиции, которые бот реально открывал сам (см.
                # _rebuild_trade_meta_from_exchange) — вручную открытые
                # пользователем позиции сюда никогда не попадают.
                self._known_open_symbols = live_symbols & bot_tracked
        except Exception as e:
            self.log.warning(f"Не удалось получить стартовые позиции: {e}")

        threading.Thread(target=self._entry_watch_loop, daemon=True, name="entry-watch").start()
        threading.Thread(target=self._position_guard_loop, daemon=True, name="position-guard").start()
        threading.Thread(target=self._watchdog_loop, daemon=True, name="watchdog").start()

        try:
            while self._running and self.tg.running:
                cycle_start = time.time()
                self._last_loop_tick = cycle_start

                if self._watchdog_stale.is_set():
                    # Поднимаем исключение ЗДЕСЬ (а не в самом watchdog-потоке —
                    # оттуда нельзя прервать основной цикл), оно уйдёт в main(),
                    # который перезапустит движок с нуля через штатный механизм.
                    raise RuntimeError("Watchdog обнаружил зависание торгового движка и форсировал перезапуск")

                try:
                    self._refresh_symbols_if_needed()
                    self._check_closed_positions()
                    if not self.tg.paused:
                        self._scan_for_pumps()
                    self._maybe_heartbeat()
                    self._maybe_save_state()
                except Exception as e:
                    self.log.exception(f"Ошибка в основном цикле: {e}")
                    self.tg.notify(f"⚠️ <b>Ошибка в основном цикле торговли</b>\n<code>{e}</code>")

                elapsed = time.time() - cycle_start
                time.sleep(max(0.5, cfg.POLL_INTERVAL_SEC - elapsed))
        finally:
            # try/finally, а не код после цикла: если watchdog форсировал
            # исключение выше, эта очистка (остановка WS, сохранение
            # состояния) должна отработать ВСЕ РАВНО — иначе старый
            # WebSocket и его supervisor-поток продолжат жить параллельно
            # с новым после перезапуска (утечка соединений/потоков).
            self.feed.stop()
            save_state(self._watched, self._position_guards, self._cooldowns, self.log)
            record_state_event("runtime", "ENGINE_STOP", payload={"version": "db-state-v2"})
            self.log.info("Торговый движок остановлен.")
            if not self._watchdog_stale.is_set():
                # При обычной штатной остановке — отдельное уведомление.
                # При перезапуске по watchdog не дублируем: он уже прислал
                # своё сообщение "обнаружено зависание, перезапускаю".
                self.tg.notify("🔴 <b>Торговый движок остановлен.</b>")

    def _watchdog_loop(self):
        """Последний рубеж защиты для круглосуточной работы: если основной
        торговый цикл или WS-поток цен тихо зависнут (не бросив исключение —
        например, сетевой вызов застрял без таймаута) — обнаруживает это по
        отсутствию прогресса и форсирует полный перезапуск движка. Внутренние
        механизмы самовосстановления (переподключение WS, ретраи запросов)
        получают достаточно времени сработать сами — watchdog вмешивается,
        только если они тоже не помогли."""
        max_stale_main = max(180, cfg.POLL_INTERVAL_SEC * 20)
        max_stale_ws = max(300, cfg.WS_STALE_TIMEOUT_SEC * 4)

        while self._running and self.tg.running:
            time.sleep(20)

            stale_main_sec = time.time() - self._last_loop_tick
            stale_ws_sec = self.feed.seconds_since_last_message()

            reasons = []
            if stale_main_sec > max_stale_main:
                reasons.append(f"основной цикл не отвечает {stale_main_sec:.0f} сек")
            if stale_ws_sec > max_stale_ws:
                reasons.append(f"WS цен молчит {stale_ws_sec:.0f} сек несмотря на авто-переподключение")

            if reasons:
                reason_text = "; ".join(reasons)
                self.log.error(f"Watchdog: обнаружено зависание ({reason_text}) — форсирую перезапуск движка.")
                self.tg.notify(f"🐕‍🦺 <b>Watchdog: обнаружено зависание бота</b>\n\n{reason_text}.\nПринудительно перезапускаю торговый движок, чтобы отслеживание не останавливалось.")
                self._watchdog_stale.set()
                return  # своё дело сделал — дальше подхватит основной цикл run()

    def _rebuild_trade_meta_from_exchange(self, open_positions: List[Dict]):
        """Восстанавливает self._trade_meta после рестарта — но ТОЛЬКО для
        позиций, которые сам бот когда-то открыл (это видно из персистентного
        реестра bot_positions в БД, см. mark_bot_position_open). Позиции,
        которых там нет — открытые пользователем вручную на бирже, либо
        позиции с версии бота до появления этого реестра — сознательно
        игнорируются: бот не берёт их под управление, не защищает прибыль,
        не делает умный выход, не восстанавливает TP/SL и не шлёт по ним
        уведомлений. Раньше здесь ЛЮБАЯ открытая на бирже позиция при
        рестарте принималась за "свою" — это и был источник вмешательства
        бота в ручные сделки пользователя."""
        try:
            bot_positions = get_all_bot_positions()
        except Exception:
            self.log.exception("Не удалось прочитать реестр 'открыто ботом' — восстановление позиций после рестарта пропущено (на всякий случай, чтобы не начать управлять чужими сделками).")
            return

        live_by_symbol = {pos.get("symbol"): pos for pos in open_positions if pos.get("symbol")}
        foreign = [s for s in live_by_symbol if s not in bot_positions]
        if foreign:
            self.log.info(f"На бирже есть открытые позиции, которые бот НЕ открывал (вручную или до этого обновления) — бот их не трогает: {', '.join(sorted(foreign))}")

        for symbol, saved in bot_positions.items():
            pos = live_by_symbol.get(symbol)
            if pos is None:
                # Реестр говорит, что бот открывал эту позицию, но на бирже
                # её уже нет — значит, закрылась, пока бот не работал.
                # Не гадаем и не шлём уведомление задним числом (см. общий
                # принцип в _finalize_closed_position) — просто убираем из
                # реестра, а фоновая REST-сверка (sync_trades) при следующем
                # проходе сама найдёт эту сделку и корректно её обработает.
                mark_bot_position_closed(symbol)
                continue

            with self._trade_meta_lock:
                already_known = symbol in self._trade_meta
            if already_known:
                continue

            entry_price = float(pos.get("avgPrice") or saved.get("entry_price") or 0)
            qty = float(pos.get("size") or saved.get("qty") or 0)
            if entry_price <= 0 or qty <= 0:
                continue

            is_long = bool(saved.get("is_long"))
            tick_size = float(saved.get("tick_size") or 0.0)
            live_tp = float(pos.get("takeProfit") or 0)
            tp_price = live_tp if live_tp > 0 else saved.get("tp_price")

            live_sl = float(pos.get("stopLoss") or 0)
            if live_sl > 0:
                sl_price = live_sl
                # Если сохранённый статус говорит, что профит ещё не был
                # зафиксирован, а текущий SL уже по нужную сторону от входа —
                # значит, подтянуть его успели до рестарта, статус обновляем.
                profit_locked = bool(saved.get("profit_locked")) or (
                    (is_long and live_sl > entry_price) or (not is_long and live_sl < entry_price)
                )
            else:
                sl_price = saved.get("sl_price")
                profit_locked = bool(saved.get("profit_locked"))

            opened_at_ms = saved.get("opened_at")
            opened_at = (opened_at_ms / 1000) if opened_at_ms else time.time()

            saved_runtime = saved.get("runtime") if isinstance(saved.get("runtime"), dict) else {}
            restored_meta = dict(saved_runtime) if saved_runtime else {}
            # Биржа — источник истины по фактическим avgPrice/size/SL/TP;
            # SQLite runtime — источник истины по внутренним шагам и TP-состояниям.
            restored_meta.update({
                "entry_price": entry_price, "qty": qty, "is_long": is_long,
                "margin_usdt": saved.get("margin_usdt") or restored_meta.get("margin_usdt") or ((entry_price * qty) / cfg.LEVERAGE if cfg.LEVERAGE else 0.0),
                "tp_price": tp_price, "sl_price": sl_price, "tick_size": tick_size,
                "opened_at": opened_at, "profit_locked": profit_locked,
                "tp_targets": _safe_json_list(saved.get("tp_targets_json"), restored_meta.get("tp_targets") or []),
                "tp_close_pcts": _safe_json_list(saved.get("tp_close_pcts_json"), restored_meta.get("tp_close_pcts") or BOT_TP_CLOSE_DEFAULTS),
                "tp_order_ids": _safe_json_dict(saved.get("tp_order_ids_json"), restored_meta.get("tp_order_ids") or {}),
                "tp_initial_qty": float(saved.get("tp_initial_qty") or restored_meta.get("tp_initial_qty") or qty),
                "tp_done": _safe_json_dict(saved.get("tp_done_json"), restored_meta.get("tp_done") or {}),
                "tp_filled_qty": _safe_json_dict(saved.get("tp_filled_qty_json"), restored_meta.get("tp_filled_qty") or {}),
                "tp1_breakeven_done": bool(saved.get("tp1_breakeven_done") or restored_meta.get("tp1_breakeven_done")),
            })
            with self._trade_meta_lock:
                self._trade_meta[symbol] = restored_meta
            self.log.info(f"[{symbol}] Восстановлена своя позиция после перезапуска: entry={entry_price}, qty={qty}, {'лонг' if is_long else 'шорт'}, TP={tp_price}, SL={sl_price}, profit_locked={profit_locked}.")

    def _maybe_heartbeat(self):
        if cfg.HEARTBEAT_MINUTES <= 0:
            return
        if time.time() - self._last_heartbeat >= cfg.HEARTBEAT_MINUTES * 60:
            self._last_heartbeat = time.time()
            self.tg.notify(f"💓 <b>Бот жив и работает</b>\n━━━━━━━━━━━━━━━\n{self.build_status_summary()}")

    def _persist_runtime_state_safely(self, watched, guards, cooldowns, context: str) -> bool:
        """A transient SQLite failure must be logged, not crash a trading loop."""
        try:
            save_runtime_state(watched, guards, cooldowns, self.log)
            return True
        except Exception:
            self.log.critical(
                "КРИТИЧЕСКИ: runtime-state не сохранён в SQLite (%s); текущая копия остаётся только в памяти",
                context,
                exc_info=True,
            )
            return False

    def _maybe_save_state(self):
        if time.time() - self._last_state_save >= 2:
            self._last_state_save = time.time()
            with self._watched_lock:
                watched_copy = dict(self._watched)
            with self._guards_lock:
                guards_copy = dict(self._position_guards)
            with self._cooldown_lock:
                cooldowns_copy = dict(self._cooldowns)
            self._persist_runtime_state_safely(
                watched_copy, guards_copy, cooldowns_copy, "periodic state snapshot"
            )

    # ---- cooldown -------------------------------------------------------------

    def _is_in_cooldown(self, symbol: str) -> bool:
        with self._cooldown_lock:
            until = self._cooldowns.get(symbol)
            if until is None:
                return False
            if time.time() >= until:
                del self._cooldowns[symbol]
                return False
            return True

    def _set_cooldown(self, symbol: str, minutes: Optional[float] = None):
        duration_min = cfg.COOLDOWN_MINUTES if minutes is None else minutes
        if duration_min <= 0:
            return
        with self._cooldown_lock:
            self._cooldowns[symbol] = time.time() + duration_min * 60
            cooldowns_copy = dict(self._cooldowns)
        with self._watched_lock:
            watched_copy = dict(self._watched)
        with self._guards_lock:
            guards_copy = dict(self._position_guards)
        self._persist_runtime_state_safely(
            watched_copy, guards_copy, cooldowns_copy, f"cooldown {symbol}"
        )
        record_state_event("runtime", "COOLDOWN_SET", symbol, {"until": self._cooldowns.get(symbol)})

    # ---- обнаружение пампа ---------------------------------------------------

    def _get_scan_symbol_pool(self) -> List[str]:
        """Список символов-кандидатов для сканирования входа. Если включён
        режим избранного (⭐ Избранные монеты в Telegram), торгуются ТОЛЬКО
        монеты из этого списка — остальной рынок полностью игнорируется. Сам
        self._symbols (полный список пар, используется для WS-подписки на
        цены) при этом не трогаем — фильтр применяется только здесь, на
        входе, поэтому режим включается/выключается мгновенно, без рестарта
        и без пересоздания подписок."""
        if not is_favorites_mode_enabled():
            return self._symbols
        favorites = set(get_favorite_symbols())
        if not favorites:
            return []
        return [s for s in self._symbols if s in favorites]

    def _scan_for_pumps(self):
        positions = self.client.get_open_positions()
        open_symbols = {p["symbol"] for p in positions}
        open_count = len(open_symbols)

        with self._watched_lock:
            watched_symbols = set(self._watched.keys())

        available_slots = cfg.MAX_OPEN_POSITIONS - open_count - len(watched_symbols)
        if available_slots <= 0:
            return

        candidates = [
            s for s in self._get_scan_symbol_pool()
            if s not in open_symbols and s not in watched_symbols and not self._is_in_cooldown(s)
        ]

        changes: Dict[str, float] = {}
        needs_rest: List[str] = []
        lookback_seconds = cfg.LOOKBACK_MINUTES * 60
        for symbol in candidates:
            change = self.feed.get_change_pct(symbol, lookback_seconds)
            if change is not None:
                changes[symbol] = change
            elif not self.feed.has_recent_data(symbol):
                needs_rest.append(symbol)

        if needs_rest:
            rest_changes = self.client.scan_rest_fallback(needs_rest)
            changes.update(rest_changes)

        pumping = sorted(((s, c) for s, c in changes.items() if c >= cfg.PUMP_THRESHOLD_PCT), key=lambda x: x[1], reverse=True)

        for symbol, change_pct in pumping:
            if available_slots <= 0:
                break

            price = self.feed.get_price(symbol) or self.client.get_last_price_rest(symbol)
            if price is None:
                continue

            now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
            self.log.info(f"[{symbol}] СИГНАЛ: рост {change_pct:.2f}% за последний час ({now}), начинаю следить за разворотом.")
            with self._watched_lock:
                self._watched[symbol] = ReversalTracker(symbol, price, "up", meta={"initial_change_pct": change_pct, "reference_price": price})
            available_slots -= 1

            self.tg.notify(
                f"📡 <b>Обнаружен памп — слежу за разворотом</b>\n━━━━━━━━━━━━━━━\n"
                f"<b>{symbol}</b>\nРост: <b>+{change_pct:.2f}%</b> за последний час\nТекущая цена: {price}\n🕒 {now}\n\n"
                f"{'Лонг' if getattr(cfg, 'ENABLE_LONG_MODE', False) else 'Шорт'} откроется, как только рост остановится."
            )

    # ---- слежение за разворотом роста (вход) ---------------------------------

    def _entry_watch_loop(self):
        self.log.info("Поток слежения за входом запущен.")
        while self._running and self.tg.running and not self._watchdog_stale.is_set():
            try:
                with self._watched_lock:
                    symbols = list(self._watched.keys())

                to_trigger, to_drop_timeout = [], []
                peak_prices: Dict[str, float] = {}
                with self._watched_lock:
                    for symbol in symbols:
                        tracker = self._watched.get(symbol)
                        if tracker is None:
                            continue
                        price_and_ts = self.feed.get_price_and_ts(symbol)
                        if price_and_ts is None:
                            continue
                        price, tick_ts = price_and_ts

                        stopped = tracker.update(price, tick_ts, cfg.STALL_CONFIRMATION_TICKS, cfg.STALL_DROP_PCT)
                        if stopped:
                            to_trigger.append(symbol)
                            peak_prices[symbol] = tracker.extreme_price
                        elif tracker.is_timed_out(cfg.WATCH_MAX_MINUTES):
                            to_drop_timeout.append(symbol)

                    for symbol in to_trigger + to_drop_timeout:
                        self._watched.pop(symbol, None)

                for symbol in to_drop_timeout:
                    self.log.info(f"[{symbol}] Снято с наблюдения по таймауту.")
                    self.tg.notify(f"⌛ <b>Слежение снято</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\nРост так и не остановился за {cfg.WATCH_MAX_MINUTES} мин.")

                for symbol in to_trigger:
                    self._open_short_on_stall(symbol, peak_prices[symbol])

            except Exception as e:
                self.log.exception(f"Ошибка в потоке слежения за входом: {e}")

            time.sleep(0.15)

    def _check_entry_filters(self, symbol: str, peak_price: float) -> Tuple[bool, str, Optional[float]]:
        """Проверяет все ВКЛЮЧЁННЫЕ фильтры входа по свежим свечам с биржи.

        Возвращает (можно_входить, причина, цена_для_повторного_наблюдения):
          - (True, "", None) — все включённые фильтры пройдены, входим;
          - (False, причина, None) — фильтр отклонил вход насовсем в этот раз
            (короткий cooldown, наблюдение снимается);
          - (False, причина, price) — частный случай "вертикальной свечи":
            вход не отменяется, а откладывается — наблюдение перезапускается
            от текущей цены, чтобы дождаться закрытия текущей свечи.
        """
        filters_enabled = any([
            getattr(cfg, "ENABLE_BREAKOUT_FILTER", False),
            getattr(cfg, "ENABLE_TREND_FILTER", False),
            getattr(cfg, "ENABLE_VOLUME_FILTER", False),
            getattr(cfg, "ENABLE_VOLUME_DECLINE_FILTER", False),
            getattr(cfg, "ENABLE_VERTICAL_CANDLE_FILTER", False),
            getattr(cfg, "ENABLE_SHORT_LOW_BOUNCE_FILTER", False),
            getattr(cfg, "ENABLE_LONG_LOW_BOUNCE_FILTER", False),
        ])
        if not filters_enabled:
            return True, "", None

        try:
            candles = self.client.get_recent_candles(symbol, interval=getattr(cfg, "FILTER_CANDLE_INTERVAL", "1"), limit=60)
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось получить свечи для фильтров входа ({e}) — вхожу без доп. проверки на этот раз.")
            return True, "", None

        if len(candles) < 5:
            self.log.debug(f"[{symbol}] Недостаточно свечей для фильтров входа ({len(candles)}) — пропускаю проверку.")
            return True, "", None

        last, prev = candles[-1], candles[-2]

        # ---- 1. Вертикальная свеча: не входить, пока она ещё летит --------
        if getattr(cfg, "ENABLE_VERTICAL_CANDLE_FILTER", False):
            interval_sec = int(getattr(cfg, "FILTER_CANDLE_INTERVAL", "1")) * 60
            candle_age_sec = max(0.0, time.time() - last["start_ms"] / 1000)
            candle_still_open = candle_age_sec < interval_sec
            candle_move_pct = ((last["close"] - last["open"]) / last["open"] * 100) if last["open"] > 0 else 0.0
            threshold = getattr(cfg, "VERTICAL_CANDLE_PCT_THRESHOLD", 5.0)
            if candle_still_open and candle_move_pct >= threshold:
                live_price = self.feed.get_price(symbol) or last["close"]
                return False, (
                    f"текущая свеча ещё летит вертикально (+{candle_move_pct:.1f}%), жду её закрытия"
                ), live_price

        # ---- 2. Провал пробоя: новый хай, но не удержался ------------------
        if getattr(cfg, "ENABLE_BREAKOUT_FILTER", False):
            margin_pct = getattr(cfg, "BREAKOUT_FAIL_MARGIN_PCT", 0.2)
            new_high = last["high"] > prev["high"]
            failed_breakout = last["high"] > 0 and last["close"] < last["high"] * (1 - margin_pct / 100.0)
            if not (new_high and failed_breakout):
                return False, "нет подтверждённого провала пробоя (новый хай не обновлён или закрытие слишком близко к хаю)", None

        # ---- 3. Не шортить сильный тренд -----------------------------------
        if getattr(cfg, "ENABLE_TREND_FILTER", False):
            closes = [c["close"] for c in candles]
            ema20 = calc_ema(closes, 20)
            ema50 = calc_ema(closes, 50)
            if ema20 is not None and ema50 is not None and ema20 > 0:
                margin_pct = getattr(cfg, "TREND_FILTER_MARGIN_PCT", 1.0)
                strong_trend = ema20 > ema50 and last["close"] > ema20 * (1 + margin_pct / 100.0)
                if strong_trend:
                    side_word = "лонг по" if getattr(cfg, "ENABLE_LONG_MODE", False) else "шорт против"
                    return False, f"сильный восходящий тренд (EMA20 > EMA50, цена на {margin_pct:.1f}%+ выше EMA20) — {side_word} тренда пропущен", None

        # ---- 4. Объёмное подтверждение пампа --------------------------------
        if getattr(cfg, "ENABLE_VOLUME_FILTER", False):
            lookback = int(getattr(cfg, "VOLUME_LOOKBACK_CANDLES", 10))
            baseline = candles[-(lookback + 1):-1] if len(candles) > lookback else candles[:-1]
            if baseline:
                avg_vol = sum(c["volume"] for c in baseline) / len(baseline)
                multiplier = getattr(cfg, "VOLUME_SPIKE_MULTIPLIER", 2.0)
                if avg_vol <= 0 or last["volume"] < avg_vol * multiplier:
                    ratio = (last["volume"] / avg_vol) if avg_vol > 0 else 0.0
                    return False, f"нет объёмного подтверждения пампа (объём x{ratio:.1f} от среднего, нужно x{multiplier:.1f})", None

        # ---- 5. Объём должен уже падать после пампа (истощение) -------------
        if getattr(cfg, "ENABLE_VOLUME_DECLINE_FILTER", False):
            peak_window = candles[-6:-1] if len(candles) >= 6 else candles[:-1]
            if peak_window:
                vol_peak = max(c["volume"] for c in peak_window)
                if vol_peak > 0 and last["volume"] >= vol_peak:
                    return False, "объём ещё не начал падать после пампа — вход рано", None

        # ---- 6. ШОРТ: подтверждённый рост от лоя свечи -----------------------
        # Актуально ТОЛЬКО для режима шорт — подтверждает, что цена ещё
        # реально растёт от своего локального дна (памп не выдохся раньше
        # времени) прямо перед входом в шорт на развороте.
        # Использует СВОЙ настраиваемый таймфрейм свечи (может отличаться от
        # FILTER_CANDLE_INTERVAL, которым пользуются остальные фильтры выше).
        if getattr(cfg, "ENABLE_SHORT_LOW_BOUNCE_FILTER", False) and not getattr(cfg, "ENABLE_LONG_MODE", False):
            passed, reason = self._check_low_bounce(
                symbol, candles,
                interval=getattr(cfg, "SHORT_LOW_BOUNCE_CANDLE_INTERVAL", "1"),
                threshold=getattr(cfg, "SHORT_LOW_BOUNCE_PCT", 1.0),
            )
            if not passed:
                return False, reason, None

        # ---- 7. ЛОНГ: подтверждённый рост от лоя свечи -----------------------
        # То же самое, но актуально ТОЛЬКО для режима лонг — страхует от
        # входа, пока цена ещё фактически не оттолкнулась от локального дна
        # на нужную величину, а лишь формально прошла проверку "рост
        # остановился" в ReversalTracker.
        if getattr(cfg, "ENABLE_LONG_LOW_BOUNCE_FILTER", False) and getattr(cfg, "ENABLE_LONG_MODE", False):
            passed, reason = self._check_low_bounce(
                symbol, candles,
                interval=getattr(cfg, "LONG_LOW_BOUNCE_CANDLE_INTERVAL", "1"),
                threshold=getattr(cfg, "LONG_LOW_BOUNCE_PCT", 1.0),
            )
            if not passed:
                return False, reason, None

        return True, "", None

    def _check_low_bounce(self, symbol: str, candles: List[Dict], interval: str, threshold: float) -> Tuple[bool, str]:
        """Общая проверка для фильтров 'рост от лоя свечи' (шорт и лонг):
        текущая цена должна быть минимум на threshold% выше лоя последней
        свечи заданного таймфрейма. Таймфрейм может отличаться от
        FILTER_CANDLE_INTERVAL, которым пользуются остальные фильтры —
        свечи в этом случае подгружаются отдельно."""
        interval = str(interval)
        try:
            if interval == getattr(cfg, "FILTER_CANDLE_INTERVAL", "1"):
                bounce_candles = candles  # тот же таймфрейм — свечи уже загружены выше
            else:
                bounce_candles = self.client.get_recent_candles(symbol, interval=interval, limit=5)
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось получить свечи для фильтра 'рост от лоя' ({e}) — пропускаю эту проверку на этот раз.")
            return True, ""

        if not bounce_candles:
            return True, ""

        bounce_low = bounce_candles[-1]["low"]
        current_price = self.feed.get_price(symbol) or bounce_candles[-1]["close"]
        if bounce_low <= 0:
            return True, ""

        growth_pct = (current_price - bounce_low) / bounce_low * 100.0
        if growth_pct < threshold:
            return False, (
                f"недостаточный рост от лоя свечи ({interval}м): "
                f"+{growth_pct:.2f}% от {bounce_low:g}, нужно от +{fmt_num(threshold)}%"
            )
        return True, ""

    def _open_short_on_stall(self, symbol: str, peak_price: float):
        now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")

        if cfg.DRY_RUN:
            self.log.info(f"[{symbol}] Рост остановился ({now}) — DRY_RUN включён, ордер отправлен не будет.")
            self.tg.notify(f"🛑 <b>Рост остановился</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\n🕒 {now}\nDRY_RUN включён — ордер отправлен не будет.")
            return

        with self._known_lock:
            if symbol in self._known_open_symbols:
                self.log.info(f"[{symbol}] Позиция уже открыта, пропуск.")
                return

        with self._unresolved_lock:
            if symbol in self._unresolved_entries:
                self.log.info(f"[{symbol}] Предыдущий вход ещё не подтверждён биржей — новый вход пропущен, чтобы не задвоить позицию.")
                return

        passed, reason, rearm_price = self._check_entry_filters(symbol, peak_price)
        if not passed:
            if rearm_price is not None:
                # "вертикальная свеча" — не отменяем сигнал, а откладываем его,
                # возобновляя наблюдение от текущей цены до закрытия свечи
                self.log.info(f"[{symbol}] Вход отложен: {reason}")
                self.tg.notify(f"⏳ <b>Вход отложен фильтром</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\n{reason}.\nПродолжаю следить.")
                with self._watched_lock:
                    self._watched[symbol] = ReversalTracker(symbol, rearm_price, "up", meta={"reference_price": peak_price})
            else:
                self.log.info(f"[{symbol}] Вход отменён фильтром: {reason}")
                self.tg.notify(f"🚫 <b>Вход отменён фильтром</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\n{reason}.")
                self._set_cooldown(symbol, minutes=getattr(cfg, "FILTER_REJECT_COOLDOWN_MINUTES", 5))
            return

        long_mode = getattr(cfg, "ENABLE_LONG_MODE", False)
        side_label = "лонг" if long_mode else "шорт"
        self.log.info(f"[{symbol}] Рост остановился ({now}) — открываю {side_label}.")
        self.tg.notify(f"🛑 <b>Рост остановился</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\n🕒 {now}\nОткрываю {side_label}...")

        with self._known_lock:
            if symbol in self._known_open_symbols:
                self.log.info(f"[{symbol}] Позиция уже открыта, пропуск.")
                return

        try:
            equity = self.client.get_equity_usdt()
        except Exception as e:
            self.tg.notify(f"⚠️ [{symbol}] Не удалось получить баланс, сделка пропущена: {e}")
            return
        if equity <= 0:
            self.log.warning("Equity <= 0, торговля невозможна.")
            return

        entry_price_hint = self.feed.get_price(symbol)
        if entry_price_hint is not None and entry_price_hint > peak_price:
            self.log.info(f"[{symbol}] Пока готовили сделку, цена обновила максимум ({entry_price_hint} > {peak_price}) — рост не остановился, возобновляю наблюдение вместо входа.")
            with self._watched_lock:
                self._watched[symbol] = ReversalTracker(symbol, entry_price_hint, "up", meta={"reference_price": peak_price})
            return

        order = self.client.open_short(symbol, equity, entry_price_hint=entry_price_hint)
        if order is None:
            return
        if order.get("_post_only_unresolved") or order.get("_entry_unresolved"):
            # Исход входа неизвестен: ордер мог остаться активным или исполниться
            # позже. Не забываем его — берём под наблюдение (см. _resolve_unresolved_entries).
            self._register_unresolved_entry(symbol, order, long_mode)
            return

        self._register_opened_bot_position(symbol, order, long_mode)

    def _register_opened_bot_position(self, symbol: str, order: Dict, long_mode: bool, adopted_note: str = ""):
        """Регистрирует фактически открытую позицию бота: trade_meta, реестр
        bot_positions в SQLite, _known_open_symbols, первичная установка TP1-TP4
        и уведомление. Вынесено из _open_short_on_stall, чтобы тем же путём
        брать под управление позицию, вход которой был «неопределённым»
        (adopted_note добавляется в уведомление)."""
        # Регистрируем позицию как "свою" СРАЗУ, используя оценку
        # entry_price/qty из самого ответа биржи на ордер (без дополнительных
        # запросов — быстро). Порядок важен: сначала trade_meta и реестр в
        # БД, ТОЛЬКО ПОТОМ добавляем символ в _known_open_symbols — иначе
        # параллельный проход _check_closed_positions (он идёт в основном
        # цикле независимо от этого потока) мог успеть увидеть символ живым
        # на бирже, но ещё не найти его в _trade_meta, и ошибочно исключить
        # только что открытую СВОЮ позицию из отслеживания как будто она
        # ручная — бот бы её больше не защищал.
        entry_price, qty = order["_entry_price"], order["_qty"]
        with self._trade_meta_lock:
            self._trade_meta[symbol] = {
                "entry_price": entry_price, "qty": qty, "is_long": long_mode,
                "margin_usdt": order["_margin_usdt"], "tp_price": order["_tp_price"],
                "sl_price": order.get("_sl_price"), "tick_size": order["_tick_size"], "opened_at": time.time(),
                "profit_locked": False,
            }
        # Сразу фиксируем конфигурацию 4 тейков для этой конкретной сделки.
        # Это не зависит от последующих изменений настроек в Telegram и
        # переживает restart/redeploy через bot_positions.
        tp_moves, tp_closes = get_bot_tp_config()
        tp_tick = float(order["_tick_size"] or 0)
        tp_targets = [self.client.round_step(entry_price * (1 + m / 100.0) if long_mode else entry_price * (1 - m / 100.0), tp_tick) for m in tp_moves]
        self._trade_meta[symbol].update({
            "tp_targets": tp_targets, "tp_close_pcts": tp_closes,
            "tp_order_ids": {}, "tp_initial_qty": qty, "tp_done": {}, "tp_filled_qty": {}, "tp1_breakeven_done": False,
            "tp_price": tp_targets[3],
        })
        if not persist_bot_position_with_retry(symbol, self._trade_meta[symbol], self.log):
            self.log.critical(
                "[%s] КРИТИЧЕСКИ: позиция открыта на бирже, но её состояние не удалось сохранить в SQLite; "
                "восстановление после рестарта не гарантировано.",
                symbol,
            )
            try:
                self.tg.notify(
                    f"🚨 <b>{symbol}: критическая ошибка сохранения БД</b>\n"
                    "Позиция открыта, но запись bot_positions не подтверждена после повторных попыток. "
                    "Проверь SQLite/Volume в Railway; не перезапускай бота до проверки защиты позиции."
                )
            except Exception:
                self.log.exception("[%s] Не удалось отправить alert о сбое сохранения позиции", symbol)

        with self._known_lock:
            self._known_open_symbols.add(symbol)

        # Уточняем entry_price/qty по факту исполнения на бирже (может
        # немного отличаться от оценки в ответе на сам ордер из-за
        # проскальзывания) — сама сделка уже открыта, эта задержка (до ~1.2
        # сек) больше не в критическом пути открытия, только в уточнении
        # учётных данных о ней.
        expected_pos_side = "Buy" if long_mode else "Sell"
        position_lookup_confirmed = False
        for attempt in range(3):
            try:
                # The entry direction is known here. Never select an arbitrary
                # side when the account uses hedge mode.
                live_pos = self.client.get_position_strict(symbol, side=expected_pos_side)
                position_lookup_confirmed = True
            except Exception:
                self.log.exception(
                    "[%s] Не удалось подтвердить позицию %s после входа; "
                    "сохраняю исходные данные ордера и откладываю уточнение.",
                    symbol, expected_pos_side,
                )
                live_pos = None
            if live_pos and float(live_pos.get("avgPrice") or 0) > 0:
                entry_price = float(live_pos["avgPrice"])
                qty = float(live_pos.get("size") or qty)
                break
            # A confirmed empty result is different from an API failure.
            # Keep the original order response values and retry; do not infer
            # that the position is closed or belongs to the opposite side.
            time.sleep(0.4)

        with self._trade_meta_lock:
            if symbol in self._trade_meta:
                self._trade_meta[symbol]["entry_price"] = entry_price
                self._trade_meta[symbol]["qty"] = qty
                tp_moves, tp_closes = get_bot_tp_config()
                tp_tick = float(self._trade_meta[symbol].get("tick_size") or 0)
                self._trade_meta[symbol]["tp_targets"] = [self.client.round_step(entry_price * (1 + m / 100.0) if long_mode else entry_price * (1 - m / 100.0), tp_tick) for m in tp_moves]
                self._trade_meta[symbol]["tp_close_pcts"] = tp_closes
                self._trade_meta[symbol]["tp_initial_qty"] = qty
                self._trade_meta[symbol]["tp_price"] = self._trade_meta[symbol]["tp_targets"][3]
                snapshot = dict(self._trade_meta[symbol])
            else:
                snapshot = None
        if snapshot is not None:
            if not persist_bot_position_with_retry(symbol, snapshot, self.log):
                self.log.critical(
                    "[%s] Не удалось сохранить уточнённые entry_price/qty в SQLite после повторных попыток.",
                    symbol,
                )
                try:
                    self.tg.notify(
                        f"🚨 <b>{symbol}: не удалось обновить состояние позиции в БД</b>\n"
                        "Проверь SQLite/Volume в Railway. Биржевая позиция продолжает существовать."
                    )
                except Exception:
                    self.log.exception("[%s] Не удалось отправить alert об ошибке обновления БД", symbol)

        # КРИТИЧЕСКИЙ ЭТАП: не ждём фонового guard-loop для TP1-TP3.
        # Сразу после фактического fill синхронно выставляем всю 4-TP схему
        # и несколько раз подтверждаем её на бирже. Если Bybit временно
        # недоступен, позиция остаётся зарегистрированной как СВОЯ и
        # reconciliation продолжит попытки, но мы не выдаём ложное
        # сообщение, будто вся защита уже установлена.
        protection_ready = False
        protection_state = {}
        if snapshot is not None and not cfg.DRY_RUN:
            for protection_attempt in range(4):
                try:
                    live_for_protection = self.client.get_position_strict(
                        symbol, side=("Buy" if long_mode else "Sell")
                    )
                    if not live_for_protection or float(live_for_protection.get("size") or 0) <= 0:
                        break
                    with self._trade_meta_lock:
                        current_meta = dict(self._trade_meta.get(symbol) or snapshot)
                        current_meta["tp_last_reconcile"] = 0.0
                    protection_state = self._ensure_bot_multi_tps(symbol, current_meta, live_for_protection) or {}
                    with self._trade_meta_lock:
                        if symbol in self._trade_meta:
                            self._trade_meta[symbol].update({
                                "entry_price": float(live_for_protection.get("avgPrice") or self._trade_meta[symbol].get("entry_price") or 0),
                                "qty": float(live_for_protection.get("size") or self._trade_meta[symbol].get("qty") or 0),
                                "tp_targets": protection_state.get("targets", self._trade_meta[symbol].get("tp_targets", [])),
                                "tp_close_pcts": protection_state.get("close_pcts", self._trade_meta[symbol].get("tp_close_pcts", [])),
                                "tp_order_ids": protection_state.get("order_ids", self._trade_meta[symbol].get("tp_order_ids", {})),
                                "tp_done": protection_state.get("done", self._trade_meta[symbol].get("tp_done", {})),
                                "tp_filled_qty": protection_state.get("filled_qty", self._trade_meta[symbol].get("tp_filled_qty", {})),
                                "tp_price": (protection_state.get("targets") or self._trade_meta[symbol].get("tp_targets") or [0,0,0,0])[3],
                            })
                            snapshot = dict(self._trade_meta[symbol])
                    enabled_now = get_bot_tp_enabled()
                    ids_now = protection_state.get("order_ids") or snapshot.get("tp_order_ids") or {}
                    done_now = protection_state.get("done") or snapshot.get("tp_done") or {}
                    verified_now = protection_state.get("verified") or snapshot.get("tp_verified") or {}
                    protection_ready = _bot_tp_protection_ready(
                        enabled_now, done_now, verified_now, bool(protection_state.get("tp4_ok"))
                    )
                    if protection_ready:
                        if persist_bot_position_with_retry(symbol, snapshot, logger=self.log):
                            break
                        self.log.critical(
                            "[%s] TP/SL подтверждены биржей, но состояние позиции не записано в SQLite; "
                            "повторяю проверку защиты, чтобы не оставить позицию без восстанавливаемого состояния.",
                            symbol,
                        )
                except Exception as e:
                    self.log.warning(f"[{symbol}] Первичная установка 4-TP: попытка {protection_attempt + 1}/4 не завершена: {e}")
                time.sleep(0.25 * (protection_attempt + 1))

        sl_pct = getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) if long_mode else getattr(cfg, "FIXED_STOP_LOSS_PCT", 0)
        tp_pct = getattr(cfg, "LONG_TAKE_PROFIT_PCT", cfg.TAKE_PROFIT_PCT) if long_mode else cfg.TAKE_PROFIT_PCT
        tp_sign = "+" if long_mode else "-"
        sl_sign = "-" if long_mode else "+"
        sl_line = f"\nСтоп-лосс: {order['_sl_price']} ({sl_sign}{sl_pct}% от входа)" if order.get("_sl_price") is not None else ""
        protection_line = (
            "\n🛡️ Защита: SL + TP1 + TP2 + TP3 + TP4 подтверждены"
            if protection_ready else
            "\n⚠️ Защита не подтверждена полностью — бот продолжает повторную установку TP/SL"
        )
        self.tg.notify(
            f"{'🟢 <b>Открыт лонг</b>' if long_mode else '🔻 <b>Открыт шорт</b>'}\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\n"
            f"Объём: {qty}\nЦена входа: ~{entry_price}\n"
            f"Маржа: {order['_margin_usdt']:.2f} USDT · Плечо: {cfg.LEVERAGE}x\n"
            f"Тейк-профит: {order['_tp_price']} ({tp_sign}{tp_pct}%){sl_line}{protection_line}"
            f"{adopted_note}"
        )


    # ---- входы с неизвестным исходом ------------------------------------------

    _UNRESOLVED_ACTIVE_STATUSES = ("new", "partiallyfilled", "untriggered", "created")

    def _register_unresolved_entry(self, symbol: str, info: Dict, long_mode: bool):
        """Запоминает вход, исход которого неизвестен. Раньше такой вход
        возвращался как None и забывался: если лимитный ордер оставался
        активным (отмена не прошла) или исполнялся позже, позиция появлялась
        без записи в реестре — бот её не защищал и не вёл."""
        with self._unresolved_lock:
            self._unresolved_entries[symbol] = {
                "link_id": info.get("_link_id"),
                "order_id": info.get("_order_id"),
                "side": info.get("_side") or ("Buy" if long_mode else "Sell"),
                "long_mode": bool(long_mode),
                "ts": time.time(),
                "last_cancel_ts": 0.0,
                "cancel_alerted": False,
            }
        self.log.error(f"[{symbol}] Вход не подтверждён биржей (link={info.get('_link_id')}, order={info.get('_order_id')}); беру под наблюдение.")
        try:
            self.tg.notify(
                f"⚠️ <b>{symbol}</b>: исход входа не подтверждён биржей (ответ потерян или статус неизвестен). "
                "Новых входов по символу не делаю; слежу за ордером и, если позиция появится, возьму её под управление."
            )
        except Exception:
            self.log.exception("[%s] Не удалось отправить уведомление о неподтверждённом входе", symbol)

    def _resolve_unresolved_entries(self):
        """Доводит до конца входы с неизвестным исходом: снимает всё ещё активный
        ордер и берёт под управление позицию, если она появилась. Вызывается
        из цикла охраны позиций; не чаще раза в 2 секунды."""
        now = time.time()
        if now - self._unresolved_last_check < 2.0:
            return
        self._unresolved_last_check = now
        with self._unresolved_lock:
            items = list(self._unresolved_entries.items())
        for symbol, info in items:
            try:
                finished = self._resolve_one_unresolved_entry(symbol, info, now)
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось выяснить исход неподтверждённого входа: {e}")
                finished = False
            if finished:
                with self._unresolved_lock:
                    self._unresolved_entries.pop(symbol, None)

    def _resolve_one_unresolved_entry(self, symbol: str, info: Dict, now: float) -> bool:
        """True — вход выяснен (позиция взята под управление либо входа нет)."""
        age = now - float(info.get("ts") or now)
        long_mode = bool(info.get("long_mode"))
        pos_side = info.get("side") or ("Buy" if long_mode else "Sell")

        with self._known_lock:
            if symbol in self._known_open_symbols:
                return True  # позицию уже ведёт обычный путь

        # 1) Состояние самого ордера.
        state = None
        lookup_ok = True
        try:
            if info.get("order_id"):
                state = self.client.get_order_state(symbol, str(info["order_id"]))
            if not state and info.get("link_id"):
                state = self.client.get_order_state_by_link(symbol, str(info["link_id"]))
        except Exception as e:
            lookup_ok = False
            self.log.debug(f"[{symbol}] Статус неподтверждённого входа не получен: {e}")
        status = str((state or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()

        if status in self._UNRESOLVED_ACTIVE_STATUSES:
            # Ордер всё ещё может исполниться — снимаем остаток (не чаще раза в 10 с).
            if now - float(info.get("last_cancel_ts") or 0) >= 10.0:
                info["last_cancel_ts"] = now
                try:
                    self.client.session.cancel_order(
                        category=cfg.CATEGORY, symbol=symbol,
                        orderId=str(state.get("orderId") or info.get("order_id")),
                    )
                except Exception as e:
                    self.log.debug(f"[{symbol}] Отмена неподтверждённого входа не прошла: {e}")
            if age > 300 and not info.get("cancel_alerted"):
                info["cancel_alerted"] = True
                self.tg.notify(f"🚨 <b>{symbol}</b>: неподтверждённый входной ордер всё ещё активен {int(age)} с и не снимается. Проверь и сними его вручную на Bybit.")
            return False

        # 2) Ордер завершён либо не найден: итог определяет позиция на бирже.
        live = self.client.get_position_strict(symbol, side=pos_side)  # ошибка API -> повтор позже
        if live and float(live.get("size") or 0) > 0 and float(live.get("avgPrice") or 0) > 0:
            order_info = self.client.order_info_from_live_position(symbol, live, long_mode)
            self._register_opened_bot_position(
                symbol, order_info, long_mode,
                adopted_note="\n🔎 Вход был в неопределённом состоянии — позиция найдена на бирже и взята под управление.",
            )
            return True

        if not lookup_ok:
            if age > 1800:
                self.tg.notify(f"⚠️ <b>{symbol}</b>: исход входа так и не удалось выяснить за 30 минут; позиции на бирже нет. Наблюдение за этим входом прекращено.")
                return True
            return False
        if state is None:
            if age < 60:
                return False  # ордер мог ещё не попасть в выдачу биржи
            self.log.warning(f"[{symbol}] Неподтверждённый вход: ордер не найден и позиции нет — входа не было.")
            self.tg.notify(f"ℹ️ <b>{symbol}</b>: неподтверждённый вход не состоялся (ордер не найден, позиции нет).")
            return True
        try:
            cum = float(state.get("cumExecQty") or 0)
        except (TypeError, ValueError):
            cum = 0.0
        if cum > 0 and age < 120:
            return False  # исполнялся, но позиция может запаздывать в выдаче
        if cum > 0:
            self.tg.notify(f"ℹ️ <b>{symbol}</b>: неподтверждённый вход исполнился, но позиции уже нет (закрыта стопом/тейком).")
        else:
            self.log.info(f"[{symbol}] Неподтверждённый вход не исполнился и снят; позиции нет.")
        return True

    # ---- управление открытой позицией ----------------------------------------

    def _position_guard_loop(self):
        self.log.info("Поток управления позициями запущен.")
        while self._running and self.tg.running and not self._watchdog_stale.is_set():
            try:
                # Сначала выясняем входы с неизвестным исходом: найденная позиция
                # должна попасть в _known_open_symbols до обхода ниже.
                try:
                    self._resolve_unresolved_entries()
                except Exception:
                    self.log.exception("Ошибка при выяснении неподтверждённых входов")

                with self._known_lock:
                    symbols = list(self._known_open_symbols)

                for symbol in symbols:
                    self._manage_position(symbol)

            except Exception as e:
                self.log.exception(f"Ошибка в потоке управления позициями: {e}")

            time.sleep(0.15)

    def _ensure_bot_multi_tps(self, symbol: str, meta: Dict, live_pos: Dict) -> Dict:
        """Идемпотентно поддерживает 4 независимые цели для СВОЕЙ позиции.

        TP1-TP3 — отдельные reduce-only LIMIT, поэтому они не меняют друг друга.
        TP4 — единственный Full takeProfit позиции и всегда закрывает весь
        оставшийся объём. Если API/бот временно не ответил, следующий цикл
        повторяет только отсутствующую операцию, не создавая дубликат.
        """
        now = time.time()
        last_reconcile = float(meta.get("tp_last_reconcile") or 0)
        # _manage_position работает часто (≈0.15 сек), но TP-реконсиляция не
        # должна превращаться в лавину REST-запросов. Двухсекундный интервал
        # достаточно быстрый для защиты и одновременно сильно снижает
        # нагрузку на Bybit.
        if now - last_reconcile < 2.0:
            # Do not report protection as verified merely because the previous
            # reconcile is recent. Preserve the last actual verification result.
            return {
                "targets": list(meta.get("tp_targets") or []),
                "close_pcts": list(meta.get("tp_close_pcts") or []),
                "tp4_ok": bool(meta.get("tp4_ok", False)),
                "order_ids": dict(meta.get("tp_order_ids") or {}),
                "done": dict(meta.get("tp_done") or {}),
                "verified": dict(meta.get("tp_verified") or {}),
            }
        meta["tp_last_reconcile"] = now

        entry = float(live_pos.get("avgPrice") or meta.get("entry_price") or 0)
        live_qty = float(live_pos.get("size") or meta.get("qty") or 0)
        if not math.isfinite(entry) or not math.isfinite(live_qty) or entry <= 0 or live_qty <= 0:
            self.log.error(f"[{symbol}] Некорректные entry/qty для TP: entry={entry!r}, qty={live_qty!r}; новые ордера не создаю.")
            return {}
        side = "LONG" if bool(meta.get("is_long")) else "SHORT"
        enabled = get_bot_tp_enabled()
        tick_size = float(meta.get("tick_size") or self.client.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
        qty_step = float(self.client.get_qty_step(symbol))

        try:
            targets = [float(x) for x in (meta.get("tp_targets") or [])]
        except (TypeError, ValueError):
            targets = []
        try:
            closes = [float(x) for x in (meta.get("tp_close_pcts") or [])]
        except (TypeError, ValueError):
            closes = []
        if len(targets) != 4 or len(closes) != 4:
            moves, cfg_closes = get_bot_tp_config()
            targets = [self.client.round_step(entry * (1 + m / 100.0) if side == "LONG" else entry * (1 - m / 100.0), tick_size) for m in moves]
            closes = cfg_closes
        else:
            # Если старая/повреждённая БД содержит пересекающиеся цели или
            # сумму закрытий >=100%, не ставим потенциально конфликтующие
            # ордера — безопасно пересобираем план из текущих валидных настроек.
            stored_moves = []
            for t in targets:
                try:
                    t = float(t)
                    stored_moves.append(abs(t - entry) / entry * 100.0)
                except (TypeError, ValueError):
                    stored_moves = []
                    break
            if len(stored_moves) != 4 or _bot_tp_validate_moves(stored_moves, enabled) or _bot_tp_validate_closes(closes, enabled):
                moves, cfg_closes = get_bot_tp_config()
                targets = [self.client.round_step(entry * (1 + m / 100.0) if side == "LONG" else entry * (1 - m / 100.0), tick_size) for m in moves]
                closes = cfg_closes
            meta["tp_targets"] = targets
            meta["tp_close_pcts"] = closes
        # Сохраняем цели от первоначального фактического входа. При
        # изменении объёма у bot-позиции новые цели не пересчитываются.
        targets = [self.client.round_step(x, tick_size) for x in targets]
        # TP4 может быть изменён вручную между получением live_pos и этим
        # циклом. Перед любым изменением читаем позицию заново; при ошибке
        # чтения запрещаем обновлять TP4 по устаревшему снимку.
        tp4_manual_override = bool(meta.get("tp4_manual_override", False))
        tp4_state_confirmed = False
        tp4_live_position = None
        try:
            tp4_live_position = self.client.get_position_strict(
                symbol, side=("Buy" if side == "LONG" else "Sell")
            )
            tp4_state_confirmed = bool(
                tp4_live_position and float(tp4_live_position.get("size") or 0) > 0
            )
        except Exception as _tp4_read_error:
            self.log.warning(
                f"[{symbol}] Не удалось подтвердить актуальный TP4; не буду менять его по устаревшему снимку: {_tp4_read_error}"
            )
        try:
            exchange_tp4 = float((tp4_live_position or {}).get("takeProfit") or 0) if tp4_state_confirmed else 0.0
        except (TypeError, ValueError, OverflowError):
            exchange_tp4 = 0.0
            tp4_state_confirmed = False
        if tp4_state_confirmed and math.isfinite(exchange_tp4) and exchange_tp4 > 0:
            old_tp4 = float(targets[3])
            tp4_tol = max(tick_size * 0.5, abs(exchange_tp4) * 1e-8, 1e-12)
            if abs(exchange_tp4 - old_tp4) > tp4_tol:
                tp4_manual_override = True
                meta["tp4_manual_override"] = True
                targets[3] = self.client.round_step(exchange_tp4, tick_size)
                self.log.info(f"[{symbol}] Обнаружен ручной перенос TP4 на бирже: принимаю цену {targets[3]} и не возвращаю старую.")
            elif tp4_manual_override:
                targets[3] = self.client.round_step(exchange_tp4, tick_size)
        # После округления к tickSize две соседние цели на очень дешёвых
        # инструментах могут схлопнуться в одну цену. Такой план нельзя
        # выставлять: TP1/TP2/TP3 тогда фактически конфликтуют. В этом случае
        # пересобираем цели из настроек с минимально допустимой проверкой.
        if not _bot_tp_rounded_targets_ordered(targets, enabled, side) and not tp4_manual_override:
            return {}
        # При ручном переносе TP4 его цена может намеренно оказаться ближе TP3.
        # Сохраняем пользовательскую цену, но продолжаем обслуживать TP1–TP3.
        meta["tp_targets"] = targets

        try:
            initial_qty = float(meta.get("tp_initial_qty") or 0)
        except (TypeError, ValueError):
            initial_qty = 0
        if initial_qty <= 0:
            initial_qty = live_qty
            meta["tp_initial_qty"] = initial_qty

        order_ids = dict(meta.get("tp_order_ids") or {})
        done = dict(meta.get("tp_done") or {})
        verified = {}
        # Ключи TP, для которых замена заблокирована (старый ордер не удалось
        # подтверждённо снять). В этой функции плана-замены нет, поэтому набор
        # изначально пуст; он обязан быть определён, иначе цикл TP1-TP3 ниже
        # падает с NameError на первой же итерации.
        blocked_tp_replacements = set()
        filled_qty = {}
        for k, v in (meta.get("tp_filled_qty") or {}).items():
            try:
                fv = float(v)
                if str(k) in {"1", "2", "3"} and math.isfinite(fv) and fv > 0:
                    filled_qty[str(k)] = fv
            except (TypeError, ValueError):
                pass

        # Сначала TP4: это страховочный Full-TP. Он никогда не конкурирует
        # с TP1-TP3 на более ранних ценах.
        tp4_ok = False
        current_tp4 = exchange_tp4 if tp4_state_confirmed else 0.0
        if current_tp4 > 0:
            tol = max(tick_size * 0.5, abs(targets[3]) * 1e-8, 1e-12)
            tp4_ok = abs(current_tp4 - targets[3]) <= tol
        if not tp4_ok and tp4_state_confirmed:
            tp4_ok = bool(self.client.update_take_profit_verified(symbol, targets[3], side))
        elif not tp4_state_confirmed:
            tp4_ok = False
        meta["tp4_ok"] = bool(tp4_ok)

        # TP1-TP3: количество считается от исходного объёма, а не от текущего.
        # Поэтому TP2 никогда не "съедает" процент TP1, а reduceOnly не даст
        # ордеру закрыть больше реально оставшейся позиции.
        active_orders = None
        try:
            active_orders = self.client.get_open_orders_all()
        except Exception as e:
            self.log.debug(f"[{symbol}] Не удалось получить список активных TP-ордеров: {e}")
        live_idx_raw = live_pos.get("positionIdx")
        try:
            live_idx = int(live_idx_raw) if live_idx_raw is not None and str(live_idx_raw).strip() != "" else 0
        except (TypeError, ValueError, OverflowError):
            live_idx = None
        if active_orders is not None:
            active_orders = [o for o in active_orders if _tp_order_matches_position(o, symbol, side, live_idx)]
        active_by_link = {str(o.get("orderLinkId")): o for o in (active_orders or []) if o.get("orderLinkId")}
        # Detect a user-amended TP1–TP3 price on the exchange and adopt it into
        # persisted targets. Otherwise a later recovery (e.g. lost orderId) could
        # search for the old price and recreate the TP at its previous location.
        for _i in range(1, 4):
            _key = str(_i)
            _saved_oid = str(order_ids.get(_key) or "")
            # Never infer a TP stage from a stored orderId alone: a stale or
            # corrupted DB mapping could point TP1 at TP2 (or at another order
            # on the same position). Only inspect a live order after both its
            # position identity and its stage-specific link prefix are verified.
            _candidate = next((o for o in (active_orders or [])
                               if _tp_order_matches_position(o, symbol, side, live_idx)
                               and str(o.get("orderLinkId") or "").startswith(f"btp{_i}-")
                               and (( _saved_oid and str(o.get("orderId") or "") == _saved_oid)
                                    or not _saved_oid)), None)
            if _saved_oid and _candidate is None:
                # Do not adopt a price from a different stage when a persisted
                # ID is stale. The dedicated reconciliation below will validate
                # that ID and recover this TP by its own prefix if possible.
                pass
            if _candidate is None:
                continue
            try:
                _live_price = float(_candidate.get("price") or _candidate.get("triggerPrice") or 0)
                _planned_price = float(targets[_i - 1])
            except (TypeError, ValueError, OverflowError):
                continue
            _tol = max(tick_size * 0.5, abs(_planned_price) * 1e-8, 1e-12)
            if math.isfinite(_live_price) and _live_price > 0 and abs(_live_price - _planned_price) > _tol:
                targets[_i - 1] = self.client.round_step(_live_price, tick_size)
                self.log.info(f"[{symbol}] TP{_i} вручную передвинут на бирже: сохраняю цену {_live_price}, не создаю возвратный тейк.")
        meta["tp_targets"] = targets
        active_by_link = {str(o.get("orderLinkId")): o for o in (active_orders or []) if o.get("orderLinkId")}

        for i in range(1, 4):
            key = str(i)
            if not enabled[i-1]:
                oid_disabled = str(order_ids.get(key) or "")
                candidates_disabled = []
                # Only orders already validated against this exact position leg
                # may be cancelled. Keep the saved ID until the exchange confirms
                # a terminal state; a successful cancel ACK alone is insufficient.
                if active_orders is not None:
                    candidates_disabled = [
                        o for o in active_orders
                        if str(o.get("orderLinkId") or "").startswith(f"btp{i}-")
                    ]
                candidate_ids = ([oid_disabled] if oid_disabled else [])
                candidate_ids.extend(
                    str(o.get("orderId")) for o in candidates_disabled
                    if o.get("orderId") and str(o.get("orderId")) not in candidate_ids
                )
                unresolved = []
                if active_orders is None and not oid_disabled:
                    verified[key] = False
                    continue
                for cancel_id in candidate_ids:
                    resolved = False
                    try:
                        state_before = self.client.get_order_state(symbol, cancel_id)
                        if not state_before:
                            unresolved.append(cancel_id)
                            continue
                        # A stale/corrupt DB ID must not cause cancellation of an
                        # unrelated order. Only our TP link and exact live leg qualify.
                        if (not _tp_order_matches_position(state_before, symbol, side, live_idx)
                                or not str(state_before.get("orderLinkId") or "").startswith(f"btp{i}-")):
                            self.log.warning(f"[{symbol}] TP{i}: сохранённый orderId {cancel_id} не совпадает с позицией/ордером; чужой ордер не трогаю")
                            # Definitive identity mismatch: forget the stale local
                            # reference, but never cancel the exchange order.
                            resolved = True
                            continue
                        status_before = str((state_before or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                        cum_before = float((state_before or {}).get("cumExecQty") or 0)
                        if math.isfinite(cum_before) and cum_before > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), cum_before)
                        if status_before == "filled":
                            done[key] = True
                            resolved = True
                        elif status_before in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                            resolved = True
                        elif state_before:
                            self.client.session.cancel_order(category=cfg.CATEGORY, symbol=symbol, orderId=cancel_id)
                            state_after = self.client.get_order_state(symbol, cancel_id)
                            status_after = str((state_after or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                            cum_after = float((state_after or {}).get("cumExecQty") or 0)
                            if math.isfinite(cum_after) and cum_after > 0:
                                filled_qty[key] = max(filled_qty.get(key, 0.0), cum_after)
                            if status_after == "filled":
                                done[key] = True
                                resolved = True
                            elif status_after in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                                resolved = True
                    except Exception as e:
                        self.log.debug(f"[{symbol}] Не удалось подтвердить отмену отключённого TP{i} {cancel_id}: {e}")
                    if not resolved:
                        unresolved.append(cancel_id)
                if unresolved:
                    order_ids[key] = unresolved[0]
                    verified[key] = False
                else:
                    order_ids.pop(key, None)
                    verified[key] = active_orders is not None or bool(candidate_ids)
                continue
            if done.get(key):
                verified[key] = True
                continue
            if key in blocked_tp_replacements:
                verified[key] = False
                continue
            oid = order_ids.get(key)
            existing = None
            if oid:
                # Сначала используем единый список активных ордеров — это
                # дешевле и надёжнее, чем три отдельных REST-запроса.
                active_known = next((o for o in active_orders or [] if str(o.get("orderId") or "") == str(oid) and o.get("symbol") == symbol), None)
                if active_known is not None and not str(active_known.get("orderLinkId") or "").startswith(f"btp{i}-"):
                    self.log.warning(f"[{symbol}] Сохранённый ID для bot TP{i} указывает на другой этап; восстанавливаю только по префиксу btp{i}.")
                    order_ids.pop(key, None)
                    oid = None
                    active_known = None
                if active_known is not None:
                    status = str(active_known.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                    try:
                        known_cum = float(active_known.get("cumExecQty") or 0)
                        if math.isfinite(known_cum) and known_cum > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), known_cum)
                    except (TypeError, ValueError, OverflowError):
                        pass
                    if status in ("new", "partiallyfilled", "untriggered", "created"):
                        verified[key] = True
                        continue
                    if status == "filled":
                        done[key] = True
                        verified[key] = True
                        continue
                    if status in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                        oid = None
                        order_ids.pop(key, None)
                    else:
                        # Unknown state must never be treated as confirmed.
                        continue
                elif oid:
                    # Отсутствие из active-list ещё не означает fill: проверяем
                    # конкретный orderId. При ошибке API состояние неизвестно,
                    # поэтому НОВЫЙ ордер не создаём.
                    try:
                        existing = self.client.get_order_state(symbol, str(oid))
                    except Exception as e:
                        self.log.debug(f"[{symbol}] TP{i} {oid}: состояние неизвестно, жду следующий цикл: {e}")
                        continue
                    if not existing:
                        # Ни active-list, ни order-history ещё не дали
                        # окончательного ответа. Это НЕ равно cancelled.
                        # Новый TP поверх такого ордера создавать запрещено.
                        continue
                    if (not _tp_order_matches_position(existing, symbol, side, live_idx)
                            or not str(existing.get("orderLinkId") or "").startswith(f"btp{i}-")):
                        self.log.warning(f"[{symbol}] Bot TP{i}: сохранённый orderId не подтверждён как ордер этого этапа; жду сверки, не создаю замену.")
                        continue
                    status = str(existing.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                    try:
                        known_cum = float(existing.get("cumExecQty") or 0)
                        if math.isfinite(known_cum) and known_cum > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), known_cum)
                    except (TypeError, ValueError, OverflowError):
                        pass
                    if status == "filled":
                        done[key] = True
                        verified[key] = True
                        continue
                    if status in ("new", "partiallyfilled", "untriggered", "created"):
                        verified[key] = True
                        continue
                    if status in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                        oid = None
                        order_ids.pop(key, None)
                        continue
                    # Неизвестный финальный статус — безопаснее подождать,
                    # чем создавать второй reduce-only ордер.
                    continue
            # Восстанавливаем ордер по префиксу после рестарта/потери БД.
            if not oid:
                if active_orders is None:
                    continue  # список состояния недоступен — не рискуем дублем
                prefix = f"btp{i}-"
                candidates = [
                    o for o in active_orders
                    if str(o.get("orderLinkId") or "").startswith(prefix) and o.get("orderId")
                ]
                if len(candidates) > 1:
                    verified[key] = False
                    self.log.error(
                        f"[{symbol}] Найдено несколько активных ордеров btp{i} без сохранённого ID; "
                        "новый TP не создаю до сверки."
                    )
                    continue
                if len(candidates) == 1:
                    existing = candidates[0]
                    status_existing = str(existing.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                    oid = existing.get("orderId")
                    try:
                        live_price = float(existing.get("price") or existing.get("triggerPrice") or 0)
                    except (TypeError, ValueError, OverflowError):
                        live_price = 0.0
                    if status_existing == "filled":
                        done[key] = True
                        verified[key] = True
                        continue
                    if status_existing in ("new", "partiallyfilled", "untriggered", "created") and oid:
                        if not math.isfinite(live_price) or live_price <= 0:
                            verified[key] = False
                            continue
                        old_saved_targets = meta.get("tp_targets") or []
                        try:
                            old_price = float(old_saved_targets[i-1])
                        except (TypeError, ValueError, IndexError, OverflowError):
                            old_price = float(targets[i-1])
                        move_tol = max(tick_size * 0.5, abs(old_price) * 1e-8, 1e-12)
                        if abs(live_price - old_price) > move_tol:
                            targets[i-1] = self.round_step(live_price, tick_size)
                            self.log.info(f"[{symbol}] Восстановил btp{i} после потери ID: сохраняю фактическую цену {targets[i-1]}.")
                        order_ids[key] = str(oid)
                        verified[key] = True
                        continue
                    verified[key] = False
                    continue
            desired_qty = self.client.round_step(initial_qty * closes[i-1] / 100.0, qty_step)
            already_filled = filled_qty.get(key, 0.0)
            qty_target = self.client.round_step(max(0.0, desired_qty - already_filled), qty_step)
            if qty_target <= 0:
                done[key] = True
                verified[key] = True
                continue
            # Если ACK создания потерялся и orderId не попал в БД, сначала
            # восстанавливаем недавний btp-ордер из истории. Никогда не
            # создаём новый reduce-only TP поверх неизвестного старого.
            if not oid:
                try:
                    hist = self.client.get_symbol_order_history(symbol, days=7)
                    since = int(float(meta.get("opened_at") or 0) * 1000)
                    recent = []
                    for ho in hist:
                        lid = str(ho.get("orderLinkId") or "")
                        if not lid.startswith(f"btp{i}-"):
                            continue
                        if not _tp_order_matches_position(ho, symbol, side, live_idx):
                            continue
                        try:
                            hist_price = float(ho.get("price") or ho.get("triggerPrice") or 0)
                        except (TypeError, ValueError, OverflowError):
                            continue
                        # Price mismatch may be a deliberate manual move. Keep
                        # the order eligible for recovery by its unique stage prefix.
                        if not math.isfinite(hist_price) or hist_price <= 0:
                            continue
                        ts = int(ho.get("updatedTime") or ho.get("createdTime") or ho.get("orderTime") or 0)
                        if since and ts and ts < since:
                            continue
                        recent.append(ho)
                    recent.sort(key=lambda x: int(x.get("updatedTime") or x.get("createdTime") or x.get("orderTime") or 0), reverse=True)
                    if recent:
                        rh = recent[0]
                        rstatus = str(rh.get("orderStatus") or "").lower()
                        rcum = float(rh.get("cumExecQty") or 0)
                        if rcum > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), rcum)
                        if rstatus == "filled":
                            done[key] = True
                            verified[key] = True
                            continue
                        if rstatus in ("new", "partiallyfilled", "untriggered", "created") and rh.get("orderId"):
                            try:
                                history_tp_price = float(rh.get("price") or rh.get("triggerPrice") or 0)
                            except (TypeError, ValueError, OverflowError):
                                history_tp_price = 0.0
                            if not math.isfinite(history_tp_price) or history_tp_price <= 0:
                                verified[key] = False
                                self.log.warning(f"[{symbol}] btp{i} из истории имеет некорректную цену; новый TP не создаю.")
                                continue
                            old_saved_targets = meta.get("tp_targets") or []
                            try:
                                old_price = float(old_saved_targets[i-1])
                            except (TypeError, ValueError, IndexError, OverflowError):
                                old_price = float(targets[i-1])
                            history_tol = max(tick_size * 0.5, abs(old_price) * 1e-8, 1e-12)
                            if abs(history_tp_price - old_price) > history_tol:
                                targets[i-1] = self.round_step(history_tp_price, tick_size)
                                self.log.info(f"[{symbol}] Восстановил btp{i} из истории по фактической цене {targets[i-1]}.")
                            order_ids[key] = str(rh.get("orderId"))
                            verified[key] = True
                            continue
                        if rstatus not in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                            verified[key] = False
                            self.log.warning(
                                f"[{symbol}] Статус btp{i} в истории неизвестен ({rstatus or 'empty'}); "
                                "новый TP не создаю до сверки."
                            )
                            continue
                except Exception as e:
                    verified[key] = False
                    self.log.warning(
                        f"[{symbol}] Не удалось восстановить btp{i} из истории ({e}); "
                        "новый TP не создаю до успешной сверки."
                    )
                    continue
            new_oid = self.client.place_bot_tp_limit(symbol, side, targets[i-1], qty_target, i)
            if new_oid:
                order_ids[key] = new_oid
                verified[key] = True

        # Любое фактическое исполнение TP1 (включая частичное) считается
        # событием TP1 для переноса стопа. Полного Filled ждать нельзя: лимитный
        # ордер может исполниться частично и затем остаться/быть отменённым.
        tp1_hit = bool(done.get("1"))
        if enabled[0] and not tp1_hit and not order_ids.get("1"):
            try:
                hist = self.client.get_symbol_order_history(symbol, days=7)
                since = int(float(meta.get("opened_at") or 0) * 1000)
                for ho in hist:
                    lid = str(ho.get("orderLinkId") or "")
                    if not lid.startswith("btp1-"):
                        continue
                    ts = int(ho.get("updatedTime") or ho.get("createdTime") or ho.get("orderTime") or 0)
                    if since and ts and ts < since:
                        continue
                    cum = float(ho.get("cumExecQty") or 0)
                    if cum > 0:
                        filled_qty["1"] = max(filled_qty.get("1", 0.0), cum)
                        tp1_hit = True
                    if str(ho.get("orderStatus") or "").lower() == "filled":
                        done["1"] = True
                        tp1_hit = True
                    if tp1_hit:
                        break
            except Exception as e:
                self.log.debug(f"[{symbol}] Не удалось восстановить факт исполнения TP1 из истории: {e}")
        if enabled[0] and order_ids.get("1"):
            try:
                st_tp1 = self.client.get_order_state(symbol, str(order_ids["1"]))
                cum_tp1 = float((st_tp1 or {}).get("cumExecQty") or 0)
                if cum_tp1 > 0:
                    filled_qty["1"] = max(filled_qty.get("1", 0.0), cum_tp1)
                    tp1_hit = True
                if str((st_tp1 or {}).get("orderStatus") or "").lower() == "filled":
                    done["1"] = True
                    tp1_hit = True
            except Exception as e:
                self.log.debug(f"[{symbol}] Не удалось проверить частичное исполнение TP1: {e}")
        if enabled[0] and tp1_hit and not meta.get("tp1_breakeven_done"):
            try:
                live_after_tp1 = self.client.get_position_strict(symbol, side=("Buy" if side == "LONG" else "Sell"))
            except Exception:
                live_after_tp1 = live_pos
            be_entry = float((live_after_tp1 or live_pos).get("avgPrice") or entry)
            be_pct = float(getattr(cfg, "SIGNAL_BREAKEVEN_BUFFER_PERCENT", 0.5)) / 100.0
            be_price = be_entry * (1 + be_pct) if side == "LONG" else be_entry * (1 - be_pct)
            be_price = self.client.round_step(be_price, tick_size)
            if self.client.update_stop_loss_verified(symbol, be_price, side):
                meta["tp1_breakeven_done"] = True
                self.log.info(f"[{symbol}] TP1 исполнен: стоп перенесён на {be_price} ({'+' if side == 'LONG' else '-'}{getattr(cfg, 'SIGNAL_BREAKEVEN_BUFFER_PERCENT', 0.5)}% от входа).")

        meta["tp_targets"] = targets
        meta["tp_close_pcts"] = closes
        meta["tp_order_ids"] = order_ids
        meta["tp_done"] = done
        meta["tp_filled_qty"] = filled_qty
        meta["tp_verified"] = verified
        meta["tp4_ok"] = bool(tp4_ok)
        meta["tp4_price"] = targets[3]
        return {"targets": targets, "close_pcts": closes, "tp4_ok": tp4_ok, "order_ids": order_ids, "done": done, "verified": verified, "filled_qty": filled_qty}

    def _persist_bot_tp_meta(self, symbol: str, meta: Dict):
        if not persist_bot_position_with_retry(symbol, meta, logger=self.log):
            self.log.critical(
                "[%s] Не удалось сохранить состояние TP1–TP4 в SQLite после повторных попыток",
                symbol,
            )
            return
        record_state_event("bot_position", "TP_STATE", symbol, {
            "tp_targets": meta.get("tp_targets") or [],
            "tp_order_ids": meta.get("tp_order_ids") or {},
            "tp_done": meta.get("tp_done") or {},
            "tp_filled_qty": meta.get("tp_filled_qty") or {},
            "tp1_breakeven_done": bool(meta.get("tp1_breakeven_done")),
            "sl_price": meta.get("sl_price"),
        })

    def _persist_bot_runtime_meta(self, symbol: str):
        """Немедленно фиксирует текущее состояние bot-позиции в SQLite.

        Это отдельный путь для изменений, которые не проходят через TP-реконсиляцию
        (profit-lock, восстановление SL, smart-exit). В памяти остаётся только
        быстрый кэш; после успешного вызова SQLite содержит тот же снимок.
        """
        with self._trade_meta_lock:
            meta = dict(self._trade_meta.get(symbol) or {})
        if not meta:
            return False
        if persist_bot_position_with_retry(symbol, meta, logger=self.log):
            return True
        self.log.critical("[%s] Не удалось сохранить runtime-state позиции в SQLite после повторных попыток", symbol)
        return False

    def _manage_position(self, symbol: str):
        with self._trade_meta_lock:
            meta = self._trade_meta.get(symbol)
        if meta is None:
            return

        price = self.feed.get_price(symbol)
        if price is None:
            return

        entry_price = meta["entry_price"]
        if entry_price <= 0:
            return
        qty = meta.get("qty", 0.0) or 0.0
        is_long = bool(meta.get("is_long", False))
        # Для шорта прибыль растёт при падении цены (entry - price), для
        # лонга — наоборот, при росте цены (price - entry).
        profit_pct = (price - entry_price) / entry_price * 100 if is_long else (entry_price - price) / entry_price * 100
        unrealized_pnl = (price - entry_price) * qty if is_long else (entry_price - price) * qty

        if not cfg.DRY_RUN:
            with self._open_positions_cache_lock:
                live_pos = self._open_positions_cache.get(symbol)
            if live_pos is not None:
                # 4 независимых тейка для позиции, открытой ботом. Эта ветка
                # выполняется только для символов из _trade_meta, поэтому
                # ручные позиции пользователя сюда не попадают.
                try:
                    tp_state = self._ensure_bot_multi_tps(symbol, meta, live_pos)
                    if tp_state:
                        with self._trade_meta_lock:
                            if symbol in self._trade_meta:
                                self._trade_meta[symbol].update({
                                    "entry_price": float(live_pos.get("avgPrice") or self._trade_meta[symbol].get("entry_price") or 0),
                                    "qty": float(live_pos.get("size") or self._trade_meta[symbol].get("qty") or 0),
                                    "tp_targets": tp_state.get("targets", []),
                                    "tp_close_pcts": tp_state.get("close_pcts", []),
                                    "tp_order_ids": tp_state.get("order_ids", {}),
                                    "tp_done": tp_state.get("done", {}),
                                    "tp_filled_qty": tp_state.get("filled_qty", {}),
                                    "tp4_manual_override": bool(meta.get("tp4_manual_override", self._trade_meta[symbol].get("tp4_manual_override", False))),
                                    "tp_price": tp_state.get("targets", [0,0,0,0])[-1] if tp_state.get("targets") else self._trade_meta[symbol].get("tp_price"),
                                })
                                meta = dict(self._trade_meta[symbol])
                        self._persist_bot_tp_meta(symbol, meta)
                except Exception as e:
                    self.log.warning(f"[{symbol}] 4 тейка: reconciliation не завершена, повторю в следующем цикле: {e}")

                live_tp = float(live_pos.get("takeProfit") or 0)
                tp_price = meta.get("tp_price")
                if live_tp <= 0 and tp_price:
                    ok = self.client.update_take_profit(symbol, tp_price, "LONG" if is_long else "SHORT")
                    if ok:
                        with self._trade_meta_lock:
                            if symbol in self._trade_meta:
                                self._trade_meta[symbol]["tp_price"] = tp_price
                        self._persist_bot_runtime_meta(symbol)
                        self.log.info(f"[{symbol}] TP отсутствовал на бирже — восстановлен на {tp_price}.")
                        self.tg.notify(f"🛠️ <b>Тейк-профит восстановлен</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\nTP был не выставлен, теперь стоит на {tp_price}.")

                live_sl = float(live_pos.get("stopLoss") or 0)
                initial_sl_price = meta.get("sl_price")
                if live_sl <= 0 and initial_sl_price and not meta.get("profit_locked") and not meta.get("tp1_breakeven_done"):
                    # Стоп-лосс отсутствует на бирже (снят вручную, не удался при
                    # открытии и т.п.), а защита прибыли ещё не переняла его на
                    # себя — восстанавливаем именно наш обычный стоп-лосс по PnL.
                    ok = self.client.update_stop_loss(symbol, initial_sl_price, "LONG" if is_long else "SHORT")
                    if ok:
                        with self._trade_meta_lock:
                            if symbol in self._trade_meta:
                                self._trade_meta[symbol]["sl_price"] = initial_sl_price
                        self._persist_bot_runtime_meta(symbol)
                        self.log.info(f"[{symbol}] Стоп-лосс отсутствовал на бирже — восстановлен на {initial_sl_price}.")
                        self.tg.notify(f"🛠️ <b>Стоп-лосс восстановлен</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\nSL был не выставлен, теперь стоит на {initial_sl_price}.")

        if cfg.ENABLE_PROFIT_LOCK and not meta.get("profit_locked") and qty > 0 and unrealized_pnl > 0 and profit_pct >= cfg.PROFIT_LOCK_TRIGGER_PCT:
            lock_usdt = min(cfg.PROFIT_LOCK_MIN_USDT, unrealized_pnl)
            # Для лонга защищённый стоп-лосс стоит ВЫШЕ входа, для шорта — НИЖЕ.
            sl_price = self.client.round_step(entry_price + (lock_usdt / qty) if is_long else entry_price - (lock_usdt / qty), meta.get("tick_size", 0.0) or 0.0)
            ok = self.client.update_stop_loss(symbol, sl_price, "LONG" if is_long else "SHORT")
            if ok:
                with self._trade_meta_lock:
                    if symbol in self._trade_meta:
                        self._trade_meta[symbol]["profit_locked"] = True
                        self._trade_meta[symbol]["sl_price"] = sl_price
                self._persist_bot_runtime_meta(symbol)
                self.log.info(f"[{symbol}] Цена прошла {profit_pct:.2f}% >= порога, стоп-лосс подтянут на {sl_price} (фиксирует ~{lock_usdt:.4f} USDT PnL).")
                self.tg.notify(f"🔒 <b>Прибыль защищена</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\nДвижение цены: +{profit_pct:.2f}% (PnL: +{unrealized_pnl:.4f} USDT)\nСтоп-лосс подтянут на {sl_price} (фиксирует ~{lock_usdt:.4f} USDT).")

        if not cfg.ENABLE_SMART_EXIT:
            return

        with self._guards_lock:
            guard = self._position_guards.get(symbol)

        if guard is None:
            if unrealized_pnl >= cfg.SMART_EXIT_MIN_PROFIT_USDT:
                # Шорт в плюсе, когда цена падает -> ждём дно ("down").
                # Лонг в плюсе, когда цена растёт -> ждём пик ("up"), с
                # purpose="exit", чтобы ReversalTracker использовал именно
                # SMART_EXIT_* тайминги, а не STALL_MIN_SECONDS входа.
                direction = "up" if is_long else "down"
                with self._guards_lock:
                    self._position_guards[symbol] = ReversalTracker(symbol, price, direction, meta={"purpose": "exit"})
                    guards_copy = dict(self._position_guards)
                with self._watched_lock:
                    watched_copy = dict(self._watched)
                with self._cooldown_lock:
                    cooldowns_copy = dict(self._cooldowns)
                self._persist_runtime_state_safely(
                    watched_copy, guards_copy, cooldowns_copy, f"guard created {symbol}"
                )
                record_state_event("runtime", "GUARD_CREATED", symbol, {"direction": direction, "price": price})
                self.log.info(f"[{symbol}] PnL {unrealized_pnl:.4f} USDT — включаю умный выход (слежу за {'пиком' if is_long else 'дном'}).")
            return

        price_and_ts = self.feed.get_price_and_ts(symbol)
        if price_and_ts is None:
            return
        _, tick_ts = price_and_ts
        stopped = guard.update(price, tick_ts, cfg.SMART_EXIT_STALL_TICKS, cfg.SMART_EXIT_BOUNCE_PCT)
        if not stopped:
            return

        with self._guards_lock:
            self._position_guards.pop(symbol, None)
            guards_copy = dict(self._position_guards)
        with self._watched_lock:
            watched_copy = dict(self._watched)
        with self._cooldown_lock:
            cooldowns_copy = dict(self._cooldowns)
        self._persist_runtime_state_safely(
            watched_copy, guards_copy, cooldowns_copy, f"guard removed {symbol}"
        )
        record_state_event("runtime", "GUARD_REMOVED", symbol, {})

        now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
        move_word = "рост остановился" if is_long else "падение остановилось"
        self.log.info(f"[{symbol}] {move_word.capitalize()} ({now}) — закрываю позицию умным выходом.")
        closed = self.client.close_position_market(symbol, meta["qty"], "LONG" if meta.get("is_long") else "SHORT")
        if closed:
            with self._trade_meta_lock:
                if symbol in self._trade_meta:
                    self._trade_meta[symbol]["smart_exit_triggered"] = True
            self._persist_bot_runtime_meta(symbol)
            self.tg.notify(f"🎯 <b>Умный выход сработал</b>\n━━━━━━━━━━━━━━━\n<b>{symbol}</b>\n{move_word.capitalize()}, позиция закрыта рыночным ордером.\n🕒 {now}")
        else:
            self.tg.notify(f"⚠️ [{symbol}] Умный выход не смог закрыть позицию — возможно, её уже закрыл тейк-профит. Проверь /positions.")

    # ---- обнаружение закрытия позиции ----------------------------------------

    def _cancel_bot_multi_tp_orders(self, symbol: str, meta: Optional[Dict]) -> None:
        """Отменяет оставшиеся TP1-TP3 после полного закрытия своей позиции.
        TP4 хранится в position trading-stop и исчезает вместе с позицией."""
        ids = dict((meta or {}).get("tp_order_ids") or {})
        for oid in ids.values():
            if not oid:
                continue
            try:
                call_with_retry(
                    self.log, self.client.session.cancel_order,
                    category=cfg.CATEGORY, symbol=symbol, orderId=str(oid),
                    description=f"cancel_bot_tp({symbol},{oid})",
                )
            except Exception as e:
                self.log.debug(f"[{symbol}] Не удалось отменить TP-ордер {oid} после закрытия позиции: {e}")

    def _check_closed_positions(self):
        try:
            positions = self.client.get_open_positions()
        except Exception as e:
            self.log.warning(f"Не удалось проверить позиции: {e}")
            return

        current_open = {p["symbol"] for p in positions}

        with self._open_positions_cache_lock:
            self._open_positions_cache = {p["symbol"]: p for p in positions}

        with self._trade_meta_lock:
            bot_tracked = set(self._trade_meta.keys())

        with self._known_lock:
            closed = self._known_open_symbols - current_open
            # _known_open_symbols должен содержать ТОЛЬКО символы, которые
            # реально открыл бот (см. self._trade_meta / реестр
            # bot_positions) — НИКОГДА не берём его напрямую из current_open,
            # иначе туда попадут и позиции, открытые пользователем вручную на
            # бирже, и бот начнёт их "видеть": управлять риском, слать
            # уведомления об открытии/закрытии, ставить cooldown и т.п.
            # Ручные сделки бота не касаются вообще.
            self._known_open_symbols = current_open & bot_tracked

        for symbol in closed:
            # Сначала фиксируем закрытие в SQLite. Если БД недоступна, сохраняем
            # метаданные и возвращаем символ в known-open, чтобы следующий цикл
            # повторил удаление, а не потерял незавершённое состояние в памяти.
            try:
                mark_bot_position_closed(symbol)
            except Exception:
                self.log.exception(
                    "[%s] Не удалось зафиксировать закрытие в SQLite; повторю в следующем цикле",
                    symbol,
                )
                with self._known_lock:
                    self._known_open_symbols.add(symbol)
                continue

            with self._guards_lock:
                self._position_guards.pop(symbol, None)
            with self._trade_meta_lock:
                meta = self._trade_meta.pop(symbol, None)
            self._cancel_bot_multi_tp_orders(symbol, meta)
            self._set_cooldown(symbol)
            threading.Thread(target=self._finalize_closed_position, args=(symbol, meta), daemon=True, name=f"pos-closed-{symbol}").start()

    def _find_matching_closed_pnl(self, symbol: str, meta: Optional[dict]) -> Optional[Dict]:
        """Надёжно находит именно ту запись closed-pnl, которая относится к
        только что закрытой позиции. Bybit иногда индексирует closed-pnl с
        задержкой в несколько секунд — наивное «взять последнюю запись»
        может по ошибке вернуть PnL от ПРЕДЫДУЩЕЙ сделки по этому же
        символу, из-за чего в уведомлении путаются прибыль и убыток (и
        затем фоновая сверка присылает ещё одно, уже верное — дубль).
        Поэтому сверяем qty/цену входа с тем, что было сохранено в meta при
        открытии позиции, и повторяем попытки в течение ~13 секунд."""
        entry_price = meta.get("entry_price") if meta else None
        qty = meta.get("qty") if meta else None

        for delay in (0, 1, 1.5, 2, 2.5, 3, 3):
            if delay:
                time.sleep(delay)
            candidates = self.client.get_recent_closed_pnl(symbol, limit=5)
            now_ms = time.time() * 1000
            for rec in candidates:
                trade_id = rec.get("orderId") or rec.get("execId") or f"{symbol}_{rec.get('updatedTime')}"
                if trade_id in self.recently_closed_ids:
                    continue  # уже обработана ранее (например, предыдущее закрытие)
                try:
                    rec_qty = float(rec.get("qty", 0) or 0)
                    rec_entry = float(rec.get("avgEntryPrice", 0) or 0)
                    updated_ms = float(rec.get("updatedTime", 0) or 0)
                except (TypeError, ValueError):
                    continue

                recent_enough = (now_ms - updated_ms) < 5 * 60 * 1000  # не старше 5 минут
                qty_ok = not qty or not rec_qty or abs(rec_qty - qty) / max(qty, 1e-9) < 0.02
                price_ok = not entry_price or not rec_entry or abs(rec_entry - entry_price) / max(entry_price, 1e-9) < 0.01

                if recent_enough and qty_ok and price_ok:
                    return rec

        return None

    def _finalize_closed_position(self, symbol: str, meta: Optional[dict]):
        """Довершает обработку закрытой позиции: ищет соответствующую запись
        closed-pnl (с retry, см. _find_matching_closed_pnl) и шлёт
        уведомление. Гарды/метаданные и cooldown уже сняты/выставлены
        синхронно в _check_closed_positions — здесь только то, что может
        подождать. Выполняется в отдельном потоке."""
        pnl_info = self._find_matching_closed_pnl(symbol, meta)

        if pnl_info is None:
            # Не смогли надёжно сопоставить запись closed-pnl сразу после
            # закрытия — не гадаем и не шлём уведомление с потенциально
            # чужим/устаревшим PnL. Точное уведомление придёт из фоновой
            # синхронизации (см. ReportsEngine.sync_trades), как только
            # запись появится на бирже — так что дублей и путаницы не будет.
            self.log.warning(f"[{symbol}] Не удалось сопоставить запись closed-pnl сразу после закрытия — жду фоновую синхронизацию для уведомления.")
            record = {
                "symbol": symbol, "pnl": None, "exit_type": "unknown",
                "entry_price": meta.get("entry_price") if meta else None,
                "qty": meta.get("qty") if meta else None,
                "closed_at": time.time(),
            }
            append_trade_record(record, self.log)
            return

        pnl = float(pnl_info.get("closedPnl", 0) or 0)
        if meta and meta.get("smart_exit_triggered"):
            exit_type = "smart_exit"
        elif meta and meta.get("profit_locked"):
            exit_type = "profit_lock"
        elif meta and meta.get("sl_price") and pnl < 0:
            # Профит-лок не срабатывал, сделка вышла в минус, а обычный
            # стоп-лосс был выставлен — с высокой вероятностью закрылись
            # именно по нему (точно узнать нельзя, Bybit не помечает
            # closed-pnl причиной закрытия, но это самое вероятное объяснение).
            exit_type = "stop_loss"
        else:
            exit_type = "tp_or_manual"

        record = {
            "symbol": symbol, "pnl": pnl, "exit_type": exit_type,
            "entry_price": meta.get("entry_price") if meta else None,
            "qty": meta.get("qty") if meta else None,
            "closed_at": time.time(),
        }
        append_trade_record(record, self.log)

        # мгновенно кладём ту же сделку в общую БД статистики и запоминаем её id,
        # чтобы фоновая REST-сверка не продублировала уведомление о ней
        trade_id = pnl_info.get("orderId") or pnl_info.get("execId") or f"{symbol}_{pnl_info.get('updatedTime')}"
        self.recently_closed_ids.add(trade_id)
        try:
            upsert_trades([pnl_info], source="engine")
        except Exception:
            self.log.exception("Не удалось записать закрытую сделку в общую БД статистики")

        pnl_emoji = "🟢" if pnl >= 0 else "🔴"
        self.log.info(f"[{symbol}] Позиция закрыта, PnL: {pnl:.2f} USDT.")

        equity_line = "?"
        try:
            equity_line = f"{self.client.get_equity_usdt():.2f}"
        except Exception:
            self.log.warning(f"[{symbol}] Не удалось получить эквити для уведомления о закрытии сделки")

        self.tg.notify(
            f"{pnl_emoji} PnL: <b>{pnl:+.2f} USDT</b>\n"
            f"<b>{symbol}</b>\n"
            f"Баланс: <b>{equity_line} USDT</b>",
            important=True,
        )


# ============================================================================
# УЧЁТ И ОТЧЁТНОСТЬ: синхронизация closed-pnl, статистика, алерты, отчёты
# ============================================================================

PERIODS = [("Сегодня", 1), ("7 дней", 7), ("30 дней", 30), ("Всё время", 3650)]
PERIOD_NAMES = {1: "сегодня", 7: "7 дней", 30: "30 дней", 3650: "всё время"}

DIVIDER = "▬▬▬▬▬▬▬▬▬▬▬▬▬▬▬"

SIGNAL_TP2_CLOSE_PERCENT_PRESETS = [25, 33, 50, 75, 100]

# Фирменная тёмная палитра Bybit — используется для PNG-таблицы сделок
BYBIT_YELLOW = "#F7A600"
BYBIT_BG = "#0b0e11"
BYBIT_BG_ROW = "#181a20"
BYBIT_GREEN = "#0ECB81"
BYBIT_GREEN_DIM = "#0a3d29"
BYBIT_RED = "#F6465D"
BYBIT_RED_DIM = "#3d0f16"

WEEKDAY_NAMES_RU = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]


def _blend_color(hex_light: str, hex_strong: str, t: float) -> str:
    """Линейно смешивает два HEX-цвета: t=0 -> hex_light, t=1 -> hex_strong.
    Используется для тепловой подсветки строк таблицы сделок по силе PnL."""
    t = max(0.0, min(1.0, t))
    lr, lg, lb = int(hex_light[1:3], 16), int(hex_light[3:5], 16), int(hex_light[5:7], 16)
    sr, sg, sb = int(hex_strong[1:3], 16), int(hex_strong[3:5], 16), int(hex_strong[5:7], 16)
    r = round(lr + (sr - lr) * t)
    g = round(lg + (sg - lg) * t)
    b = round(lb + (sb - lb) * t)
    return f"#{r:02x}{g:02x}{b:02x}"


START_TIME = datetime.now(timezone.utc)

_sync_lock = threading.Lock()
_open_pnl_alert_lock = threading.Lock()
_open_pnl_alert_state = {}


class ReportsEngine:
    """Обёртка над функциями отчётности, чтобы не таскать client/notifier
    отдельным аргументом в каждую функцию."""

    def __init__(self, logger, client, notifier):
        self.log = logger
        self.client = client            # bybit_client.BybitClient
        self.session = client.session   # «сырой» HTTP-session pybit, для отдельных REST-вызовов
        self.tg = notifier              # объект с .notify(text) и .chat_id
        # Telegram-кнопки изменения ручных настроек и 10-секундный монитор
        # могут одновременно попасть в одну и ту же ручную позицию. Один
        # re-entrant lock исключает гонку cancel/amend/place TP и перестановку
        # SL двумя потоками одновременно.
        self._manual_protection_lock = threading.RLock()
        # Один lock сериализует фоновые сканирования слотов, второй защищает
        # только один REST amend от гонки с кнопкой немедленного отключения.
        self._manual_limit_value_lock = threading.RLock()
        self._manual_limit_amend_lock = threading.Lock()
        self._manual_limit_toggle_lock = threading.Lock()
        # Сигнализируем фоновому проходу остановить новые amend сразу при
        # нажатии «Выкл», пока он ожидает завершения уже начатого REST-запроса.
        self._manual_limit_disable_requested = threading.Event()
        # Аналогично останавливаем старый проход, когда пользователь меняет
        # целевой номинал L1/L2: старое значение не должно применяться к другим
        # монетам, пока запись новой настройки ожидает блокировку amend.
        self._manual_limit_target_update_requested = threading.Event()
        self._manual_limit_target_update_lock = threading.Lock()
        # Сколько подряд циклов не удалось подтвердить снятие ордеров закрытой
        # сигнальной позиции (для ограничения частоты алертов).
        self._signal_close_cleanup_attempts: Dict[str, int] = {}

    def build_open_limit_orders_message(self) -> str:
        """Показывает входные лимитные ордера и их текущий номинал по монетам.

        Для частично исполненного ордера считает оставшийся объём через
        leavesQty, если биржа его вернула. Условные и reduce-only ордера
        исключаются: они не являются входными лимитками и могут закрывать
        уже открытую позицию.
        """
        orders = self.client.get_open_orders_all()
        grouped: Dict[str, List[Dict]] = {}
        ignored = 0
        for order in orders:
            if str(order.get("orderType") or "").strip().lower() != "limit":
                continue
            status = str(order.get("orderStatus") or "New").strip().lower()
            # Untriggered обычно относится к условному ордеру; не показываем его
            # как обычную входную лимитку даже если API не вернул triggerPrice.
            if status not in {"new", "partiallyfilled", "partially_filled"}:
                continue
            try:
                trigger_price = float(order.get("triggerPrice") or 0)
                trigger_direction = int(order.get("triggerDirection") or 0)
            except (TypeError, ValueError):
                ignored += 1
                continue
            reduce_only = order.get("reduceOnly")
            if isinstance(reduce_only, str):
                reduce_only = reduce_only.strip().lower() in {"1", "true", "yes"}
            if trigger_price > 0 or trigger_direction != 0 or _is_conditional_stop_type(order.get("stopOrderType")) or bool(reduce_only):
                ignored += 1
                continue
            symbol = str(order.get("symbol") or "").strip().upper()
            side = str(order.get("side") or "").strip()
            if not symbol or side not in {"Buy", "Sell"}:
                ignored += 1
                continue
            try:
                price = float(order.get("price") or 0)
                original_qty = float(order.get("qty") or 0)
                leaves_raw = order.get("leavesQty")
                remaining_qty = float(leaves_raw) if leaves_raw not in (None, "") else original_qty
                if not all(math.isfinite(x) for x in (price, original_qty, remaining_qty)) or price <= 0 or remaining_qty <= 0:
                    ignored += 1
                    continue
            except (TypeError, ValueError):
                ignored += 1
                continue
            grouped.setdefault(symbol, []).append({
                "side": side, "price": price, "qty": original_qty,
                "remaining_qty": remaining_qty, "remaining_value": price * remaining_qty,
                "order_id": str(order.get("orderId") or ""),
                "status": status,
            })

        if not grouped:
            return ("📋 <b>Открытые входные лимитки</b>\n"
                    "Сейчас нет обычных входных LIMIT-ордеров.\n\n"
                    "Условные и reduce-only ордера в этот отчёт не входят.")

        lines = ["📋 <b>Открытые входные лимитки по монетам</b>",
                 "Стоимость = цена × оставшееся количество; это номинал ордера, не маржа.", ""]
        grand_total = 0.0
        grand_count = 0
        for symbol in sorted(grouped):
            # Порядок = порядок исполнения. SELL (шорт): от меньшей цены к большей;
            # BUY (лонг): от большей к меньшей. Раньше BUY шли по возрастанию цены,
            # и «1.» в списке оказывалась САМОЙ ДАЛЬНЕЙ лимиткой, а ближайшая — последней.
            items = sorted(grouped[symbol], key=lambda x: (x["side"], x["price"] if x["side"] == "Sell" else -x["price"], x["order_id"]))
            try:
                pinned_labels = {
                    str(r.get("order_id") or ""): f"L{int(r.get('slot') or 0)}"
                    for r in get_manual_limit_slot_rows(symbol)
                    if str(r.get("status") or "") == "active" and int(r.get("slot") or 0) in (1, 2)
                }
            except Exception:
                pinned_labels = {}
            symbol_total = sum(x["remaining_value"] for x in items)
            grand_total += symbol_total
            grand_count += len(items)
            lines.append(f"<b>{symbol}</b> — {len(items)} лимит. · всего <b>{symbol_total:.2f} USDT</b>")
            for i, item in enumerate(items, 1):
                side = "BUY" if item["side"] == "Buy" else "SELL"
                status_text = " · частично исполнена" if item["status"] in {"partiallyfilled", "partially_filled"} else ""
                order_suffix = f" · ID <code>{item['order_id'][-8:]}</code>" if item["order_id"] else ""
                pin_label = pinned_labels.get(item["order_id"])
                if pin_label:
                    order_suffix += f" · <b>{pin_label}</b>"
                lines.append(
                    f"  {i}. {side} · цена {item['price']:.10g} · остаток {item['remaining_qty']:.10g} "
                    f"· <b>{item['remaining_value']:.2f} USDT</b>{status_text}{order_suffix}"
                )
            lines.append("")
        lines.append(f"<b>ИТОГО: {grand_count} лимиток · {grand_total:.2f} USDT</b>")
        lines.append("\nУсловные и reduce-only ордера (например, тейки/закрывающие заявки) не учитываются.")
        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Синхронизация закрытых сделок
    # ------------------------------------------------------------------

    def sync_trades(self, silent_notify=False) -> int:
        if not _sync_lock.acquire(blocking=False):
            self.log.debug("Синхронизация уже выполняется в другом потоке — пропускаю")
            return 0
        try:
            last_sync = get_last_sync_time()
            now_ms = int(datetime.now(timezone.utc).timestamp() * 1000)
            is_first_run = last_sync == 0

            if is_first_run:
                start_ms = now_ms - cfg.INITIAL_BACKFILL_DAYS * 24 * 60 * 60 * 1000
                self.log.info("Первый запуск учёта: загружаю историю за %s дней", cfg.INITIAL_BACKFILL_DAYS)
            else:
                start_ms = last_sync

            trades = self.client.fetch_closed_pnl_range(start_ms, now_ms)
            new_trades = upsert_trades(trades, source="sync")
            set_last_sync_time(now_ms)
            self.log.info("Синхронизация: получено %s сделок, новых записей: %s", len(trades), len(new_trades))

            engine_ids = getattr(self.tg, "recently_closed_ids", None)

            if get_setting("notify_new_trade", cfg.NOTIFY_ON_NEW_TRADE) and not silent_notify and not is_first_run and new_trades and cfg.TELEGRAM_CHAT_ID and not self.is_quiet_hours():
                for t in new_trades:
                    trade_id = t.get("orderId") or t.get("execId") or f"{t.get('symbol')}_{t.get('updatedTime')}"
                    if engine_ids is not None and trade_id in engine_ids:
                        # уже уведомили о ней мгновенно из торгового движка — не дублируем
                        continue
                    self.notify_new_trade(t)

            if not is_first_run and new_trades and cfg.TELEGRAM_CHAT_ID:
                for t in new_trades:
                    self.check_trade_pnl_threshold_alert(t)

            loss_limit = get_setting("max_daily_loss_alert", cfg.MAX_DAILY_LOSS_ALERT)
            if not is_first_run and loss_limit > 0 and cfg.TELEGRAM_CHAT_ID:
                self.check_daily_loss_alert(loss_limit)

            return len(new_trades)
        finally:
            _sync_lock.release()

    def is_quiet_hours(self) -> bool:
        quiet = get_setting("quiet_hours", cfg.QUIET_HOURS)
        if not quiet or "-" not in quiet:
            return False
        try:
            start_h, end_h = (int(x) for x in quiet.split("-"))
        except ValueError:
            return False

        tz_offset = get_setting("tz_offset", 0)
        now_hour = (datetime.now(timezone.utc) + timedelta(hours=tz_offset)).hour

        if start_h == end_h:
            return False
        if start_h < end_h:
            return start_h <= now_hour < end_h
        return now_hour >= start_h or now_hour < end_h

    def check_daily_loss_alert(self, loss_limit: int):
        today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        already_alerted = get_meta("loss_alert_date", "")
        if already_alerted == today_str:
            return

        day_start = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0)
        trades_today = query_trades(int(day_start.timestamp() * 1000), int(datetime.now(timezone.utc).timestamp() * 1000))
        pnl_today = sum(t["closed_pnl"] for t in trades_today)

        if pnl_today <= -abs(loss_limit):
            msg = (
                f"⚠️ <b>Риск-алерт</b>\n\nУбыток за сегодня составил <b>{pnl_today:.2f} USDT</b>, "
                f"это превышает установленный лимит ({loss_limit} USDT).\n"
                f"Возможно, стоит сделать паузу в торговле (кнопка «⏸ Пауза»)."
            )
            self.tg.notify(msg)
            set_meta("loss_alert_date", today_str)

    def notify_new_trade(self, t: dict):
        try:
            pnl = float(t.get("closedPnl", 0) or 0)
            emoji = "🟢" if pnl >= 0 else "🔴"
            symbol = t.get("symbol")

            equity_line = "?"
            try:
                equity_line = f"{self.client.get_equity_usdt():.2f}"
            except Exception:
                self.log.warning("Не удалось получить эквити для уведомления о новой сделке")

            msg = (
                f"{emoji} PnL: <b>{pnl:+.2f} USDT</b>\n"
                f"<b>{symbol}</b>\n"
                f"Баланс: <b>{equity_line} USDT</b>"
            )
            self.tg.notify(msg, important=True)
        except Exception:
            self.log.exception("Не удалось отправить уведомление о новой сделке")

    def check_trade_pnl_threshold_alert(self, t: dict):
        try:
            pnl = float(t.get("closedPnl", 0) or 0)
            plus_th = get_setting("pnl_alert_plus", cfg.PNL_TRADE_ALERT_PLUS)
            minus_th = get_setting("pnl_alert_minus", cfg.PNL_TRADE_ALERT_MINUS)
            if not plus_th and not minus_th:
                return

            symbol = t.get("symbol")
            side = "Short" if t.get("side") == "Sell" else "Long"
            qty = t.get("qty")

            if plus_th and pnl >= abs(plus_th):
                self.tg.notify(
                    f"🟢🚀 <b>Крупная прибыль по сделке!</b>\n\n"
                    f"Инструмент: <b>{symbol}</b> ({side}) | Объём: {qty}\n"
                    f"PnL сделки: <b>+{pnl:.2f} USDT</b>\nПорог алерта на прибыль: {abs(plus_th):.2f} USDT"
                )
            if minus_th and pnl <= -abs(minus_th):
                self.tg.notify(
                    f"🔴⚠️ <b>Крупный убыток по сделке!</b>\n\n"
                    f"Инструмент: <b>{symbol}</b> ({side}) | Объём: {qty}\n"
                    f"PnL сделки: <b>{pnl:.2f} USDT</b>\nПорог алерта на убыток: −{abs(minus_th):.2f} USDT"
                )
        except Exception:
            self.log.exception("Не удалось отправить алерт по порогу PnL сделки")

    # ------------------------------------------------------------------
    # PnL-алерт по ОТКРЫТЫМ позициям (нереализованный PnL, шаг за шагом)
    # ------------------------------------------------------------------

    def check_open_positions_pnl_alert(self):
        plus_th = get_setting("pnl_alert_plus", cfg.PNL_TRADE_ALERT_PLUS)
        minus_th = get_setting("pnl_alert_minus", cfg.PNL_TRADE_ALERT_MINUS)
        if not plus_th and not minus_th:
            return
        if not cfg.TELEGRAM_CHAT_ID:
            return

        plus_step = abs(plus_th)
        minus_step = abs(minus_th)

        try:
            positions = self.client.get_open_positions()
        except Exception:
            self.log.exception("Не удалось получить открытые позиции для проверки PnL-алерта")
            return

        seen_keys = set()
        with _open_pnl_alert_lock:
            for p in positions:
                symbol = p.get("symbol")
                side = p.get("side")
                key = f"{symbol}_{side}"
                seen_keys.add(key)

                upl = float(p.get("unrealisedPnl", 0) or 0)
                size = p.get("size")
                entry = float(p.get("avgPrice", 0) or 0)
                leverage = p.get("leverage", "?")
                side_ru = "Long" if side == "Buy" else "Short"

                st = _open_pnl_alert_state.setdefault(key, {"plus_level": 0.0, "minus_level": 0.0})

                if plus_step and upl > 0:
                    current_level = (int(upl // plus_step)) * plus_step
                    if current_level >= plus_step and current_level > st["plus_level"]:
                        self.tg.notify(
                            f"🟢🔥 Монета: {symbol} PnL: +{upl:.2f} USDT! прибавила {plus_step:g} USDT! Монета: {symbol} ({side_ru}) x{leverage}."
                        )
                        st["plus_level"] = current_level
                elif upl <= 0:
                    st["plus_level"] = 0.0

                if minus_step and upl < 0:
                    current_level = (int(abs(upl) // minus_step)) * minus_step
                    if current_level >= minus_step and current_level > st["minus_level"]:
                        self.tg.notify(
                            f"🔴⚠️ {symbol} потеряла {minus_step:g} USDT! PnL: {upl:.2f} USDT."
                        )
                        st["minus_level"] = current_level
                elif upl >= 0:
                    st["minus_level"] = 0.0

            for key in list(_open_pnl_alert_state.keys()):
                if key not in seen_keys:
                    del _open_pnl_alert_state[key]

    # ------------------------------------------------------------------
    # Комиссии, баланс, позиции
    # ------------------------------------------------------------------

    def build_fees_message(self, period_name: str, days: int) -> str:
        end = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        try:
            total_fee, count = self.client.fetch_fees_sum(int(start.timestamp() * 1000), int(end.timestamp() * 1000))
        except Exception:
            self.log.exception("Не удалось получить комиссии с биржи")
            return "⚠️ Не удалось получить данные о комиссиях с биржи. Попробуй ещё раз чуть позже."

        avg_fee = total_fee / count if count else 0.0
        return (
            f"💸 <b>Комиссии за {period_name}</b>\n\n"
            f"Всего списано комиссий: <b>{total_fee:.2f} USDT</b>\n"
            f"Исполнений (fills): {count}\nСредняя комиссия за исполнение: {avg_fee:.4f} USDT"
        )

    def get_balance_message(self) -> str:
        resp = call_with_retry(self.log, self.session.get_wallet_balance, accountType="UNIFIED", description="get_wallet_balance")
        result = resp.get("result", {}).get("list", [])
        if not result:
            return "Не удалось получить баланс."

        account = result[0]
        total_equity = account.get("totalEquity", "N/A")
        total_pnl_unrealized = account.get("totalPerpUPL", "N/A")
        available = account.get("totalAvailableBalance", "N/A")

        lines = ["💰 <b>Баланс аккаунта</b>\n"]
        lines.append(f"Общий эквити: <b>{float(total_equity):.2f} USDT</b>")
        if available not in ("N/A", None, ""):
            lines.append(f"Доступно: <b>{float(available):.2f} USDT</b>")
        if total_pnl_unrealized not in ("N/A", None, ""):
            lines.append(f"Нереализованный PnL: <b>{float(total_pnl_unrealized):.2f} USDT</b>")
        return "\n".join(lines)

    def build_open_positions_message(self) -> str:
        positions = self.client.get_open_positions()
        if not positions:
            return "📭 <b>Открытых позиций нет.</b>"

        lines = [f"📈 <b>Открытые позиции ({len(positions)})</b>\n"]
        total_upl = 0.0
        for p in positions:
            symbol = p.get("symbol")
            side = "🟢 Long" if p.get("side") == "Buy" else "🔴 Short"
            size = p.get("size")
            entry = float(p.get("avgPrice", 0) or 0)
            mark = float(p.get("markPrice", 0) or 0)
            upl = float(p.get("unrealisedPnl", 0) or 0)
            leverage = p.get("leverage", "?")
            sl = p.get("stopLoss") or "—"
            tp = p.get("takeProfit") or "—"
            total_upl += upl
            pct = ((entry - mark) / entry * 100) if entry and p.get("side") == "Sell" else (((mark - entry) / entry * 100) if entry else 0)
            emoji = "🟢" if upl >= 0 else "🔴"
            lines.append(
                f"<b>{symbol}</b> {side} x{leverage}\n"
                f"  Объём: {size} · Вход: {entry:g} · Марк: {mark:g} ({pct:+.2f}%)\n"
                f"  PnL: {emoji} {upl:+.2f} USDT · SL: {sl} · TP: {tp}\n"
            )
        emoji_total = "🟢" if total_upl >= 0 else "🔴"
        lines.append(f"\nИтого нереализованный PnL: {emoji_total} <b>{total_upl:+.2f} USDT</b>")
        return "\n".join(lines)

    def build_quick_status_message(self) -> str:
        lines = ["⚡ <b>Быстрый статус</b>", DIVIDER, ""]

        try:
            resp = call_with_retry(self.log, self.session.get_wallet_balance, accountType="UNIFIED", description="get_wallet_balance")
            result = resp.get("result", {}).get("list", [])
            if result:
                account = result[0]
                equity = float(account.get("totalEquity", 0) or 0)
                available = account.get("totalAvailableBalance")
                extra = f" · доступно {float(available):.2f} USDT" if available not in (None, "", "N/A") else ""
                lines.append(f"💰 Эквити: <b>{equity:.2f} USDT</b>{extra}")
            else:
                lines.append("💰 Баланс: недоступен")
        except Exception:
            self.log.exception("Не удалось получить баланс для быстрого статуса")
            lines.append("💰 Баланс: ошибка получения")

        try:
            positions = self.client.get_open_positions()
            total_upl = sum(float(p.get("unrealisedPnl", 0) or 0) for p in positions)
            if positions:
                emoji = "🟢" if total_upl >= 0 else "🔴"
                lines.append(f"📈 Открытых позиций: <b>{len(positions)}</b> · плавающий PnL: {emoji} <b>{total_upl:+.2f} USDT</b>")
            else:
                lines.append("📈 Открытых позиций нет")
        except Exception:
            self.log.exception("Не удалось получить открытые позиции для быстрого статуса")
            lines.append("📈 Позиции: ошибка получения")

        pnl_today = 0.0
        try:
            now = datetime.now(timezone.utc)
            day_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
            trades_today = query_trades(int(day_start.timestamp() * 1000), int(now.timestamp() * 1000))
            pnl_today = sum(t["closed_pnl"] for t in trades_today)
            wins = sum(1 for t in trades_today if t["closed_pnl"] > 0)
            losses = sum(1 for t in trades_today if t["closed_pnl"] < 0)
            emoji = "🟢" if pnl_today >= 0 else "🔴"
            lines.append(f"📊 PnL за сегодня: {emoji} <b>{pnl_today:+.2f} USDT</b> ({len(trades_today)} сделок · W:{wins} L:{losses})")
        except Exception:
            self.log.exception("Не удалось получить статистику за сегодня для быстрого статуса")
            lines.append("📊 PnL за сегодня: ошибка получения")

        lines.append("")
        lines.append("⚠️ <b>Риск-лимиты</b>")
        loss_limit = get_setting("max_daily_loss_alert", cfg.MAX_DAILY_LOSS_ALERT)
        plus_th = get_setting("pnl_alert_plus", cfg.PNL_TRADE_ALERT_PLUS)
        minus_th = get_setting("pnl_alert_minus", cfg.PNL_TRADE_ALERT_MINUS)

        if loss_limit:
            used_pct = min(abs(pnl_today) / loss_limit * 100, 999) if pnl_today < 0 else 0
            bar_len = 10
            filled = min(bar_len, round(used_pct / 100 * bar_len))
            bar = "🟥" * filled + "▫️" * (bar_len - filled)
            lines.append(f"Дневной лимит убытка: {loss_limit:g} USDT\n{bar} использовано {used_pct:.0f}%")
        else:
            lines.append("Дневной лимит убытка: выключен")

        lines.append(f"Алерт на прибыль по сделке: {f'от +{plus_th:g} USDT' if plus_th else 'выключен'}")
        lines.append(f"Алерт на убыток по сделке: {f'от −{minus_th:g} USDT' if minus_th else 'выключен'}")
        lines.append(DIVIDER)
        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Статистика по закрытым сделкам
    # ------------------------------------------------------------------

    @staticmethod
    def compute_stats(trades: list, tz_offset: int = 0) -> dict:
        total_pnl = sum(t["closed_pnl"] for t in trades)
        wins = [t for t in trades if t["closed_pnl"] > 0]
        losses = [t for t in trades if t["closed_pnl"] < 0]
        breakeven = [t for t in trades if t["closed_pnl"] == 0]

        win_sum = sum(t["closed_pnl"] for t in wins)
        loss_sum = sum(t["closed_pnl"] for t in losses)

        win_rate = (len(wins) / len(trades) * 100) if trades else 0
        avg_win = (win_sum / len(wins)) if wins else 0
        avg_loss = (loss_sum / len(losses)) if losses else 0
        profit_factor = (win_sum / abs(loss_sum)) if loss_sum != 0 else (float("inf") if win_sum > 0 else 0)
        expectancy = (total_pnl / len(trades)) if trades else 0

        best = max(trades, key=lambda t: t["closed_pnl"]) if trades else None
        worst = min(trades, key=lambda t: t["closed_pnl"]) if trades else None

        cur_streak_type, cur_streak_len = None, 0
        for t in reversed(trades):
            pnl = t["closed_pnl"]
            cur_type = "win" if pnl > 0 else ("loss" if pnl < 0 else None)
            if cur_type is None:
                break
            if cur_streak_type is None:
                cur_streak_type = cur_type
                cur_streak_len = 1
            elif cur_type == cur_streak_type:
                cur_streak_len += 1
            else:
                break

        max_win_streak = max_loss_streak = run = 0
        run_type = None
        for t in trades:
            pnl = t["closed_pnl"]
            t_type = "win" if pnl > 0 else ("loss" if pnl < 0 else None)
            if t_type == run_type:
                run += 1
            else:
                run_type = t_type
                run = 1
            if t_type == "win":
                max_win_streak = max(max_win_streak, run)
            elif t_type == "loss":
                max_loss_streak = max(max_loss_streak, run)

        cum = 0.0
        peak = 0.0
        max_dd = 0.0
        equity_curve = []
        for t in trades:
            cum += t["closed_pnl"]
            equity_curve.append(cum)
            peak = max(peak, cum)
            max_dd = min(max_dd, cum - peak)

        durations = [
            (t["updated_time"] - t["created_time"]) / 1000 / 60
            for t in trades
            if t["updated_time"] and t["created_time"] and t["updated_time"] > t["created_time"]
        ]
        avg_duration_min = sum(durations) / len(durations) if durations else 0

        by_symbol = {}
        for t in trades:
            sym = t["symbol"]
            by_symbol.setdefault(sym, {"count": 0, "pnl": 0.0})
            by_symbol[sym]["count"] += 1
            by_symbol[sym]["pnl"] += t["closed_pnl"]
        top_symbols = sorted(by_symbol.items(), key=lambda kv: kv[1]["count"], reverse=True)[:5]

        weekday_names = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]
        by_weekday = {i: 0.0 for i in range(7)}
        by_hour = {i: 0.0 for i in range(24)}
        for t in trades:
            if t["updated_time"]:
                dt = datetime.fromtimestamp(t["updated_time"] / 1000, tz=timezone.utc) + timedelta(hours=tz_offset)
                by_weekday[dt.weekday()] += t["closed_pnl"]
                by_hour[dt.hour] += t["closed_pnl"]

        best_weekday = max(by_weekday.items(), key=lambda kv: kv[1]) if trades else None
        worst_weekday = min(by_weekday.items(), key=lambda kv: kv[1]) if trades else None
        best_hour = max(by_hour.items(), key=lambda kv: kv[1]) if trades else None
        worst_hour = min(by_hour.items(), key=lambda kv: kv[1]) if trades else None

        return dict(
            total=len(trades), total_pnl=total_pnl, wins=len(wins), losses=len(losses), breakeven=len(breakeven),
            win_rate=win_rate, avg_win=avg_win, avg_loss=avg_loss, profit_factor=profit_factor, expectancy=expectancy,
            best=best, worst=worst, cur_streak_type=cur_streak_type, cur_streak_len=cur_streak_len,
            max_win_streak=max_win_streak, max_loss_streak=max_loss_streak, max_dd=max_dd,
            avg_duration_min=avg_duration_min, top_symbols=top_symbols, equity_curve=equity_curve,
            weekday_names=weekday_names, best_weekday=best_weekday, worst_weekday=worst_weekday,
            best_hour=best_hour, worst_hour=worst_hour,
        )

    @staticmethod
    def _fmt_duration(minutes: float) -> str:
        if minutes < 60:
            return f"{minutes:.0f} мин"
        if minutes < 60 * 24:
            return f"{minutes / 60:.1f} ч"
        return f"{minutes / 60 / 24:.1f} дн"

    @staticmethod
    def _fmt_delta(cur: float, prev: float, suffix: str = "") -> str:
        if prev == 0 and cur == 0:
            return ""
        diff = cur - prev
        arrow = "▲" if diff > 0 else ("▼" if diff < 0 else "▬")
        return f" ({arrow}{abs(diff):.2f}{suffix} к пред. периоду)"

    def build_stats_message(self, period_name: str, days: int, symbol: str = None) -> str:
        end = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        trades = query_trades(int(start.timestamp() * 1000), int(end.timestamp() * 1000), symbol=symbol)

        title_suffix = f" · {symbol}" if symbol else ""
        title = f"📊 <b>СТАТИСТИКА</b> — {period_name}{title_suffix}"

        if not trades:
            return f"{title}\n{DIVIDER}\n\nЗа этот период закрытых сделок не найдено."

        s = self.compute_stats(trades, tz_offset=get_setting("tz_offset", 0))

        compare_str = ""
        if days < 3000:
            prev_end = start
            prev_start = prev_end - timedelta(days=days)
            prev_trades = query_trades(int(prev_start.timestamp() * 1000), int(prev_end.timestamp() * 1000), symbol=symbol)
            if prev_trades:
                prev_pnl = sum(t["closed_pnl"] for t in prev_trades)
                compare_str = self._fmt_delta(s["total_pnl"], prev_pnl, " USDT")

        pf_str = "∞" if s["profit_factor"] == float("inf") else f"{s['profit_factor']:.2f}"
        streak_emoji = "🔥" if s["cur_streak_type"] == "win" else "❄️"
        streak_str = (
            f"{streak_emoji} {s['cur_streak_len']} {'побед' if s['cur_streak_type'] == 'win' else 'поражений'} подряд"
            if s["cur_streak_type"] else "нет активной серии"
        )

        if s["total_pnl"] > 0:
            verdict = f"📈 <b>Прибыльный период: +{s['total_pnl']:.2f} USDT</b>{compare_str}"
        elif s["total_pnl"] < 0:
            verdict = f"📉 <b>Убыточный период: {s['total_pnl']:.2f} USDT</b>{compare_str}"
        else:
            verdict = f"⚪ <b>Период в ноль (0.00 USDT)</b>{compare_str}"

        lines = [title, DIVIDER, "", verdict, ""]
        lines.append("🎯 <b>Результативность</b>")
        lines.append(f"Сделок: <b>{s['total']}</b>  (🟢 {s['wins']} / 🔴 {s['losses']} / ⚪ {s['breakeven']})")
        lines.append(f"Win rate: <b>{s['win_rate']:.1f}%</b>")
        lines.append(f"Серия сейчас: {streak_str}")
        lines.append(f"Рекордные серии: 🔥{s['max_win_streak']} побед подряд · ❄️{s['max_loss_streak']} поражений подряд")
        lines.append("")
        lines.append("💰 <b>Деньги</b>")
        lines.append(f"Средняя прибыльная сделка: <b>+{s['avg_win']:.2f} USDT</b>")
        lines.append(f"Средняя убыточная сделка: <b>{s['avg_loss']:.2f} USDT</b>")
        lines.append(f"Profit factor: <b>{pf_str}</b>")
        lines.append(f"Ожидание на сделку: <b>{s['expectancy']:+.2f} USDT</b>")
        lines.append(f"Макс. просадка: <b>{s['max_dd']:.2f} USDT</b>")
        lines.append("")
        lines.append("⏱ <b>Время в сделке</b>")
        lines.append(f"В среднем сделка длится: <b>{self._fmt_duration(s['avg_duration_min'])}</b>")
        lines.append("")
        lines.append("🏆 <b>Рекорды периода</b>")
        lines.append(f"Лучшая: {s['best']['symbol']} → <b>+{s['best']['closed_pnl']:.2f} USDT</b>")
        lines.append(f"Худшая: {s['worst']['symbol']} → <b>{s['worst']['closed_pnl']:.2f} USDT</b>")

        if not symbol and s["top_symbols"]:
            lines.append("")
            lines.append("📋 <b>По инструментам</b>")
            for sym, data in s["top_symbols"]:
                emoji = "🟢" if data["pnl"] >= 0 else "🔴"
                lines.append(f"{emoji} <b>{sym}</b> — {data['count']} сделок, {data['pnl']:+.2f} USDT")

        if days >= 7 and s["total"] >= 5:
            wd = s["weekday_names"]
            time_lines = []
            if s["best_weekday"] and s["best_weekday"][1] > 0:
                time_lines.append(f"Прибыльнее всего: {wd[s['best_weekday'][0]]} ({s['best_weekday'][1]:+.2f} USDT)")
            if s["worst_weekday"] and s["worst_weekday"][1] < 0:
                time_lines.append(f"Убыточнее всего: {wd[s['worst_weekday'][0]]} ({s['worst_weekday'][1]:+.2f} USDT)")
            if s["best_hour"] and s["best_hour"][1] > 0:
                time_lines.append(f"Лучший час: {s['best_hour'][0]}:00 ({s['best_hour'][1]:+.2f} USDT)")
            if s["worst_hour"] and s["worst_hour"][1] < 0:
                time_lines.append(f"Худший час: {s['worst_hour'][0]}:00 ({s['worst_hour'][1]:+.2f} USDT)")
            if time_lines:
                lines.append("")
                lines.append("🗓 <b>Когда торгуешь лучше</b>")
                lines.extend(time_lines)

        lines.append("")
        lines.append(DIVIDER)
        return "\n".join(lines)

    def build_top_trades_message(self, days: int, top_n: int = 5) -> str:
        end = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        trades = query_trades(int(start.timestamp() * 1000), int(end.timestamp() * 1000))

        period_name = PERIOD_NAMES.get(days, f"{days} дней")
        title = f"🏆 <b>ТОП СДЕЛОК</b> — {period_name}"
        if not trades:
            return f"{title}\n{DIVIDER}\n\nЗа этот период закрытых сделок не найдено."

        best = sorted(trades, key=lambda t: t["closed_pnl"], reverse=True)[:top_n]
        worst = sorted(trades, key=lambda t: t["closed_pnl"])[:top_n]
        medals = ["🥇", "🥈", "🥉"]

        def fmt(t, i):
            dt = datetime.fromtimestamp(t["updated_time"] / 1000, tz=timezone.utc).strftime("%d.%m %H:%M") if t["updated_time"] else "—"
            mark = medals[i] if i < len(medals) else f"{i + 1}."
            return f"{mark} <b>{t['symbol']}</b> — {t['closed_pnl']:+.2f} USDT  <i>({dt})</i>"

        lines = [title, DIVIDER, "", "🟢 <b>Лучшие сделки</b>"]
        for i, t in enumerate(best):
            lines.append(fmt(t, i))
        lines.append("")
        lines.append("🔴 <b>Худшие сделки</b>")
        for i, t in enumerate(worst):
            lines.append(fmt(t, i))
        lines.append("")
        lines.append(DIVIDER)
        return "\n".join(lines)

    def build_equity_chart(self, days: int, symbol: str = None):
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        BYBIT_YELLOW, BYBIT_BG, BYBIT_GREEN, BYBIT_RED = "#F7A600", "#0b0e11", "#0ECB81", "#F6465D"

        end = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        trades = query_trades(int(start.timestamp() * 1000), int(end.timestamp() * 1000), symbol=symbol)
        if not trades:
            return None

        s = self.compute_stats(trades)
        curve = s["equity_curve"]

        fig, ax = plt.subplots(figsize=(8, 4.5), dpi=140)
        fig.patch.set_facecolor(BYBIT_BG)
        ax.set_facecolor(BYBIT_BG)
        color = BYBIT_GREEN if curve[-1] >= 0 else BYBIT_RED
        ax.plot(range(1, len(curve) + 1), curve, color=color, linewidth=2)
        ax.axhline(0, color="#5a5f66", linewidth=0.8, linestyle="--")
        ax.fill_between(range(1, len(curve) + 1), curve, 0, color=color, alpha=0.18)
        ax.set_title(f"Кривая капитала{f' — {symbol}' if symbol else ''}", fontsize=13, color=BYBIT_YELLOW, fontweight="bold")
        ax.set_xlabel("Сделка №", color="#eaecef")
        ax.set_ylabel("Накопительный PnL, USDT", color="#eaecef")
        ax.tick_params(colors="#848e9c")
        for spine in ax.spines.values():
            spine.set_color("#2b2f36")
        ax.grid(alpha=0.15, color="#848e9c")
        fig.tight_layout()

        buf = io.BytesIO()
        fig.savefig(buf, format="png", facecolor=BYBIT_BG)
        plt.close(fig)
        buf.seek(0)
        return buf

    def build_trades_table_image(self, days: int, symbol: str = None, max_rows: int = 25):
        """Строит аккуратную PNG-таблицу сделок за период: ROI% с учётом
        реального плеча, накопительный баланс по ходу таблицы, тепловая
        подсветка по силе сделки и итоговая строка со сводной статистикой —
        оформление в фирменной тёмной палитре Bybit."""
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        end = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        all_trades = query_trades(int(start.timestamp() * 1000), int(end.timestamp() * 1000), symbol=symbol)
        if not all_trades:
            return None, 0

        total_found = len(all_trades)

        # сводная статистика считается по ВСЕМ сделкам периода, а не только по показанным строкам
        total_pnl = sum(t["closed_pnl"] for t in all_trades)
        wins = [t for t in all_trades if t["closed_pnl"] > 0]
        losses = [t for t in all_trades if t["closed_pnl"] < 0]
        win_rate = (len(wins) / total_found * 100) if total_found else 0
        avg_win = (sum(t["closed_pnl"] for t in wins) / len(wins)) if wins else 0
        avg_loss = (sum(t["closed_pnl"] for t in losses) / len(losses)) if losses else 0
        profit_factor_str = "∞"
        loss_sum = sum(t["closed_pnl"] for t in losses)
        if loss_sum != 0:
            win_sum = sum(t["closed_pnl"] for t in wins)
            profit_factor_str = f"{(win_sum / abs(loss_sum)):.2f}"
        best_id = max(all_trades, key=lambda t: t["closed_pnl"])["id"]
        worst_id = min(all_trades, key=lambda t: t["closed_pnl"])["id"]
        max_abs_pnl = max(abs(t["closed_pnl"]) for t in all_trades) or 1  # для тепловой карты, избегаем деления на 0

        # накопительный баланс считается в хронологическом порядке по ВСЕМ сделкам периода,
        # чтобы колонка "Баланс" отражала реальную кривую капитала, а не только видимые строки
        running_balance = {}
        running = 0.0
        for t in sorted(all_trades, key=lambda t: t["updated_time"]):
            running += t["closed_pnl"]
            running_balance[t["id"]] = running

        trades = list(reversed(all_trades[-max_rows:]))  # свежие сверху, максимум max_rows строк

        COL_HEADERS = ["Дата", "День", "Символ", "Сторона", "Объём", "Вход", "Выход", "Длит-сть", "PnL, USDT", "ROI, %", "Баланс"]
        IDX_WEEKDAY, IDX_PNL, IDX_ROI, IDX_BALANCE = 1, 8, 9, 10
        tz_offset = get_setting("tz_offset", 0)

        rows = []
        row_colors = []
        pnl_values = []
        weekday_idxs = []
        for t in trades:
            dt = datetime.fromtimestamp(t["updated_time"] / 1000, tz=timezone.utc) + timedelta(hours=tz_offset) if t["updated_time"] else None
            date_str = dt.strftime("%d.%m %H:%M") if dt else "—"
            weekday_str = WEEKDAY_NAMES_RU[dt.weekday()] if dt else "—"
            weekday_idxs.append(dt.weekday() if dt else None)
            side_ru = "Short" if t["side"] == "Sell" else "Long"  # side в closed-pnl — сторона закрытой позиции
            pnl = t["closed_pnl"]

            # ROI считаем от реально задействованной маржи (цена * объём / плечо), а не от полной
            # стоимости позиции — так процент отражает настоящую доходность сделки на твой депозит
            position_value = t["entry_price"] * t["qty"] if t["entry_price"] and t["qty"] else 0
            leverage = t["leverage"] if t["leverage"] and t["leverage"] > 0 else 1
            margin = position_value / leverage if leverage else position_value
            roi_pct = (pnl / margin * 100) if margin else 0

            mark = ""
            if t["id"] == best_id:
                mark = " ★"
            elif t["id"] == worst_id:
                mark = " ✗"

            duration_min = (t["updated_time"] - t["created_time"]) / 1000 / 60 if t["updated_time"] and t["created_time"] and t["updated_time"] > t["created_time"] else None
            duration_str = self._fmt_duration(duration_min) if duration_min is not None else "—"

            rows.append([
                date_str,
                weekday_str,
                t["symbol"] + mark,
                side_ru,
                f"{t['qty']:g}",
                f"{t['entry_price']:g}",
                f"{t['exit_price']:g}",
                duration_str,
                f"{pnl:+.2f}",
                f"{roi_pct:+.1f}%",
                f"{running_balance[t['id']]:+.2f}",
            ])

            # тепловая карта в стиле Bybit (тёмная тема): чем сильнее сделка, тем ярче зелёный/красный на тёмном фоне
            intensity = min(abs(pnl) / max_abs_pnl, 1.0)
            if pnl >= 0:
                row_colors.append(_blend_color(BYBIT_BG_ROW, BYBIT_GREEN_DIM, intensity))
            else:
                row_colors.append(_blend_color(BYBIT_BG_ROW, BYBIT_RED_DIM, intensity))
            pnl_values.append(pnl)

        n_data_rows = len(rows)
        n_cols = len(COL_HEADERS)

        avg_duration_all = [
            (t["updated_time"] - t["created_time"]) / 1000 / 60
            for t in all_trades
            if t["updated_time"] and t["created_time"] and t["updated_time"] > t["created_time"]
        ]
        avg_duration_str = self._fmt_duration(sum(avg_duration_all) / len(avg_duration_all)) if avg_duration_all else "—"

        # определяем самый прибыльный и самый убыточный день недели за весь период (по ВСЕМ сделкам)
        weekday_pnl = {i: 0.0 for i in range(7)}
        weekday_count = {i: 0 for i in range(7)}
        for t in all_trades:
            if not t["updated_time"]:
                continue
            wd = (datetime.fromtimestamp(t["updated_time"] / 1000, tz=timezone.utc) + timedelta(hours=tz_offset)).weekday()
            weekday_pnl[wd] += t["closed_pnl"]
            weekday_count[wd] += 1
        active_weekdays = [i for i in range(7) if weekday_count[i] > 0]
        best_weekday_str = worst_weekday_str = "—"
        if active_weekdays:
            best_wd = max(active_weekdays, key=lambda i: weekday_pnl[i])
            worst_wd = min(active_weekdays, key=lambda i: weekday_pnl[i])
            best_weekday_str = f"{WEEKDAY_NAMES_RU[best_wd]} ({weekday_pnl[best_wd]:+.2f})"
            worst_weekday_str = f"{WEEKDAY_NAMES_RU[worst_wd]} ({weekday_pnl[worst_wd]:+.2f})"

        # итоговая строка
        summary_row = [
            "ИТОГО",
            "—",
            f"{total_found} сделок",
            f"W:{len(wins)} L:{len(losses)}",
            f"WR {win_rate:.0f}%",
            f"Avg+ {avg_win:.2f}",
            f"Avg- {avg_loss:.2f}",
            f"~{avg_duration_str}",
            f"{total_pnl:+.2f}",
            f"PF {profit_factor_str}",
            f"{running:+.2f}",
        ]
        rows.append(summary_row)

        fig_height = 1.1 + 0.42 * (n_data_rows + 1)
        fig, ax = plt.subplots(figsize=(13, fig_height), dpi=150)
        fig.patch.set_facecolor(BYBIT_BG)
        ax.set_facecolor(BYBIT_BG)
        ax.axis("off")

        title_symbol = f" — {symbol}" if symbol else ""
        ax.set_title(
            f"Таблица сделок ({PERIOD_NAMES.get(days, str(days) + ' дней')}{title_symbol})\n"
            f"Показано {n_data_rows} из {total_found} · ★ лучшая · ✗ худшая · цвет = сила сделки · ROI от маржи с учётом плеча\n"
            f"Лучший день недели: {best_weekday_str}  ·  Худший день недели: {worst_weekday_str}",
            fontsize=11.5, fontweight="bold", pad=16, loc="left", color=BYBIT_YELLOW,
        )

        table = ax.table(cellText=rows, colLabels=COL_HEADERS, cellLoc="center", loc="upper center")
        table.auto_set_font_size(False)
        table.set_fontsize(9.5)
        table.scale(1, 1.55)

        # шапка — фирменный чёрно-жёлтый Bybit
        for col in range(n_cols):
            cell = table[0, col]
            cell.set_facecolor(BYBIT_YELLOW)
            cell.set_text_props(color="#0b0e11", fontweight="bold")
            cell.set_edgecolor(BYBIT_BG)

        # строки данных
        for r in range(n_data_rows):
            pnl_val = pnl_values[r]
            wd = weekday_idxs[r]
            for col in range(n_cols):
                cell = table[r + 1, col]
                cell.set_facecolor(row_colors[r])
                cell.set_edgecolor("#242830")
                cell.set_linewidth(0.6)
                base_color = BYBIT_GREEN if pnl_val >= 0 else BYBIT_RED
                if col in (IDX_PNL, IDX_ROI, IDX_BALANCE):  # PnL, ROI, Баланс — фирменные зелёный/красный
                    cell.set_text_props(fontweight="bold" if col == IDX_PNL else "normal", color=base_color)
                elif col == IDX_WEEKDAY:
                    # выходные (Сб/Вс) выделяем жёлтым, чтобы паттерн по дням недели бросался в глаза
                    is_weekend = wd is not None and wd >= 5
                    cell.set_text_props(color=BYBIT_YELLOW if is_weekend else "#eaecef", fontweight="bold" if is_weekend else "normal")
                else:
                    cell.set_text_props(color="#eaecef")  # светло-серый текст для остальных колонок

        # итоговая строка — тёмно-жёлтая плашка, как итоговые панели в приложении Bybit
        summary_row_idx = n_data_rows + 1
        for col in range(n_cols):
            cell = table[summary_row_idx, col]
            cell.set_facecolor("#2b2f36")
            cell.set_edgecolor(BYBIT_YELLOW)
            cell.set_text_props(fontweight="bold", color=BYBIT_YELLOW)
            if col == IDX_PNL or col == IDX_BALANCE:
                cell.set_text_props(fontweight="bold", color=BYBIT_GREEN if total_pnl >= 0 else BYBIT_RED)

        fig.tight_layout()
        buf = io.BytesIO()
        fig.savefig(buf, format="png", bbox_inches="tight", facecolor=BYBIT_BG)
        plt.close(fig)
        buf.seek(0)
        return buf, total_found

    def build_csv_export(self, days: int, symbol: str = None):
        end = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        trades = query_trades(int(start.timestamp() * 1000), int(end.timestamp() * 1000), symbol=symbol)
        if not trades:
            return None

        buf = io.StringIO()
        writer = csv.writer(buf)
        writer.writerow(["Символ", "Сторона", "Объём", "Цена входа", "Цена выхода", "PnL (USDT)", "Открыта", "Закрыта"])
        for t in trades:
            opened = datetime.fromtimestamp(t["created_time"] / 1000, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S") if t["created_time"] else ""
            closed = datetime.fromtimestamp(t["updated_time"] / 1000, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S") if t["updated_time"] else ""
            writer.writerow([t["symbol"], t["side"], t["qty"], t["entry_price"], t["exit_price"], f"{t['closed_pnl']:.4f}", opened, closed])

        data = io.BytesIO(buf.getvalue().encode("utf-8-sig"))
        data.seek(0)
        return data

    def check_connection(self) -> str:
        t0 = time.perf_counter()
        try:
            resp = call_with_retry(self.log, self.session.get_server_time, description="get_server_time")
            latency_ms = (time.perf_counter() - t0) * 1000
            ret_code = resp.get("retCode")
            if ret_code == 0:
                return f"🟢 <b>Соединение с Bybit в порядке</b>\n\nЗадержка: {latency_ms:.0f} мс"
            return f"🟡 <b>Bybit ответил с кодом {ret_code}</b>\n\n{resp.get('retMsg', '')}"
        except Exception as e:
            return f"🔴 <b>Не удалось подключиться к Bybit</b>\n\n<code>{e}</code>"

    def build_status_message(self) -> str:
        uptime = datetime.now(timezone.utc) - START_TIME
        hours, rem = divmod(int(uptime.total_seconds()), 3600)
        minutes = rem // 60

        last_sync_ms = get_last_sync_time()
        last_sync_str = (
            datetime.fromtimestamp(last_sync_ms / 1000, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
            if last_sync_ms else "ещё не было"
        )

        total = total_trade_count()
        notify = get_setting("notify_new_trade", cfg.NOTIFY_ON_NEW_TRADE)
        daily = get_setting("enable_daily_report", cfg.ENABLE_DAILY_REPORT)
        weekly = get_setting("enable_weekly_report", cfg.ENABLE_WEEKLY_REPORT)
        loss_limit = get_setting("max_daily_loss_alert", cfg.MAX_DAILY_LOSS_ALERT)
        pnl_plus = get_setting("pnl_alert_plus", cfg.PNL_TRADE_ALERT_PLUS)
        pnl_minus = get_setting("pnl_alert_minus", cfg.PNL_TRADE_ALERT_MINUS)
        quiet_hours = get_setting("quiet_hours", cfg.QUIET_HOURS)
        sync_interval = get_setting("sync_interval_sec", cfg.SYNC_INTERVAL_SEC)

        lines = [
            "ℹ️ <b>Статус учёта сделок</b>\n",
            f"Аптайм процесса: <b>{hours} ч {minutes} мин</b>",
            f"Сделок в базе: <b>{total}</b>",
            f"Последняя фоновая сверка: <b>{last_sync_str}</b>",
            f"Интервал фоновой сверки: {sync_interval} сек (+ мгновенно из торгового движка)",
            f"Категория Bybit: {cfg.CATEGORY} | Testnet: {cfg.TESTNET}",
            f"Уведомления о сделках: {'вкл' if notify else 'выкл'}" + (f" (тихие часы: {quiet_hours})" if quiet_hours else ""),
            f"Ежедневный отчёт: {'вкл в ' + str(get_setting('daily_report_hour', cfg.DAILY_REPORT_HOUR_UTC)) + ':00 UTC' if daily else 'выкл'}",
            f"Еженедельный отчёт: {'вкл' if weekly else 'выкл'}",
            f"Риск-алерт по убытку (сутки): {(str(loss_limit) + ' USDT') if loss_limit > 0 else 'выкл'}",
            f"PnL-алерт по сделке: прибыль {f'от +{pnl_plus:g}' if pnl_plus else 'выкл'} · убыток {f'от −{pnl_minus:g}' if pnl_minus else 'выкл'} USDT",
        ]
        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Фоновые циклы
    # ------------------------------------------------------------------

    def report_sync_result(self, connection_state: dict, success: bool, error: str = None):
        threshold = getattr(cfg, "CONSECUTIVE_ERROR_THRESHOLD", 3)
        notify_enabled = get_setting("notify_connection_issues", cfg.NOTIFY_ON_CONNECTION_ISSUES)
        if success:
            if connection_state["is_down"]:
                connection_state["is_down"] = False
                if notify_enabled:
                    self.tg.notify("🟢 <b>Соединение с Bybit восстановлено.</b> Синхронизация снова работает штатно.")
            connection_state["consecutive_failures"] = 0
        else:
            connection_state["consecutive_failures"] += 1
            if connection_state["consecutive_failures"] >= threshold and not connection_state["is_down"]:
                connection_state["is_down"] = True
                if notify_enabled:
                    self.tg.notify(
                        f"🔴 <b>Проблема с подключением к Bybit</b>\n\n"
                        f"Последние {connection_state['consecutive_failures']} попыток синхронизации завершились ошибкой:\n"
                        f"<code>{error}</code>\n\nБот продолжит пытаться автоматически."
                    )

    def sync_loop(self):
        connection_state = {"is_down": False, "consecutive_failures": 0}
        while True:
            try:
                self.sync_trades()
                self.report_sync_result(connection_state, True)
            except Exception as e:
                self.log.error("Ошибка синхронизации: %s", str(e))
                self.report_sync_result(connection_state, False, str(e))
            time.sleep(get_setting("sync_interval_sec", cfg.SYNC_INTERVAL_SEC))

    def open_positions_pnl_alert_loop(self):
        while True:
            try:
                self.check_open_positions_pnl_alert()
            except Exception:
                self.log.exception("Ошибка в цикле проверки PnL-алерта открытых позиций")
            time.sleep(2)

    # ------------------------------------------------------------------
    # Сигнальные позиции (посты в чате): тейк на весь объём ставится на
    # бирже сразу при открытии (цена последней цели поста), а стоп
    # переносится в безубыток, когда ЦЕНА дойдёт до 2-й цели поста.
    # ------------------------------------------------------------------

    # Префиксы orderLinkId, которыми бот метит СВОИ ЖЕ ордера — по ним и
    # отличаем "бот поставил" от "пользователь поставил сам вручную".
    # sg1-/op1-/op2-/po1- — входные ордера бота; stp1-/stp2-/stp3- и
    # btp1-…btp4- — тейки; sg2- — legacy TP старой версии; cl- — закрытия.
    # mtp1-…mtp3- намеренно не включены в общий набор: это тейки ручных позиций,
    # по которым после потери БД ещё нужно восстановить ручное управление. Их
    # исключаем отдельно только из поиска входных лимиток для изменения размера.
    _BOT_ORDER_LINK_PREFIXES = (
        "sg1-", "sg2-", "stp1-", "stp2-", "stp3-", "btp1-", "btp2-", "btp3-", "btp4-",
        "op1-", "op2-", "po1-", "cl-",
    )

    def _is_manual_entry_limit(self, order: Dict, symbol: str, entry_side: str, position_idx: Optional[int]) -> bool:
        """Обычная ПОЛЬЗОВАТЕЛЬСКАЯ входная лимитка: не бот, не reduce-only, не условная."""
        if not isinstance(order, dict):
            return False
        if order.get("symbol") != symbol or order.get("side") != entry_side:
            return False
        if not _manual_order_position_idx_matches(order, position_idx):
            return False
        reduce_only = order.get("reduceOnly")
        if isinstance(reduce_only, str):
            reduce_only = reduce_only.strip().lower() in {"true", "1", "yes", "y"}
        if bool(reduce_only):
            return False
        if str(order.get("orderType") or "").lower() != "limit":
            return False
        if _is_conditional_stop_type(order.get("stopOrderType")):
            return False
        if str(order.get("orderStatus") or "").strip().lower() == "untriggered":
            return False
        if any(str(order.get("orderLinkId") or "").startswith(p) for p in self._BOT_ORDER_LINK_PREFIXES):
            return False
        if not order.get("orderId"):
            return False
        try:
            return float(order.get("price") or 0) > 0
        except (TypeError, ValueError, OverflowError):
            return False

    def _manual_entry_ladder(self, symbol: str, side: str, live_pos: Dict, open_orders: List[Dict],
                             history: List[Dict], reference_price: float = 0.0) -> Dict:
        """Строит «лестницу» входных лимиток ТЕКУЩЕЙ позиции в порядке исполнения.

        Начало текущей позиции определяется ПО БАЛАНСУ ИСПОЛНЕНИЙ, а не по времени:
        идём от самых свежих исполнений назад, прибавляя закрытия и вычитая входы,
        пока объём не дойдёт до нуля — всё, что старше, относится к прошлым сделкам
        по монете. (createdTime позиции Bybit для этого НЕ годится: это время самой
        первой позиции по монете за всё время, а не текущей.)

        В лестницу входят: исполненные входные лимитки текущей позиции + открытые
        (в том числе частично исполненные). Порядок исполнения: SHORT — цена по
        возрастанию, LONG — по убыванию. Лимитки, выставленные уже ПОСЛЕ первого
        исполнения, в исходную пару не попадают, пока хватает остальных.

        Возвращает {"explained": bool, "members": [(price, ts, order_id, kind, cum_qty, raw)]}.
        explained=False — истории не хватило, чтобы объяснить размер позиции
        (история запаздывает/позиция старше окна): пару по ней фиксировать нельзя.
        """
        result = {"explained": False, "members": [], "remaining": None}
        entry_side = "Buy" if str(side).upper() == "LONG" else "Sell"
        close_side = "Sell" if entry_side == "Buy" else "Buy"
        try:
            live_idx = int(live_pos.get("positionIdx")) if live_pos.get("positionIdx") is not None and str(live_pos.get("positionIdx")).strip() != "" else 0
        except (TypeError, ValueError, OverflowError):
            live_idx = 0
        try:
            live_size = float(live_pos.get("size") or 0)
        except (TypeError, ValueError, OverflowError):
            live_size = 0.0
        if not math.isfinite(live_size) or live_size <= 0:
            return result

        def _num(o, key):
            try:
                v = float(o.get(key) or 0)
            except (TypeError, ValueError, OverflowError):
                return 0.0
            return v if math.isfinite(v) else 0.0

        def _ts(o, *keys):
            for k in keys:
                try:
                    v = int(float(o.get(k) or 0))
                except (TypeError, ValueError, OverflowError):
                    v = 0
                if v > 0:
                    return v
            return 0

        open_by_id: Dict[str, Dict] = {}
        for o in open_orders or []:
            if isinstance(o, dict) and o.get("symbol") == symbol and o.get("orderId"):
                open_by_id[str(o["orderId"])] = o

        events = []   # (ts, delta, member|None): delta>0 — вход, delta<0 — сокращение позиции
        seen = set()
        for o in history or []:
            if not isinstance(o, dict):
                continue
            if o.get("symbol") and o.get("symbol") != symbol:
                continue
            oid = str(o.get("orderId") or "")
            if not oid or oid in seen or oid in open_by_id:
                continue
            if not _manual_order_position_idx_matches(o, live_idx):
                continue
            status = str(o.get("orderStatus") or "").strip().lower().replace("_", "")
            if status not in ("filled", "partiallyfilledcanceled"):
                continue
            cum = _num(o, "cumExecQty")
            ts = _ts(o, "updatedTime", "createdTime")
            if cum <= 0 or ts <= 0:
                continue
            seen.add(oid)
            if o.get("side") == entry_side:
                member = None
                if self._is_manual_entry_limit(o, symbol, entry_side, live_idx):
                    px = _num(o, "avgPrice") or _num(o, "price")
                    if px > 0:
                        member = (px, ts, oid, "filled", cum, o)
                events.append((ts, cum, member))
            elif o.get("side") == close_side:
                events.append((ts, -cum, None))

        unfilled_open = []
        for oid, o in open_by_id.items():
            if not _manual_order_position_idx_matches(o, live_idx):
                continue
            cum = _num(o, "cumExecQty")
            if cum > 0:
                ts = _ts(o, "updatedTime", "createdTime")
                if o.get("side") == entry_side:
                    member = None
                    if self._is_manual_entry_limit(o, symbol, entry_side, live_idx) and _num(o, "price") > 0:
                        member = (_num(o, "price"), ts, oid, "partial", cum, o)
                    events.append((ts, cum, member))
                elif o.get("side") == close_side:
                    events.append((ts, -cum, None))
            elif self._is_manual_entry_limit(o, symbol, entry_side, live_idx):
                unfilled_open.append((_num(o, "price"), _ts(o, "createdTime"), oid, "open", 0.0, o))

        # Идём назад от самых свежих событий, пока объём не дойдёт до нуля.
        events.sort(key=lambda e: e[0], reverse=True)
        tol = max(live_size * 0.005, 1e-12)
        remaining = live_size
        window_members = []
        first_entry_ts = 0
        explained = False
        for ts, delta, member in events:
            remaining -= delta
            if delta > 0:
                first_entry_ts = ts if not first_entry_ts else min(first_entry_ts, ts)
            if member:
                window_members.append(member)
            if remaining <= tol:
                explained = True
                break
        result["explained"] = explained
        result["remaining"] = remaining
        if not explained:
            return result

        if not window_members and reference_price > 0:
            # Исполнений своими лимитками нет: берём только открытые с правильной стороны рынка.
            tol_ref = max(abs(reference_price) * 1e-10, 1e-12)
            unfilled_open = [
                m for m in unfilled_open
                if (m[0] >= reference_price - tol_ref if entry_side == "Sell" else m[0] <= reference_price + tol_ref)
            ]
        if first_entry_ts:
            not_late = [m for m in unfilled_open if not (m[1] and m[1] > first_entry_ts)]
            if len(window_members) + len(not_late) >= 2:
                unfilled_open = not_late

        members = list(window_members) + unfilled_open
        members.sort(key=lambda m: ((m[0] if entry_side == "Sell" else -m[0]), m[1], m[2]))
        result["members"] = members
        return result

    def _select_manual_entry_orders(self, symbol: str, side: str, live_pos: Dict, open_orders: List[Dict], allow_history_recovery: bool = True) -> Tuple[List[float], List[str], str]:
        """Выбирает ДВЕ исходные ручные входные лимитки максимально устойчиво.

        Нормальный сценарий: обе ближайшие валидные LIMIT ещё открыты -> берём
        их по расстоянию до цены обнаружения. Сложный сценарий: первая из этих
        двух уже успела исполниться ДО того, как бот впервые увидел позицию ->
        восстанавливаем её из истории и выбираем второй ордер относительно цены
        фактического первого входа, а не относительно новой рыночной цены.

        Это принципиально: если рынок после первого исполнения ушёл ниже/выше,
        простая повторная сортировка текущих ордеров может выбрать третью
        лимитку вместо исходной второй. Сохраняемые orderId после этого становятся
        единственным источником истины для данной ручной позиции.
        """
        entry_side = "Buy" if side == "LONG" else "Sell"
        # Если раньше бот уже закрепил L1/L2, эти orderId и цены важнее
        # текущей близости к рынку. Это предотвращает подмену второй лимитки
        # третьей после исполнения первой или движения markPrice. Запись может
        # быть terminal: её историческая цена всё равно нужна для стоп-якоря.
        try:
            try:
                live_position_idx = int(live_pos.get("positionIdx")) if live_pos.get("positionIdx") is not None else 0
            except (TypeError, ValueError):
                live_position_idx = 0
            persisted_slots = []
            persisted_slots_repaired = False
            l2_history_unavailable = False
            for r in get_manual_limit_slot_rows(symbol):
                # Стоп-якорь может быть только из закреплённых слотов L1/L2.
                # Старые/ошибочные записи L3+ никогда не должны участвовать в выборе.
                try:
                    saved_slot = int(r.get("slot") or 0)
                except (TypeError, ValueError):
                    continue
                if saved_slot not in (1, 2):
                    continue
                if str(r.get("side") or "") != entry_side or not str(r.get("order_id") or ""):
                    continue
                try:
                    saved_price = float(r.get("price") or 0)
                except (TypeError, ValueError, OverflowError):
                    saved_price = float("nan")
                if not math.isfinite(saved_price) or saved_price <= 0:
                    # A malformed L2 record must not silently fall back to a
                    # newly-ranked L3/L4 order. Fail closed and retry after the
                    # exact pinned orderId can be reconciled from exchange history.
                    if saved_slot == 2:
                        l2_history_unavailable = True
                        self.log.error(
                            f"[{symbol}] Сохранённая L2 имеет некорректную цену {r.get('price')!r}; "
                            "пару не переупорядочиваю и стоп от другого входа не рассчитываю."
                        )
                    else:
                        self.log.warning(
                            f"[{symbol}] Сохранённая L1 имеет некорректную цену {r.get('price')!r}; запись пропущена."
                        )
                    continue
                try:
                    saved_idx = int(r.get("position_idx")) if r.get("position_idx") is not None else None
                except (TypeError, ValueError):
                    saved_idx = None
                # В hedge-mode нельзя переносить ID между long/short positionIdx.
                if live_position_idx not in (None, 0) and saved_idx != live_position_idx:
                    continue
                if live_position_idx == 0 and saved_idx not in (None, 0):
                    continue
                persisted_slots.append(r)
            if l2_history_unavailable:
                self.log.error(
                    f"[{symbol}] Нельзя доверять сохранённой цене L2; откладываю выбор пары до точной сверки по orderId."
                )
                return [], [], "history_unavailable_retry"
            persisted_slots.sort(key=lambda r: int(r.get("slot") or 99))
            if persisted_slots:
                # Исправление устаревшей ошибочной привязки: если L1 и L2
                # ОБЕ всё ещё открыты и не исполнены, сверяем пару с реальными
                # входными лимитками. Старый код безусловно доверял сохранённому
                # L2; если раньше туда ошибочно попал четвёртый ордер, эта ошибка
                # закреплялась навсегда. Проверка не применяется после исполнения
                # любой из двух лимиток — тогда исходный ID/цена должны сохраниться.
                try:
                    rows_by_slot = {int(r.get("slot") or 0): r for r in persisted_slots}
                    slot1 = rows_by_slot.get(1)
                    slot2 = rows_by_slot.get(2)
                    open_by_id = {
                        str(o.get("orderId")): o for o in (open_orders or [])
                        if o.get("orderId")
                    }
                    o1 = open_by_id.get(str((slot1 or {}).get("order_id") or ""))
                    o2 = open_by_id.get(str((slot2 or {}).get("order_id") or ""))

                    # orderId often survives an exchange-side price amendment. The pinned
                    # slot must keep the current exchange price (especially L2, which is
                    # the stop anchor), otherwise the SL percentage button would calculate
                    # from a stale price after a manual amend. Never adopt a different ID
                    # here and never sync a bot/closing order.
                    for slot_row in list(persisted_slots):
                        try:
                            pinned_id = str(slot_row.get("order_id") or "")
                            live_order = open_by_id.get(pinned_id)
                            if not pinned_id or not isinstance(live_order, dict):
                                continue
                            if (str(live_order.get("symbol") or "") != symbol
                                    or str(live_order.get("side") or "") != entry_side
                                    or str(live_order.get("orderType") or "").lower() != "limit"):
                                continue
                            if any(str(live_order.get("orderLinkId") or "").startswith(x) for x in self._BOT_ORDER_LINK_PREFIXES):
                                continue
                            ro = live_order.get("reduceOnly")
                            if isinstance(ro, str):
                                ro = ro.strip().lower() in {"true", "1", "yes", "y"}
                            if ro:
                                continue
                            if not _manual_order_position_idx_matches(live_order, live_position_idx):
                                continue
                            live_price = float(live_order.get("price") or 0)
                            live_qty = float(live_order.get("qty") or 0)
                            if not math.isfinite(live_price) or live_price <= 0:
                                continue
                            if not math.isfinite(live_qty) or live_qty < 0:
                                continue
                            saved_price = float(slot_row.get("price") or 0)
                            saved_qty = float(slot_row.get("qty") or 0)
                            if abs(live_price - saved_price) > max(abs(live_price) * 1e-12, 1e-12) or abs(live_qty - saved_qty) > max(abs(live_qty) * 1e-12, 1e-12):
                                slot_no = int(slot_row.get("slot") or 0)
                                saved_ok = save_manual_limit_slot(
                                    symbol, slot_no, pinned_id, entry_side, live_price, live_qty,
                                    float(slot_row.get("target_notional_usdt") or get_setting(f"manual_limit{slot_no}_value_usdt", 10.0) or 0),
                                    status="active", replace=False,
                                    position_idx=int(live_order.get("positionIdx") or 0),
                                )
                                if saved_ok:
                                    persisted_slots_repaired = True
                        except (TypeError, ValueError, OverflowError) as slot_sync_error:
                            self.log.warning(f"[{symbol}] Не удалось синхронизировать цену закреплённой L{slot_row.get('slot')} с биржей: {slot_sync_error}")
                    # If a pinned entry is no longer in open-orders, it may have
                    # filled/cancelled between scans. Query its exact ID history so
                    # an exchange-side price amendment immediately before fill is
                    # not lost and L2 does not keep an obsolete stop anchor forever.
                    for slot_row in list(persisted_slots):
                        try:
                            pinned_id = str(slot_row.get("order_id") or "")
                            if not pinned_id or pinned_id in open_by_id:
                                continue
                            historical = self.client.get_order_state(symbol, pinned_id)
                            if not isinstance(historical, dict) or not historical:
                                if int(slot_row.get("slot") or 0) == 2:
                                    l2_history_unavailable = True
                                continue
                            if (str(historical.get("symbol") or "") != symbol
                                    or str(historical.get("orderId") or "") != pinned_id
                                    or str(historical.get("side") or "") != entry_side
                                    or str(historical.get("orderType") or "").lower() != "limit"):
                                if int(slot_row.get("slot") or 0) == 2:
                                    l2_history_unavailable = True
                                self.log.warning(f"[{symbol}] История закреплённой L{slot_row.get('slot')} {pinned_id} не совпадает по идентичности; цена не синхронизирована")
                                continue
                            hist_reduce_only = historical.get("reduceOnly")
                            if isinstance(hist_reduce_only, str):
                                hist_reduce_only = hist_reduce_only.strip().lower() in {"true", "1", "yes", "y"}
                            if hist_reduce_only:
                                continue
                            try:
                                hist_idx = int(historical.get("positionIdx")) if historical.get("positionIdx") is not None and str(historical.get("positionIdx")).strip() != "" else None
                                saved_idx = int(slot_row.get("position_idx")) if slot_row.get("position_idx") is not None and str(slot_row.get("position_idx")).strip() != "" else None
                            except (TypeError, ValueError, OverflowError):
                                if int(slot_row.get("slot") or 0) == 2:
                                    l2_history_unavailable = True
                                continue
                            if live_position_idx in (1, 2):
                                if hist_idx != live_position_idx and not (hist_idx is None and saved_idx == live_position_idx):
                                    if int(slot_row.get("slot") or 0) == 2:
                                        l2_history_unavailable = True
                                    self.log.warning(f"[{symbol}] История L{slot_row.get('slot')} {pinned_id} имеет другой/неизвестный positionIdx; цена не синхронизирована")
                                    continue
                            elif live_position_idx == 0 and hist_idx not in (None, 0):
                                continue
                            try:
                                hist_price = float(historical.get("price") or 0)
                                hist_qty = float(historical.get("qty") or slot_row.get("qty") or 0)
                            except (TypeError, ValueError, OverflowError):
                                if int(slot_row.get("slot") or 0) == 2:
                                    l2_history_unavailable = True
                                continue
                            if not math.isfinite(hist_price) or hist_price <= 0 or not math.isfinite(hist_qty) or hist_qty < 0:
                                if int(slot_row.get("slot") or 0) == 2:
                                    l2_history_unavailable = True
                                continue
                            hist_status_raw = str(historical.get("orderStatus") or "").strip().lower().replace("_", "").replace(" ", "")
                            if hist_status_raw in {"new", "partiallyfilled", "untriggered", "created"}:
                                hist_status, hist_terminal_reason = "active", None
                            elif hist_status_raw in {"filled", "partiallyfilledcanceled"}:
                                hist_status, hist_terminal_reason = "filled", hist_status_raw
                            elif hist_status_raw in {"cancelled", "canceled", "rejected", "deactivated"}:
                                hist_status, hist_terminal_reason = "cancelled", hist_status_raw
                            else:
                                hist_status, hist_terminal_reason = "unknown", hist_status_raw or "unknown_status"
                            old_price = float(slot_row.get("price") or 0)
                            old_qty = float(slot_row.get("qty") or 0)
                            old_status = str(slot_row.get("status") or "")
                            if (abs(hist_price - old_price) > max(abs(hist_price) * 1e-12, 1e-12)
                                    or abs(hist_qty - old_qty) > max(abs(hist_qty) * 1e-12, 1e-12)
                                    or old_status != hist_status):
                                slot_no = int(slot_row.get("slot") or 0)
                                saved_ok = save_manual_limit_slot(
                                    symbol, slot_no, pinned_id, entry_side, hist_price, hist_qty,
                                    float(slot_row.get("target_notional_usdt") or get_setting(f"manual_limit{slot_no}_value_usdt", 10.0) or 0),
                                    status=hist_status, terminal_reason=hist_terminal_reason,
                                    replace=False, position_idx=hist_idx if hist_idx is not None else saved_idx,
                                )
                                if saved_ok:
                                    if abs(hist_price - old_price) > max(abs(hist_price) * 1e-12, 1e-12):
                                        persisted_slots_repaired = True
                                    self.log.info(
                                        f"[{symbol}] Синхронизирована история L{slot_no} {pinned_id}: "
                                        f"price {old_price:g}->{hist_price:g}, status {old_status or 'unknown'}->{hist_status}"
                                    )
                        except Exception as history_sync_error:
                            if int(slot_row.get("slot") or 0) == 2:
                                l2_history_unavailable = True
                            self.log.warning(f"[{symbol}] Не удалось синхронизировать исторический статус закреплённой L{slot_row.get('slot')}: {history_sync_error}")

                    if l2_history_unavailable:
                        self.log.warning(
                            f"[{symbol}] Точная история L2 {((rows_by_slot.get(2) or {}).get('order_id') if 'rows_by_slot' in locals() else '')} недоступна/не прошла проверку; "
                            "не использую устаревшую цену якоря. Требуется повторная сверка."
                        )
                        return [], [], "history_unavailable_retry"

                    if persisted_slots_repaired:
                        persisted_slots = get_manual_limit_slot_rows(symbol)
                        persisted_slots = [r for r in persisted_slots if int(r.get("slot") or 0) in (1, 2)]
                        persisted_slots.sort(key=lambda r: int(r.get("slot") or 99))
                        rows_by_slot = {int(r.get("slot") or 0): r for r in persisted_slots}
                        slot1 = rows_by_slot.get(1)
                        slot2 = rows_by_slot.get(2)
                        o1 = open_by_id.get(str((slot1 or {}).get("order_id") or ""))
                        o2 = open_by_id.get(str((slot2 or {}).get("order_id") or ""))

                    # Once signal_positions and the two SQLite slots agree on
                    # exact order IDs, treat that pair as immutable. Re-ranking it
                    # against today's market or a newly added L3/L4 order could
                    # silently swap the stop anchor away from the user's original L2.
                    pair_locked_to_signal = True if persisted_slots else False
                    try:
                        current_pair_state = get_signal_position(symbol) or {}
                        current_pair_ids = [str(x) for x in (current_pair_state.get("entry_order_ids") or [])]
                        pair_locked_to_signal = (
                            str(current_pair_state.get("source") or "").lower() == "manual"
                            and len(current_pair_ids) >= 2
                            and str((slot1 or {}).get("order_id") or "") == current_pair_ids[0]
                            and str((slot2 or {}).get("order_id") or "") == current_pair_ids[1]
                        )
                    except Exception as pair_state_error:
                        # On a DB read problem prefer preserving existing identity;
                        # do not opportunistically bind another order as L2.
                        pair_locked_to_signal = bool(persisted_slots)
                        self.log.warning(f"[{symbol}] Не удалось сверить идентичность L1/L2 с signal_positions; сохраняю закреплённые ID: {pair_state_error}")

                    def _is_unfilled_new(order):
                        if not order:
                            return False
                        status = str(order.get("orderStatus") or "New").strip().lower()
                        try:
                            executed = float(order.get("cumExecQty") or 0)
                        except (TypeError, ValueError):
                            executed = 0.0
                        return status == "new" and executed <= 0

                    def _is_terminal_or_missing(order):
                        if not order:
                            return True
                        status = str(order.get("orderStatus") or "").strip().lower().replace("_", "")
                        return status in {"filled", "partiallyfilledcanceled", "cancelled", "canceled", "rejected", "deactivated"}

                    if slot1 and slot2 and _is_unfilled_new(o1) and _is_unfilled_new(o2) and not pair_locked_to_signal:
                        ref = float(live_pos.get("markPrice") or live_pos.get("avgPrice") or 0)
                        candidates = []
                        if ref > 0:
                            for o in (open_orders or []):
                                try:
                                    if o.get("symbol") != symbol or o.get("side") != entry_side:
                                        continue
                                    if str(o.get("orderType") or "").lower() != "limit":
                                        continue
                                    if any(str(o.get("orderLinkId") or "").startswith(x) for x in self._BOT_ORDER_LINK_PREFIXES):
                                        continue
                                    ro = o.get("reduceOnly")
                                    if isinstance(ro, str):
                                        ro = ro.strip().lower() in {"true", "1", "yes", "y"}
                                    if bool(ro):
                                        continue
                                    oi = int(o.get("positionIdx") or 0)
                                    if live_position_idx not in (None, 0) and oi != live_position_idx:
                                        continue
                                    if live_position_idx == 0 and oi != 0:
                                        continue
                                    px = float(o.get("price") or 0)
                                    if px <= 0:
                                        continue
                                    tol = max(abs(ref) * 1e-10, 1e-12)
                                    if side == "LONG" and px > ref + tol:
                                        continue
                                    if side == "SHORT" and px < ref - tol:
                                        continue
                                    candidates.append((abs(px-ref), -px if side == "LONG" else px, str(o.get("orderId")), o, px))
                                except (TypeError, ValueError):
                                    continue
                            candidates.sort(key=lambda x: (x[0], x[1], x[2]))
                            candidate_ids = {x[2] for x in candidates}
                            saved_ids = [str(rows_by_slot.get(n, {}).get("order_id") or "") for n in (1, 2)]
                            # Не пересортировываем закреплённую пару по рынку,
                            # если один из сохранённых ордеров сам уже не подходит
                            # под текущую сторону рынка: это может быть обычное
                            # движение цены, а не ошибка слота. Ремонтируем лишь
                            # доказанно неверную пару, где ОБА старых ордера всё
                            # ещё открыты и входят в тот же допустимый пул.
                            if len(candidates) >= 2 and all(oid in candidate_ids for oid in saved_ids):
                                expected = candidates[:2]
                                expected_ids = [x[2] for x in expected]
                                if expected_ids != saved_ids:
                                    # Заменяем пару одной транзакцией. Иначе уникальный
                                    # индекс order_id блокировал перестановку L1↔L2,
                                    # а последовательные записи могли оставить полупару.
                                    replacement_items = []
                                    for slot_no, item in enumerate(expected, start=1):
                                        o = item[3]
                                        q = float(o.get("qty") or 0)
                                        idx = int(o.get("positionIdx") or 0)
                                        notional = float(rows_by_slot.get(slot_no, {}).get("target_notional_usdt") or get_setting(f"manual_limit{slot_no}_value_usdt", 10.0) or 0)
                                        replacement_items.append({
                                            "slot": slot_no, "order_id": item[2], "side": entry_side,
                                            "price": item[4], "qty": q, "target_notional_usdt": notional,
                                            "status": "active", "position_idx": idx,
                                        })
                                    repaired = replace_manual_limit_slots_atomically(
                                        symbol, replacement_items,
                                        expected_order_ids={1: saved_ids[0], 2: saved_ids[1]},
                                    )
                                    if repaired:
                                        persisted_slots_repaired = True
                                        self.log.warning(f"[{symbol}] Исправлена устаревшая пара L1/L2 по открытым лимиткам: {saved_ids} -> {expected_ids}; L3/L4 больше не используются вместо L2")
                                        persisted_slots = get_manual_limit_slot_rows(symbol)
                                        persisted_slots = [r for r in persisted_slots if int(r.get("slot") or 0) in (1, 2)]
                                        persisted_slots.sort(key=lambda r: int(r.get("slot") or 99))
                    # Если L1 уже исполнена/исчезла, а сохранённая L2 всё ещё
                    # открыта, исправляем устаревший L2 только если есть другой
                    # входной ордер ближе к ИСХОДНОЙ цене L1. Это закрывает случай,
                    # когда старая версия уже закрепила L4 как L2, а затем L1
                    # исполнилась: простая проверка двух открытых ордеров больше
                    # не сработала бы. L3/L4 не могут вытеснить более близкую L2.
                    elif slot1 and slot2 and _is_terminal_or_missing(o1) and _is_unfilled_new(o2) and not pair_locked_to_signal:
                        try:
                            anchor1 = float(slot1.get("price") or 0)
                            if anchor1 > 0:
                                alternatives = []
                                for o in (open_orders or []):
                                    try:
                                        oid = str(o.get("orderId") or "")
                                        if not oid or oid == str(slot2.get("order_id") or ""):
                                            continue
                                        if o.get("symbol") != symbol or o.get("side") != entry_side or str(o.get("orderType") or "").lower() != "limit":
                                            continue
                                        if any(str(o.get("orderLinkId") or "").startswith(x) for x in self._BOT_ORDER_LINK_PREFIXES):
                                            continue
                                        ro = o.get("reduceOnly")
                                        if isinstance(ro, str): ro = ro.strip().lower() in {"true", "1", "yes", "y"}
                                        if bool(ro): continue
                                        if not _is_unfilled_new(o): continue
                                        oi = int(o.get("positionIdx") or 0)
                                        if live_position_idx not in (None, 0) and oi != live_position_idx: continue
                                        if live_position_idx == 0 and oi != 0: continue
                                        px = float(o.get("price") or 0)
                                        if px <= 0: continue
                                        tol = max(abs(anchor1) * 1e-10, 1e-12)
                                        if side == "LONG" and px >= anchor1 - tol: continue
                                        if side == "SHORT" and px <= anchor1 + tol: continue
                                        alternatives.append((abs(px-anchor1), oid, o, px))
                                    except (TypeError, ValueError):
                                        continue
                                alternatives.sort(key=lambda x: (x[0], x[1]))
                                old_l2_price = float(slot2.get("price") or 0)
                                if alternatives and alternatives[0][0] + max(anchor1 * 1e-10, 1e-12) < abs(old_l2_price-anchor1):
                                    _, oid2, order2, px2 = alternatives[0]
                                    ok = save_manual_limit_slot(
                                        symbol, 2, oid2, entry_side, px2,
                                        float(order2.get("qty") or 0),
                                        float(slot2.get("target_notional_usdt") or get_setting("manual_limit2_value_usdt", 10.0) or 0),
                                        status="active", replace=True, position_idx=int(order2.get("positionIdx") or 0),
                                    )
                                    if ok:
                                        persisted_slots_repaired = True
                                        self.log.warning(f"[{symbol}] Исправлена L2 после исполнения L1: старый L2={slot2.get('order_id')} ({old_l2_price}), новый L2={oid2} ({px2}); выбран ближайший корректный ордер к исходной L1")
                                        persisted_slots = get_manual_limit_slot_rows(symbol)
                                        persisted_slots = [r for r in persisted_slots if int(r.get("slot") or 0) in (1, 2)]
                                        persisted_slots.sort(key=lambda r: int(r.get("slot") or 99))
                        except Exception as post_fill_repair_error:
                            self.log.warning(f"[{symbol}] Не удалось восстановить правильную L2 после исполнения L1: {post_fill_repair_error}")
                except Exception as repair_error:
                    self.log.warning(f"[{symbol}] Не удалось безопасно проверить старую пару L1/L2; сохраняю прежние закреплённые ID: {repair_error}")
                if persisted_slots:
                    return (
                        [float(r["price"]) for r in persisted_slots[:2]],
                        [str(r["order_id"]) for r in persisted_slots[:2]],
                        "persisted_manual_limit_slots_repaired" if persisted_slots_repaired else "persisted_manual_limit_slots",
                    )
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось прочитать сохранённые слоты ручных лимиток, использую безопасное восстановление: {e}")

        reference_price = float(live_pos.get("markPrice") or live_pos.get("avgPrice") or 0)
        avg_entry = float(live_pos.get("avgPrice") or 0)
        try:
            live_qty = float(live_pos.get("size") or 0)
        except (TypeError, ValueError):
            live_qty = 0.0
        position_idx_raw = live_pos.get("positionIdx")
        try:
            position_idx = int(position_idx_raw)
        except (TypeError, ValueError):
            position_idx = None

        def position_idx_matches(order: Dict) -> bool:
            # В hedge-режиме и при неизвестном индексе позиции не подбираем
            # заявки с несовпадающим positionIdx: иначе можно связать L2
            # другой стороны и выставить стоп от чужого входа.
            return _manual_order_position_idx_matches(order, position_idx)

        def valid_manual_entry(order: Dict) -> bool:
            if order.get("symbol") != symbol or order.get("side") != entry_side:
                return False
            if not position_idx_matches(order):
                return False
            reduce_only = order.get("reduceOnly")
            if isinstance(reduce_only, str):
                reduce_only = reduce_only.strip().lower() in {"true", "1", "yes", "y"}
            if bool(reduce_only):
                return False
            if str(order.get("orderType") or "").lower() != "limit":
                return False
            if any(str(order.get("orderLinkId") or "").startswith(p) for p in self._BOT_ORDER_LINK_PREFIXES):
                return False
            if not order.get("orderId"):
                return False
            try:
                price = float(order.get("price") or 0)
            except (TypeError, ValueError):
                return False
            return price > 0

        def directional_price_ok(price: float, ref: float) -> bool:
            # Небольшой допуск нужен только для числовой погрешности на границе.
            tol = max(abs(ref) * 1e-10, 1e-12)
            if side == "LONG":
                return price <= ref + tol
            return price >= ref - tol

        # 1) Сначала собираем ВСЕ валидные пользовательские LIMIT по символу.
        # Отдельно строим directional-подмножество для обычного сценария
        # "две ближайшие к текущему рынку". Хранение всех кандидатов нужно для
        # восстановления после быстрого движения рынка: уже исполненный первый
        # вход мог оставить вторую/третью лимитку формально по другую сторону
        # текущего markPrice, но это всё ещё исходные ордера позиции.
        all_open_candidates = []
        open_ids = set()
        for o in open_orders or []:
            if not valid_manual_entry(o):
                continue
            try:
                price = float(o.get("price") or 0)
            except (TypeError, ValueError):
                continue
            oid = str(o.get("orderId"))
            open_ids.add(oid)
            try:
                created_ts = int(o.get("createdTime") or 0)
            except (TypeError, ValueError):
                created_ts = 0
            all_open_candidates.append({"price": price, "order_id": oid, "created_ts": created_ts, "raw": o})

        directional_open_candidates = []
        for item in all_open_candidates:
            price = item["price"]
            if not directional_price_ok(price, reference_price):
                continue
            distance = abs(price - reference_price)
            # При одинаковом расстоянии предпочитаем более близкую к рынку
            # сторону цены: LONG — более высокую, SHORT — более низкую.
            tie_price = -price if side == "LONG" else price
            directional_open_candidates.append((distance, tie_price, price, item["order_id"], item["raw"]))

        directional_open_candidates.sort(key=lambda x: (x[0], x[1]))

        # ------------------------------------------------------------------
        # ЛЕСТНИЦА ВХОДОВ ТЕКУЩЕЙ ПОЗИЦИИ (исправление «берёт последние лимитки»).
        #
        # Старая логика ниже искала исполненный вход в истории за 30 ДНЕЙ и
        # сверяла его с avgPrice позиции с допуском 0.1–0.15%. Она ломалась:
        #   1) если в истории монеты были исполненные лимитки ПРОШЛЫХ сделок —
        #      «исполненных входов 2+», своя L1 терялась, парой становились
        #      2-я/3-я (или одна лимитка);
        #   2) если 2-я лимитка исполнилась ЧАСТИЧНО — avgPrice уходил от цены
        #      1-й дальше допуска, L1 «не находилась», парой становились 2-я и 3-я;
        #   3) если лимитки стоят плотнее 0.1% — avgPrice «совпадал» с открытой 2-й.
        # Теперь пара = ПЕРВЫЕ ДВЕ лимитки лестницы текущей позиции
        # (исполненные + открытые, порядок исполнения). См. _manual_entry_ladder.
        # ------------------------------------------------------------------
        prefetched_history = None
        if allow_history_recovery and avg_entry > 0 and live_qty > 0:
            try:
                prefetched_history = self.client.get_symbol_order_history(symbol, days=30)
            except Exception as ladder_err:
                prefetched_history = None
                self.log.warning(f"[{symbol}] Не удалось получить историю для построения лестницы входов: {ladder_err}")
            if prefetched_history is not None:
                ladder = self._manual_entry_ladder(symbol, side, live_pos, open_orders, prefetched_history, reference_price)
                if not ladder["explained"]:
                    # История запаздывает или позиция старше окна: пару закреплять нельзя —
                    # она фиксируется навсегда. Вызывающий код повторит попытку в следующем цикле.
                    self.log.warning(
                        f"[{symbol}] История исполнений не объясняет размер позиции "
                        f"(остаток {ladder.get('remaining')}); пару лимиток пока не закрепляю"
                    )
                    return ([], [], "history_unavailable_retry")
                ladder_members = ladder["members"]
                if len(ladder_members) >= 2:
                    pair = ladder_members[:2]
                    self.log.info(
                        f"[{symbol}] Лестница входов: {[(m[2], m[0], m[3]) for m in ladder_members]} -> "
                        f"первые две: {[m[2] for m in pair]}"
                    )
                    return ([m[0] for m in pair], [m[2] for m in pair], "position_window_ladder")

        # ВАЖНО: открытый PartiallyFilled LIMIT нельзя терять только потому,
        # что рынок уже ушёл через него. Если его avgPrice совпадает с текущим
        # avgPrice позиции, это надёжный признак первого входа. Сначала фиксируем
        # такой ордер, затем выбираем ВТОРОЙ исходный вход относительно его цены.
        partial_first = None
        if avg_entry > 0:
            partial_candidates = []
            partial_tol = max(avg_entry * 0.0015, 1e-12)
            for item in all_open_candidates:
                try:
                    cum_exec_qty = float(item["raw"].get("cumExecQty") or 0)
                except (TypeError, ValueError):
                    cum_exec_qty = 0.0
                try:
                    fill_price = float(item["raw"].get("avgPrice") or item["price"] or 0)
                except (TypeError, ValueError):
                    fill_price = item["price"]
                if cum_exec_qty <= 0 or fill_price <= 0:
                    continue
                if abs(fill_price - avg_entry) > partial_tol:
                    continue
                partial_candidates.append((abs(fill_price - avg_entry), -cum_exec_qty, -item["created_ts"], item, fill_price))
            partial_candidates.sort(key=lambda x: (x[0], x[1], x[2], x[3]["order_id"]))
            if partial_candidates:
                partial_first = partial_candidates[0]
                first_item = partial_first[3]
                first_price = partial_first[4]
                remaining = [x for x in all_open_candidates if x["order_id"] != first_item["order_id"]]
                # Для уже частично исполненного ордера updatedTime ближе к
                # фактическому fill, чем createdTime. Поэтому новую лимитку,
                # поставленную ПОСЛЕ первого fill, не допускаем в исходную пару.
                try:
                    first_ts = int(first_item["raw"].get("updatedTime") or first_item.get("created_ts") or 0)
                except (TypeError, ValueError):
                    first_ts = first_item.get("created_ts") or 0
                before_first = [
                    x for x in remaining
                    if not first_ts or not x.get("created_ts") or x["created_ts"] <= first_ts
                ]
                pool = before_first or remaining
                compatible = []
                anchor_tol = max(abs(first_price) * 1e-10, 1e-12)
                for x in pool:
                    if side == "LONG" and x["price"] > first_price + anchor_tol:
                        continue
                    if side == "SHORT" and x["price"] < first_price - anchor_tol:
                        continue
                    compatible.append(x)
                if compatible:
                    compatible.sort(key=lambda x: (abs(x["price"] - first_price), x["price"] if side == "LONG" else -x["price"], x.get("created_ts") or 0, x["order_id"]))
                    second_item = compatible[0]
                    return (
                        [first_price, second_item["price"]],
                        [first_item["order_id"], second_item["order_id"]],
                        "open_partial_first_plus_nearest",
                    )

        # Если avgPrice уже совпадает с одной из открытых лимиток, это обычно
        # значит, что позиция была получена именно от неё. В таком случае при
        # наличии ещё одной корректной лимитки можно сразу зафиксировать пару.
        # Если avgPrice НЕ совпадает ни с одной из открытых, сначала проверяем
        # историю: это и есть ключевой признак того, что одна исходная лимитка
        # уже исполнилась, а две/три следующие всё ещё висят.
        avg_matches_open = False
        if avg_entry > 0:
            match_tol = max(avg_entry * 0.001, 1e-12)
            avg_matches_open = any(abs(item["price"] - avg_entry) <= match_tol for item in all_open_candidates)

        history = []
        history_attempted = False
        history_failed = False
        need_history = bool(allow_history_recovery and avg_entry > 0 and (
            len(directional_open_candidates) < 2 or not avg_matches_open
        ))
        if need_history:
            history_attempted = True
            if prefetched_history is not None:
                history = prefetched_history
            else:
                try:
                    history = self.client.get_symbol_order_history(symbol, days=30)
                except Exception as e:
                    history_failed = True
                    self.log.warning(f"[{symbol}] Не удалось получить историю для восстановления ручных входов: {e}")

        # Обычный случай без признаков уже исполненного первого входа.
        if len(directional_open_candidates) >= 2 and avg_matches_open:
            selected = directional_open_candidates[:2]
            return (
                [x[2] for x in selected],
                [x[3] for x in selected],
                "open_pair",
            )

        filled_candidates = []
        filled_seen_ids = set()
        for o in history or []:
            if not valid_manual_entry(o):
                continue
            order_id = str(o.get("orderId"))
            if order_id in open_ids or order_id in filled_seen_ids:
                continue
            filled_seen_ids.add(order_id)
            status = str(o.get("orderStatus") or "").lower()
            if status not in ("filled", "partiallyfilledcanceled"):
                continue
            try:
                cum_qty = float(o.get("cumExecQty") or 0)
            except (TypeError, ValueError):
                cum_qty = 0.0
            if cum_qty <= 0:
                continue
            try:
                fill_price = float(o.get("avgPrice") or o.get("price") or 0)
            except (TypeError, ValueError):
                fill_price = 0.0
            if fill_price <= 0:
                continue
            try:
                ts = int(o.get("updatedTime") or o.get("createdTime") or o.get("orderTime") or 0)
            except (TypeError, ValueError):
                ts = 0
            filled_candidates.append({
                "price": fill_price,
                "qty": cum_qty,
                "order_id": str(o.get("orderId")),
                "ts": ts,
                "raw": o,
            })

        # Если история содержит реальный manual LIMIT, соответствующий текущей
        # avgPrice, используем его как УЖЕ ИСПОЛНЕННУЮ первую из пары даже тогда,
        # когда после неё осталось 2+ лимиток. Это закрывает критичный сценарий:
        # A=109 исполнилась, B=108 и C=107 ещё висят — выбираем A+B, а не B+C.
        # Этот путь предназначен именно для случая ОДНОЙ уже исполненной
        # исходной лимитки. Если история уже показывает 2+ исполненных manual
        # LIMIT по текущей позиции, нельзя брать первую + текущую открытую:
        # при неравных объёмах avgPrice может быть очень близок к первой, и тогда
        # третья открытая лимитка ошибочно станет "второй". Ниже для 2+ fill
        # используется отдельная реконструкция пары по avgPrice + объёму.
        if len(filled_candidates) == 1 and avg_entry > 0 and all_open_candidates:
            avg_tol = max(avg_entry * 0.0015, 1e-12)
            ranked_first = []
            for f in filled_candidates:
                if abs(f["price"] - avg_entry) > avg_tol:
                    continue
                ranked_first.append((abs(f["price"] - avg_entry), -f["ts"], f))
            ranked_first.sort(key=lambda x: (x[0], x[1]))
            if ranked_first:
                first = ranked_first[0][2]
                pending_candidates = []
                anchor_tol = max(abs(first["price"]) * 1e-10, 1e-12)

                # Сначала рассматриваем только лимитки, которые уже существовали
                # к моменту исполнения первого входа. Это не даёт новой третьей
                # лимитке, поставленной ПОСЛЕ первого fill, попасть в исходную
                # пару и стать стоп-якорем. Если timestamp недоступен или
                # подходящих старых ордеров нет, ниже безопасно используем все
                # валидные ордера на правильной стороне от первого входа.
                before_first = []
                if first.get("ts"):
                    before_first = [
                        x for x in all_open_candidates
                        if not x.get("created_ts") or x["created_ts"] <= first["ts"]
                    ]
                pool = before_first or all_open_candidates

                for x in pool:
                    if side == "LONG" and x["price"] > first["price"] + anchor_tol:
                        continue
                    if side == "SHORT" and x["price"] < first["price"] - anchor_tol:
                        continue
                    distance = abs(x["price"] - first["price"])
                    tie_price = -x["price"] if side == "LONG" else x["price"]
                    pending_candidates.append((distance, tie_price, x["price"], x["order_id"]))
                pending_candidates.sort(key=lambda x: (x[0], x[1]))
                if pending_candidates:
                    second = pending_candidates[0]
                    return ([first["price"], second[2]], [first["order_id"], second[3]], "history_first_plus_nearest_open")

        # Самый важный fallback: одна лимитка ещё открыта, а первая уже
        # исполнилась. Ищем исторический вход, который реально соответствует
        # текущей средней цене позиции, а затем выбираем вторую лимитку
        # относительно ЭТОЙ цены, а не относительно текущего markPrice.
        if len(all_open_candidates) == 1 and len(filled_candidates) == 1 and avg_entry > 0:
            pending = all_open_candidates[0]
            avg_tol = max(avg_entry * 0.01, abs(pending["price"]) * 1e-4, 1e-12)
            ranked = []
            for f in filled_candidates:
                price = f["price"]
                # Первый ближайший вход должен находиться с правильной стороны
                # от второго: LONG — выше/на уровне второго, SHORT — ниже/на уровне.
                if side == "LONG" and price + avg_tol < pending["price"]:
                    continue
                if side == "SHORT" and price - avg_tol > pending["price"]:
                    continue
                price_diff = abs(price - avg_entry)
                # Сначала близость к реальному avgPrice, затем свежесть.
                ranked.append((price_diff, -f["ts"], f))
            ranked.sort(key=lambda x: (x[0], x[1]))
            if ranked:
                first = ranked[0][2]
                first_item = (
                    abs(first["price"] - reference_price),
                    (-first["price"] if side == "LONG" else first["price"]),
                    first["price"],
                    first["order_id"],
                )
                # Это [ближайший, второй] для дальнейшего anchor = second.
                return (
                    [first_item[2], pending["price"]],
                    [first_item[3], pending["order_id"]],
                    "history_first_plus_open_second",
                )

        # Если история была нужна именно для восстановления исполненного
        # первого входа, но API истории временно недоступен, НЕ фиксируем
        # текущую пару B+C как окончательную — она может быть неправильной.
        # Возвращаем специальный источник; вызывающий сканер не создаст
        # постоянную запись и повторит попытку в следующем проходе.
        if history_attempted and history_failed and all_open_candidates and not avg_matches_open:
            return ([], [], "history_unavailable_retry")

        # Если история успешно проверена, но подходящего исполненного первого
        # входа в ней нет, считаем это обычной ручной позицией с текущими
        # pending-лимитками и используем две ближайшие.
        if len(directional_open_candidates) >= 2 and len(filled_candidates) < 2:
            selected = directional_open_candidates[:2]
            return (
                [x[2] for x in selected],
                [x[3] for x in selected],
                "open_pair_after_history_check",
            )

        # 3) Если две ручные входные лимитки уже исполнились, сначала пытаемся
        # восстановить ИМЕННО их по истории. Нельзя до этой проверки взять
        # текущие C/D и случайно сделать C второй исходной лимиткой. Из двух
        # исполнений можем восстановить исходную пару по текущему avgPrice
        # и суммарному исполненному объёму. Это полезно после быстрого прохода
        # цены через обе лимитки ещё до первого запуска/рестарта бота.
        if len(filled_candidates) >= 2 and avg_entry > 0 and live_qty > 0:
            # Оставляем только разумное число самых свежих кандидатов; история
            # одного символа за 30 дней может быть большой, а нам нужна локальная
            # реконструкция текущей позиции.
            filled_candidates.sort(key=lambda x: x["ts"], reverse=True)
            pool = filled_candidates[:80]
            best = None
            n = len(pool)
            for i in range(n):
                a = pool[i]
                for j in range(i + 1, n):
                    b = pool[j]
                    # Для LONG более дорогой ордер — ближайший к рынку; для SHORT
                    # наоборот, более дешёвый — ближайший.
                    if side == "LONG" and a["price"] < b["price"]:
                        first, second = b, a
                    elif side == "LONG":
                        first, second = a, b
                    elif a["price"] > b["price"]:
                        first, second = b, a
                    else:
                        first, second = a, b

                    qsum = a["qty"] + b["qty"]
                    qty_diff_ratio = abs(qsum - live_qty) / max(live_qty, 1e-12) if live_qty > 0 else 0.0
                    if live_qty > 0 and qty_diff_ratio > 0.06:
                        continue
                    weighted_avg = (a["price"] * a["qty"] + b["price"] * b["qty"]) / qsum if qsum > 0 else 0
                    avg_diff = abs(weighted_avg - avg_entry) / max(avg_entry, 1e-12)
                    if avg_diff > 0.0025:
                        continue
                    # Небольшой бонус за свежесть пары. Главная метрика —
                    # соответствие текущей средней цене и объёму.
                    newest_ts = max(a["ts"], b["ts"])
                    temporal_gap = abs(a["ts"] - b["ts"]) if a["ts"] and b["ts"] else 10**18
                    score = (avg_diff, qty_diff_ratio, temporal_gap, -newest_ts)
                    if best is None or score < best[0]:
                        best = (score, first, second)
            if best:
                first, second = best[1], best[2]
                return ([first["price"], second["price"]], [first["order_id"], second["order_id"]], "history_two_fills")

        # 4) Честный безопасный fallback, когда восстановить пару нельзя.
        # Никаких чужих/третьих ордеров здесь не выбираем.
        if len(directional_open_candidates) == 1:
            x = directional_open_candidates[0]
            return ([x[2]], [x[3]], "single_open_fallback")
        if directional_open_candidates:
            x = directional_open_candidates[0]
            return ([x[2]], [x[3]], "open_fallback")
        return ([avg_entry] if avg_entry > 0 else [], [], "avg_only_fallback")

    def _audit_manual_entry_pair(self, symbol: str, side: str, live_pos: Dict, open_orders: List[Dict]) -> str:
        """Один раз за запуск проверяет пару L1/L2 уже отслеживаемой ручной позиции.

        Раньше пара могла быть закреплена НЕВЕРНО (2-я/3-я вместо 1-й/2-й), а после
        закрепления она не пересматривалась никогда. Исправляем только доказанную
        ошибку: пара пересобирается, когда по восстановленной лестнице входов
        (история полностью объясняет размер позиции) ОБЕ сохранённые лимитки в ней
        есть, а первые две лимитки — другие и БЛИЖЕ к рынку. Если сохранённая лимитка
        отменена пользователем, историей не подтверждается или лестница даёт более
        далёкие цены — ничего не меняем.
        """
        state = self.__dict__.setdefault("_manual_pair_audit", {}).setdefault(symbol, {"done": False, "tries": 0})
        if state["done"]:
            return "done"
        if state["tries"] >= 3:
            state["done"] = True
            return "gave_up"
        state["tries"] += 1
        sp = get_signal_position(symbol) or {}
        if sp.get("source") != "manual" or sp.get("breakeven_done") or (sp.get("manual_tp_done") or {}).get("1"):
            state["done"] = True
            return "not_applicable"
        stored_ids = [str(x) for x in (sp.get("entry_order_ids") or [])]
        try:
            stored_prices = [float(x) for x in (sp.get("entries") or [])]
        except (TypeError, ValueError, OverflowError):
            stored_prices = []
        if len(stored_ids) != 2 or len(stored_prices) != 2:
            state["done"] = True
            return "no_pair"
        try:
            history = self.client.get_symbol_order_history(symbol, days=30)
        except Exception as e:
            self.log.warning(f"[{symbol}] Ревизия пары L1/L2: история недоступна ({state['tries']}/3): {e}")
            return "history_error"
        reference_price = 0.0
        try:
            reference_price = float(live_pos.get("markPrice") or live_pos.get("avgPrice") or 0)
        except (TypeError, ValueError, OverflowError):
            reference_price = 0.0
        ladder = self._manual_entry_ladder(symbol, side, live_pos, open_orders, history, reference_price)
        if not ladder["explained"]:
            self.log.warning(f"[{symbol}] Ревизия пары L1/L2: история не объясняет размер позиции ({state['tries']}/3) — пока не трогаю")
            return "unexplained"
        state["done"] = True
        members = ladder["members"]
        member_ids = [m[2] for m in members]
        if len(members) < 2 or not all(i in member_ids for i in stored_ids):
            return "stored_not_in_ladder"
        expected = members[:2]
        expected_ids = [m[2] for m in expected]
        if expected_ids == stored_ids:
            return "ok"
        expected_prices = [float(m[0]) for m in expected]
        # Чиним только «слишком далёкие» лимитки: новая пара должна быть не дальше сохранённой.
        sign = 1.0 if str(side).upper() == "SHORT" else -1.0
        if any(sign * (new - old) > max(abs(old) * 1e-9, 1e-12) for new, old in zip(expected_prices, stored_prices)):
            self.log.warning(f"[{symbol}] Ревизия пары L1/L2: лестница даёт более дальние цены, чем сохранено — не меняю")
            return "ladder_farther"

        rows = {int(r.get("slot") or 0): r for r in get_manual_limit_slot_rows(symbol)}
        items = []
        for slot, m in enumerate(expected, start=1):
            raw = m[5]
            filled = m[3] == "filled"
            try:
                qty = float(raw.get("cumExecQty") or raw.get("qty") or 0) if filled else float(raw.get("qty") or 0)
            except (TypeError, ValueError, OverflowError):
                qty = 0.0
            try:
                idx = int(raw.get("positionIdx") or 0)
            except (TypeError, ValueError):
                idx = 0
            notional = float((rows.get(slot) or {}).get("target_notional_usdt") or get_setting(f"manual_limit{slot}_value_usdt", 10.0) or 0)
            items.append({
                "slot": slot, "order_id": m[2], "side": "Buy" if str(side).upper() == "LONG" else "Sell",
                "price": float(m[0]), "qty": qty, "target_notional_usdt": notional,
                "status": "filled" if filled else "active",
                "terminal_reason": "filled" if filled else None, "position_idx": idx,
            })

        with self._manual_limit_value_lock:
            if not update_manual_entry_pair(symbol, expected_prices, expected_ids,
                                            expected_order_ids=stored_ids, expected_entries=stored_prices):
                self.log.warning(f"[{symbol}] Ревизия пары L1/L2: сохранённая пара изменилась параллельно — пропускаю")
                state["done"] = False
                return "cas_conflict"
            if set(rows) == {1, 2}:
                slots_ok = replace_manual_limit_slots_atomically(
                    symbol, items, expected_order_ids={1: str(rows[1].get("order_id") or ""), 2: str(rows[2].get("order_id") or "")},
                )
            elif not rows:
                slots_ok = save_manual_limit_slots_atomically(symbol, items)
            else:
                slots_ok = False
            if not slots_ok:
                # Возвращаем пару сделки назад, чтобы сделка и слоты не разошлись.
                update_manual_entry_pair(symbol, stored_prices, stored_ids, expected_order_ids=expected_ids, expected_entries=expected_prices)
                self.log.error(f"[{symbol}] Ревизия пары L1/L2: не удалось обновить слоты в SQLite — пара оставлена прежней")
                return "slots_failed"

        self.log.warning(f"[{symbol}] Исправлена ошибочно закреплённая пара L1/L2: {stored_ids}{stored_prices} -> {expected_ids}{expected_prices}")
        try:
            result = self._recalculate_manual_position_protection(
                symbol, live_pos, reason="исправление пары L1/L2 (первые две лимитки)",
                use_open_order_anchor=True, preserve_existing_stop=False,
            )
            stop_txt = fmt_num(result.get("stop")) if result.get("stop") else "—"
            ok_txt = "стоп обновлён" if result.get("stop_ok") else "⚠️ обновление стопа не подтверждено — проверь на бирже"
        except Exception:
            self.log.exception(f"[{symbol}] Пара L1/L2 исправлена, но пересчёт защиты не удался")
            stop_txt, ok_txt = "—", "⚠️ пересчёт стопа не удался — проверь на бирже"
        try:
            self.tg.notify(
                f"🔧 <b>{symbol}</b>: пара входных лимиток была закреплена неверно "
                f"({' / '.join(fmt_num(p) for p in stored_prices)}). Теперь это первые две: "
                f"{' / '.join(fmt_num(p) for p in expected_prices)}. Стоп от L2: {stop_txt} ({ok_txt})."
            )
        except Exception:
            self.log.exception(f"[{symbol}] Не удалось отправить уведомление об исправлении пары")
        return "repaired"

    def scan_manual_positions(self):
        """Находит позиции, которые пользователь открыл САМ на Bybit (не
        через посты в этом чате и не через памп-шорт стратегию бота), и
        берёт их под управление — с процентами по умолчанию для ручных
        сделок (MANUAL_TRADE_* в config.py), а не для постов. Определяет
        "своё" по метке orderLinkId на ордерах символа: если ни один ордер
        (открытый или из недавней истории) не помечен ни одним из известных
        префиксов бота — значит, ордер выставлен вручную, символ ручной."""
        if not get_setting("manual_trade_management_enabled", getattr(cfg, "MANUAL_TRADE_MANAGEMENT_ENABLED_DEFAULT", True)):
            return
        try:
            already_tracked = set(get_all_open_signal_positions().keys())
            positions = self.client.get_all_open_positions()
            # Причины, по которым позиция в этом проходе НЕ была взята под управление
            # (раньше большинство пропусков было молчаливым) и счётчики повторов.
            skip_reasons: Dict[str, str] = {}
            history_retries = self.__dict__.setdefault("_manual_adopt_history_retries", {})
            if not positions:
                self._update_untracked_watchdog([], {}, set(), set(), set())
                history_retries.clear()
                return

            # Доп. защита: если у памп-шорт стратегии есть свой список
            # отслеживаемых символов — не трогаем их тоже, даже если по
            # каким-то причинам их ордера не попались в окно поиска меток.
            # Не выходим при отсутствии новых позиций: ниже есть обязательная
            # перепроверка уже отслеживаемых manual-позиций и исправление старой L2.
            pump_engine = getattr(self.tg, "engine", None)
            pump_symbols = set(getattr(pump_engine, "_known_open_symbols", set()) or set())

            # Не блокируем ручное управление только потому, что ЭТОТ ЖЕ
            # символ когда-то торговался ботом. История ордеров за 14 дней не
            # доказывает, что текущая позиция открыта ботом. Источник истины —
            # текущий реестр bot_positions / живые бот-символы и только активные
            # помеченные ордера.
            # Открытые ордера запрашиваются ОДИН раз за проход (раньше дважды). При
            # сбое не прерываем весь проход: уже отслеживаемые позиции остаются под
            # управлением, а захват новых в этот цикл пропускается (повтор позже).
            # Они нужны также, чтобы для ещё не полностью набранной ручной
            # ШОРТ-позиции стоп считался от ВЕРХНЕЙ ожидающей лимитки (для LONG — нижней).
            open_orders_fetch_ok = True
            try:
                open_orders_all = self.client.get_open_orders_all()
            except Exception:
                # В этот цикл НЕЛЬЗЯ восстанавливать исходную пару по истории:
                # список pending-ордеров неизвестен, поэтому история может привести
                # к ложному выбору второго якоря. Следующий цикл повторит запрос.
                open_orders_all = []
                open_orders_fetch_ok = False
                self.log.exception("Не удалось получить открытые ордера при сканировании ручных позиций")
            tagged_symbols = set()
            bot_open_prefixes = self._BOT_ORDER_LINK_PREFIXES
            for o in open_orders_all:
                link = str(o.get("orderLinkId", ""))
                if any(link.startswith(p) for p in bot_open_prefixes) and o.get("symbol"):
                    tagged_symbols.add(o.get("symbol"))
            try:
                current_bot_symbols = set(get_all_bot_positions().keys())
            except Exception:
                current_bot_symbols = set()
            engine_lock = getattr(pump_engine, "_known_lock", None)
            if engine_lock is not None:
                try:
                    with engine_lock:
                        current_bot_symbols.update(getattr(pump_engine, "_known_open_symbols", set()) or set())
                except Exception:
                    current_bot_symbols.update(getattr(pump_engine, "_known_open_symbols", set()) or set())
            else:
                current_bot_symbols.update(getattr(pump_engine, "_known_open_symbols", set()) or set())
            # Символы с неподтверждённым входом бота ведёт сам бот (_resolve_unresolved_entries):
            # иначе позиция была бы ошибочно захвачена здесь как «ручная».
            try:
                current_bot_symbols.update(set((getattr(pump_engine, "_unresolved_entries", None) or {}).keys()))
            except Exception:
                pass
            registry_symbols = set(current_bot_symbols)  # реестр бота БЕЗ символов, найденных только по меткам ордеров
            current_bot_symbols.update(tagged_symbols)

            manual_tp_pct = 3.0 / 100.0
            # Keep the configured value in human percent units (1..10) everywhere.
            # A prior mix of fraction units in initial capture and percent units in
            # reconciliation made it easy for a later edit to apply /100 twice or
            # not at all. _calculate_manual_l2_stop is now the single formula.
            manual_stop_pct = get_manual_stop_percent()
            manual_tp2_pct = get_manual_tp_close_percent()

            excluded = set(get_excluded_symbols())
            for pos in positions:
                try:
                    symbol = pos["symbol"]
                    if symbol in excluded or (pump_symbols and symbol in pump_symbols):
                        continue  # исключённые символы и памп-шорт не трогаем

                    # Ранее уже отслеживаемые ручные позиции тоже нужно перепроверять:
                    # в противном случае старая ошибочная L2= L4 в БД/позиции остаётся
                    # навсегда, потому что ниже первичное обнаружение для них пропускается.
                    if symbol in already_tracked:
                        tracked_sp = get_signal_position(symbol) or {}
                        tp1_done = bool(tracked_sp.get("breakeven_done")) or bool((tracked_sp.get("manual_tp_done") or {}).get("1"))
                        live_side_raw = str(pos.get("side") or "")
                        tracked_side = "LONG" if live_side_raw == "Buy" else "SHORT" if live_side_raw == "Sell" else None
                        saved_side = str(tracked_sp.get("side") or "").upper()
                        if tracked_sp.get("source") == "manual" and (tracked_side is None or saved_side != tracked_side):
                            # signal_positions is currently keyed by symbol. In hedge mode
                            # a second leg may share the same symbol, and must never borrow
                            # the first leg's L2 anchor or have its SL overwritten.
                            self.log.error(
                                f"[{symbol}] Конфликт стороны ручной позиции: live={live_side_raw!r}, "
                                f"SQLite={saved_side!r}. Управление этой ногой и переназначение L1/L2 пропущены."
                            )
                            continue
                        if tracked_sp.get("source") == "manual" and open_orders_fetch_ok:
                            try:
                                with self._manual_limit_value_lock:
                                    tracked_entries, tracked_ids, tracked_source = self._select_manual_entry_orders(
                                        symbol, tracked_side, pos, open_orders_all,
                                        allow_history_recovery=open_orders_fetch_ok,
                                    )
                                if tracked_source == "persisted_manual_limit_slots_repaired":
                                    old_ids = [str(x) for x in (tracked_sp.get("entry_order_ids") or [])]
                                    old_entries = list(tracked_sp.get("entries") or [])
                                    prices_changed = (
                                        len(tracked_entries) == 2 and len(old_entries) == 2
                                        and any(
                                            abs(float(new_px) - float(old_px)) > max(abs(float(new_px)) * 1e-12, 1e-12)
                                            for new_px, old_px in zip(tracked_entries, old_entries)
                                        )
                                    )
                                    if (tracked_ids != old_ids or prices_changed) and len(tracked_entries) == 2 and len(tracked_ids) == 2:
                                        if update_manual_entry_pair(
                                            symbol, tracked_entries, tracked_ids,
                                            expected_order_ids=old_ids,
                                            expected_entries=old_entries if len(old_entries) == 2 else None,
                                        ):
                                            self.log.warning(
                                                f"[{symbol}] Синхронизирована исправленная пара ручных входов в signal_positions: "
                                                f"{old_ids} -> {tracked_ids}; цены {old_entries} -> {tracked_entries}"
                                            )
                                            if not tp1_done:
                                                repair_result = self._recalculate_manual_position_protection(
                                                    symbol, pos,
                                                    reason="исправление сохранённой пары L1/L2",
                                                    use_open_order_anchor=True,
                                                    preserve_existing_stop=False,
                                                )
                                                if not repair_result.get("stop_ok"):
                                                    self.log.error(
                                                        f"[{symbol}] Пара L1/L2 исправлена, но обновление SL не подтверждено: "
                                                        f"{repair_result.get('reason') or repair_result.get('stop')}"
                                                    )
                            except Exception:
                                self.log.exception(f"[{symbol}] Не удалось исправить пару L1/L2 у уже отслеживаемой ручной позиции")
                        if tracked_sp.get("source") == "manual" and open_orders_fetch_ok and not tp1_done:
                            try:
                                self._audit_manual_entry_pair(symbol, tracked_side, pos, open_orders_all)
                            except Exception:
                                self.log.exception(f"[{symbol}] Ревизия пары L1/L2 не удалась")
                        continue  # уже отслеживается; после возможной сверки не создавать запись повторно

                    if symbol in current_bot_symbols:
                        if symbol in registry_symbols:
                            skip_reasons[symbol] = "символ в реестре бота (bot_positions / памп-стратегия / неподтверждённый вход)"
                        else:
                            skip_reasons[symbol] = "по символу есть активные ордера с метками бота (sg/po/op/stp/btp/cl) — позиция не считается ручной"
                        continue  # незакреплённая позиция с метками ордеров бота не является ручной

                    live_side_raw = str(pos.get("side") or "")
                    if live_side_raw not in {"Buy", "Sell"}:
                        self.log.error(f"[{symbol}] Пропускаю захват ручной позиции: неизвестная сторона {live_side_raw!r}")
                        skip_reasons[symbol] = f"биржа вернула неизвестную сторону позиции {live_side_raw!r}"
                        continue
                    side = "LONG" if live_side_raw == "Buy" else "SHORT"
                    try:
                        avg_entry = float(pos.get("avgPrice") or 0)
                        live_qty = float(pos.get("size") or 0)
                    except (TypeError, ValueError, OverflowError):
                        self.log.error(f"[{symbol}] Пропускаю захват ручной позиции: цена/объём не являются числами")
                        skip_reasons[symbol] = "avgPrice/size позиции не являются числами"
                        continue
                    if not math.isfinite(avg_entry) or not math.isfinite(live_qty) or avg_entry <= 0 or live_qty <= 0:
                        self.log.error(f"[{symbol}] Пропускаю захват ручной позиции: некорректные avgPrice/size ({avg_entry!r}/{live_qty!r})")
                        skip_reasons[symbol] = f"некорректные avgPrice/size ({avg_entry!r}/{live_qty!r})"
                        continue

                    target = avg_entry * (1 + manual_tp_pct) if side == "LONG" else avg_entry * (1 - manual_tp_pct)

                    # Без достоверного списка открытых ордеров или при временной
                    # недоступности истории нельзя безопасно решить, какая именно
                    # лимитка является второй исходной. Не создаём постоянную запись
                    # с сомнительным anchor: следующий цикл повторит обнаружение и
                    # попытается восстановить пару заново. Так третья лимитка никогда
                    # не превращается в ошибочный стоп просто из-за REST-сбоя.
                    if not open_orders_fetch_ok:
                        self.log.warning(f"[{symbol}] Пропускаю захват ручной позиции в этом цикле: список открытых ордеров недоступен")
                        skip_reasons[symbol] = "список открытых ордеров недоступен (повтор в следующем цикле)"
                        continue

                    with self._manual_limit_value_lock:
                        nearest_two, selected_entry_order_ids, selection_source = self._select_manual_entry_orders(
                            symbol, side, pos, open_orders_all, allow_history_recovery=open_orders_fetch_ok
                        )

                        if selection_source == "history_unavailable_retry":
                            retries = int(history_retries.get(symbol, 0)) + 1
                            history_retries[symbol] = retries
                            try:
                                max_retries = max(1, int(getattr(cfg, "MANUAL_ADOPT_HISTORY_MAX_RETRIES", 3)))
                            except (TypeError, ValueError):
                                max_retries = 3
                            if retries < max_retries:
                                self.log.warning(
                                    f"[{symbol}] Не удалось восстановить исходную пару ручных лимиток (попытка {retries}/{max_retries}) — "
                                    "повторю в следующем цикле без фиксации сомнительного стоп-якоря"
                                )
                                skip_reasons[symbol] = f"история ордеров недоступна, повтор {retries}/{max_retries}"
                                continue
                            # История недоступна уже несколько циклов подряд, а позиция живёт
                            # БЕЗ сопровождения. Позиция без стопа опаснее стопа от запасного
                            # якоря, поэтому берём её под управление по доступным данным
                            # (открытые лимитки / средняя цена) и честно предупреждаем.
                            nearest_two, selected_entry_order_ids, selection_source = self._select_manual_entry_orders(
                                symbol, side, pos, open_orders_all, allow_history_recovery=False
                            )
                            selection_source = f"{selection_source}+history_unavailable_fallback"
                            self.log.error(
                                f"[{symbol}] История ордеров недоступна {retries} циклов подряд — беру позицию под управление "
                                f"с запасным якорем стопа ({selection_source})."
                            )
                            self.tg.notify(
                                f"⚠️ <b>{symbol}</b>: не удалось восстановить историю входов (Bybit недоступен, история запаздывает или позиция старше 30 дней), а позиция была без сопровождения. "
                                "Взял её под управление с запасным якорем стопа (по открытым лимиткам/средней цене) — проверь стоп."
                            )

                        # Стоп считается именно от ВТОРОЙ зафиксированной лимитки.
                        # Главное отличие от старой логики: если первая уже успела
                        # исполниться, второй ордер не переопределяется третьим только
                        # потому, что рынок успел далеко уйти.
                        stop_anchor = nearest_two[1] if len(nearest_two) >= 2 else (nearest_two[0] if nearest_two else avg_entry)
                        try:
                            stop = _calculate_manual_l2_stop(side, stop_anchor, manual_stop_pct)
                        except (TypeError, ValueError, OverflowError) as stop_calc_error:
                            self.log.error(
                                f"[{symbol}] Не создаю запись ручной позиции: нельзя корректно рассчитать SL от L2 "
                                f"(side={side}, anchor={stop_anchor!r}, percent={manual_stop_pct!r}): {stop_calc_error}"
                            )
                            continue

                        create_signal_position({
                            "symbol": symbol, "side": side,
                            # Сохраняем именно цены ДВУХ выбранных ближайших входов
                            # в порядке [ближайший, второй]. Это позволяет после
                            # исполнения первого входа и даже после рестарта точно
                            # восстановить стоп от ИМЕННО второй исходной лимитки,
                            # не подменяя её третьей лимиткой пользователя.
                            "entries": nearest_two if nearest_two else [avg_entry], "targets": [target],
                            "stop_price": stop, "avg_entry_price": avg_entry, "qty_total": live_qty,
                            # Храним только две выбранные ближайшие ручные лимитки.
                            # После TP будет отменена только оставшаяся из них.
                            "entry_order_ids": selected_entry_order_ids, "breakeven_after_tp1": True,
                            "single_target_is_partial": True, "source": "manual",
                        })
                        # Записываем те же orderId в реестр слотов. После этой точки
                        # монитор стопа/TP и изменение стоимости лимиток используют одну
                        # и ту же пару, а не пересчитывают её по текущей цене.
                        seed_position_state = get_signal_position(symbol) or {}
                        # Если history API не вернул positionIdx у уже исполненного
                        # ордера, используем фактический индекс позиции из ответа биржи.
                        seed_position_state["_live_position_idx"] = pos.get("positionIdx")
                        self._seed_manual_limit_slots_from_position(symbol, seed_position_state)
                        update_signal_position_opened(symbol, live_qty)
                        history_retries.pop(symbol, None)
                    sp_now = get_signal_position(symbol) or {}
                    result = self._recalculate_manual_position_protection(
                        symbol, pos,
                        reason="первичное обнаружение ручной позиции",
                        use_open_order_anchor=True,
                        preserve_existing_stop=False,
                    )
                    self.log.info(
                        f"[{symbol}] Ручная позиция взята под управление: "
                        f"TP={fmt_num(result.get('target', target))}, "
                        f"SL={fmt_num(result.get('stop', stop))}, "
                        f"TP order={result.get('tp_order_id')}, "
                        f"entry_pair={nearest_two}, source={selection_source}"
                    )
                    self.tg.notify(
                        f"👀 <b>{symbol}</b>: нашёл ручную позицию (не через посты) — взял под управление. "
                        f"{side}, вход ≈{fmt_num(avg_entry)}, 4 тейка по общим настройкам бота/ручных сделок, "
                        f"TP4 закрывает весь остаток; стоп {fmt_num(result.get('stop', stop))} ({fmt_num(manual_stop_pct)}%)."
                    )
                except Exception:
                    # Сбой на ОДНОЙ позиции не должен останавливать обработку остальных:
                    # раньше исключение (БД, REST, расчёт защиты) прерывало весь проход,
                    # и позиции после неё в списке не брались под управление вовсе.
                    bad_symbol = str((pos or {}).get("symbol") or "?")
                    self.log.exception(f"[{bad_symbol}] Ошибка при взятии ручной позиции под управление — остальные позиции проверяю дальше, повторю в следующем цикле")
                    skip_reasons[bad_symbol] = "ошибка обработки позиции (см. лог), повтор в следующем цикле"
                    err_ts = self.__dict__.setdefault("_manual_scan_err_alert_ts", {})
                    if time.time() - err_ts.get(bad_symbol, 0.0) > 600:
                        err_ts[bad_symbol] = time.time()
                        self.tg.notify(f"⚠️ <b>{bad_symbol}</b>: ошибка при взятии позиции под управление. Повторю в следующем цикле; остальные позиции проверяю дальше.")
            # Наблюдатель: позиция, которая остаётся без сопровождения дольше порога,
            # больше не «молчит» — приходит предупреждение с причиной.
            try:
                tracked_now = set(get_all_open_signal_positions().keys()) | registry_symbols
            except Exception:
                tracked_now = set(already_tracked) | registry_symbols
            self._update_untracked_watchdog(positions, skip_reasons, tracked_now, excluded, pump_symbols)
            live_symbols_now = {str(p.get("symbol")) for p in positions}
            for stale_symbol in [x for x in history_retries if x not in live_symbols_now]:
                history_retries.pop(stale_symbol, None)
        except Exception:
            self.log.exception("Ошибка сканирования ручных позиций (не критично — бот продолжит работу)")

    def _update_untracked_watchdog(self, positions, skip_reasons, tracked_symbols, excluded, pump_symbols):
        """Следит за позициями на бирже, которые бот не ведёт. Если такая позиция
        остаётся без сопровождения дольше MANUAL_UNTRACKED_ALERT_SECONDS (по
        умолчанию 90 с), один раз отправляет предупреждение с причиной —
        вместо молчаливого пропуска, из-за которого незаметно, что лимитка
        исполнилась, а слежение не началось."""
        state = self.__dict__.setdefault("_untracked_positions", {})
        now = time.time()
        try:
            threshold = float(getattr(cfg, "MANUAL_UNTRACKED_ALERT_SECONDS", 90))
        except (TypeError, ValueError):
            threshold = 90.0
        live = set()
        for pos in positions or []:
            symbol = str((pos or {}).get("symbol") or "")
            if not symbol:
                continue
            live.add(symbol)
            if symbol in tracked_symbols or symbol in (excluded or ()) or symbol in (pump_symbols or ()):
                state.pop(symbol, None)  # ведётся ботом либо исключена намеренно
                continue
            entry = state.setdefault(symbol, {"first": now, "alerted": False})
            reason = skip_reasons.get(symbol) or "причина не определена (см. лог)"
            entry["reason"] = reason
            waited = now - entry["first"]
            if waited >= threshold:
                self.log.warning(f"[{symbol}] Позиция на бирже {int(waited)} с без сопровождения ботом: {reason}")
                if not entry["alerted"]:
                    entry["alerted"] = True
                    self.tg.notify(
                        f"⚠️ <b>{symbol}</b>: позиция на бирже уже {int(waited)} с не взята под управление ботом (нет стопа/тейков от бота).\n"
                        f"Причина: {reason}"
                    )
        for symbol in [x for x in state if x not in live]:
            state.pop(symbol, None)  # позиция закрыта

    def _recalculate_manual_position_protection(
        self, symbol: str, live_pos: Dict, reason: str = "",
        use_open_order_anchor: bool = False, preserve_existing_stop: bool = False,
        order_prefix: str = "mtp", force_stop_from_l2: bool = False,
        open_orders_snapshot: Optional[List[Dict]] = None,
        open_orders_snapshot_loaded: bool = False,
    ) -> Dict:
        with self._manual_protection_lock:
            return self._recalculate_manual_position_protection_unlocked(
                symbol, live_pos, reason, use_open_order_anchor, preserve_existing_stop,
                order_prefix, force_stop_from_l2, open_orders_snapshot,
                open_orders_snapshot_loaded,
            )

    @staticmethod
    def _manual_tp_order_stale_reason(order, target, qty_cap, tick_size, qty_step):
        """Возвращает причину, по которой активный ручной TP не соответствует
        текущему плану, либо None.

        Проверяется только то, что однозначно указывает на устаревший ордер:
        цена не совпадает с целью, либо qty больше полной доли стадии (риск
        закрыть лишнее). Qty МЕНЬШЕ доли не считается устареванием: биржа
        может сама уменьшить reduce-only ордер, и замена на каждом цикле
        превратилась бы в бесконечный cancel/place. Если данных недостаточно,
        ордер не считается устаревшим (поведение как раньше)."""
        if not isinstance(order, dict):
            return None
        try:
            price = float(order.get("price") or order.get("triggerPrice") or 0)
        except (TypeError, ValueError, OverflowError):
            price = 0.0
        try:
            tgt = float(target or 0)
        except (TypeError, ValueError, OverflowError):
            tgt = 0.0
        if math.isfinite(price) and price > 0 and math.isfinite(tgt) and tgt > 0:
            tol = max(float(tick_size or 0) * 0.5, abs(tgt) * 1e-8, 1e-12)
            if abs(price - tgt) > tol:
                return f"цена ордера {price} не равна цели {tgt}"
        try:
            order_qty = float(order.get("qty") or 0)
        except (TypeError, ValueError, OverflowError):
            order_qty = 0.0
        try:
            cap = float(qty_cap or 0)
        except (TypeError, ValueError, OverflowError):
            cap = 0.0
        if math.isfinite(order_qty) and order_qty > 0 and math.isfinite(cap) and cap > 0:
            if order_qty > cap + max(float(qty_step or 0) * 0.5, 1e-12):
                return f"qty ордера {order_qty} больше доли стадии {cap}"
        return None

    def _cancel_manual_tp_order_confirmed(self, symbol, oid, expected_prefix, side, live_idx):
        """Снимает наш ручной TP и подтверждает итог чтением статуса с биржи.

        Возвращает (outcome, cum_exec_qty), outcome:
          "cancelled" - ордер в терминальном состоянии без полного исполнения;
          "filled"    - ордер уже исполнен полностью;
          "foreign"   - ID не принадлежит этой позиции/этому TP (не отменяли);
          "unknown"   - состояние не подтверждено (нельзя ставить замену).
        Ошибка cancel сама по себе не критична: итог определяет статус."""
        terminal = ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled")

        def _norm(st):
            return str((st or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()

        def _cum(st):
            try:
                v = float((st or {}).get("cumExecQty") or 0)
            except (TypeError, ValueError, OverflowError):
                return 0.0
            return v if math.isfinite(v) and v > 0 else 0.0

        try:
            before = self.client.get_order_state(symbol, str(oid))
            if not before:
                return "unknown", 0.0
            if (not _tp_order_matches_position(before, symbol, side, live_idx)
                    or not str(before.get("orderLinkId") or "").startswith(expected_prefix)):
                return "foreign", 0.0
            cum = _cum(before)
            status_before = _norm(before)
            if status_before == "filled":
                return "filled", cum
            if status_before in terminal:
                return "cancelled", cum
            try:
                self.client.session.cancel_order(category=cfg.CATEGORY, symbol=symbol, orderId=str(oid))
            except Exception as e:
                # «Уже исполнен/снят» тоже приходит исключением; решает статус ниже.
                self.log.debug(f"[{symbol}] cancel устаревшего manual TP {oid}: {e}")
            after = self.client.get_order_state(symbol, str(oid))
            if not after:
                return "unknown", cum
            cum = max(cum, _cum(after))
            status_after = _norm(after)
            if status_after == "filled":
                return "filled", cum
            if status_after in terminal:
                return "cancelled", cum
            return "unknown", cum
        except Exception as e:
            self.log.debug(f"[{symbol}] Не удалось подтвердить снятие устаревшего manual TP {oid}: {e}")
            return "unknown", 0.0

    def _resolve_stale_manual_tp(
        self, symbol, i, oid, stale_reason, order_prefix, side, live_idx,
        order_ids, done, filled_qty, blocked, verified, active_by_link, stale_cancelled_ids,
    ):
        """Обрабатывает активный TP, который не соответствует текущему плану.

        Возвращает "replace" (старый ордер подтверждённо снят — можно ставить
        новый по плану) или "skip" (замена запрещена в этом цикле: TP исполнен
        либо отмена не подтверждена; verified[key] выставлен соответственно)."""
        key = str(i)
        self.log.warning(
            f"[{symbol}] Manual TP{i}: активный ордер {oid} не соответствует плану ({stale_reason}); "
            "снимаю и ставлю заново по текущему плану."
        )
        outcome, cum = self._cancel_manual_tp_order_confirmed(
            symbol, oid, f"{order_prefix}{i}-", side, live_idx
        )
        if cum > 0:
            filled_qty[key] = max(filled_qty.get(key, 0.0), cum)
        if outcome == "filled":
            done[key] = True
            verified[key] = True
            return "skip"
        if outcome in ("cancelled", "foreign"):
            order_ids.pop(key, None)
            stale_cancelled_ids.add(str(oid))
            for lid, ao in list(active_by_link.items()):
                if str((ao or {}).get("orderId") or "") == str(oid):
                    active_by_link.pop(lid, None)
            return "replace"
        # Снятие не подтверждено: старый ордер остаётся, нового не ставим
        # (иначе удвоим закрываемый объём), TP считаем НЕ подтверждённым.
        blocked.add(key)
        verified[key] = False
        self.log.warning(
            f"[{symbol}] Manual TP{i}: снятие ордера {oid} не подтверждено; замену отложил до следующей сверки."
        )
        return "skip"

    def _recalculate_manual_position_protection_unlocked(
        self, symbol: str, live_pos: Dict, reason: str = "",
        use_open_order_anchor: bool = False, preserve_existing_stop: bool = False,
        order_prefix: str = "mtp", force_stop_from_l2: bool = False,
        open_orders_snapshot: Optional[List[Dict]] = None,
        open_orders_snapshot_loaded: bool = False,
    ) -> Dict:
        """4 независимых TP для ручной позиции + существующая логика SL."""
        live_side_raw = str(live_pos.get("side") or "")
        if live_side_raw not in {"Buy", "Sell"}:
            self.log.error(f"[{symbol}] Неизвестная сторона live-позиции {live_side_raw!r}; SL/TP не изменены")
            return {"changed": False, "side": None, "stop_ok": False, "reason": "invalid_position_side"}
        side = "LONG" if live_side_raw == "Buy" else "SHORT"
        try:
            live_idx_for_side = int(live_pos.get("positionIdx")) if live_pos.get("positionIdx") is not None and str(live_pos.get("positionIdx")).strip() != "" else None
        except (TypeError, ValueError, OverflowError):
            live_idx_for_side = None
        if live_idx_for_side in (1, 2) and live_idx_for_side != (1 if side == "LONG" else 2):
            self.log.error(f"[{symbol}] Конфликт side={live_side_raw} и positionIdx={live_idx_for_side}; стоп/тейки не изменены")
            return {"changed": False, "side": side, "stop_ok": False, "reason": "position_idx_side_conflict"}
        try:
            avg_entry = float(live_pos.get("avgPrice") or 0)
            live_qty = float(live_pos.get("size") or 0)
        except (TypeError, ValueError, OverflowError):
            avg_entry, live_qty = 0.0, 0.0
        if not math.isfinite(avg_entry) or not math.isfinite(live_qty) or avg_entry <= 0 or live_qty <= 0:
            self.log.error(f"[{symbol}] Некорректные avg_entry/qty для ручной защиты: entry={avg_entry!r}, qty={live_qty!r}; изменения TP/SL пропущены.")
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "invalid_position_values"}

        moves, closes = get_bot_tp_config()
        enabled = get_bot_tp_enabled()
        sp_now = get_signal_position(symbol) or {}
        manual_stop_pct = get_manual_stop_percent()

        # A partial TP1 fill is already enough to activate the established
        # break-even rule. Do this BEFORE calculating an L2-based stop; otherwise
        # a failed BE API update could leave the stop reverted to the L2 formula
        # on every monitor pass.
        tp1_done_state = dict(sp_now.get("manual_tp_done") or {})
        tp1_filled_state = dict(sp_now.get("manual_tp_filled_qty") or {})
        try:
            tp1_cum_saved = float(tp1_filled_state.get("1", 0) or 0)
        except (TypeError, ValueError, OverflowError):
            tp1_cum_saved = 0.0
        if not math.isfinite(tp1_cum_saved) or tp1_cum_saved < 0:
            tp1_cum_saved = 0.0
        tp1_already_hit = (
            bool(sp_now.get("breakeven_done"))
            or bool(tp1_done_state.get("1"))
            or tp1_cum_saved > 0
        )
        # Reuse a single order-history snapshot in this reconciliation pass.
        # A missing TP order ID is rare but can otherwise trigger repeated
        # symbol-history requests for TP1, TP2 and TP3 in the same loop.
        manual_tp_history_cache = None
        manual_tp_history_cache_loaded = False

        # If the DB lost the TP1 orderId after a lost API acknowledgement, a
        # previously saved TP plan is not enough to assume there was no TP1 fill.
        # Recover the exact TP1 candidate BEFORE calculating an L2-based stop;
        # otherwise a filled-but-unrecorded TP1 can briefly move SL back to L2.
        try:
            saved_tp_initial_qty = float(sp_now.get("manual_tp_initial_qty") or 0)
        except (TypeError, ValueError, OverflowError):
            saved_tp_initial_qty = 0.0
        has_saved_tp_plan = bool(sp_now.get("manual_tp_targets")) or (
            math.isfinite(saved_tp_initial_qty) and saved_tp_initial_qty > 0
        )
        if (sp_now.get("source") == "manual" and not tp1_already_hit
                and isinstance(sp_now.get("manual_tp_order_ids"), dict)
                and not sp_now.get("manual_tp_order_ids", {}).get("1")
                and has_saved_tp_plan):
            try:
                # Unknown index cannot safely identify a TP from one hedge leg.
                raw_recovery_idx = live_pos.get("positionIdx")
                if raw_recovery_idx is None or str(raw_recovery_idx).strip() == "":
                    raise RuntimeError("positionIdx не возвращён перед восстановлением TP1")
                recovery_idx = int(raw_recovery_idx)
                if (recovery_idx not in (0, 1, 2)
                        or (recovery_idx == 1 and side != "LONG")
                        or (recovery_idx == 2 and side != "SHORT")):
                    raise RuntimeError(f"конфликт positionIdx={recovery_idx} и side={side}")
                recovery_created_at = int(sp_now.get("created_at") or 0)
                if 0 < recovery_created_at < 1_000_000_000_000:
                    recovery_created_at *= 1000
                recovery_now_ms = int(time.time() * 1000)
                if not recovery_created_at:
                    raise RuntimeError("в SQLite отсутствует created_at позиции — нельзя отличить TP1 текущей сделки от старого ордера")
                if recovery_created_at > recovery_now_ms + 5 * 60 * 1000:
                    raise RuntimeError("created_at позиции из будущего; восстановление TP1 небезопасно")

                old_targets = sp_now.get("manual_tp_targets")
                if not isinstance(old_targets, list) or not old_targets:
                    raise RuntimeError("сохранённый план TP1 имеет неверный тип или пуст")
                try:
                    target_hint = float(old_targets[0])
                except (TypeError, ValueError, OverflowError, IndexError) as target_error:
                    raise RuntimeError("сохранённая цена TP1 повреждена") from target_error
                if not math.isfinite(target_hint) or target_hint <= 0:
                    raise RuntimeError(f"сохранённая цена TP1 недопустима: {target_hint!r}")
                try:
                    recovery_tick = float(self.client.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
                except Exception as filter_error:
                    raise RuntimeError(f"не удалось получить tickSize для проверки старого TP1: {filter_error}") from filter_error
                if not math.isfinite(recovery_tick) or recovery_tick <= 0:
                    raise RuntimeError(f"некорректный tickSize при восстановлении TP1: {recovery_tick!r}")
                target_tol = max(recovery_tick * 0.5, abs(target_hint) * 1e-8, 1e-12)
                recovery_prefix = f"{order_prefix}1-"

                if open_orders_snapshot_loaded:
                    recovery_active = open_orders_snapshot
                else:
                    recovery_active = self.client.get_open_orders_all()
                    open_orders_snapshot = recovery_active
                    open_orders_snapshot_loaded = True
                if recovery_active is None:
                    raise RuntimeError("активные ордера недоступны при восстановлении TP1")

                def _tp1_recovery_matches(order, require_history_time=False):
                    if not isinstance(order, dict):
                        return False
                    if str(order.get("symbol") or "") != symbol:
                        return False
                    if not str(order.get("orderLinkId") or "").startswith(recovery_prefix):
                        return False
                    if not _tp_order_matches_position(order, symbol, side, recovery_idx):
                        return False
                    if str(order.get("orderType") or "").strip().lower() != "limit":
                        return False
                    try:
                        order_price = float(order.get("price") or 0)
                    except (TypeError, ValueError, OverflowError):
                        return False
                    if not math.isfinite(order_price) or order_price <= 0 or abs(order_price - target_hint) > target_tol:
                        return False
                    if require_history_time:
                        try:
                            raw_ts = order.get("createdTime") or order.get("orderTime") or order.get("updatedTime")
                            order_ts = int(raw_ts or 0)
                        except (TypeError, ValueError, OverflowError):
                            return False
                        # Both current-trade and order timestamps must be known;
                        # otherwise an old TP with the same price could be adopted.
                        if not order_ts or order_ts < recovery_created_at:
                            return False
                    return bool(order.get("orderId"))

                active_candidates = [o for o in recovery_active if _tp1_recovery_matches(o)]
                active_matches = [o for o in recovery_active if _tp1_recovery_matches(o, require_history_time=True)]
                recovered_tp1 = None
                if active_candidates and not active_matches:
                    raise RuntimeError("найден похожий активный TP1, но его время не подтверждает принадлежность текущей сделке")
                if len(active_matches) == 1:
                    recovered_tp1 = active_matches[0]
                elif len(active_matches) > 1:
                    raise RuntimeError(f"найдено несколько активных TP1 с той же ценой: {[str(o.get('orderId')) for o in active_matches]}")
                else:
                    # Search history only on this exceptional no-ID path. A successful
                    # empty result is considered conclusive only within the history
                    # window; older positions fail closed rather than assume no fill.
                    history_days = 30
                    try:
                        history = self.client.get_symbol_order_history(symbol, days=history_days)
                        manual_tp_history_cache = history
                        manual_tp_history_cache_loaded = history is not None
                    except Exception as history_error:
                        raise RuntimeError(f"история TP1 недоступна: {history_error}") from history_error
                    if history is None:
                        raise RuntimeError("история TP1 вернула неизвестный результат")
                    since = recovery_created_at
                    now_ms = int(time.time() * 1000)
                    if since < now_ms - history_days * 24 * 60 * 60 * 1000:
                        raise RuntimeError("позиция старше доступного окна истории; отсутствие TP1 не доказано")
                    history_matches = [o for o in history if _tp1_recovery_matches(o, require_history_time=True)]
                    if history_matches:
                        # Any positive cumulative execution on any generation of TP1
                        # activates the established break-even rule. Prefer that
                        # generation over a later cancelled/unfilled replacement.
                        def _tp1_rank(order):
                            try:
                                cumulative = float(order.get("cumExecQty") or 0)
                            except (TypeError, ValueError, OverflowError):
                                cumulative = 0.0
                            try:
                                timestamp = int(order.get("updatedTime") or order.get("createdTime") or order.get("orderTime") or 0)
                            except (TypeError, ValueError, OverflowError):
                                timestamp = 0
                            return (1 if math.isfinite(cumulative) and cumulative > 0 else 0, timestamp)
                        history_matches.sort(key=_tp1_rank, reverse=True)
                        recovered_tp1 = history_matches[0]

                if recovered_tp1:
                    recovered_oid = str(recovered_tp1.get("orderId") or "")
                    if not recovered_oid:
                        raise RuntimeError("найденный TP1 не содержит orderId")
                    recovered_ids = dict(sp_now.get("manual_tp_order_ids") or {})
                    recovered_ids["1"] = recovered_oid
                    sp_now["manual_tp_order_ids"] = recovered_ids
                    self.log.warning(
                        f"[{symbol}] Восстановил потерянный orderId TP1={recovered_oid} перед расчётом SL; "
                        "сверяю его фактическое исполнение до изменения стопа."
                    )
            except Exception as missing_tp1_recovery_error:
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                existing_live_sl = existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None
                self.log.error(
                    f"[{symbol}] Не удалось безопасно подтвердить TP1 без сохранённого orderId; "
                    f"стоп от L2 не перезаписываю до сверки: {missing_tp1_recovery_error}"
                )
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl, "stop_ok": existing_live_sl is not None,
                        "reason": "tp1_id_missing_recovery_uncertain"}

        # Before using the L2 formula, reconcile TP1 by its exact persisted ID.
        # A partial TP1 fill might have happened after the last DB write. Without
        # this early check, the bot could reapply the L2 stop before noticing the
        # fill later in the same pass. If exchange state is ambiguous, preserve
        # the currently installed SL and retry next cycle instead of guessing.
        if (sp_now.get("source") == "manual" and not tp1_already_hit
                and isinstance(sp_now.get("manual_tp_order_ids"), dict)
                and sp_now.get("manual_tp_order_ids", {}).get("1")):
            early_tp1_oid = str(sp_now.get("manual_tp_order_ids", {}).get("1"))
            try:
                early_tp1_state = self.client.get_order_state(symbol, early_tp1_oid)
            except Exception as early_tp1_error:
                early_tp1_state = None
                self.log.warning(f"[{symbol}] Не удалось проверить TP1 {early_tp1_oid} до пересчёта стопа: {early_tp1_error}")
            if not isinstance(early_tp1_state, dict) or not early_tp1_state:
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                self.log.error(f"[{symbol}] Статус сохранённого TP1 {early_tp1_oid} неизвестен; стоп от L2 не пересчитываю до сверки")
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None,
                        "stop_ok": bool(math.isfinite(existing_live_sl) and existing_live_sl > 0),
                        "reason": "tp1_state_uncertain_before_stop_update"}
            try:
                early_live_idx = int(live_pos.get("positionIdx")) if live_pos.get("positionIdx") is not None and str(live_pos.get("positionIdx")).strip() != "" else None
            except (TypeError, ValueError, OverflowError):
                early_live_idx = None
            if early_live_idx not in (0, 1, 2):
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                self.log.error(f"[{symbol}] Неизвестный positionIdx live-позиции перед сверкой TP1; стоп не изменяю")
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None,
                        "stop_ok": bool(math.isfinite(existing_live_sl) and existing_live_sl > 0),
                        "reason": "position_idx_unknown_before_tp1_check"}
            if (str(early_tp1_state.get("orderId") or "") != early_tp1_oid
                    or not _tp_order_matches_position(early_tp1_state, symbol, side, early_live_idx)
                    or not str(early_tp1_state.get("orderLinkId") or "").startswith(f"{order_prefix}1-")):
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                self.log.error(f"[{symbol}] Сохранённый TP1 {early_tp1_oid} не прошёл проверку позиции/префикса; стоп не изменяю")
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None,
                        "stop_ok": bool(math.isfinite(existing_live_sl) and existing_live_sl > 0),
                        "reason": "tp1_identity_uncertain_before_stop_update"}
            early_status = str(early_tp1_state.get("orderStatus") or "").strip().lower().replace("_", "").replace(" ", "")
            try:
                early_cum = float(early_tp1_state.get("cumExecQty") or 0)
            except (TypeError, ValueError, OverflowError):
                early_cum = float("nan")
            if not math.isfinite(early_cum) or early_cum < 0:
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                self.log.error(f"[{symbol}] Некорректный cumExecQty сохранённого TP1 {early_tp1_oid}; стоп не изменяю")
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None,
                        "stop_ok": bool(math.isfinite(existing_live_sl) and existing_live_sl > 0),
                        "reason": "tp1_fill_state_invalid_before_stop_update"}
            if early_cum > 0:
                tp1_cum_saved = max(tp1_cum_saved, early_cum)
                tp1_filled_state["1"] = tp1_cum_saved
                sp_now["manual_tp_filled_qty"] = tp1_filled_state
            if early_status == "filled":
                tp1_done_state["1"] = True
                sp_now["manual_tp_done"] = tp1_done_state
            elif early_status in {"partiallyfilled", "partiallyfilledcanceled"} and early_cum <= 0:
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                self.log.error(f"[{symbol}] TP1 {early_tp1_oid} указан как частично исполненный без cumExecQty; стоп не изменяю")
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None,
                        "stop_ok": bool(math.isfinite(existing_live_sl) and existing_live_sl > 0),
                        "reason": "tp1_partial_fill_unverified_before_stop_update"}
            elif early_cum <= 0 and early_status not in {"new", "untriggered", "created", "cancelled", "canceled", "rejected", "deactivated", "filled", "partiallyfilled", "partiallyfilledcanceled"}:
                try:
                    existing_live_sl = float(live_pos.get("stopLoss") or 0)
                except (TypeError, ValueError, OverflowError):
                    existing_live_sl = 0.0
                self.log.error(f"[{symbol}] Неизвестный статус TP1 {early_status!r}; стоп не изменяю до сверки")
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop": existing_live_sl if math.isfinite(existing_live_sl) and existing_live_sl > 0 else None,
                        "stop_ok": bool(math.isfinite(existing_live_sl) and existing_live_sl > 0),
                        "reason": "tp1_status_unknown_before_stop_update"}
            # Persist the fill/done observation immediately, before any next
            # exchange action. If persistence fails, keep the in-memory evidence
            # and continue towards BE because exchange confirms that TP1 executed;
            # a DB failure must never make us revert to the old L2 stop formula.
            if early_cum > 0 or early_status == "filled":
                try:
                    persist_manual_tp1_fill_observation(
                        symbol, early_cum, order_id=early_tp1_oid,
                        done=(early_status == "filled"), logger=self.log,
                    )
                except Exception as persist_tp1_error:
                    self.log.exception(
                        f"[{symbol}] TP1 исполнение подтверждено биржей, но немедленное сохранение в БД не удалось; "
                        f"продолжаю защитный перенос стопа: {persist_tp1_error}"
                    )
            tp1_already_hit = (
                bool(sp_now.get("breakeven_done"))
                or bool(tp1_done_state.get("1"))
                or tp1_cum_saved > 0
            )

        anchor = avg_entry
        anchor_source = "avg_entry"
        if tp1_already_hit:
            # Once TP1 has any confirmed fill, the old L2 stop rule no longer
            # applies. Preserve the existing +buffer/-buffer from actual entry.
            be_buffer = float(getattr(cfg, "SIGNAL_BREAKEVEN_BUFFER_PERCENT", 0.5) or 0.5) / 100.0
            if not math.isfinite(be_buffer) or be_buffer < 0 or be_buffer >= 1:
                be_buffer = 0.005
            anchor_source = "break_even_after_tp1"
            stop = avg_entry * (1 + be_buffer) if side == "LONG" else avg_entry * (1 - be_buffer)
        else:
            if use_open_order_anchor:
                # Use the exact pinned L2, never a newly sorted L3/L4 order.
                try:
                    slot_rows = get_manual_limit_slot_rows(symbol)
                except Exception as e:
                    slot_rows = []
                    self.log.error(f"[{symbol}] Не удалось прочитать DB-слоты L1/L2: {e}")

                if force_stop_from_l2:
                    # The stop-% button is an explicit request, so refresh the
                    # pinned L2's current price by its exact orderId. This covers
                    # a manual price amendment made immediately before the button
                    # press, before the 30-second background scan has run.
                    rows_l2 = []
                    for slot_row in slot_rows:
                        try:
                            slot_number = int(slot_row.get("slot") or 0)
                        except (TypeError, ValueError, OverflowError):
                            self.log.warning(
                                f"[{symbol}] Игнорирую повреждённый номер слота ручной лимитки: "
                                f"{slot_row.get('slot')!r}"
                            )
                            continue
                        if slot_number == 2:
                            rows_l2.append(slot_row)
                    if len(rows_l2) > 1:
                        return {"changed": False, "side": side, "avg_entry": avg_entry,
                                "stop_ok": False, "reason": "duplicate_l2_slot_rows"}
                    slot_l2 = rows_l2[0] if rows_l2 else None
                    entry_ids_now = sp_now.get("entry_order_ids") or []
                    # For an explicit change from Telegram, do not guess the second
                    # limit from an orphan slot: require the trade row's exact L2 ID.
                    # Otherwise a stale slot might silently become the stop anchor.
                    if len(entry_ids_now) < 2 or not entry_ids_now[1]:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "missing_l2_order_id"}
                    l2_oid = str(entry_ids_now[1])
                    if slot_l2 and str(slot_l2.get("order_id") or "") != l2_oid:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_slot_identity_conflict"}
                    try:
                        l2_state = self.client.get_order_state(symbol, l2_oid)
                    except Exception as e:
                        self.log.warning(f"[{symbol}] Не удалось проверить исходную L2 {l2_oid} перед применением процента стопа: {e}")
                        l2_state = None
                    if not isinstance(l2_state, dict) or not l2_state:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_exchange_state_unavailable"}
                    if str(l2_state.get("symbol") or "") != symbol or str(l2_state.get("orderId") or "") != l2_oid:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_exchange_identity_mismatch"}
                    entry_side_expected = "Buy" if side == "LONG" else "Sell"
                    if str(l2_state.get("side") or "") != entry_side_expected or str(l2_state.get("orderType") or "").lower() != "limit":
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_not_entry_limit"}
                    state_reduce_only = l2_state.get("reduceOnly")
                    if isinstance(state_reduce_only, bool):
                        reduce_only_verified = state_reduce_only
                    elif isinstance(state_reduce_only, (int, float)) and state_reduce_only in (0, 1):
                        reduce_only_verified = bool(state_reduce_only)
                    elif isinstance(state_reduce_only, str):
                        reduce_only_text = state_reduce_only.strip().lower()
                        if reduce_only_text in {"true", "1", "yes", "y"}:
                            reduce_only_verified = True
                        elif reduce_only_text in {"false", "0", "no", "n"}:
                            reduce_only_verified = False
                        else:
                            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_reduce_only_unknown"}
                    else:
                        # For a stop explicitly recalculated from L2, missing
                        # reduceOnly metadata is not proof that this is an entry
                        # order. Avoid accepting an ambiguous exchange payload.
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_reduce_only_missing"}
                    if reduce_only_verified:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_is_reduce_only"}
                    try:
                        live_idx_value = int(live_pos.get("positionIdx")) if live_pos.get("positionIdx") is not None else None
                        state_idx_value = int(l2_state.get("positionIdx")) if l2_state.get("positionIdx") is not None else None
                        saved_idx_value = int((slot_l2 or {}).get("position_idx")) if (slot_l2 or {}).get("position_idx") is not None else None
                    except (TypeError, ValueError, OverflowError):
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_position_idx_invalid"}
                    if live_idx_value not in (0, 1, 2):
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "live_position_idx_unknown"}
                    trusted_idx = state_idx_value if state_idx_value is not None else saved_idx_value
                    if live_idx_value in (1, 2) and trusted_idx != live_idx_value:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_position_idx_mismatch"}
                    if live_idx_value == 0 and trusted_idx not in (None, 0):
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_position_idx_mismatch"}
                    try:
                        exchange_l2_price = float(l2_state.get("price") or 0)
                    except (TypeError, ValueError, OverflowError):
                        exchange_l2_price = 0.0
                    if not math.isfinite(exchange_l2_price) or exchange_l2_price <= 0:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_price_invalid"}
                    state_qty_raw = l2_state.get("qty")
                    try:
                        exchange_l2_qty = float(state_qty_raw) if state_qty_raw not in (None, "") else float((slot_l2 or {}).get("qty") or 0)
                    except (TypeError, ValueError, OverflowError):
                        exchange_l2_qty = float((slot_l2 or {}).get("qty") or 0)
                    if not math.isfinite(exchange_l2_qty) or exchange_l2_qty < 0:
                        exchange_l2_qty = float((slot_l2 or {}).get("qty") or 0)
                    try:
                        l2_status_raw = str(l2_state.get("orderStatus") or "unknown").strip().lower()
                        if l2_status_raw in {"new", "partiallyfilled", "partially_filled", "untriggered", "created"}:
                            l2_slot_status, l2_terminal_reason = "active", None
                        elif l2_status_raw in {"filled", "partiallyfilledcanceled", "partially_filled_canceled"}:
                            l2_slot_status, l2_terminal_reason = "filled", l2_status_raw
                        elif l2_status_raw in {"cancelled", "canceled", "rejected", "deactivated"}:
                            l2_slot_status, l2_terminal_reason = "cancelled", l2_status_raw
                        else:
                            l2_slot_status, l2_terminal_reason = "unknown", l2_status_raw or "unknown_status"
                        slot_notional = float((slot_l2 or {}).get("target_notional_usdt") or get_setting("manual_limit2_value_usdt", 10.0) or 0)
                        saved_slot = save_manual_limit_slot(
                            symbol, 2, l2_oid, entry_side_expected, exchange_l2_price, exchange_l2_qty,
                            slot_notional, status=l2_slot_status, terminal_reason=l2_terminal_reason,
                            replace=bool(slot_l2 and str(slot_l2.get("order_id") or "") != l2_oid),
                            position_idx=trusted_idx,
                        )
                    except Exception as e:
                        self.log.exception(f"[{symbol}] Не удалось синхронизировать L2 в SQLite перед пересчётом стопа: {e}")
                        saved_slot = False
                    if not saved_slot:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "l2_slot_persist_failed"}
                    slot_rows = get_manual_limit_slot_rows(symbol)
                    # Keep the signal position's pair price consistent with the
                    # slot so recovery after a restart uses exactly the same L2.
                    try:
                        ids_pair = [str(x) for x in (sp_now.get("entry_order_ids") or [])]
                        entries_pair = [float(x) for x in (sp_now.get("entries") or [])]
                        if len(ids_pair) == 2 and len(entries_pair) == 2 and ids_pair[1] == l2_oid:
                            if abs(entries_pair[1] - exchange_l2_price) > max(abs(exchange_l2_price) * 1e-12, 1e-12):
                                if not update_manual_entry_pair(
                                    symbol, [entries_pair[0], exchange_l2_price], ids_pair,
                                    expected_order_ids=ids_pair, expected_entries=entries_pair,
                                ):
                                    return {"changed": False, "side": side, "avg_entry": avg_entry,
                                            "stop_ok": False, "reason": "l2_pair_persist_conflict"}
                                sp_now = get_signal_position(symbol) or sp_now
                    except Exception:
                        self.log.exception(f"[{symbol}] Не удалось синхронизировать entries[1] с подтверждённой L2")

                anchor, anchor_source = _resolve_manual_stop_anchor_from_state(
                    side, live_pos, sp_now, slot_rows
                )
                if anchor_source == "signal_position_l2_fallback":
                    self.log.warning(f"[{symbol}] Для стопа использована сохранённая entries[1] как L2: DB-слот не подтверждён")
                elif anchor_source == "avg_entry_emergency_fallback":
                    self.log.error(f"[{symbol}] L2 не найдена; временный якорь стопа — средний вход. Проверь пару лимиток в БД")
                    if force_stop_from_l2:
                        return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "missing_l2_for_requested_stop_change"}
                elif anchor_source == "missing_l2_and_entry":
                    self.log.error(f"[{symbol}] Невозможно определить безопасный якорь стопа: нет L2 и нет корректной цены входа")
                    return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "missing_l2_anchor"}
            try:
                stop = _calculate_manual_l2_stop(side, anchor, manual_stop_pct)
            except (TypeError, ValueError, OverflowError) as stop_calc_error:
                self.log.error(
                    f"[{symbol}] Не изменяю SL: не удалось рассчитать стоп от подтверждённого якоря "
                    f"(source={anchor_source}, anchor={anchor!r}, percent={manual_stop_pct!r}): {stop_calc_error}"
                )
                return {"changed": False, "side": side, "avg_entry": avg_entry,
                        "stop_ok": False, "reason": "manual_l2_stop_calculation_invalid"}
        try:
            tick_size = float(self.client.get_instrument_filters(symbol)["priceFilter"]["tickSize"])
            qty_step = float(self.client.get_qty_step(symbol))
        except (KeyError, TypeError, ValueError, OverflowError, AttributeError) as e:
            self.log.error(f"[{symbol}] Не удалось проверить шаги цены/количества для SL и TP: {e}")
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "invalid_instrument_filters"}
        if not math.isfinite(tick_size) or tick_size <= 0 or not math.isfinite(qty_step) or qty_step <= 0:
            self.log.error(f"[{symbol}] Некорректные tick_size/qty_step: {tick_size!r}/{qty_step!r}; изменения SL/TP пропущены")
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop_ok": False, "reason": "invalid_instrument_filters"}
        if not math.isfinite(stop) or stop <= 0:
            self.log.error(f"[{symbol}] Рассчитан недопустимый стоп {stop!r}; SL не изменён")
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop": stop, "stop_ok": False, "reason": "invalid_calculated_stop"}
        try:
            stop = _round_stop_price_for_side(stop, tick_size, side)
        except (TypeError, ValueError, OverflowError) as rounding_error:
            self.log.error(f"[{symbol}] Не удалось безопасно округлить SL для {side}: {rounding_error}")
            return {"changed": False, "side": side, "avg_entry": avg_entry,
                    "stop_ok": False, "reason": "invalid_rounded_stop"}
        if not math.isfinite(stop) or stop <= 0:
            self.log.error(f"[{symbol}] Стоп после округления недопустим: {stop!r}; SL не изменён")
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop": stop, "stop_ok": False, "reason": "invalid_rounded_stop"}
        try:
            old_stop = float(sp_now.get("stop_price") or 0)
            if not math.isfinite(old_stop) or old_stop < 0:
                old_stop = 0.0
        except (TypeError, ValueError, OverflowError):
            old_stop = 0.0
        try:
            exchange_stop = float(live_pos.get("stopLoss") or 0)
        except (TypeError, ValueError, OverflowError):
            exchange_stop = 0.0
        if not math.isfinite(exchange_stop) or exchange_stop < 0:
            # Malformed exchange payload is not an installed stop. Treat it as
            # unknown/absent and require a verified read-back before success.
            exchange_stop = 0.0
        if anchor_source == "avg_entry_emergency_fallback" and exchange_stop > 0:
            # If L2 is missing, never overwrite an existing exchange stop with
            # a guessed stop derived from average entry. Keep current protection.
            stop = _round_stop_price_for_side(exchange_stop, tick_size, side)
            self.log.error(
                "[%s] L2 не подтверждена; сохраняю существующий SL биржи %s вместо пересчёта от среднего входа",
                symbol, fmt_num(stop),
            )

        # Ручной SL должен переживать не только один цикл, но и все последующие
        # циклы/перезапуски. Для этого latch manual_sl_override сохраняется в БД.
        # После успешного TP1-break-even штатный перенос получает приоритет и снимает latch.
        manual_sl_override = bool(sp_now.get("manual_sl_override")) and not tp1_already_hit and not force_stop_from_l2
        if sp_now.get("source") == "manual" and not tp1_already_hit and not force_stop_from_l2:
            if exchange_stop > 0:
                compare_tol = max(tick_size * 0.5, abs(old_stop) * 1e-8, 1e-12)
                newly_changed = old_stop <= 0 or abs(exchange_stop - old_stop) > compare_tol
                if newly_changed and not manual_sl_override:
                    manual_sl_override = True
                    set_signal_manual_sl_override(symbol, True, exchange_stop)
                    self.log.info(
                        f"[{symbol}] Обнаружен ручной перенос SL на бирже: {fmt_num(exchange_stop)}. "
                        "Закрепляю ручной SL в БД; бот не будет возвращать его к L2 до исполнения TP1."
                    )
                if manual_sl_override:
                    # При latch сохраняем любое новое значение SL, которое пользователь
                    # установил на бирже, но не отправляем set_trading_stop обратно.
                    # Важно обновлять stop_price в БД и при повторном ручном переносе:
                    # если SL позже временно исчезнет из ответа биржи, восстановим
                    # последнюю пользовательскую цену, а не предыдущую.
                    stop = _round_stop_price_for_side(exchange_stop, tick_size, side)
                    if old_stop <= 0 or abs(exchange_stop - old_stop) > compare_tol:
                        set_signal_manual_sl_override(symbol, True, exchange_stop)
                    old_stop = exchange_stop
            elif manual_sl_override:
                # Если ручной SL был удалён/временно пропал из ответа биржи,
                # не считаем защиту успешно установленной. Восстанавливаем
                # последнюю сохранённую вручную цену, а не формулу от L2.
                stop = _round_stop_price_for_side(old_stop if old_stop > 0 else stop, tick_size, side)
                self.log.warning(
                    f"[{symbol}] Ручной SL отсутствует на бирже; пытаюсь восстановить последнюю сохранённую цену {fmt_num(stop)}."
                )

        if preserve_existing_stop and not force_stop_from_l2 and not tp1_already_hit:
            existing_stop = float(exchange_stop or old_stop or 0)
            if existing_stop > 0:
                stop = _round_stop_price_for_side(existing_stop, tick_size, side)

        tol_stop = max(tick_size * 0.5, abs(stop) * 1e-8, 1e-12)
        stop_ok = exchange_stop > 0 and abs(exchange_stop - stop) <= tol_stop
        if not stop_ok and (not manual_sl_override or exchange_stop <= 0):
            stop_ok = self.client.update_stop_loss_verified(symbol, stop, side)
        elif manual_sl_override and exchange_stop > 0:
            # Считаем защищённой только существующую и совпадающую с биржей SL.
            stop_ok = True
        if not stop_ok:
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop": stop, "stop_ok": False, "reason": reason}
        if force_stop_from_l2 and not tp1_already_hit:
            # This explicit Telegram action is the user's request to replace an
            # earlier exchange-side manual SL with the configured L2 stop. Clear
            # the override latch only after the exchange stop is verified.
            set_signal_manual_sl_override(symbol, False, stop)
            manual_sl_override = False

        targets = [self.client.round_step(avg_entry * (1 + m / 100.0) if side == "LONG" else avg_entry * (1 - m / 100.0), tick_size) for m in moves]
        manual_tp_overrides = {}
        for _k, _v in (sp_now.get("manual_tp_overrides") or {}).items():
            if str(_k) not in {"1", "2", "3", "4"}:
                continue
            try:
                _v = float(_v)
            except (TypeError, ValueError, OverflowError):
                continue
            if math.isfinite(_v) and _v > 0:
                manual_tp_overrides[str(_k)] = _v
        # Validate the configured plan before applying deliberate user overrides.
        if _bot_tp_validate_moves(moves, enabled) or _bot_tp_validate_closes(closes, enabled):
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop": stop, "stop_ok": stop_ok, "reason": "invalid_tp_config"}
        if not _bot_tp_rounded_targets_ordered(targets, enabled, side):
            return {"changed": False, "side": side, "avg_entry": avg_entry, "stop": stop, "stop_ok": stop_ok, "reason": "rounded_tp_levels_conflict"}
        # Persisted manual edits win over percentages/config changes until the user
        # moves that particular TP again. Only that TP is overridden.
        for _tp_key, _tp_price in manual_tp_overrides.items():
            targets[int(_tp_key) - 1] = self.client.round_step(_tp_price, tick_size)
        # Старый сохранённый план нужен для различения ручного переноса TP4
        # и обычного TP4, который совпадает с текущим расчётом.
        saved_targets = []
        for _saved_target in (sp_now.get("manual_tp_targets") or []):
            try:
                _saved_target = float(_saved_target)
            except (TypeError, ValueError, OverflowError):
                _saved_target = 0.0
            # Preserve the stage index even if a corrupt/legacy value is empty.
            saved_targets.append(_saved_target if math.isfinite(_saved_target) and _saved_target > 0 else 0.0)
        saved_closes = [float(x) for x in (sp_now.get("manual_tp_close_pcts") or []) if x]

        # TP4 читаем из свежей позиции перед любым обновлением: live_pos может
        # быть снимком, сделанным до ручного переноса тейка на бирже.
        tp4_state_confirmed = False
        tp4_position = None
        try:
            tp4_position = self.client.get_position_strict(
                symbol, side=("Buy" if side == "LONG" else "Sell")
            )
            tp4_state_confirmed = bool(tp4_position and float(tp4_position.get("size") or 0) > 0)
        except Exception as _tp4_read_error:
            self.log.warning(
                f"[{symbol}] Не удалось подтвердить актуальный TP4 перед синхронизацией; "
                f"не буду перезаписывать его по устаревшему снимку: {_tp4_read_error}"
            )
        try:
            exchange_tp4 = float((tp4_position or {}).get("takeProfit") or 0) if tp4_state_confirmed else 0.0
        except (TypeError, ValueError, OverflowError):
            exchange_tp4 = 0.0
            tp4_state_confirmed = False
        if tp4_state_confirmed and math.isfinite(exchange_tp4) and exchange_tp4 > 0:
            tp4_tol = max(tick_size * 0.5, abs(exchange_tp4) * 1e-8, 1e-12)
            # If an override is already stored, any newer exchange price wins.
            # Otherwise compare against the last persisted target, not the new
            # config target. Do not mark an ordinary unchanged TP4 as manual.
            reference_tp4 = (
                float(manual_tp_overrides["4"]) if "4" in manual_tp_overrides
                else (saved_targets[3] if len(saved_targets) >= 4 and saved_targets[3] > 0 else targets[3])
            )
            if math.isfinite(reference_tp4) and reference_tp4 > 0 and abs(exchange_tp4 - reference_tp4) > tp4_tol:
                manual_tp_overrides["4"] = self.client.round_step(exchange_tp4, tick_size)
                targets[3] = manual_tp_overrides["4"]
                self.log.info(f"[{symbol}] Обнаружен ручной перенос TP4 на бирже: сохраняю {targets[3]}, автоматический возврат отключён.")
            elif "4" in manual_tp_overrides:
                # The live exchange is the source of truth if the user moved TP4
                # again, including moving it back to a former calculated level.
                manual_tp_overrides["4"] = self.client.round_step(exchange_tp4, tick_size)
                targets[3] = manual_tp_overrides["4"]
        saved_initial_qty = float(sp_now.get("manual_tp_initial_qty") or 0)
        initial_qty = saved_initial_qty
        if initial_qty <= 0:
            initial_qty = live_qty
        order_ids = {str(k): str(v) for k,v in (sp_now.get("manual_tp_order_ids") or {}).items() if v}
        done = {str(k): bool(v) for k,v in (sp_now.get("manual_tp_done") or {}).items()}
        filled_qty = {}
        for k, v in (sp_now.get("manual_tp_filled_qty") or {}).items():
            try:
                fv = float(v)
                if str(k) in {"1","2","3"} and math.isfinite(fv) and fv > 0:
                    filled_qty[str(k)] = fv
            except (TypeError, ValueError):
                pass
        if initial_qty > 0 and not any(done.get(str(i)) for i in range(1, 4)) and live_qty > initial_qty * 1.001:
            # До первого TP мог исполниться второй ручной вход — тогда доли
            # TP должны считаться от полного уже набранного объёма.
            initial_qty = live_qty

        qty_basis_changed = (
            saved_initial_qty > 0
            and abs(initial_qty - saved_initial_qty) > max(qty_step * 0.5, abs(initial_qty) * 1e-8, 1e-12)
        )
        # A moved TP price should be preserved, but an increase in the planned
        # close fraction or a changed initial quantity still requires rebuilding
        # that same TP at the same user-selected price with the correct size.
        qty_plan_changed = (
            qty_basis_changed
            or len(saved_closes) != 4
            or any(abs(saved_closes[j] - closes[j]) > 1e-9 for j in range(min(4, len(saved_closes))))
        )
        plan_changed = (
            len(saved_targets) != 4
            or len(saved_closes) != 4
            or any(
                str(i + 1) not in manual_tp_overrides
                and abs(saved_targets[i] - targets[i]) > max(tick_size, abs(targets[i]) * 1e-8)
                for i in range(min(4, len(saved_targets)))
            )
            or any(abs(saved_closes[i]-closes[i]) > 1e-9 for i in range(min(4,len(saved_closes))))
            or qty_basis_changed
        )
        active_orders = None
        if open_orders_snapshot_loaded:
            active_orders = open_orders_snapshot
        else:
            try: active_orders = self.client.get_open_orders_all()
            except Exception as e: self.log.debug(f"[{symbol}] Не удалось получить активные ручные TP: {e}")
        live_idx_raw = live_pos.get("positionIdx")
        try:
            live_idx = int(live_idx_raw) if live_idx_raw is not None and str(live_idx_raw).strip() != "" else 0
        except (TypeError, ValueError, OverflowError):
            live_idx = None
        if active_orders is not None:
            active_orders = [o for o in active_orders if _tp_order_matches_position(o, symbol, side, live_idx)]

        # Do not place a new partial TP when the previous order's cancellation
        # or state lookup was inconclusive; that could double the close quantity.
        blocked_tp_replacements = set()
        # ID ордеров, снятых как устаревшие в этом проходе: их нельзя заново
        # «усыновить» по устаревшему снимку открытых ордеров/истории.
        stale_cancelled_ids = set()
        # До первого TP при изменении среднего входа/настроек снимаем только наши mtp1-3.
        if plan_changed:
            # При изменении настроек отменяем только ещё не исполненные наши
            # mtp-ордера. Уже зафиксированный TP не трогаем.
            for i in range(1, 4):
                key = str(i)
                if done.get(key):
                    continue
                oid = order_ids.get(key)
                if oid:
                    cancel_confirmed = False
                    try:
                        state_before_cancel = self.client.get_order_state(symbol, oid)
                        if not state_before_cancel:
                            # Unknown order state: do not cancel or replace it.
                            blocked_tp_replacements.add(key)
                            continue
                        expected_prefix = f"{order_prefix}{i}-"
                        if (not _tp_order_matches_position(state_before_cancel, symbol, side, live_idx)
                                or not str(state_before_cancel.get("orderLinkId") or "").startswith(expected_prefix)):
                            self.log.warning(f"[{symbol}] Manual TP{i}: saved orderId {oid} does not match this position/TP; refusing cancellation")
                            # Stale DB reference: forget only after definitive identity mismatch.
                            order_ids.pop(key, None)
                            cancel_confirmed = True
                            continue
                        cum_before = float((state_before_cancel or {}).get("cumExecQty") or 0)
                        if math.isfinite(cum_before) and cum_before > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), cum_before)
                        state_status = str(state_before_cancel.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                        try:
                            exchange_tp_price = float(state_before_cancel.get("price") or state_before_cancel.get("triggerPrice") or 0)
                            old_planned_price = float(saved_targets[i-1]) if len(saved_targets) >= i else 0.0
                        except (TypeError, ValueError, OverflowError):
                            exchange_tp_price, old_planned_price = 0.0, 0.0
                        move_tol = max(tick_size * 0.5, abs(old_planned_price) * 1e-8, 1e-12)
                        if (state_status in ("new", "partiallyfilled", "untriggered", "created")
                                and math.isfinite(exchange_tp_price) and exchange_tp_price > 0
                                and (old_planned_price <= 0 or abs(exchange_tp_price - old_planned_price) > move_tol)):
                            # The order price changed on the exchange, or the old DB has no
                            # trustworthy baseline. Preserve the live order instead of guessing.
                            manual_tp_overrides[key] = self.client.round_step(exchange_tp_price, tick_size)
                            targets[i-1] = manual_tp_overrides[key]
                            if not qty_plan_changed:
                                self.log.info(f"[{symbol}] TP{i}: сохраняю фактический уровень {targets[i-1]} и существующий ордер; старая цена в БД отсутствует или отличается.")
                                continue
                            self.log.info(f"[{symbol}] TP{i}: цена пользователя {targets[i-1]} сохранена; пересоздаю этот тейк на той же цене только для применения нового объёма закрытия.")
                        self.client.session.cancel_order(category=cfg.CATEGORY, symbol=symbol, orderId=oid)
                        state_after_cancel = self.client.get_order_state(symbol, oid)
                        status_after_cancel = str((state_after_cancel or {}).get("orderStatus") or "").lower()
                        cum_after = float((state_after_cancel or {}).get("cumExecQty") or 0)
                        if cum_after > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), cum_after)
                        if status_after_cancel == "filled":
                            done[key] = True
                            cancel_confirmed = True
                        elif status_after_cancel in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                            cancel_confirmed = True
                    except Exception as e:
                        self.log.debug(f"[{symbol}] Не удалось подтвердить отмену manual TP{key} {oid}: {e}")
                    if not cancel_confirmed:
                        # Сохраняем старый orderId до следующей сверки. Это
                        # защищает от дубля, если cancel/lookup закончились
                        # неизвестным состоянием.
                        blocked_tp_replacements.add(key)
                        continue
                order_ids.pop(key, None)

        # TP4 — Full TP остатка. План отмены/проверки TP1–TP3 мог занять время,
        # поэтому непосредственно перед set_trading_stop ещё раз читаем TP4.
        # Это закрывает окно гонки: пользователь передвинул TP4 во время цикла.
        tp4_state_confirmed = False
        current_tp4 = 0.0
        try:
            _tp4_latest = self.client.get_position_strict(
                symbol, side=("Buy" if side == "LONG" else "Sell")
            )
            tp4_state_confirmed = bool(_tp4_latest and float(_tp4_latest.get("size") or 0) > 0)
            current_tp4 = float((_tp4_latest or {}).get("takeProfit") or 0) if tp4_state_confirmed else 0.0
        except Exception as _tp4_latest_error:
            self.log.warning(
                f"[{symbol}] Повторное чтение TP4 перед обновлением не удалось; "
                f"не меняю TP4 по устаревшему снимку: {_tp4_latest_error}"
            )
        tol_tp = max(tick_size * 0.5, abs(targets[3]) * 1e-8, 1e-12)
        if tp4_state_confirmed and current_tp4 > 0:
            if "4" in manual_tp_overrides:
                _tp4_reference = float(manual_tp_overrides["4"])
            else:
                _tp4_reference = saved_targets[3] if len(saved_targets) >= 4 and saved_targets[3] > 0 else targets[3]
            _tp4_compare_tol = max(tick_size * 0.5, abs(current_tp4) * 1e-8, 1e-12)
            if math.isfinite(_tp4_reference) and _tp4_reference > 0 and abs(current_tp4 - _tp4_reference) > _tp4_compare_tol:
                manual_tp_overrides["4"] = self.client.round_step(current_tp4, tick_size)
                targets[3] = manual_tp_overrides["4"]
                self.log.info(f"[{symbol}] Перед установкой TP4 обнаружен новый ручной уровень {targets[3]}; сохраняю его.")
            elif "4" in manual_tp_overrides:
                manual_tp_overrides["4"] = self.client.round_step(current_tp4, tick_size)
                targets[3] = manual_tp_overrides["4"]
        tp4_ok = tp4_state_confirmed and current_tp4 > 0 and abs(current_tp4-targets[3]) <= tol_tp
        if not tp4_ok and tp4_state_confirmed:
            tp4_ok = bool(self.client.update_take_profit_verified(symbol, targets[3], side))
        elif not tp4_state_confirmed:
            tp4_ok = False

        active_by_link = {str(o.get("orderLinkId")): o for o in (active_orders or []) if o.get("symbol") == symbol}
        verified = {}
        for i in range(1, 4):
            key = str(i)
            if not enabled[i - 1]:
                oid = order_ids.get(key)
                orphan_candidates = [
                    o for o in (active_orders or [])
                    if o.get("symbol") == symbol and str(o.get("orderLinkId") or "").startswith(f"{order_prefix}{i}-")
                ]
                if oid:
                    matching = [o for o in orphan_candidates if str(o.get("orderId") or "") == str(oid)]
                    orphan_candidates = matching or orphan_candidates
                # A disabled TP is not resolved merely because cancel_order
                # returned (or timed out). Keep its ID until the exchange confirms
                # Filled or a terminal unfilled status; otherwise re-check next loop.
                candidate_ids = []
                if oid:
                    candidate_ids.append(str(oid))
                candidate_ids.extend(
                    str(c.get("orderId")) for c in orphan_candidates
                    if c.get("orderId") and str(c.get("orderId")) not in candidate_ids
                )
                unresolved_ids = []
                if active_orders is None:
                    # Without a complete open-order snapshot and without a known
                    # ID, absence cannot be proven; keep this TP unresolved.
                    if not candidate_ids:
                        verified[key] = False
                        continue
                for cancel_id in candidate_ids[:3]:
                    resolved = False
                    try:
                        state_before = self.client.get_order_state(symbol, cancel_id)
                        if not state_before:
                            unresolved_ids.append(cancel_id)
                            continue
                        if (not _tp_order_matches_position(state_before, symbol, side, live_idx)
                                or not str(state_before.get("orderLinkId") or "").startswith(f"{order_prefix}{i}-")):
                            self.log.warning(f"[{symbol}] Disabled manual TP{i}: orderId {cancel_id} does not match this position/TP; refusing cancellation")
                            # This is a stale local reference, not an order to cancel.
                            resolved = True
                            continue
                        before_status = str((state_before or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                        before_cum = float((state_before or {}).get("cumExecQty") or 0)
                        if before_cum > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), before_cum)
                        if before_status == "filled":
                            done[key] = True
                            resolved = True
                        elif before_status in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                            resolved = True
                        else:
                            self.client.session.cancel_order(category=cfg.CATEGORY, symbol=symbol, orderId=cancel_id)
                            state_after = self.client.get_order_state(symbol, cancel_id)
                            after_status = str((state_after or {}).get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                            after_cum = float((state_after or {}).get("cumExecQty") or 0)
                            if after_cum > 0:
                                filled_qty[key] = max(filled_qty.get(key, 0.0), after_cum)
                            if after_status == "filled":
                                done[key] = True
                                resolved = True
                            elif after_status in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                                resolved = True
                    except Exception as e:
                        self.log.debug(f"[{symbol}] Не удалось подтвердить отмену отключённого TP{i} {cancel_id}: {e}")
                    if not resolved:
                        unresolved_ids.append(cancel_id)
                if unresolved_ids:
                    order_ids[key] = unresolved_ids[0]
                    verified[key] = False
                else:
                    # No candidate IDs is safe only when the account-wide open
                    # order list succeeded and did not contain an orphan.
                    order_ids.pop(key, None)
                    verified[key] = active_orders is not None
                    if not verified[key] and oid:
                        order_ids[key] = str(oid)
                continue
            if done.get(key):
                verified[key] = True
                continue
            if key in blocked_tp_replacements:
                # Старый ордер не удалось подтверждённо снять: он не может
                # считаться подтверждённым TP, а новый ставить нельзя.
                verified[key] = False
                continue
            stage_qty_cap = self.client.round_step(initial_qty * closes[i - 1] / 100.0, qty_step)
            oid = order_ids.get(key)
            if oid:
                active_known = next(
                    (o for o in (active_orders or []) if str(o.get("orderId") or "") == str(oid) and o.get("symbol") == symbol),
                    None,
                ) if active_orders is not None else None
                if active_known is not None and not str(active_known.get("orderLinkId") or "").startswith(f"{order_prefix}{i}-"):
                    # A stale/corrupt DB mapping must never make TP2 be treated as TP1.
                    # Do not cancel that other order; forget only this bad mapping and
                    # recover the correct stage by its own prefix below.
                    self.log.warning(f"[{symbol}] Сохранённый ID для TP{i} указывает на другой этап; ищу ордер по префиксу TP{i} без отмены чужого этапа.")
                    order_ids.pop(key, None)
                    oid = None
                    active_known = None
                if active_known is not None:
                    st = str(active_known.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                    if st in ("new", "partiallyfilled", "untriggered", "created"):
                        try:
                            cum = float(active_known.get("cumExecQty") or 0)
                            if cum > 0:
                                filled_qty[key] = max(filled_qty.get(key, 0.0), cum)
                        except (TypeError, ValueError, OverflowError):
                            pass
                        try:
                            live_order_tp_price = float(active_known.get("price") or active_known.get("triggerPrice") or 0)
                            saved_plan_price = float(saved_targets[i-1]) if len(saved_targets) >= i else 0.0
                        except (TypeError, ValueError, OverflowError):
                            live_order_tp_price, saved_plan_price = 0.0, 0.0
                        moved_tol = max(tick_size * 0.5, abs(saved_plan_price) * 1e-8, 1e-12)
                        if (math.isfinite(live_order_tp_price) and live_order_tp_price > 0
                                and ((saved_plan_price > 0 and abs(live_order_tp_price - saved_plan_price) > moved_tol)
                                     or saved_plan_price <= 0)):
                            # A missing legacy baseline cannot prove that this order is stale.
                            # Preserve the live exchange price rather than reverting a user edit.
                            manual_tp_overrides[key] = self.client.round_step(live_order_tp_price, tick_size)
                            targets[i-1] = manual_tp_overrides[key]
                            verified[key] = True
                            self.log.info(f"[{symbol}] TP{i}: сохранён фактический уровень {targets[i-1]} (ручной перенос или отсутствующая старая цена в БД); не возвращаю расчётную.")
                            continue
                        stale_reason = self._manual_tp_order_stale_reason(
                            active_known, targets[i - 1], stage_qty_cap, tick_size, qty_step
                        )
                        if not stale_reason:
                            verified[key] = True
                            continue
                        if self._resolve_stale_manual_tp(
                            symbol, i, oid, stale_reason, order_prefix, side, live_idx,
                            order_ids, done, filled_qty, blocked_tp_replacements, verified,
                            active_by_link, stale_cancelled_ids,
                        ) == "skip":
                            continue
                        oid = None
                    elif st == "filled":
                        done[key] = True
                        verified[key] = True
                        continue
                    elif st in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                        oid = None
                        order_ids.pop(key, None)
                    else:
                        continue
                elif oid:
                    # Even when the account-wide open-order request fails, verify
                    # a known ID individually. Unknown state must never trigger a duplicate.
                    try:
                        state = self.client.get_order_state(symbol, str(oid))
                    except Exception:
                        continue
                    if not state:
                        continue
                    if (not _tp_order_matches_position(state, symbol, side, live_idx)
                            or not str(state.get("orderLinkId") or "").startswith(f"{order_prefix}{i}-")):
                        self.log.warning(f"[{symbol}] TP{i}: сохранённый orderId не подтверждён как ордер этого этапа; не отменяю и не создаю замену до сверки.")
                        continue
                    st = str(state.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                    try:
                        cum = float(state.get("cumExecQty") or 0)
                        if cum > 0:
                            filled_qty[key] = max(filled_qty.get(key, 0.0), cum)
                    except (TypeError, ValueError, OverflowError):
                        pass
                    if st == "filled":
                        done[key] = True
                        verified[key] = True
                        continue
                    if st in ("new", "partiallyfilled", "untriggered", "created"):
                        try:
                            live_order_tp_price = float(state.get("price") or state.get("triggerPrice") or 0)
                            saved_plan_price = float(saved_targets[i-1]) if len(saved_targets) >= i else 0.0
                        except (TypeError, ValueError, OverflowError):
                            live_order_tp_price, saved_plan_price = 0.0, 0.0
                        moved_tol = max(tick_size * 0.5, abs(saved_plan_price) * 1e-8, 1e-12)
                        if (math.isfinite(live_order_tp_price) and live_order_tp_price > 0
                                and ((saved_plan_price > 0 and abs(live_order_tp_price - saved_plan_price) > moved_tol)
                                     or saved_plan_price <= 0)):
                            manual_tp_overrides[key] = self.client.round_step(live_order_tp_price, tick_size)
                            targets[i-1] = manual_tp_overrides[key]
                            verified[key] = True
                            self.log.info(f"[{symbol}] TP{i}: сохранён фактический уровень {targets[i-1]} (ручной перенос или отсутствующая старая цена в БД); не возвращаю расчётную.")
                            continue
                        stale_reason = self._manual_tp_order_stale_reason(
                            state, targets[i - 1], stage_qty_cap, tick_size, qty_step
                        )
                        if not stale_reason:
                            verified[key] = True
                            continue
                        if self._resolve_stale_manual_tp(
                            symbol, i, oid, stale_reason, order_prefix, side, live_idx,
                            order_ids, done, filled_qty, blocked_tp_replacements, verified,
                            active_by_link, stale_cancelled_ids,
                        ) == "skip":
                            continue
                        oid = None
                    elif st in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                        oid = None
                        order_ids.pop(key, None)
                    else:
                        continue
            if not oid and active_orders is not None:
                # При потере orderId нельзя искать только по расчётной цене:
                # пользователь мог передвинуть ордер, и тогда старый поиск
                # пропускал бы его и создавал второй TP на старом уровне.
                candidates = [
                    o for o in active_orders
                    if str(o.get("orderLinkId") or "").startswith(f"{order_prefix}{i}-")
                    and o.get("orderId")
                ]
                if len(candidates) > 1:
                    # Несколько активных ордеров одной стадии — неоднозначное
                    # состояние. Не усыновляем произвольный и не создаём новый.
                    blocked_tp_replacements.add(key)
                    verified[key] = False
                    self.log.error(
                        f"[{symbol}] Найдено несколько активных ордеров TP{i} без сохранённого ID; "
                        "не создаю новый тейк до ручной/автоматической сверки."
                    )
                    continue
                if len(candidates) == 1:
                    candidate = candidates[0]
                    candidate_status = str(candidate.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                    candidate_id = candidate.get("orderId")
                    if candidate_status == "filled":
                        done[key] = True
                        verified[key] = True
                        continue
                    if candidate_id and candidate_status in ("new", "partiallyfilled", "untriggered", "created"):
                        try:
                            candidate_price = float(candidate.get("price") or candidate.get("triggerPrice") or 0)
                        except (TypeError, ValueError, OverflowError):
                            candidate_price = 0.0
                        if not math.isfinite(candidate_price) or candidate_price <= 0:
                            blocked_tp_replacements.add(key)
                            verified[key] = False
                            self.log.warning(f"[{symbol}] TP{i} найден без достоверной цены; новый ордер не создаю.")
                            continue
                        saved_plan_price = saved_targets[i-1] if len(saved_targets) >= i else targets[i-1]
                        move_tol = max(tick_size * 0.5, abs(saved_plan_price) * 1e-8, 1e-12)
                        if abs(candidate_price - saved_plan_price) > move_tol:
                            manual_tp_overrides[key] = self.client.round_step(candidate_price, tick_size)
                            targets[i-1] = manual_tp_overrides[key]
                            self.log.info(f"[{symbol}] Восстановил TP{i} по префиксу после потери ID; ручная цена {targets[i-1]} сохранена.")
                        order_ids[key] = str(candidate_id)
                        verified[key] = True
                        continue
                    # Неизвестный статус не доказывает, что ордер отсутствует.
                    blocked_tp_replacements.add(key)
                    verified[key] = False
                    continue
            desired_qty=self.client.round_step(initial_qty*closes[i-1]/100.0,qty_step)
            already_filled=filled_qty.get(key,0.0)
            qty_target=self.client.round_step(max(0.0, desired_qty-already_filled),qty_step)
            if qty_target<=0:
                done[key]=True
                verified[key]=True
                continue
            # После потерянного ACK orderId может отсутствовать в БД. Перед
            # новым place обязательно восстанавливаем недавний mtp-ордер по
            # истории: Filled -> считаем TP исполненным, Active -> возвращаем
            # orderId. Это закрывает окно для дубля после сетевого сбоя.
            if not oid:
                try:
                    if manual_tp_history_cache_loaded:
                        hist = manual_tp_history_cache
                    else:
                        hist = self.client.get_symbol_order_history(symbol, days=7)
                        manual_tp_history_cache = hist
                        manual_tp_history_cache_loaded = hist is not None
                    if hist is None:
                        raise RuntimeError("история ордеров вернула неизвестный результат")
                    recent=[]
                    since=int(sp_now.get("created_at") or 0)
                    for ho in hist:
                        lid=str(ho.get("orderLinkId") or "")
                        if not lid.startswith(f"{order_prefix}{i}-"):
                            continue
                        if str(ho.get("orderId") or "") in stale_cancelled_ids:
                            continue
                        if not _tp_order_matches_position(ho, symbol, side, live_idx):
                            continue
                        try:
                            hist_price=float(ho.get("price") or ho.get("triggerPrice") or 0)
                        except (TypeError, ValueError, OverflowError):
                            continue
                        # Do not filter history by the calculated price: a
                        # manually moved order is expected to differ from it.
                        if not math.isfinite(hist_price) or hist_price <= 0:
                            continue
                        ts=int(ho.get("updatedTime") or ho.get("createdTime") or ho.get("orderTime") or 0)
                        if since and ts and ts < since:
                            continue
                        recent.append(ho)
                    recent.sort(key=lambda x:int(x.get("updatedTime") or x.get("createdTime") or x.get("orderTime") or 0),reverse=True)
                    if recent:
                        rh=recent[0]
                        rstatus=str(rh.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
                        rcum=float(rh.get("cumExecQty") or 0)
                        if rcum>0:
                            filled_qty[key]=max(filled_qty.get(key,0.0),rcum)
                        if rstatus=="filled":
                            done[key]=True
                            verified[key]=True
                            continue
                        if rstatus in ("new","partiallyfilled","untriggered","created") and rh.get("orderId"):
                            try:
                                history_tp_price = float(rh.get("price") or rh.get("triggerPrice") or 0)
                            except (TypeError, ValueError, OverflowError):
                                history_tp_price = 0.0
                            if not math.isfinite(history_tp_price) or history_tp_price <= 0:
                                verified[key] = False
                                self.log.warning(f"[{symbol}] TP{i} из истории имеет некорректную цену; новый ордер не создаю.")
                                continue
                            saved_plan_price = saved_targets[i-1] if len(saved_targets) >= i else targets[i-1]
                            history_tol = max(tick_size * 0.5, abs(saved_plan_price) * 1e-8, 1e-12)
                            if abs(history_tp_price - saved_plan_price) > history_tol:
                                manual_tp_overrides[key] = self.client.round_step(history_tp_price, tick_size)
                                targets[i-1] = manual_tp_overrides[key]
                                self.log.info(f"[{symbol}] Восстановил TP{i} из истории по фактической ручной цене {targets[i-1]}.")
                            order_ids[key]=str(rh.get("orderId"))
                            verified[key]=True
                            continue
                        if rstatus not in ("cancelled", "rejected", "deactivated", "partiallyfilledcanceled"):
                            # A matching historical order with unknown status is
                            # not proof that it is safe to place a replacement.
                            verified[key]=False
                            self.log.warning(
                                f"[{symbol}] Статус ранее созданного TP{i} неизвестен ({rstatus or 'empty'}); "
                                "новый TP не создаю до сверки."
                            )
                            continue
                except Exception as e:
                    # With no persisted orderId, failed history lookup leaves a
                    # possible lost-ACK order unresolved. Never create a duplicate.
                    verified[key]=False
                    self.log.warning(
                        f"[{symbol}] Не удалось восстановить TP{i} из истории ({e}); "
                        "новый тейк не создаю до успешной сверки."
                    )
                    continue
            new_oid=self.client.place_manual_tp_limit(symbol,side,targets[i-1],qty_target,i,prefix=order_prefix)
            if new_oid:
                order_ids[key]=new_oid
                verified[key]=True

        # Обновляем факт исполнения TP1. После него оставшаяся ручная входная лимитка
        # отменяется, а SL переносится на +0.5%/-0.5%, как в прежней ручной логике.
        tp1_done=bool(done.get("1"))
        # Сохранённый cumExecQty означает реальное частичное исполнение TP1,
        # даже если ордер после этого отменили/заменили и его orderId уже снят.
        # Такое исполнение по прежней логике уже должно запускать перенос SL.
        tp1_hit=tp1_done or float(filled_qty.get("1", 0.0) or 0.0) > 0
        if order_ids.get("1"):
            try:
                state=self.client.get_order_state(symbol,order_ids["1"])
                cum=float((state or {}).get("cumExecQty") or 0)
                if cum>0:
                    filled_qty["1"]=max(filled_qty.get("1",0.0),cum)
                    tp1_hit=True
                if str((state or {}).get("orderStatus") or "").lower()=="filled":
                    tp1_done=True; done["1"]=True
            except Exception: pass
        if tp1_hit and not sp_now.get("stale_entries_cancelled"):
            if self._cancel_remaining_entry_orders_after_tp(symbol,sp_now):
                mark_signal_stale_entries_cancelled(symbol); sp_now["stale_entries_cancelled"]=True
        if tp1_hit and sp_now.get("breakeven_after_tp1") and not sp_now.get("breakeven_done"):
            try: live_after=self.client.get_position_strict(symbol,side=("Buy" if side=="LONG" else "Sell"))
            except Exception: live_after=None
            entry_ref=float((live_after or live_pos).get("avgPrice") or avg_entry)
            buf=getattr(cfg,"SIGNAL_BREAKEVEN_BUFFER_PERCENT",0.5)/100.0
            be_raw = entry_ref * (1 + buf) if side == "LONG" else entry_ref * (1 - buf)
            # Округление стопа зависит от стороны: LONG вниз, SHORT вверх.
            # Обычный round_step() всегда вниз и для SHORT мог сдвинуть стоп
            # дальше от заданной цены переноса после TP1.
            be = _round_stop_price_for_side(be_raw, tick_size, side)
            if self.client.update_stop_loss_verified(symbol,be,side):
                mark_signal_breakeven_done(symbol,be)
                sp_now["breakeven_done"] = True
                sp_now["manual_sl_override"] = False
                manual_sl_override = False
                stop = be
                stop_ok = True
                self.tg.notify(f"🛡️ <b>{symbol}</b>: TP1 исполнен. Стоп перенесён на {fmt_num(be)} ({'+' if side=='LONG' else '-'}{getattr(cfg,'SIGNAL_BREAKEVEN_BUFFER_PERCENT',0.5)}% от входа).")

        persist_signal_position_tp_state_with_retry(
            symbol, avg_entry, targets, stop, live_qty, closes, order_ids,
            initial_qty, done, filled_qty, manual_sl_override, logger=self.log,
            manual_tp_overrides=manual_tp_overrides,
        )
        tp_partial_ok = _bot_tp_protection_ready(enabled, done, verified, tp4_ok)
        return {
            "changed": plan_changed,
            "side": side,
            "avg_entry": avg_entry,
            "target": targets[0],
            "targets": targets,
            "stop": stop,
            "manual_stop_pct": manual_stop_pct,
            "manual_tp_pct": moves[0],
            "manual_tp2_pct": closes[0],
            "stop_ok": stop_ok,
            "tp4_ok": tp4_ok,
            "tp_partial_ok": tp_partial_ok,
            "tp_order_id": order_ids.get("1"),
            "tp_order_ok": tp_partial_ok,
            "manual_tp_order_ids": order_ids,
            "manual_tp_done": done,
            "manual_tp_filled_qty": filled_qty,
            "tp1_done": tp1_done,
            "reason": reason,
        }

    def _seed_manual_limit_slots_from_position(self, symbol: str, sp: Dict) -> None:
        """Синхронизирует сохранённые entry_order_ids ручной позиции со слотами.

        Уже закреплённый ID не заменяется другим. Если в старой БД был только
        один слот, недостающий добавляется лишь когда ID точно совпадает с
        сохранённой парой signal_positions; угадывать третью лимитку нельзя.
        """
        if not symbol or not isinstance(sp, dict) or sp.get("source") != "manual":
            return
        with self._manual_limit_value_lock:
            symbol = str(symbol).upper()
            ids = [str(x) for x in (sp.get("entry_order_ids") or []) if x][:2]
            entries = list(sp.get("entries") or [])
            entry_side = "Buy" if str(sp.get("side") or "").upper() == "LONG" else "Sell"
            existing_rows = get_manual_limit_slot_rows(symbol)
            existing_by_slot = {int(r.get("slot") or 0): r for r in existing_rows}

            # Прежде чем дополнять старую неполную пару, проверяем, что ни один
            # уже закреплённый ID не расходится с source-of-truth позиции.
            if existing_by_slot:
                for slot, row in existing_by_slot.items():
                    if slot > len(ids) or str(row.get("order_id") or "") != ids[slot - 1]:
                        self.log.error(
                            f"[{symbol}] Конфликт сохранённых ручных лимиток: DB L{slot}="
                            f"{row.get('order_id')} не совпадает с entry_order_ids позиции. "
                            "Автоматическая замена запрещена; слоты оставлены без изменений."
                        )
                        return

            pending_items = []
            for slot, oid in enumerate(ids, start=1):
                if slot in existing_by_slot:
                    continue
                try:
                    state = self.client.get_order_state(symbol, oid)
                except Exception as e:
                    state = None
                    self.log.warning(f"[{symbol}] Не удалось проверить entry {oid} перед привязкой слота: {e}")
                try:
                    price = float(entries[slot - 1]) if len(entries) >= slot else 0.0
                except (TypeError, ValueError):
                    price = 0.0
                if price <= 0:
                    try:
                        price = float((state or {}).get("price") or 0)
                    except (TypeError, ValueError):
                        price = 0.0
                if price <= 0:
                    self.log.warning(f"[{symbol}] Не могу закрепить L{slot}={oid}: цена не подтверждена")
                    continue
                state_idx = (state or {}).get("positionIdx")
                if state_idx is None:
                    state_idx = sp.get("_live_position_idx")
                pending_items.append({
                    "slot": slot, "order_id": oid, "side": entry_side,
                    "price": price,
                    "qty": float((state or {}).get("qty") or 0),
                    "target_notional_usdt": float(get_setting(f"manual_limit{slot}_value_usdt", 10.0) or 0),
                    "status": "active", "position_idx": state_idx,
                })

            if not pending_items:
                return
            if not existing_rows:
                # При восстановлении пары из двух orderId не сохраняем только
                # один из них, если для второго не подтверждена цена: иначе L2
                # можно было бы ошибочно считать L1 после рестарта.
                if len(pending_items) != len(ids):
                    self.log.error(f"[{symbol}] Не удалось достоверно восстановить все цены entry_order_ids; пару не записываю частично")
                    return
                if not save_manual_limit_slots_atomically(symbol, pending_items):
                    self.log.error(f"[{symbol}] Не удалось атомарно сохранить пару ручных лимиток; текущие слоты не перезаписаны")
                return

            # При восстановлении неполной пары дополняем только её отсутствующий
            # слот и только известным из signal_positions ID. Существующая запись
            # остаётся неизменной, а уникальный индекс защищает от чужого слота.
            for item in pending_items:
                ok = save_manual_limit_slot(
                    symbol, item["slot"], item["order_id"], item["side"], item["price"],
                    item["qty"], item["target_notional_usdt"], status=item["status"],
                    position_idx=item["position_idx"],
                )
                if not ok:
                    self.log.error(
                        f"[{symbol}] Не удалось восстановить L{item['slot']}={item['order_id']}: "
                        "ID уже принадлежит другому слоту или запись конфликтует"
                    )

    def apply_manual_limit_values_to_open_orders(self, reason: str = "") -> Tuple[int, int, int, List[str]]:
        """Закрепляет L1/L2 за конкретными orderId и меняет только qty.

        Новая пара выбирается один раз: сначала определяется сторона ближайшей
        подходящей лимитки (Buy ниже рынка либо Sell выше рынка), затем вторая
        берётся с той же стороны. При дальнейших вызовах расстояние до рынка
        больше не меняет роли L1/L2. Исполнение, частичное исполнение или
        отмена одного ордера фиксируется в SQLite; третья лимитка не занимает
        освободившееся место, пока вторая активна или позиция не завершилась.

        100 USDT — это номинал ордера, а не маржа. Цена/сторона ордера не меняются.
        """
        with self._manual_limit_value_lock:
            changed = skipped = failed = 0
            errors: List[str] = []
            # Этот переключатель блокирует ВСЕ автоматические изменения размера
            # уже выставленных лимиток, включая фоновую синхронизацию. Слоты и
            # цены при этом не очищаются: после включения можно продолжить работу.
            if not bool(get_setting("manual_limit_value_changes_enabled", True)):
                return 0, 0, 0, ["Автоизменение стоимости лимиток выключено; размеры ордеров оставлены без изменений"]
            target_update_event = getattr(self, "_manual_limit_target_update_requested", None)
            if target_update_event is not None and target_update_event.is_set():
                return 0, 0, 0, ["Изменение номинала L1/L2 сохраняется; синхронизация ордеров временно приостановлена"]
            try:
                target_values = {
                    1: float(get_setting("manual_limit1_value_usdt", 10.0) or 0),
                    2: float(get_setting("manual_limit2_value_usdt", 10.0) or 0),
                }
                if any((not math.isfinite(v)) or v <= 0 for v in target_values.values()):
                    return 0, 0, 0, ["Стоимость 1-й и 2-й лимитки должна быть конечным числом больше 0 USDT"]

                # Если API списка ордеров временно недоступен — ничего не
                # переназначаем и не меняем. Неизвестное состояние нельзя
                # трактовать как отмену/исполнение.
                all_orders = self.client.get_open_orders_all() or []
                open_by_id = {str(o.get("orderId")): o for o in all_orders if o.get("orderId")}

                open_signal_positions = get_all_open_signal_positions() or {}
                manual_signal_positions = {
                    str(sym).upper(): sp for sym, sp in open_signal_positions.items()
                    if isinstance(sp, dict) and sp.get("source") == "manual"
                }
                for sym, sp in manual_signal_positions.items():
                    self._seed_manual_limit_slots_from_position(sym, sp)

                # Получаем позиции один раз. При ошибке API запрещаем любые
                # новые назначения/reset слотов и изменение leverage.
                active_position_symbols = set()
                active_position_sides: Dict[str, str] = {}
                positions_state_known = True
                try:
                    for pos in self.client.get_all_open_positions():
                        ps = str(pos.get("symbol") or "").upper()
                        if ps and float(pos.get("size") or 0) > 0:
                            active_position_symbols.add(ps)
                            if pos.get("side") in {"Buy", "Sell"}:
                                active_position_sides[ps] = str(pos.get("side"))
                except Exception as e:
                    positions_state_known = False
                    self.log.warning(f"Не удалось получить активные позиции перед изменением лимиток: {e}. Новые слоты и leverage менять не будем.")

                protected_ids = set()
                for sp in open_signal_positions.values():
                    if not isinstance(sp, dict):
                        continue
                    for oid in (sp.get("entry_order_ids") or []):
                        if oid:
                            protected_ids.add(str(oid))

                bot_symbols = set(str(x).upper() for x in get_all_bot_positions().keys())
                pump_engine = getattr(self.tg, "engine", None)
                if pump_engine is not None:
                    try:
                        lock = getattr(pump_engine, "_known_lock", None)
                        if lock is not None:
                            with lock:
                                bot_symbols.update(str(x).upper() for x in (getattr(pump_engine, "_known_open_symbols", set()) or set()))
                        else:
                            bot_symbols.update(str(x).upper() for x in (getattr(pump_engine, "_known_open_symbols", set()) or set()))
                    except Exception:
                        pass

                # Сначала подтверждаем состояние уже закреплённых orderId.
                # Отсутствие из open orders само по себе не означает fill/cancel:
                # для каждого такого ID ищем финальный статус в order history.
                slots_by_symbol: Dict[str, List[Dict]] = {}
                for row in get_manual_limit_slot_rows():
                    slots_by_symbol.setdefault(str(row["symbol"]).upper(), []).append(row)
                now_ms = int(time.time() * 1000)
                # Если orderId из SQLite не совпадает с живым символом/стороной/
                # hedge-leg, не «исправляем» привязку молча по ответу биржи —
                # блокируем amend для этого ID до ручной/отдельной сверки.
                unsafe_bound_order_ids = set()
                for sym, rows in list(slots_by_symbol.items()):
                    updated_rows = []
                    for row in sorted(rows, key=lambda r: int(r.get("slot") or 99)):
                        oid = str(row.get("order_id") or "")
                        live_order = open_by_id.get(oid)
                        order_position_idx = None
                        slot_side_for_save = str(row.get("side") or "Buy")
                        if live_order is not None:
                            live_symbol = str(live_order.get("symbol") or "").upper()
                            live_side = str(live_order.get("side") or "")
                            saved_side = str(row.get("side") or "")
                            try:
                                saved_idx_raw = row.get("position_idx")
                                live_idx_raw = live_order.get("positionIdx")
                                saved_idx = int(saved_idx_raw) if saved_idx_raw is not None and str(saved_idx_raw).strip() != "" else None
                                live_idx = int(live_idx_raw) if live_idx_raw is not None and str(live_idx_raw).strip() != "" else None
                            except (TypeError, ValueError, OverflowError):
                                saved_idx, live_idx = None, None
                            mismatch_reason = None
                            if live_symbol != sym:
                                mismatch_reason = f"symbol биржи={live_symbol or 'не указан'}"
                            elif live_side not in {"Buy", "Sell"} or (saved_side and live_side != saved_side):
                                mismatch_reason = f"сторона биржи={live_side or 'не указана'}"
                            elif live_idx is None or (saved_idx is not None and live_idx != saved_idx):
                                mismatch_reason = f"positionIdx SQLite={saved_idx!r}, биржа={live_idx!r}"
                            if mismatch_reason:
                                unsafe_bound_order_ids.add(oid)
                                self.log.error(
                                    f"[{sym}] Запись L{row.get('slot')} привязана к {oid}, но идентичность ордера не совпала ({mismatch_reason}); "
                                    "не переписываю слот и запрещаю amend этого ордера"
                                )
                                continue
                            order_position_idx = live_order.get("positionIdx")
                            slot_side_for_save = live_side
                            order_status = str(live_order.get("orderStatus") or "New").strip().lower()
                            if order_status in {"new", "partiallyfilled", "partially_filled", "untriggered"}:
                                state = "active"
                                terminal_reason = None
                            elif order_status == "filled" or order_status == "partiallyfilledcanceled":
                                state = "filled"
                                terminal_reason = order_status
                            elif order_status in {"cancelled", "canceled", "rejected", "deactivated"}:
                                state = "cancelled"
                                terminal_reason = order_status
                            else:
                                state = "unknown"
                                terminal_reason = order_status or "unknown_status"
                            try:
                                # Для живого ордера не используем старую цену/qty
                                # из SQLite как fallback: после ручного изменения
                                # они могли устареть и привести к неверному номиналу.
                                price = float(live_order.get("price"))
                                qty = float(live_order.get("qty"))
                            except (TypeError, ValueError, OverflowError):
                                price, qty = float("nan"), float("nan")
                            if not math.isfinite(price) or price <= 0 or not math.isfinite(qty) or qty <= 0:
                                unsafe_bound_order_ids.add(oid)
                                self.log.error(
                                    f"[{sym}] Биржа вернула некорректные price/qty для {oid}; "
                                    "не обновляю SQLite и не разрешаю amend"
                                )
                                continue
                        else:
                            try:
                                hist_state = self.client.get_order_state(sym, oid)
                            except Exception as e:
                                hist_state = None
                                self.log.warning(f"[{sym}] Не удалось подтвердить состояние закреплённой лимитки {oid}; слот остаётся зарезервирован: {e}")
                            if not hist_state:
                                state = "unknown"
                                terminal_reason = "not_found_or_history_unavailable"
                                price = float(row.get("price") or 0)
                                qty = float(row.get("qty") or 0)
                            else:
                                order_position_idx = hist_state.get("positionIdx")
                                order_status = str(hist_state.get("orderStatus") or "").strip().lower()
                                price = float(hist_state.get("price") or row.get("price") or 0)
                                qty = float(hist_state.get("qty") or row.get("qty") or 0)
                                if order_status in {"new", "partiallyfilled", "partially_filled", "untriggered"}:
                                    state = "active"
                                    terminal_reason = None
                                elif order_status == "filled" or order_status == "partiallyfilledcanceled":
                                    state = "filled"
                                    terminal_reason = order_status
                                elif order_status in {"cancelled", "canceled", "rejected", "deactivated"}:
                                    state = "cancelled"
                                    terminal_reason = order_status
                                else:
                                    state = "unknown"
                                    terminal_reason = order_status or "unknown_status"
                        save_manual_limit_slot(
                            sym, int(row["slot"]), oid, slot_side_for_save,
                            price, qty, float(row.get("target_notional_usdt") or 0),
                            status=state, terminal_reason=terminal_reason,
                            position_idx=order_position_idx,
                        )
                    slots_by_symbol[sym] = get_manual_limit_slot_rows(sym)

                # Освобождаем старую пару только когда оба её ордера доказанно
                # завершены, биржа подтвердила отсутствие позиции, нет ручной
                # позиции под управлением, а после fill прошёл защитный интервал.
                # Так не будет race: первый ордер исчез, позиция ещё не успела
                # попасть в REST-ответ, а третий ордер ошибочно стал L1/L2.
                reset_symbols = []
                if positions_state_known:
                    for sym, rows in slots_by_symbol.items():
                        statuses = {str(r.get("status") or "unknown") for r in rows}
                        if not rows or not statuses.issubset({"filled", "cancelled", "rejected"}):
                            continue
                        if sym in active_position_symbols or sym in open_signal_positions:
                            continue
                        if any(str(r.get("order_id") or "") in open_by_id for r in rows):
                            continue
                        fill_rows = [r for r in rows if str(r.get("status")) == "filled"]
                        if fill_rows and any(now_ms - int(r.get("updated_at") or now_ms) < 120_000 for r in fill_rows):
                            continue
                        reset_symbols.append(sym)
                for sym in reset_symbols:
                    clear_manual_limit_slots(sym, reason="все закреплённые ордера завершены, открытой позиции нет")
                    slots_by_symbol.pop(sym, None)

                # mtp1-…mtp3- — собственные reduce-only TP ручных позиций.
                # Они не должны попадать в L1/L2 даже если reduceOnly отсутствует
                # в неполном REST-ответе; при этом общий детектор manual-позиций
                # должен и дальше уметь восстановить ручную позицию по этим TP.
                limit_value_protected_prefixes = tuple(self._BOT_ORDER_LINK_PREFIXES) + ("mtp1-", "mtp2-", "mtp3-")
                # Строим пул новых кандидатов. Смешанные Buy/Sell не смешиваем:
                # иначе слот 2 мог бы относиться к другой стороне позиции.
                candidates_by_symbol: Dict[str, List[Dict]] = {}
                for order in all_orders:
                    oid = str(order.get("orderId") or "")
                    sym = str(order.get("symbol") or "").upper()
                    if not oid or not sym or sym in bot_symbols or oid in protected_ids:
                        continue
                    link = str(order.get("orderLinkId") or "")
                    if any(link.startswith(prefix) for prefix in limit_value_protected_prefixes):
                        continue
                    if str(order.get("orderType") or "").strip().lower() != "limit":
                        continue
                    # Условные Stop/TP/триггерные LIMIT не являются обычными
                    # входными лимитками: не позволяем менять их размер как L1/L2.
                    try:
                        trigger_price = float(order.get("triggerPrice") or 0)
                        trigger_direction = int(order.get("triggerDirection") or 0)
                    except (TypeError, ValueError):
                        continue
                    if trigger_price > 0 or trigger_direction != 0 or _is_conditional_stop_type(order.get("stopOrderType")):
                        continue
                    reduce_only = order.get("reduceOnly")
                    if isinstance(reduce_only, str):
                        reduce_only_text = reduce_only.strip().lower()
                        if reduce_only_text in {"1", "true", "yes", "on"}:
                            reduce_only = True
                        elif reduce_only_text in {"0", "false", "no", "off"}:
                            reduce_only = False
                        else:
                            continue
                    elif isinstance(reduce_only, (int, float)) and reduce_only in (0, 1):
                        reduce_only = bool(reduce_only)
                    elif not isinstance(reduce_only, bool):
                        # Не закрепляем неполные REST-объекты: иначе неизвестный
                        # ордер может занять слот навсегда, а на amend всё равно
                        # будет заблокирован.
                        continue
                    if reduce_only:
                        continue
                    if str(order.get("orderStatus") or "New").strip().lower() != "new":
                        continue
                    if str(order.get("side") or "") not in {"Buy", "Sell"}:
                        continue
                    try:
                        price = float(order.get("price") or 0)
                        qty = float(order.get("qty") or 0)
                        position_idx = int(order.get("positionIdx"))
                    except (TypeError, ValueError, OverflowError):
                        continue
                    if (not math.isfinite(price) or price <= 0 or
                            not math.isfinite(qty) or qty <= 0 or
                            position_idx not in (0, 1, 2)):
                        # Не закрепляем неполный/испорченный REST-объект в L1/L2.
                        continue
                    candidates_by_symbol.setdefault(sym, []).append(order)

                # Для незакреплённых символов один раз выбираем пару. Если по
                # символу уже есть live-позиция, ничего нового не выбираем:
                # scan_manual_positions сначала закрепит именно её исходные IDs.
                for sym, orders in candidates_by_symbol.items():
                    if (not positions_state_known) or sym in bot_symbols or sym in active_position_symbols or sym in open_signal_positions:
                        continue
                    existing = get_manual_limit_slot_rows(sym)
                    if existing:
                        # Если при первом обнаружении существовала только L1,
                        # разрешаем закрепить L2 позднее, но строго пока L1 всё
                        # ещё открыта и не частично исполнена. После fill/cancel
                        # новые ордера не занимают её место и не становятся L2.
                        existing_by_slot = {int(r.get("slot") or 0): r for r in existing}

                        # ДО исполнения (позиции ещё нет) пара L1/L2 — это ДВЕ БЛИЖАЙШИЕ к рынку
                        # лимитки, а не «те, что бот увидел первыми». Раньше, если дальнюю
                        # лимитку бот успевал закрепить раньше, чем пользователь выставил
                        # ближние, она навсегда оставалась L1, а L2 становилась ближайшей из
                        # остальных. Пока ни одна из закреплённых не тронута (статус New,
                        # исполнено 0), перепроверяем пару и при расхождении пересобираем атомарно.
                        try:
                            rr_rows = [existing_by_slot[s] for s in sorted(existing_by_slot) if s in (1, 2)]
                            rr_live = [open_by_id.get(str(r.get("order_id") or "")) for r in rr_rows]

                            def _rr_fresh(o):
                                if not o:
                                    return False
                                try:
                                    done_qty = float(o.get("cumExecQty") or 0)
                                except (TypeError, ValueError):
                                    return False
                                return str(o.get("orderStatus") or "New").strip().lower() == "new" and done_qty <= 0

                            if (rr_rows and len(rr_rows) == len(existing_by_slot)
                                    and all(str(r.get("status") or "") == "active" for r in rr_rows)
                                    and all(_rr_fresh(o) for o in rr_live)):
                                rr_side = str(rr_rows[0].get("side") or "")
                                try:
                                    rr_idx = int(rr_rows[0].get("position_idx") if rr_rows[0].get("position_idx") is not None
                                                 else (rr_live[0].get("positionIdx") or 0))
                                except (TypeError, ValueError):
                                    rr_idx = 0
                                saved_ids_rr = [str(r.get("order_id") or "") for r in rr_rows]
                                same_group = []
                                for o in orders:
                                    try:
                                        if str(o.get("side") or "") == rr_side and int(o.get("positionIdx") or 0) == rr_idx:
                                            same_group.append(o)
                                    except (TypeError, ValueError):
                                        continue
                                # Лишний REST-запрос цены нужен, только если есть ещё лимитки кроме закреплённых.
                                if rr_side in ("Buy", "Sell") and any(str(o.get("orderId") or "") not in saved_ids_rr for o in same_group) \
                                        and all(str(r.get("side") or "") == rr_side for r in rr_rows):
                                    rr_market = float(self.client.get_last_price_rest(sym) or 0)
                                    if rr_market > 0:
                                        rr_tol = max(abs(rr_market) * 1e-10, 1e-12)
                                        rr_pool = []
                                        for o in same_group:
                                            try:
                                                px = float(o.get("price") or 0)
                                                if px <= 0:
                                                    continue
                                                if rr_side == "Buy" and px > rr_market + rr_tol:
                                                    continue
                                                if rr_side == "Sell" and px < rr_market - rr_tol:
                                                    continue
                                                rr_pool.append((abs(px - rr_market), int(o.get("createdTime") or 0), str(o.get("orderId") or ""), o, px))
                                            except (TypeError, ValueError, OverflowError):
                                                continue
                                        rr_pool.sort(key=lambda x: (x[0], x[1], x[2]))
                                        rr_desired = rr_pool[:2]
                                        desired_ids_rr = [x[2] for x in rr_desired]
                                        need_rerank = False
                                        if len(saved_ids_rr) == 2:
                                            need_rerank = len(desired_ids_rr) == 2 and desired_ids_rr != saved_ids_rr
                                        elif len(saved_ids_rr) == 1:
                                            need_rerank = bool(desired_ids_rr) and desired_ids_rr[0] != saved_ids_rr[0]
                                        if need_rerank:
                                            rr_items = []
                                            for rr_slot, x in enumerate(rr_desired, start=1):
                                                o = x[3]
                                                rr_items.append({
                                                    "slot": rr_slot, "order_id": x[2], "side": rr_side, "price": x[4],
                                                    "qty": float(o.get("qty") or 0),
                                                    "target_notional_usdt": target_values[rr_slot],
                                                    "status": "active", "position_idx": rr_idx,
                                                })
                                            if len(saved_ids_rr) == 2:
                                                rr_saved = replace_manual_limit_slots_atomically(
                                                    sym, rr_items, expected_order_ids={1: saved_ids_rr[0], 2: saved_ids_rr[1]},
                                                )
                                            else:
                                                clear_manual_limit_slots(sym, reason="пересборка пары: появились лимитки ближе к рынку")
                                                rr_saved = save_manual_limit_slots_atomically(sym, rr_items)
                                            if rr_saved:
                                                self.log.warning(
                                                    f"[{sym}] До исполнения пара L1/L2 пересобрана по ближайшим к рынку: "
                                                    f"{saved_ids_rr} -> {desired_ids_rr}"
                                                )
                                            else:
                                                failed += 1
                                                errors.append(f"{sym}: не удалось пересобрать пару L1/L2 по ближайшим лимиткам")
                                            slots_by_symbol[sym] = get_manual_limit_slot_rows(sym)
                                            continue
                        except Exception as rr_err:
                            self.log.warning(f"[{sym}] Не удалось перепроверить пару L1/L2 до исполнения: {rr_err}")

                        if set(existing_by_slot) == {1}:
                            row1 = existing_by_slot[1]
                            oid1 = str(row1.get("order_id") or "")
                            live1 = open_by_id.get(oid1)
                            if (str(row1.get("status") or "") == "active" and live1 and
                                    str(live1.get("orderStatus") or "New").strip().lower() == "new"):
                                try:
                                    market2 = float(self.client.get_last_price_rest(sym) or 0)
                                except Exception as e:
                                    market2 = 0.0
                                    self.log.warning(f"[{sym}] Не удалось получить цену для закрепления недостающей L2: {e}")
                                if market2 > 0:
                                    side1 = str(row1.get("side") or "")
                                    try:
                                        idx1 = int(row1.get("position_idx") if row1.get("position_idx") is not None else live1.get("positionIdx") or 0)
                                    except (TypeError, ValueError):
                                        idx1 = 0
                                    tol2 = max(abs(market2) * 1e-10, 1e-12)
                                    already_ids = {str(r.get("order_id") or "") for r in existing}
                                    second_candidates = []
                                    for candidate in orders:
                                        oid2 = str(candidate.get("orderId") or "")
                                        if not oid2 or oid2 in already_ids:
                                            continue
                                        if str(candidate.get("side") or "") != side1:
                                            continue
                                        try:
                                            idx2 = int(candidate.get("positionIdx") or 0)
                                            px2 = float(candidate.get("price") or 0)
                                            created2 = int(candidate.get("createdTime") or 0)
                                        except (TypeError, ValueError):
                                            continue
                                        if idx2 != idx1 or px2 <= 0:
                                            continue
                                        if side1 == "Buy" and px2 > market2 + tol2:
                                            continue
                                        if side1 == "Sell" and px2 < market2 - tol2:
                                            continue
                                        second_candidates.append((abs(px2 - market2), created2, oid2, candidate, px2))
                                    second_candidates.sort(key=lambda x: (x[0], x[1], x[2]))
                                    if second_candidates:
                                        _, _, oid2, order2, px2 = second_candidates[0]
                                        try:
                                            qty2 = float(order2.get("qty") or 0)
                                        except (TypeError, ValueError):
                                            qty2 = 0.0
                                        if save_manual_limit_slot(
                                            sym, 2, oid2, side1, px2, qty2, target_values[2],
                                            status="active", position_idx=idx1,
                                        ):
                                            slots_by_symbol[sym] = get_manual_limit_slot_rows(sym)
                                            self.log.info(f"[{sym}] Закреплена недостающая L2={oid2}; L1={oid1} сохранена без изменений")
                                        else:
                                            failed += 1
                                            errors.append(f"{sym}: не удалось закрепить L2={oid2}; существующая L1 не изменена")
                        continue
                    try:
                        market = float(self.client.get_last_price_rest(sym) or 0)
                    except (TypeError, ValueError, OverflowError):
                        market = float("nan")
                    if not math.isfinite(market) or market <= 0:
                        failed += min(len(orders), 2)
                        errors.append(f"{sym}: не удалось получить корректную конечную текущую цену")
                        continue
                    resting_groups: Dict[Tuple[str, int], List[Dict]] = {}
                    tol = max(abs(float(market)) * 1e-10, 1e-12)
                    for order in orders:
                        price = float(order.get("price") or 0)
                        order_side = str(order.get("side") or "")
                        try:
                            order_position_idx = int(order.get("positionIdx") or 0)
                        except (TypeError, ValueError):
                            order_position_idx = 0
                        if order_side == "Buy" and price <= market + tol:
                            resting_groups.setdefault((order_side, order_position_idx), []).append(order)
                        elif order_side == "Sell" and price >= market - tol:
                            resting_groups.setdefault((order_side, order_position_idx), []).append(order)
                    ranked_sides = []
                    def _created_time_or_zero(candidate):
                        try:
                            return max(0, int(candidate.get("createdTime") or 0))
                        except (TypeError, ValueError, OverflowError):
                            return 0

                    for (order_side, order_position_idx), side_orders in resting_groups.items():
                        if not side_orders:
                            continue
                        nearest_distance = min(abs(float(o.get("price") or 0) - market) for o in side_orders)
                        oldest = min(_created_time_or_zero(o) for o in side_orders)
                        ranked_sides.append((nearest_distance, -oldest, order_side, order_position_idx, side_orders))
                    if not ranked_sides:
                        continue
                    ranked_sides.sort(key=lambda x: (x[0], x[1], x[2], x[3]))
                    chosen_side, chosen_position_idx, selected = ranked_sides[0][2], ranked_sides[0][3], ranked_sides[0][4]
                    selected = sorted(
                        selected,
                        key=lambda o: (
                            abs(float(o.get("price") or 0) - market),
                            _created_time_or_zero(o),
                            str(o.get("orderId") or ""),
                        ),
                    )[:2]
                    atomic_items = []
                    for slot, order in enumerate(selected, start=1):
                        oid = str(order.get("orderId") or "")
                        price = float(order.get("price") or 0)
                        qty = float(order.get("qty") or 0)
                        if not oid or price <= 0:
                            errors.append(f"{sym} L{slot}: у кандидата нет корректного orderId/цены; пара не закреплена")
                            failed += 1
                            atomic_items = []
                            break
                        atomic_items.append({
                            "slot": slot, "order_id": oid, "side": chosen_side,
                            "price": price, "qty": qty, "target_notional_usdt": target_values[slot],
                            "status": "active", "position_idx": chosen_position_idx,
                        })
                    if atomic_items:
                        if not save_manual_limit_slots_atomically(sym, atomic_items):
                            errors.append(f"{sym}: пара L1/L2 не сохранена атомарно — обнаружен конфликт со слотами/ID; ордера не изменены")
                            failed += len(atomic_items)
                        slots_by_symbol[sym] = get_manual_limit_slot_rows(sym)

                # Мax leverage разрешаем менять только если запрос позиций
                # удался и по символу нет уже открытой позиции.
                leverage_cache: Dict[str, Optional[float]] = {}
                instrument_cache: Dict[str, Dict] = {}
                for sym, rows in list(slots_by_symbol.items()):
                    if sym in bot_symbols or sym in open_signal_positions:
                        # Позиция/сигнал уже управляется отдельным TP/SL-монитором.
                        # Не изменяем посторонние/устаревшие слоты по этому символу.
                        continue
                    for row in sorted(rows, key=lambda r: int(r.get("slot") or 99)):
                        slot = int(row.get("slot") or 0)
                        oid = str(row.get("order_id") or "")
                        if slot not in (1, 2) or not oid:
                            continue
                        status = str(row.get("status") or "unknown")
                        if status != "active":
                            continue
                        if oid in unsafe_bound_order_ids:
                            skipped += 1
                            continue
                        order = open_by_id.get(oid)
                        if not order:
                            # API history мог сообщить active, но общего open-list
                            # сейчас нет. Резервируем слот, но не меняем его вслепую.
                            skipped += 1
                            continue
                        if str(order.get("orderStatus") or "New").strip().lower() != "new":
                            skipped += 1
                            continue
                        if oid in protected_ids:
                            skipped += 1
                            continue

                        # Перед REST amend доверяем фактическому ответу биржи, а не
                        # только строке слота SQLite. При любом несовпадении безопасно
                        # пропускаем ордер, чтобы не изменить не тот контракт/hedge-leg.
                        live_symbol = str(order.get("symbol") or "").upper()
                        if live_symbol != sym:
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): symbol биржи {live_symbol or 'не указан'} не совпадает со слотом; ордер не изменён")
                            continue
                        live_side = str(order.get("side") or "")
                        saved_side = str(row.get("side") or "")
                        if live_side not in {"Buy", "Sell"} or (saved_side and live_side != saved_side):
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): сторона биржи не совпадает с сохранённой; ордер не изменён")
                            continue
                        if str(order.get("orderType") or "").strip().lower() != "limit":
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): ордер больше не является обычным LIMIT; размер не меняю")
                            continue
                        reduce_only = order.get("reduceOnly")
                        if isinstance(reduce_only, str):
                            reduce_only_text = reduce_only.strip().lower()
                            if reduce_only_text in {"1", "true", "yes", "on"}:
                                reduce_only = True
                            elif reduce_only_text in {"0", "false", "no", "off"}:
                                reduce_only = False
                            else:
                                failed += 1
                                errors.append(f"{sym} L{slot} ({oid}): неизвестное значение reduceOnly; размер не меняю")
                                continue
                        elif not isinstance(reduce_only, bool):
                            if isinstance(reduce_only, (int, float)) and reduce_only in (0, 1):
                                reduce_only = bool(reduce_only)
                            else:
                                failed += 1
                                errors.append(f"{sym} L{slot} ({oid}): reduceOnly отсутствует/не подтверждён; размер не меняю")
                                continue
                        try:
                            trigger_price_live = float(order.get("triggerPrice") or 0)
                            trigger_direction_live = int(order.get("triggerDirection") or 0)
                        except (TypeError, ValueError, OverflowError):
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): некорректные параметры условного ордера; размер не меняю")
                            continue
                        if (not math.isfinite(trigger_price_live) or trigger_price_live < 0 or
                                bool(reduce_only) or trigger_price_live > 0 or trigger_direction_live != 0 or _is_conditional_stop_type(order.get("stopOrderType"))):
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): reduce-only/условный ордер; размер не меняю")
                            continue
                        link_live = str(order.get("orderLinkId") or "")
                        if any(link_live.startswith(prefix) for prefix in limit_value_protected_prefixes):
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): ордер помечен как ордер торгового движка; размер не меняю")
                            continue
                        try:
                            live_idx_raw = order.get("positionIdx")
                            saved_idx_raw = row.get("position_idx")
                            live_idx = int(live_idx_raw) if live_idx_raw is not None and str(live_idx_raw).strip() != "" else None
                            saved_idx = int(saved_idx_raw) if saved_idx_raw is not None and str(saved_idx_raw).strip() != "" else None
                        except (TypeError, ValueError, OverflowError):
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): некорректный positionIdx; ордер не изменён")
                            continue
                        if live_idx is None or (saved_idx is not None and live_idx != saved_idx):
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): positionIdx не подтверждён/изменился; ордер не изменён")
                            continue

                        try:
                            # Для активного ордера доверяем только живой цене из
                            # ответа биржи. Устаревшая цена SQLite не должна
                            # использоваться для расчёта нового номинала.
                            price = float(order.get("price"))
                        except (TypeError, ValueError, OverflowError):
                            price = float("nan")
                        if not math.isfinite(price) or price <= 0:
                            failed += 1
                            errors.append(f"{sym} L{slot}: у сохранённого ордера {oid} некорректная цена")
                            continue
                        try:
                            if sym not in instrument_cache:
                                instrument_cache[sym] = self.client.get_instrument_filters(sym)
                            filters = instrument_cache[sym]
                            lot_filter = filters["lotSizeFilter"]
                            min_qty = float(lot_filter["minOrderQty"])
                            qty_step = float(lot_filter["qtyStep"])
                            min_notional = float(lot_filter.get("minNotionalValue") or 0)
                            max_qty = float(lot_filter.get("maxOrderQty") or lot_filter.get("maxLimitOrderQty") or 0)
                            if (not math.isfinite(qty_step) or qty_step <= 0 or
                                    not math.isfinite(min_qty) or min_qty <= 0 or
                                    not math.isfinite(min_notional) or min_notional < 0 or
                                    not math.isfinite(max_qty) or max_qty < 0):
                                raise RuntimeError("биржа вернула некорректные minOrderQty/qtyStep/лимиты количества")
                            # Количество считается в Decimal за одно деление: частное
                            # float USDT/цена на точных кратных теряло шаг количества и
                            # давало ложное «номинал меньше minNotional».
                            desired_qty = float(self.client.qty_for_notional(target_values[slot], price, qty_step))
                            if not math.isfinite(desired_qty):
                                raise RuntimeError("рассчитанное количество не является конечным числом")
                            price_dec = Decimal(str(price))
                            step_dec = Decimal(str(qty_step))
                            target_dec = Decimal(str(target_values[slot]))
                            # Минимальное допустимое количество/стоимость лимитки с учётом
                            # minOrderQty и minNotionalValue (кратное шагу, округление вверх).
                            need_qty_dec = Decimal(str(min_qty))
                            if min_notional > 0:
                                need_qty_dec = max(
                                    need_qty_dec,
                                    (Decimal(str(min_notional)) / (price_dec * step_dec)).to_integral_value(rounding=ROUND_CEILING) * step_dec,
                                )
                            need_qty_dec = (need_qty_dec / step_dec).to_integral_value(rounding=ROUND_CEILING) * step_dec
                            min_value_usdt = float(need_qty_dec * price_dec)
                            # Цель сама по себе допустима для биржи, но округление количества
                            # ВНИЗ упёрлось в минимум (например, 5 USDT при minNotional 5):
                            # поднимаем до минимального ордера, если перерасход не больше 1%.
                            if (Decimal(str(desired_qty)) < need_qty_dec
                                    and need_qty_dec * price_dec <= target_dec * Decimal("1.01")):
                                self.log.info(
                                    f"[{sym}] L{slot}: {target_values[slot]:g} USDT округлены вверх до минимального ордера "
                                    f"{float(need_qty_dec):g} (≈{min_value_usdt:.8g} USDT)"
                                )
                                desired_qty = float(need_qty_dec)
                            if desired_qty <= 0:
                                failed += 1
                                errors.append(
                                    f"{sym} L{slot}: {target_values[slot]:g} USDT меньше одного шага количества "
                                    f"({qty_step:g} ≈ {qty_step * price:.8g} USDT по цене {price:g}); "
                                    f"увеличь стоимость лимитки (нужно не меньше ≈{min_value_usdt:.8g} USDT)"
                                )
                                continue
                            if desired_qty < min_qty:
                                failed += 1
                                errors.append(
                                    f"{sym} L{slot}: qty {desired_qty:g} меньше minQty {min_qty:g} для {target_values[slot]:g} USDT; "
                                    f"нужно не меньше ≈{min_value_usdt:.8g} USDT"
                                )
                                continue
                            actual_notional_dec = Decimal(str(desired_qty)) * price_dec
                            actual_notional = float(actual_notional_dec)
                            if not math.isfinite(actual_notional) or actual_notional <= 0:
                                raise RuntimeError("рассчитанный номинал ордера недопустим")
                            if max_qty > 0 and desired_qty > max_qty:
                                failed += 1
                                errors.append(f"{sym} L{slot}: qty {desired_qty:g} превышает maxOrderQty {max_qty:g}; уменьши номинал лимитки")
                                continue
                            if min_notional > 0 and actual_notional_dec < Decimal(str(min_notional)):
                                failed += 1
                                errors.append(
                                    f"{sym} L{slot}: номинал {actual_notional:.8g} USDT меньше minNotional {min_notional:g} USDT; "
                                    f"увеличь стоимость лимитки в настройках (нужно не меньше ≈{min_value_usdt:.8g} USDT)"
                                )
                                continue
                            try:
                                current_qty = float(order.get("qty") or 0)
                            except (TypeError, ValueError, OverflowError):
                                current_qty = float("nan")
                            if not math.isfinite(current_qty) or current_qty <= 0:
                                raise RuntimeError(f"биржа вернула некорректный текущий qty: {order.get('qty')!r}")

                            # Leverage вызываем максимум один раз на символ;
                            # при неизвестном состоянии позиций — никогда.
                            max_leverage = None
                            if positions_state_known and sym not in active_position_symbols:
                                if sym not in leverage_cache:
                                    lev = self.client.get_max_leverage(sym)
                                    try:
                                        lev = float(lev)
                                    except (TypeError, ValueError, OverflowError):
                                        lev = float("nan")
                                    if not math.isfinite(lev) or lev <= 0:
                                        raise RuntimeError("биржа не вернула корректное максимальное плечо")
                                    # Проверенная установка плеча: при устаревшем кэше
                                    # (плечо поменяли вручную в приложении) выставит заново.
                                    actual_lev = self.client.ensure_leverage_verified(sym, lev)
                                    if actual_lev is not None:
                                        try:
                                            actual_lev = float(actual_lev)
                                        except (TypeError, ValueError, OverflowError):
                                            actual_lev = float("nan")
                                        if not math.isfinite(actual_lev) or actual_lev <= 0 or abs(actual_lev - lev) > 0.01:
                                            raise RuntimeError(f"биржа не подтвердила max-плечо {lev:g}x (фактически {actual_lev!r})")
                                    leverage_cache[sym] = lev
                                max_leverage = leverage_cache[sym]

                            # Сохраняем связь orderId->слот ДО REST amend. Если
                            # ордер исполнится прямо во время amend, следующий цикл
                            # всё равно однозначно узнает, какой именно это был вход.
                            if not save_manual_limit_slot(
                                sym, slot, oid, str(order.get("side") or row.get("side") or "Buy"),
                                price, current_qty, target_values[slot], status="active",
                                position_idx=order.get("positionIdx", row.get("position_idx")),
                            ):
                                raise RuntimeError(f"не удалось подтвердить привязку orderId {oid} к L{slot} в SQLite; ордер не изменён")
                            if abs(current_qty - desired_qty) <= max(qty_step / 2.0, 1e-12):
                                skipped += 1
                                continue

                            # Кнопка «Выкл» синхронизируется только с одним amend,
                            # а не ждёт окончания сканирования всех символов. Перед
                            # КАЖДЫМ REST-запросом проверяем настройку под тем же lock:
                            # после подтверждения выключения новый amend не стартует.
                            with self._manual_limit_amend_lock:
                                disable_event = getattr(self, "_manual_limit_disable_requested", None)
                                target_update_event = getattr(self, "_manual_limit_target_update_requested", None)
                                if (not bool(get_setting("manual_limit_value_changes_enabled", True)) or
                                        (disable_event is not None and disable_event.is_set())):
                                    skipped += 1
                                    errors.append(f"{sym} L{slot} ({oid}): автоизменение выключено/отключается; ордер не изменён")
                                    continue
                                if target_update_event is not None and target_update_event.is_set():
                                    skipped += 1
                                    errors.append(f"{sym} L{slot} ({oid}): изменение номинала ожидает сохранения; старое значение не применено")
                                    continue
                                # Настройка номинала могла измениться, пока этот
                                # фоновый проход готовил остальные символы. Не
                                # применяем старый снимок настройки: обновлённый
                                # проход использует уже сохранённое значение.
                                try:
                                    current_target_value = float(get_setting(
                                        f"manual_limit{slot}_value_usdt", target_values[slot]
                                    ))
                                except (TypeError, ValueError, OverflowError):
                                    current_target_value = float("nan")
                                if (not math.isfinite(current_target_value) or current_target_value <= 0 or
                                        abs(current_target_value - target_values[slot]) > max(1e-9, abs(target_values[slot]) * 1e-9)):
                                    skipped += 1
                                    errors.append(
                                        f"{sym} L{slot} ({oid}): значение номинала изменилось во время прохода; "
                                        "старое значение не применено, повторный проход использует актуальную настройку"
                                    )
                                    continue
                                amend_ok = self.client.amend_manual_entry_limit(sym, oid, desired_qty)
                            if amend_ok is not True:
                                raise RuntimeError(f"биржевой метод не подтвердил изменение qty для {oid}; перепроверь ордер")
                            changed += 1  # биржа уже подтвердила новое количество
                            if not save_manual_limit_slot(
                                sym, slot, oid, str(order.get("side") or row.get("side") or "Buy"),
                                price, desired_qty, target_values[slot], status="active",
                                position_idx=order.get("positionIdx", row.get("position_idx")),
                            ):
                                raise RuntimeError(
                                    f"биржа подтвердила qty={desired_qty:g}, но SQLite не подтвердила сохранение; "
                                    "следующий цикл должен сверить количество с биржей"
                                )
                            margin_estimate = (actual_notional / max_leverage) if max_leverage and max_leverage > 0 else None
                            record_state_event("manual_limit", "VALUE_CHANGED", sym, {
                                "slot": slot, "order_id": oid, "side": order.get("side"),
                                "position_idx": order.get("positionIdx", row.get("position_idx")), "price": price,
                                "old_qty": current_qty, "new_qty": desired_qty,
                                "target_notional_usdt": target_values[slot],
                                "actual_notional_usdt": actual_notional,
                                "max_leverage": max_leverage,
                                "estimated_margin_usdt": margin_estimate,
                            })
                            lev_text = f", max плечо {max_leverage:g}x, маржа ≈ {margin_estimate:.4g} USDT" if margin_estimate is not None else ""
                            self.log.info(
                                f"[{sym}] Ручная лимитка L{slot} закреплена за {oid}: qty {current_qty:g} -> {desired_qty:g}, "
                                f"цена {price:g}, номинал {actual_notional:g} USDT (цель {target_values[slot]:g} USDT){lev_text}"
                            )
                        except Exception as e:
                            failed += 1
                            errors.append(f"{sym} L{slot} ({oid}): {e}")
                            self.log.warning(f"[{sym}] Не удалось изменить закреплённую L{slot} ({oid}): {e}")

            except Exception as e:
                failed += 1
                errors.append(str(e))
                self.log.exception("Не удалось применить стоимость двух закреплённых ручных лимиток")
            return changed, skipped, failed, errors

    def apply_manual_settings_to_open_positions(self, reason: str = "", force_stop_from_l2: bool = False) -> Tuple[int, int]:
        """Немедленно применяет сохранённые ручные настройки ко всем открытым
        ручным позициям. Если позиция появилась совсем недавно и ещё не попала
        в реестр, один раз запускаем обычное обнаружение ручных позиций — так
        кнопка не зависит от 30-секундного интервала фонового сканера."""
        updated = 0
        failed = 0
        try:
            positions = self.client.get_all_open_positions()
            tracked = get_all_open_signal_positions()
            untracked = {p.get("symbol") for p in (positions or []) if p.get("symbol") and p.get("symbol") not in tracked}
            if untracked:
                self.scan_manual_positions()
                tracked = get_all_open_signal_positions()
            for live_pos in positions or []:
                symbol = live_pos.get("symbol")
                sp = tracked.get(symbol)
                if not symbol or not sp or sp.get("source") != "manual":
                    continue
                live_side_raw = str(live_pos.get("side") or "")
                live_side = "LONG" if live_side_raw == "Buy" else "SHORT" if live_side_raw == "Sell" else None
                saved_side = str(sp.get("side") or "").upper()
                if live_side is None or saved_side != live_side:
                    # Fail closed in hedge mode: never apply this symbol-keyed
                    # row's L2/SL to the opposite exchange position leg.
                    failed += 1
                    self.log.error(
                        f"[{symbol}] Не применяю ручной стоп: сторона live-позиции {live_side_raw!r} "
                        f"не совпадает с сохранённой стороной SQLite {saved_side!r}. "
                        "Проверь hedge-mode/дубли одной монеты."
                    )
                    continue
                try:
                    manual_tp1_done = bool(sp.get("breakeven_done")) or bool((sp.get("manual_tp_done") or {}).get("1"))
                    result = self._recalculate_manual_position_protection(
                        symbol, live_pos, reason=reason,
                        use_open_order_anchor=not manual_tp1_done,
                        preserve_existing_stop=manual_tp1_done,
                        force_stop_from_l2=bool(force_stop_from_l2 and not manual_tp1_done),
                    )
                    # Успешно только если стоп принят ИЛИ partial TP уже был
                    # исполнен раньше, либо новый TP действительно установлен.
                    tp_ok = bool(result.get("tp2_done") or result.get("tp_order_ok"))
                    if result.get("stop_ok") and tp_ok:
                        updated += 1
                    else:
                        failed += 1
                except Exception:
                    failed += 1
                    self.log.exception(f"[{symbol}] Не удалось применить новые настройки ручной позиции")
        except Exception:
            failed += 1
            self.log.exception("Не удалось применить настройки ко всем открытым ручным позициям")
        return updated, failed

    def manual_positions_scan_loop(self):
        while True:
            started = time.time()
            # Обнаружение исполнившейся лимитки (позиции без сопровождения) важнее
            # изменения размера лимиток, поэтому идёт ПЕРВЫМ. Шаги изолированы: сбой
            # или долгая работа одного не должны откладывать/отключать другой (раньше
            # исключение или медленные REST-вызовы синхронизации размеров пропускали
            # сканирование, и позиция оставалась без стопа до следующего цикла).
            try:
                self.scan_manual_positions()
            except Exception:
                self.log.exception("Ошибка в цикле сканирования ручных позиций")
            try:
                self.apply_manual_limit_values_to_open_orders(reason="фоновая синхронизация стоимости лимиток")
            except Exception:
                self.log.exception("Ошибка фоновой синхронизации стоимости лимиток")
            try:
                interval = float(getattr(cfg, "MANUAL_TRADE_SCAN_INTERVAL_SECONDS", 15))
            except (TypeError, ValueError):
                interval = 15.0
            if not math.isfinite(interval) or interval <= 0:
                interval = 15.0
            # Период считается от начала прохода: длительная работа не растягивает
            # паузу между сканированиями (раньше пауза добавлялась к времени работы).
            time.sleep(max(1.0, interval - (time.time() - started)))

    def reconcile_signal_positions_from_exchange(self):
        """Восстанавливает отслеживание сделок, открытых ботом по постам,
        если локальная база потерялась (например, после редеплоя на Railway
        без постоянного диска — контейнер пересоздаётся с нуля вместе с
        файлом trades.db). Ищет на бирже ордера с меткой 'sg1-' (её бот сам
        проставляет на все входы по постам, см. _new_order_link_id) и по ним
        восстанавливает символ/направление/входы/стоп; если на бирже уже
        стоят тейки — восстанавливает и их цены. Вызывается один раз при
        старте, до включения фонового мониторинга.

        ЧЕСТНОЕ ОГРАНИЧЕНИЕ: полный список целей из поста восстановить
        невозможно, если тейки на момент потери базы ещё не были выставлены
        на бирже — этих цен просто нет ни в одном ответе API. В этом случае
        бот всё равно восстановит слежение за позицией (стоп, статус), но
        предупредит, что цели и тейки нужно проверить/выставить вручную."""
        try:
            already_tracked = set(get_all_open_signal_positions().keys())

            # Однократно на старте очищаем оставшиеся sg2-ордера старой версии
            # независимо от наличия локальной записи signal_positions. Префикс
            # sg2- принадлежал старому коду бота, поэтому такие ордера безопасно
            # считать legacy-ордерами бота, а не пользовательскими TP.
            try:
                self._cancel_legacy_signal_tp_orders("*")
            except Exception:
                self.log.exception("Не удалось выполнить стартовую очистку legacy sg2-ордеров")

            tagged = [o for o in self.client.get_open_orders_all() if str(o.get("orderLinkId", "")).startswith("sg1-")]
            tagged += [o for o in self.client.get_recent_order_history_all(days=14) if str(o.get("orderLinkId", "")).startswith("sg1-")]

            by_symbol: Dict[str, Dict] = {}
            for o in tagged:
                symbol = o.get("symbol")
                if not symbol:
                    continue
                order_side = str(o.get("side") or "").strip()
                if order_side not in {"Buy", "Sell"}:
                    self.log.warning(
                        "[%s] Пропускаю tagged-ордер с неизвестной стороной при восстановлении БД: %s",
                        symbol, o.get("orderId"),
                    )
                    continue
                slot = by_symbol.setdefault(symbol, {
                    "entries": set(), "entry_orders": {}, "side": None,
                    "sides": set(), "stop": None, "order_ids": set(),
                })
                slot["sides"].add(order_side)
                try:
                    price = float(o.get("price") or 0)
                    if price > 0:
                        slot["entries"].add(price)
                        if o.get("orderId"):
                            # Preserve the price ↔ orderId relationship. Sets
                            # lose this pairing and can make TP1 cancel the wrong
                            # leftover entry after a database-loss recovery.
                            slot["entry_orders"][str(o["orderId"])] = price
                except (TypeError, ValueError, OverflowError):
                    pass
                slot["side"] = "LONG" if order_side == "Buy" else "SHORT"
                sl = o.get("stopLoss")
                if sl not in (None, "", "0"):
                    try:
                        slot["stop"] = float(sl)
                    except (TypeError, ValueError, OverflowError):
                        pass
                if o.get("orderId"):
                    slot["order_ids"].add(str(o["orderId"]))

            restored = 0
            excluded = set(get_excluded_symbols())
            for symbol, info in by_symbol.items():
                if symbol in already_tracked or not info["side"] or not info["entries"] or symbol in excluded:
                    continue
                # The database has one signal tracker per symbol. Historical
                # sg1 orders may contain both directions; never merge their
                # prices/IDs or let iteration order decide which side to restore.
                if len(info.get("sides") or set()) != 1:
                    self.log.error(
                        "[%s] В tagged-истории обнаружены входы в разных направлениях; "
                        "автовосстановление пропущено во избежание неверного TP/SL и отмены чужого входа.",
                        symbol,
                    )
                    try:
                        self.tg.notify(
                            f"🚨 <b>{symbol}</b>: в истории входных ордеров обнаружены LONG и SHORT. "
                            "Автовосстановление остановлено для этой монеты; проверь позиции и ордера на Bybit."
                        )
                    except Exception:
                        self.log.exception("[%s] Не удалось отправить уведомление о конфликте направлений", symbol)
                    continue

                expected_pos_side = "Buy" if info["side"] == "LONG" else "Sell"
                # During DB-loss recovery, an API error must not be interpreted
                # as "no position": doing so could skip recovery of a live trade.
                try:
                    pos = self.client.get_position_strict(symbol, side=expected_pos_side)
                except Exception as e:
                    self.log.error(
                        "[%s] Не удалось достоверно проверить позицию при восстановлении БД; "
                        "символ пропущен без удаления/перезаписи состояния: %s",
                        symbol, e,
                    )
                    try:
                        self.tg.notify(
                            f"🚨 <b>{symbol}</b>: не удалось проверить позицию на Bybit при восстановлении состояния. "
                            "Автовосстановление отложено; проверь позицию и TP/SL на бирже."
                        )
                    except Exception:
                        self.log.exception("[%s] Не удалось отправить уведомление о сбое восстановления", symbol)
                    continue
                live_qty = float(pos.get("size") or 0) if pos else 0.0

                open_ids = self.client.get_open_order_ids(symbol)
                if open_ids is None:
                    self.log.error(
                        "[%s] Не удалось проверить список открытых ордеров при восстановлении БД; "
                        "символ пропущен, так как нельзя подтвердить отсутствие входов.",
                        symbol,
                    )
                    try:
                        self.tg.notify(
                            f"🚨 <b>{symbol}</b>: не удалось проверить открытые ордера на Bybit при восстановлении. "
                            "Автовосстановление отложено; проверь входные ордера и защиту вручную."
                        )
                    except Exception:
                        self.log.exception("[%s] Не удалось отправить уведомление о сбое проверки ордеров", symbol)
                    continue
                has_open_entries = bool(info["order_ids"] & open_ids)

                if live_qty <= 0 and not has_open_entries:
                    continue  # ни позиции, ни висящих лимиток этого символа сейчас нет — восстанавливать нечего

                avg_entry = float(pos.get("avgPrice") or 0) if pos and live_qty > 0 else 0.0
                if avg_entry <= 0:
                    avg_entry = sum(info["entries"]) / len(info["entries"])

                stop_price = float(pos.get("stopLoss") or 0) if pos else 0.0
                if stop_price <= 0:
                    stop_price = info["stop"] or avg_entry  # лучше стоп на цене входа, чем не иметь стопа вообще

                # Do not treat every conditional trigger as a TP: StopLoss and
                # conditional-entry orders also have triggerPrice. Only explicit
                # TakeProfit/PartialTakeProfit orders (or a dedicated takeProfit
                # field) are eligible for target recovery.
                try:
                    conditional_orders = self.client.get_symbol_conditional_orders_strict(symbol)
                except Exception as e:
                    self.log.error(
                        "[%s] Не удалось проверить существующие условные TP/SL при восстановлении; "
                        "новые защитные ордера не создаются до успешной сверки: %s",
                        symbol, e,
                    )
                    try:
                        self.tg.notify(
                            f"🚨 <b>{symbol}</b>: не удалось проверить условные TP/SL на Bybit. "
                            "Автовосстановление отложено, чтобы не создать конфликтующие ордера."
                        )
                    except Exception:
                        self.log.exception("[%s] Не удалось отправить уведомление о сбое проверки TP/SL", symbol)
                    continue
                targets = _recovery_take_profit_prices(
                    conditional_orders, info["side"], avg_entry
                )

                entries_sorted, entry_order_ids_sorted = _sort_recovered_entry_orders(
                    info.get("entry_orders") or {}, info["side"]
                )
                if not entries_sorted:
                    # Legacy API responses without usable prices are not expected,
                    # but retain safe recovery metadata without mismatched pairs.
                    entries_sorted = sorted(info["entries"], reverse=(info["side"] == "LONG"))
                    entry_order_ids_sorted = []

                # Если ни целей, ни стопа с биржи восстановить не удалось —
                # НЕ оставляем сделку без защиты и без тейка: считаем те же
                # значения по умолчанию, что и для постов-зон (см. config.py
                # SIGNAL_ZONE_TP_PERCENT / SIGNAL_ZONE_AUTO_STOP_PERCENT) от
                # средней цены входа, и сразу применяем их на бирже — а не
                # просто предупреждаем "настрой вручную".
                used_defaults = False
                if not targets:
                    zone_tp_pct = getattr(cfg, "SIGNAL_ZONE_TP_PERCENT", 3) / 100.0
                    synthetic_tp = avg_entry * (1 + zone_tp_pct) if info["side"] == "LONG" else avg_entry * (1 - zone_tp_pct)
                    targets = [synthetic_tp]
                    used_defaults = True
                if stop_price == avg_entry:  # т.е. реального стопа на бирже/во входах не нашли, используем avg_entry как временную заглушку выше
                    zone_stop_pct = getattr(cfg, "SIGNAL_ZONE_AUTO_STOP_PERCENT", 7) / 100.0
                    stop_price = avg_entry * (1 - zone_stop_pct) if info["side"] == "LONG" else avg_entry * (1 + zone_stop_pct)
                    used_defaults = True
                    if live_qty > 0:
                        self.client.update_stop_loss_verified(symbol, stop_price, info["side"])

                create_signal_position({
                    "symbol": symbol,
                    "side": info["side"],
                    "entries": entries_sorted,
                    "targets": targets,
                    "stop_price": stop_price,
                    "avg_entry_price": avg_entry,
                    "qty_total": live_qty,
                    "entry_order_ids": entry_order_ids_sorted,
                    "breakeven_after_tp1": True,
                })
                restored_sp = get_signal_position(symbol) or {}
                # После восстановления сразу переводим позицию на единую
                # систему TP1-TP4. Старые sg2 не анализируем как текущий TP:
                # если такой ордер ещё висит, монитор миграции снимет его.
                if live_qty > 0:
                    update_signal_position_opened(symbol, live_qty)
                    restored_sp = get_signal_position(symbol) or restored_sp
                    try:
                        result = self._recalculate_manual_position_protection(
                            symbol, pos,
                            reason="восстановление сигнальной позиции после рестарта",
                            use_open_order_anchor=False,
                            preserve_existing_stop=True,
                            order_prefix="stp",
                        )
                        tp_state = "TP1-TP4 подтверждены" if result.get("tp4_ok") and result.get("tp_partial_ok") else "TP1-TP4 будут повторно проверены монитором"
                    except Exception as e:
                        tp_state = f"TP1-TP4 не удалось подтвердить сразу: {e}"
                else:
                    tp_state = "позиция ещё не набрана; TP установятся после первого исполнения входа"

                restored += 1
                # Не добавляем неподтверждённую переменную в уведомление: в этой
                # ветке восстановление уже рассчитано выше, а already_done_note
                # нигде не формируется. Ранее это могло вызвать NameError и
                # прервать восстановление остальных сигнальных позиций.
                note = f"♻️ <b>{symbol}</b>: восстановил слежение за сделкой по посту после рестарта (по данным биржи). Перевёл её на единую систему TP1–TP4. {tp_state}."
                if used_defaults:
                    note += f" ⚠️ Цели/стоп из поста восстановить не удалось — использовал дефолт ({getattr(cfg, 'SIGNAL_ZONE_TP_PERCENT', 3)}% тейк / {getattr(cfg, 'SIGNAL_ZONE_AUTO_STOP_PERCENT', 7)}% стоп от цены входа), проверь и поправь при необходимости."
                self.tg.notify(note)

            if restored:
                self.log.info(f"Восстановлено {restored} сигнальных позиций с биржи после рестарта")
        except Exception as e:
            self.log.exception("Ошибка восстановления сигнальных позиций с биржи; автоматическое восстановление остановлено")
            try:
                self.tg.notify(
                    "🚨 <b>Не удалось восстановить сигнальные позиции после запуска.</b> "
                    "Автоматическое восстановление остановлено, чтобы не менять ордера вслепую. "
                    "Проверь на Bybit открытые позиции, входные лимитки и TP/SL. "
                    f"Причина: {str(e)[:300]}"
                )
            except Exception:
                self.log.exception("Не удалось отправить критическое уведомление об ошибке восстановления")

    def signal_positions_monitor_loop(self):
        while True:
            try:
                tracked_positions = get_all_open_signal_positions()
                # One fresh snapshot per monitor pass avoids a REST call for
                # every manual position. If it fails, pass an explicit unknown
                # snapshot so SL/TP reconciliation does not mistake API failure
                # for an empty order list.
                has_manual = any((sp.get("source") or "post") == "manual" for sp in tracked_positions.values())
                snapshot_loaded = False
                open_orders_snapshot = None
                if has_manual:
                    snapshot_loaded = True
                    try:
                        open_orders_snapshot = self.client.get_open_orders_all()
                    except Exception:
                        open_orders_snapshot = None
                        self.log.exception("Не удалось получить общий снимок открытых ордеров для ручного SL/TP")
                for symbol, sp in tracked_positions.items():
                    try:
                        self._check_signal_position(
                            symbol, sp, open_orders_snapshot=open_orders_snapshot,
                            open_orders_snapshot_loaded=snapshot_loaded,
                        )
                    except Exception:
                        self.log.exception(f"Ошибка мониторинга сигнальной позиции {symbol}")
            except Exception:
                self.log.exception("Ошибка в цикле мониторинга сигнальных позиций")
            time.sleep(10)

    # ------------------------------------------------------------------
    # Мониторинг постов трейдера в ленте OKX
    # ------------------------------------------------------------------

    def okx_feed_monitor_loop(self):
        while True:
            try:
                if get_setting("okx_feed_enabled", cfg.OKX_FEED_ENABLED_DEFAULT):
                    self._check_okx_feed()
            except Exception:
                self.log.exception("Ошибка в цикле мониторинга постов OKX")
            time.sleep(cfg.OKX_FEED_POLL_SECONDS)

    def _check_okx_feed(self):
        posts = _fetch_okx_feed_posts()
        new_posts = [p for p in posts if not is_okx_post_seen(p["id"])]
        if not new_posts:
            return
        # Первый прогон после включения функции: не заваливаем чат всей
        # историей ленты разом — просто запоминаем текущие посты как уже
        # виденные и молча ждём следующих, реально новых.
        if len(new_posts) == len(posts) and not get_setting("okx_feed_primed", False):
            for p in posts:
                mark_okx_post_seen(p["id"])
            set_setting("okx_feed_primed", True)
            return
        for p in new_posts:
            try:
                self._send_okx_post(p)
            except Exception:
                self.log.exception(f"Не удалось переслать пост OKX {p['id']}")
            mark_okx_post_seen(p["id"])

    def _send_okx_post(self, post: Dict):
        translated = _translate_to_russian(post["text"])
        caption = f"📢 <b>Новый пост трейдера OKX</b>\n━━━━━━━━━━━━━━━\n{translated}\n\n🔗 {cfg.OKX_FEED_URL}"
        images = post.get("images") or []

        if not images:
            # Telegram режет подписи к текстовым сообщениям на 4096 символов
            for chunk_start in range(0, len(caption), 4000):
                self.tg.bot.send_message(self.tg.chat_id, caption[chunk_start:chunk_start + 4000])
            return

        if len(images) == 1:
            # send_media_group у Telegram требует 2-10 элементов — с одним
            # фото это упадёт с ошибкой, поэтому шлём обычным send_photo
            if len(caption) <= 1024:
                self.tg.bot.send_photo(self.tg.chat_id, images[0], caption=caption)
            else:
                self.tg.bot.send_photo(self.tg.chat_id, images[0])
                for chunk_start in range(0, len(caption), 4000):
                    self.tg.bot.send_message(self.tg.chat_id, caption[chunk_start:chunk_start + 4000])
            return

        if len(caption) <= 1024:
            # подпись влезает в лимит альбома (1024 символа) — прикрепляем
            # прямо к первому фото, отдельным сообщением текст не дублируем
            media = [types.InputMediaPhoto(images[0], caption=caption)]
            media += [types.InputMediaPhoto(u) for u in images[1:10]]
            self.tg.bot.send_media_group(self.tg.chat_id, media)
        else:
            # подпись не влезает — шлём фото без подписи, текст отдельно
            # ОДИН раз целиком (не обрезанным дублем под фото + полным текстом)
            media = [types.InputMediaPhoto(u) for u in images[:10]]
            self.tg.bot.send_media_group(self.tg.chat_id, media)
            for chunk_start in range(0, len(caption), 4000):
                self.tg.bot.send_message(self.tg.chat_id, caption[chunk_start:chunk_start + 4000])

    def _check_signal_position(
        self, symbol: str, sp: Dict,
        open_orders_snapshot: Optional[List[Dict]] = None,
        open_orders_snapshot_loaded: bool = False,
    ):
        if sp.get("source") == "manual":
            with self._manual_protection_lock:
                return self._check_signal_position_unlocked(
                    symbol, sp, open_orders_snapshot=open_orders_snapshot,
                    open_orders_snapshot_loaded=open_orders_snapshot_loaded,
                )
        return self._check_signal_position_unlocked(
            symbol, sp, open_orders_snapshot=open_orders_snapshot,
            open_orders_snapshot_loaded=open_orders_snapshot_loaded,
        )

    def _check_signal_position_unlocked(
        self, symbol: str, sp: Dict,
        open_orders_snapshot: Optional[List[Dict]] = None,
        open_orders_snapshot_loaded: bool = False,
    ):
        """Единое управление сигнальной/ручной позицией через TP1-TP4.

        Для source=post используются stp1-/stp2-/stp3- и Full TP4.
        Старые sg2-ордера только мигрируются/отменяются и больше никогда не
        создаются. Входная логика поста остаётся прежней: после исполнения
        первого входа второй выбранный вход может исполниться позже; средняя
        цена пересчитывает TP1-TP4, а существующий SL сохраняется. После TP1
        оставшийся вход отменяется и SL переносится на ±0.5% от фактического
        среднего входа.
        """
        if symbol in get_excluded_symbols():
            return
        expected_pos_side = "Buy" if sp["side"] == "LONG" else "Sell"
        try:
            pos = self.client.get_position_strict(symbol, side=expected_pos_side)
        except Exception:
            self.log.warning(f"[{symbol}] Не удалось проверить сигнальную позицию — пропускаю цикл")
            return

        live_qty = float(pos.get("size") or 0) if pos else 0.0
        source = sp.get("source") or "post"
        is_manual = source == "manual"
        tp_prefix = "mtp" if is_manual else "stp"

        # Старые sg2-ордера от предыдущих версий не являются частью стратегии.
        # Если они остались на бирже после обновления, снимаем их перед
        # постановкой новых stp1-/stp2-/stp3-ордеров.
        if not is_manual:
            self._cancel_legacy_signal_tp_orders(symbol)

        # Позиция закрыта: снимаем только наши входы и TP-ордера, затем удаляем
        # локальное отслеживание. Ошибка запроса позиции выше не попадает сюда.
        if live_qty <= 0:
            executed_and_closed = False
            # Pending limit entries are not a closed position. Keep their DB
            # state while any tracked entry is open, filled, partially filled,
            # or its exchange status cannot be verified. Otherwise the first
            # monitor tick after posting would cancel entries before they fill.
            if str(sp.get("status") or "").lower() == "pending":
                tracked_ids = list(sp.get("entry_order_ids") or [])
                try:
                    open_ids = self.client.get_open_order_ids(symbol)
                except Exception as e:
                    self.log.warning(f"[{symbol}] Не удалось проверить pending-входы; состояние сохранено: {e}")
                    return
                order_states = []
                for order_id in tracked_ids:
                    try:
                        state = self.client.get_order_state(symbol, str(order_id))
                    except Exception as e:
                        self.log.warning(f"[{symbol}] Не удалось проверить статус входа {order_id}; состояние сохранено: {e}")
                        return
                    if not state:
                        return
                    order_states.append(state)
                if _pending_signal_has_live_or_uncertain_entries(tracked_ids, open_ids, order_states):
                    # Исполненные входы без позиции — это либо лаг выдачи биржи (секунды),
                    # либо позиция уже успела закрыться стопом/тейком между проверками.
                    # Во втором случае запись навсегда оставалась «pending».
                    if not self._pending_entries_executed_and_closed(symbol, tracked_ids, open_ids, order_states):
                        return
                    executed_and_closed = True
            if self._cleanup_closed_signal_position(symbol, sp, expected_pos_side):
                if executed_and_closed:
                    self.tg.notify(f"🔵 <b>{symbol}</b>: вход исполнился, но позиция уже закрыта (сработал стоп/тейк между проверками). Слежение завершено.")
                else:
                    self.tg.notify(f"🔵 <b>{symbol}</b>: сигнальная позиция полностью закрыта.")
            return

        # Пока все входы не исполнились, не считаем позицию открытой. Как только
        # появился реальный объём — сразу создаём единый TP1-TP4 план.
        was_pending = sp.get("status") == "pending"
        if was_pending:
            self.__dict__.setdefault("_pending_closed_checks", {}).pop(symbol, None)
            update_signal_position_opened(symbol, live_qty)
            self.tg.notify(f"🟢 <b>{symbol}</b>: сигнальная позиция открыта, объём {live_qty:g}.")
            sp = get_signal_position(symbol) or sp

        stored_avg = float(sp.get("avg_entry_price") or 0)
        stored_qty = float(sp.get("last_known_qty") or sp.get("opened_qty") or 0)
        current_avg = float(pos.get("avgPrice") or 0)
        avg_changed = stored_avg > 0 and current_avg > 0 and abs(current_avg - stored_avg) > max(1e-12, stored_avg * 1e-8)
        qty_increased = stored_qty > 0 and live_qty > stored_qty * 1.001

        # На каждом цикле управления ручной позицией синхронизируем цену
        # ИМЕННО закреплённой L2. Монитор выполняется чаще 30-секундного сканера,
        # поэтому без этой сверки быстро изменённая цена L2 могла быть уже
        # исполнена, а стоп временно пересчитывался бы от старой цены SQLite.
        l2_refresh_uncertain = False
        if is_manual and not bool(sp.get("breakeven_done")) and not bool((sp.get("manual_tp_done") or {}).get("1")):
            try:
                filled_raw = (sp.get("manual_tp_filled_qty") or {}).get("1", 0)
                filled_tp1 = float(filled_raw or 0)
                tp1_already_recorded = math.isfinite(filled_tp1) and filled_tp1 > 0
            except (TypeError, ValueError, OverflowError):
                tp1_already_recorded = True  # invalid TP1 state: preserve stop, don't guess L2
            if not tp1_already_recorded:
                pinned_ids = [str(x) for x in (sp.get("entry_order_ids") or []) if x]
                if len(pinned_ids) != 2:
                    l2_refresh_uncertain = True
                    self.log.error(f"[{symbol}] Невозможно обновить якорь SL: нет полной закреплённой пары L1/L2")
                else:
                    try:
                        live_side_confirmed = str(pos.get("side") or "")
                        if live_side_confirmed != expected_pos_side:
                            raise RuntimeError(
                                f"сторона live-позиции {live_side_confirmed!r} не совпадает с {expected_pos_side!r}"
                            )
                        raw_live_idx = pos.get("positionIdx")
                        if raw_live_idx is None or str(raw_live_idx).strip() == "":
                            raise RuntimeError("Bybit не вернул positionIdx live-позиции")
                        live_idx_confirmed = int(raw_live_idx)
                        if (live_idx_confirmed not in (0, 1, 2)
                                or (live_idx_confirmed == 1 and expected_pos_side != "Buy")
                                or (live_idx_confirmed == 2 and expected_pos_side != "Sell")):
                            raise RuntimeError(
                                f"конфликт positionIdx={live_idx_confirmed} и стороны {expected_pos_side}"
                            )
                        if open_orders_snapshot_loaded:
                            fresh_open_orders = open_orders_snapshot
                        else:
                            fresh_open_orders = self.client.get_open_orders_all()
                            if fresh_open_orders is not None:
                                # Reuse this successful response for TP recovery
                                # later in the same monitor pass; avoid a second
                                # identical REST call per position.
                                open_orders_snapshot = fresh_open_orders
                                open_orders_snapshot_loaded = True
                        if fresh_open_orders is None:
                            raise RuntimeError("снимок открытых ордеров недоступен")
                        # A second entry has just executed when avg/size changed.
                        # The shared monitor snapshot may have been taken a few
                        # milliseconds before that fill; omit pinned L2 so the
                        # selector checks its exact orderId in exchange history.
                        if avg_changed or qty_increased:
                            fresh_open_orders = [
                                o for o in fresh_open_orders
                                if str(o.get("orderId") or "") != pinned_ids[1]
                            ]
                        fresh_prices, fresh_ids, fresh_source = self._select_manual_entry_orders(
                            symbol, sp["side"], pos, fresh_open_orders, allow_history_recovery=True
                        )
                        if (fresh_source == "history_unavailable_retry" or len(fresh_ids) != 2
                                or [str(x) for x in fresh_ids] != pinned_ids or len(fresh_prices) != 2):
                            raise RuntimeError(
                                f"закреплённая пара не подтверждена: source={fresh_source}, ids={fresh_ids}"
                            )
                        fresh_prices = [float(x) for x in fresh_prices]
                        if any(not math.isfinite(x) or x <= 0 for x in fresh_prices):
                            raise RuntimeError(f"L1/L2 имеют некорректные цены: {fresh_prices!r}")
                        stored_prices = [float(x) for x in (sp.get("entries") or [])]
                        prices_changed = (len(stored_prices) != 2 or any(
                            abs(a - b) > max(abs(a) * 1e-12, 1e-12)
                            for a, b in zip(fresh_prices, stored_prices)
                        ))
                        if prices_changed:
                            if not update_manual_entry_pair(
                                symbol, fresh_prices, pinned_ids,
                                expected_order_ids=pinned_ids,
                                expected_entries=stored_prices if len(stored_prices) == 2 else None,
                            ):
                                raise RuntimeError("пара L1/L2 уже изменена другим циклом либо не удалось сохранить актуальные цены")
                            sp = get_signal_position(symbol) or sp
                            self.log.info(
                                f"[{symbol}] Перед пересчётом защиты синхронизирована цена закреплённой L2: "
                                f"{stored_prices[1] if len(stored_prices) > 1 else 'нет'} -> {fresh_prices[1]}"
                            )
                    except Exception as l2_sync_error:
                        l2_refresh_uncertain = True
                        self.log.warning(
                            f"[{symbol}] Не удалось подтвердить текущую цену закреплённой L2 перед пересчётом SL; "
                            f"буду сохранять существующий стоп: {l2_sync_error}"
                        )

        # Для post сохраняем исходный стоп из сигнала/биржи. Для manual действует
        # прежняя логика ручного стопа. use_open_order_anchor оставляем только
        # для manual; у post стоп всегда уже задан самим сигналом.
        preserve_stop = True if not is_manual else (bool(sp.get("breakeven_done")) or l2_refresh_uncertain)
        result = self._recalculate_manual_position_protection(
            symbol, pos,
            reason=("пересчёт TP1-TP4 после дополнительного входа" if (avg_changed or qty_increased) else "плановая проверка TP1-TP4"),
            use_open_order_anchor=(is_manual and not bool(sp.get("breakeven_done"))),
            preserve_existing_stop=preserve_stop,
            order_prefix=tp_prefix,
            open_orders_snapshot=open_orders_snapshot,
            open_orders_snapshot_loaded=open_orders_snapshot_loaded,
        )
        sp = get_signal_position(symbol) or sp

        if not result.get("stop_ok"):
            self.tg.notify(f"⚠️ <b>{symbol}</b>: SL не подтверждён — повторю установку вместе с TP1-TP4.")
        elif not result.get("tp4_ok") or not result.get("tp_partial_ok"):
            self.tg.notify(f"⚠️ <b>{symbol}</b>: TP1-TP4 не подтверждены полностью — повторю установку.")
        elif avg_changed or qty_increased:
            self.tg.notify(
                f"🔄 <b>{symbol}</b>: дополнительный вход исполнен. "
                f"Новый средний вход ≈{fmt_num(result['avg_entry'])}; TP1-TP4 пересчитаны, "
                f"стоп сохранён {fmt_num(result['stop'])}."
            )

        # _recalculate_manual_position_protection сам отслеживает фактическое
        # исполнение TP1 по cumExecQty и после TP1 переносит SL на ±0.5% и
        # снимает оставшийся отслеживаемый вход. Поэтому отдельный ценовой
        # триггер/market-close здесь больше НЕ нужен.
        live_qty_after = live_qty
        try:
            latest = self.client.get_position_strict(symbol, side=expected_pos_side)
            live_qty_after = float(latest.get("size") or 0) if latest else 0.0
        except Exception:
            pass
        if live_qty_after <= 0:
            self._cleanup_closed_signal_position(symbol, sp, expected_pos_side)
            return

        baseline_qty = float(sp.get("last_known_qty") or sp.get("opened_qty") or live_qty_after)
        if live_qty_after < baseline_qty * 0.999 and not result.get("tp1_done"):
            self.tg.notify(f"🎯 <b>{symbol}</b>: объём позиции уменьшился ({baseline_qty:g} → {live_qty_after:g}).")
        if abs(live_qty_after - baseline_qty) > 1e-12:
            update_signal_position_qty(symbol, live_qty_after)

    # Терминальные статусы: ордер больше не может исполниться (Filled тоже —
    # позиция при этом перепроверяется отдельно, см. _cleanup_closed_signal_position).
    _TERMINAL_ORDER_STATUSES = frozenset({
        "cancelled", "rejected", "deactivated", "filled", "partiallyfilledcanceled",
    })

    def _pending_entries_executed_and_closed(self, symbol: str, tracked_ids, open_ids, order_states) -> bool:
        """True, если все входы pending-записи завершены (ни один не активен), хотя
        бы один исполнялся, а позиции на бирже нет достаточно долго, чтобы это
        не было лагом выдачи. Срок отсчитывается от updatedTime ордера (если
        биржа его вернула), иначе по числу подряд идущих проверок."""
        ids = [str(x) for x in (tracked_ids or []) if x]
        if not ids or open_ids is None or order_states is None or len(order_states) != len(ids):
            return False
        if any(order_id in {str(x) for x in open_ids} for order_id in ids):
            return False
        terminal = {"cancelled", "rejected", "deactivated", "filled", "partiallyfilledcanceled"}
        executed = False
        latest_update_ms = 0.0
        for state in order_states:
            if not isinstance(state, dict):
                return False
            status = str(state.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
            if status not in terminal:
                return False
            try:
                if status == "filled" or float(state.get("cumExecQty") or 0) > 0:
                    executed = True
            except (TypeError, ValueError):
                return False
            try:
                latest_update_ms = max(latest_update_ms, float(state.get("updatedTime") or 0))
            except (TypeError, ValueError):
                pass
        counters = self.__dict__.setdefault("_pending_closed_checks", {})
        if not executed:
            counters.pop(symbol, None)
            return False
        try:
            grace_sec = float(getattr(cfg, "SIGNAL_PENDING_FILLED_GRACE_SECONDS", 60))
        except (TypeError, ValueError):
            grace_sec = 60.0
        if latest_update_ms > 0:
            return (time.time() * 1000.0 - latest_update_ms) >= grace_sec * 1000.0
        counters[symbol] = counters.get(symbol, 0) + 1
        return counters[symbol] >= 6

    def _cancel_order_confirmed(self, symbol: str, order_id) -> bool:
        """Снимает ордер и возвращает True только если биржа подтвердила, что
        он больше не активен.

        Ошибка cancel_order сама по себе ничего не доказывает: «ордер не
        найден/уже исполнен» приходит исключением, но так же выглядит и сетевой
        сбой. Поэтому итог определяется чтением статуса. Если статус не найден
        вообще и cancel вернул ошибку, ордера на бирже нет. Если статус
        прочитать не удалось (исключение) или он всё ещё активен — результат
        False, и вызывающий код обязан сохранить запись и повторить позже."""
        order_id = str(order_id)
        cancel_error = None
        try:
            self.session.cancel_order(category=cfg.CATEGORY, symbol=symbol, orderId=order_id)
        except Exception as e:
            cancel_error = e
        try:
            state = self.client.get_order_state(symbol, order_id)
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось проверить статус ордера {order_id} после отмены: {e}")
            return False
        if not state:
            # Ордер не найден ни среди активных, ни в истории; вместе с ошибкой
            # cancel («не существует») это означает, что снимать нечего.
            return cancel_error is not None
        status = str(state.get("orderStatus") or "").replace("_", "").replace(" ", "").lower()
        return status in self._TERMINAL_ORDER_STATUSES

    def _cancel_signal_entry_orders(self, symbol: str, sp: Dict) -> bool:
        """Снимает входные ордера позиции. True — все подтверждённо неактивны."""
        all_confirmed = True
        for order_id in sp.get("entry_order_ids") or []:
            if not order_id:
                continue
            if not self._cancel_order_confirmed(symbol, order_id):
                self.log.warning(f"[{symbol}] Входной ордер {order_id} не подтверждён как снятый; запись позиции сохранена.")
                all_confirmed = False
        return all_confirmed

    def _cleanup_closed_signal_position(self, symbol: str, sp: Dict, expected_pos_side: str) -> bool:
        """Снимает входы и TP закрытой позиции и удаляет запись из SQLite
        ТОЛЬКО после подтверждения. Иначе запись остаётся, и следующий цикл
        повторит очистку: удалённая запись при живом входном лимитнике дала бы
        позицию без сопровождения.

        Возвращает True, если запись удалена."""
        attempts_map = self.__dict__.setdefault("_signal_close_cleanup_attempts", {})
        entries_ok = self._cancel_signal_entry_orders(symbol, sp)
        tps_ok = self._cancel_signal_tp_orders(symbol, sp)
        if entries_ok and tps_ok:
            # Пока снимали ордера, входной лимитник мог исполниться и открыть
            # новую позицию — тогда запись нужна для её сопровождения.
            try:
                latest = self.client.get_position_strict(symbol, side=expected_pos_side)
                size = float(latest.get("size") or 0) if latest else 0.0
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось перепроверить позицию перед удалением записи: {e}")
                return False
            if size > 0:
                self.log.warning(f"[{symbol}] После снятия ордеров появился объём {size:g}; запись сохранена для сопровождения.")
                return False
            delete_signal_position(symbol)
            attempts_map.pop(symbol, None)
            self.__dict__.setdefault("_pending_closed_checks", {}).pop(symbol, None)
            return True

        attempts = attempts_map.get(symbol, 0) + 1
        attempts_map[symbol] = attempts
        self.log.warning(f"[{symbol}] Очистка закрытой позиции не подтверждена (попытка {attempts}); запись сохранена.")
        if attempts == 3 or attempts % 30 == 0:
            self.tg.notify(
                f"⚠️ <b>{symbol}</b>: позиция закрыта, но снятие её ордеров не подтверждено уже {attempts} циклов. "
                "Запись сохранена, бот повторяет попытки. Проверьте открытые ордера по символу вручную."
            )
        return False

    def _cancel_remaining_entry_orders_after_tp(self, symbol: str, sp: Dict) -> bool:
        """Отменяет ТОЛЬКО заранее сохранённые входные orderId этой позиции.

        Никогда не ищет и не отменяет все LIMIT по символу. Для ручной позиции
        здесь находятся максимум две ближайшие лимитки, сохранённые при
        обнаружении позиции. После TP обычно останется ровно одна — её и
        снимаем. Если Bybit временно недоступен или после cancel ордер всё ещё
        открыт, возвращаем False, чтобы следующий цикл повторил попытку.
        """
        order_ids = _entry_order_ids_to_cancel_after_tp(
            sp.get("entry_order_ids") or [], sp.get("source") or "post"
        )
        if not order_ids:
            # Для старых ручных позиций без известных orderId безопаснее ничего
            # не отменять. Для постовых позиций отсутствие входов означает, что
            # нечего отменять. Не ищем заявки по символу.
            return True

        try:
            open_ids = self.client.get_open_order_ids(symbol)
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось получить открытые ордера перед отменой входов: {e}")
            return False

        if open_ids is None:
            return False

        remaining = [oid for oid in order_ids if oid in open_ids]
        if not remaining:
            return True

        cancel_errors = False
        for order_id in remaining:
            try:
                self.session.cancel_order(
                    category=cfg.CATEGORY,
                    symbol=symbol,
                    orderId=order_id,
                )
                self.log.info(f"[{symbol}] После TP отменён только отслеживаемый вход {order_id}")
            except Exception as e:
                # Между GET и CANCEL ордер мог исполниться — это нормальная
                # гонка. Но подтверждаем состояние ниже, поэтому здесь не
                # считаем операцию завершённой автоматически.
                cancel_errors = True
                self.log.debug(f"[{symbol}] Не удалось отменить отслеживаемый вход {order_id}: {e}")

        # Обязательная верификация: если хотя бы один из известных orderId всё
        # ещё открыт, считаем отмену незавершённой. Никаких новых orderId не
        # ищем — это принципиальная защита от удаления лимиток №3/№4 и т.д.
        try:
            open_after = self.client.get_open_order_ids(symbol)
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось подтвердить отмену входов после TP: {e}")
            return False

        if open_after is None:
            return False

        still_open = [oid for oid in order_ids if oid in open_after]
        if still_open:
            self.log.warning(f"[{symbol}] После отмены ещё открыты отслеживаемые входы: {still_open}. Повторю в следующем цикле.")
            return False

        return not still_open

    def _cancel_signal_tp_orders(self, symbol: str, sp: Dict) -> bool:
        """Идемпотентно снимает только TP-ордера этой сигнальной/ручной позиции.
        Возвращает True, если все найденные ордера подтверждённо неактивны и
        список активных ордеров удалось получить целиком.

        Сначала используются сохранённые orderId, затем выполняется поиск по
        собственным orderLinkId-префиксам. Это важно после рестарта/сбоя записи:
        даже если SQLite успел потерять конкретный orderId, старый stp/mtp не
        должен остаться висеть на уже закрытой позиции. Чужие LIMIT-ордера по
        символу никогда не затрагиваются.
        """
        source = sp.get("source") or "post"
        prefixes = ("mtp1-", "mtp2-", "mtp3-") if source == "manual" else ("stp1-", "stp2-", "stp3-")
        order_ids = {str(oid) for oid in (sp.get("manual_tp_order_ids") or {}).values() if oid}
        try:
            active = self.client.get_open_orders_all()
        except Exception as e:
            self.log.warning(f"[{symbol}] Не удалось получить активные TP при закрытии позиции: {e}")
            active = None

        if active is not None:
            for o in active:
                if o.get("symbol") != symbol:
                    continue
                link = str(o.get("orderLinkId") or "")
                if any(link.startswith(p) for p in prefixes):
                    if o.get("orderId"):
                        order_ids.add(str(o["orderId"]))
                elif source != "manual" and link.startswith("sg2-"):
                    # Только legacy-TP сигнальных постов. Никогда не применяем
                    # этот fallback к ручным сделкам.
                    if o.get("orderId"):
                        order_ids.add(str(o["orderId"]))

        # Без полного списка активных ордеров нельзя доказать, что «забытых»
        # ордеров с нашим префиксом нет — результат считаем неподтверждённым.
        all_confirmed = active is not None
        expected_close_side = "Sell" if str(sp.get("side") or "").upper() == "LONG" else "Buy"
        allowed_prefixes = tuple(prefixes) + (("sg2-",) if source != "manual" else ())
        for order_id in order_ids:
            # A stale/corrupt DB mapping must not cancel an unrelated same-symbol
            # order. Confirm symbol, closing side, reduceOnly and our TP prefix
            # before sending cancel. If lookup is unavailable, retry later.
            try:
                state = self.client.get_order_state(symbol, str(order_id))
            except Exception as e:
                self.log.warning(f"[{symbol}] Не удалось подтвердить принадлежность TP-ордера {order_id}; отмену откладываю: {e}")
                all_confirmed = False
                continue
            if state:
                link = str(state.get("orderLinkId") or "")
                state_side = str(state.get("side") or "")
                reduce_only = state.get("reduceOnly")
                is_reduce_only = reduce_only is True or str(reduce_only).strip().lower() in {"true", "1"}
                if (str(state.get("symbol") or "") != str(symbol)
                        or state_side.lower() != expected_close_side.lower()
                        or not any(link.startswith(prefix) for prefix in allowed_prefixes)):
                    self.log.warning(f"[{symbol}] Сохранённый TP ID {order_id} не принадлежит тейкам этой позиции; не отменяю его.")
                    # This is definitively not one of our TP orders. It is safe
                    # to ignore this stale DB reference without touching it.
                    continue
                if not is_reduce_only:
                    self.log.warning(f"[{symbol}] Ордер {order_id} имеет наш TP-префикс, но reduceOnly не подтверждён; очистку откладываю во избежание риска.")
                    all_confirmed = False
                    continue
            else:
                # Missing status is not enough evidence to cancel blindly.
                self.log.warning(f"[{symbol}] TP-ордер {order_id} не найден при проверке принадлежности; повторю сверку позже.")
                all_confirmed = False
                continue
            if self._cancel_order_confirmed(symbol, order_id):
                self.log.info(f"[{symbol}] После закрытия позиции TP-ордер {order_id} снят/неактивен")
            else:
                self.log.warning(f"[{symbol}] TP-ордер {order_id} не подтверждён как снятый после закрытия позиции")
                all_confirmed = False
        return all_confirmed

    def _cancel_legacy_signal_tp_orders(self, symbol: str):
        """Удаляет старые sg2-частичные тейки. Новая система использует только stp1-/stp2-/stp3- + Full TP4."""
        try:
            orders = self.client.get_open_orders_all()
        except Exception as e:
            self.log.debug(f"[{symbol}] Не удалось проверить старые sg2-ордера: {e}")
            return
        for o in orders or []:
            order_symbol = str(o.get("symbol") or "")
            if not order_symbol or (symbol != "*" and order_symbol != symbol) or not str(o.get("orderLinkId") or "").startswith("sg2-"):
                continue
            oid = o.get("orderId")
            if not oid:
                continue
            try:
                # При symbol="*" чистим legacy-ордера по всем монетам, но
                # cancel_order всегда требует реальный символ конкретного ордера.
                self.client.session.cancel_order(category=cfg.CATEGORY, symbol=order_symbol, orderId=str(oid))
                self.log.info(f"[{order_symbol}] Отменён старый sg2-TP {oid}; используется новая система TP1-TP4")
            except Exception as e:
                self.log.warning(f"[{order_symbol}] Не удалось отменить старый sg2-TP {oid}: {e}")

    def daily_report_loop(self):
        if not cfg.TELEGRAM_CHAT_ID:
            return
        last_sent_date = get_meta("last_daily_report_date", "")
        while True:
            if get_setting("enable_daily_report", cfg.ENABLE_DAILY_REPORT):
                now = datetime.now(timezone.utc)
                today_str = now.strftime("%Y-%m-%d")
                report_hour = get_setting("daily_report_hour", cfg.DAILY_REPORT_HOUR_UTC)
                if now.hour == report_hour and today_str != last_sent_date:
                    try:
                        msg = "🗓 <b>Ежедневный отчёт</b>\n\n" + self.build_stats_message("сутки", 1)
                        try:
                            day_start_ms = int(now.replace(hour=0, minute=0, second=0, microsecond=0).timestamp() * 1000)
                            fee_total, fee_count = self.client.fetch_fees_sum(day_start_ms, int(now.timestamp() * 1000))
                            msg += f"\n\n💸 Комиссии за сегодня: <b>{fee_total:.2f} USDT</b> ({fee_count} исполнений)"
                        except Exception:
                            self.log.exception("Не удалось добавить комиссии в ежедневный отчёт")
                        self.tg.notify(msg)
                        set_meta("last_daily_report_date", today_str)
                        last_sent_date = today_str
                    except Exception:
                        self.log.exception("Ошибка отправки ежедневного отчёта")
            time.sleep(60)

    def weekly_report_loop(self):
        if not cfg.TELEGRAM_CHAT_ID:
            return
        last_sent_week = get_meta("last_weekly_report_week", "")
        while True:
            if get_setting("enable_weekly_report", cfg.ENABLE_WEEKLY_REPORT):
                now = datetime.now(timezone.utc)
                week_key = now.strftime("%G-W%V")
                if now.weekday() == cfg.WEEKLY_REPORT_WEEKDAY and now.hour == cfg.WEEKLY_REPORT_HOUR_UTC and week_key != last_sent_week:
                    try:
                        msg = "📅 <b>Итоги недели</b>\n\n" + self.build_stats_message("7 дней", 7)
                        try:
                            week_start_ms = int((now - timedelta(days=7)).timestamp() * 1000)
                            fee_total, fee_count = self.client.fetch_fees_sum(week_start_ms, int(now.timestamp() * 1000))
                            msg += f"\n\n💸 Комиссии за неделю: <b>{fee_total:.2f} USDT</b> ({fee_count} исполнений)"
                        except Exception:
                            self.log.exception("Не удалось добавить комиссии в еженедельный отчёт")
                        self.tg.notify(msg)
                        set_meta("last_weekly_report_week", week_key)
                        last_sent_week = week_key
                    except Exception:
                        self.log.exception("Ошибка отправки еженедельного отчёта")
            time.sleep(60)

    # ------------------------------------------------------------------
    # Автобэкап файла БД в Telegram (переживает передеплой на Railway и
    # подобных платформах без persistent-диска: файл базы данных иначе
    # безвозвратно терялся бы при каждом redeploy)
    # ------------------------------------------------------------------

    def send_db_backup(self, caption: str = None, reply_markup=None):
        """Отправляет текущий файл базы данных документом в чат. Используется
        и плановым автобэкапом, и кнопкой ручного бэкапа — единая логика."""
        if not cfg.TELEGRAM_CHAT_ID:
            return False
        # Не проверяем количество закрытых сделок: в БД могут уже находиться
        # открытые позиции, runtime-state, ручные L1/L2, настройки и история
        # переходов. Даже БД без единой сделки должна резервироваться.
        db_path = resolve_path(cfg.DB_PATH)
        if not os.path.isfile(db_path):
            raise FileNotFoundError(f"Файл SQLite не найден: {db_path}")

        stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M")
        fd, snapshot_path = tempfile.mkstemp(prefix="trades_backup_", suffix=".db")
        os.close(fd)
        try:
            # Нельзя копировать только trades.db при активном WAL: последние
            # подтверждённые транзакции могут оставаться в -wal. Connection.backup
            # создаёт согласованный снимок всей БД, не останавливая бота.
            snapshot_conn = sqlite3.connect(snapshot_path, timeout=30.0)
            try:
                with _db_lock:
                    _conn.backup(snapshot_conn)
                snapshot_conn.commit()
            finally:
                snapshot_conn.close()

            with open(snapshot_path, "rb") as f:
                buf = io.BytesIO(f.read())
            buf.name = f"trades_backup_{stamp}.db"
            self.tg.bot.send_document(
                self.tg.chat_id,
                buf,
                caption=caption or f"💾 Бэкап базы данных — {stamp} UTC",
                reply_markup=reply_markup,
            )
            return True
        finally:
            try:
                os.unlink(snapshot_path)
            except FileNotFoundError:
                pass

    def db_backup_loop(self):
        if not cfg.TELEGRAM_CHAT_ID:
            return
        last_sent_date = get_meta("last_db_backup_date", "")
        while True:
            if get_setting("enable_db_backup", getattr(cfg, "ENABLE_DB_BACKUP", True)):
                now = datetime.now(timezone.utc)
                today_str = now.strftime("%Y-%m-%d")
                backup_hour = get_setting("db_backup_hour", getattr(cfg, "DB_BACKUP_HOUR_UTC", 3))
                if now.hour == int(backup_hour) and today_str != last_sent_date:
                    try:
                        self.send_db_backup(caption=f"💾 <b>Плановый автобэкап базы сделок</b> — {today_str} UTC")
                        set_meta("last_db_backup_date", today_str)
                        last_sent_date = today_str
                        self.log.info("Плановый автобэкап БД отправлен в Telegram.")
                    except Exception:
                        self.log.exception("Ошибка планового автобэкапа БД")
            time.sleep(60)


# ============================================================================
# TELEGRAM UI: один бот, объединённые меню (торговля + учёт)
# ============================================================================

CONFIG_PATH = os.path.join(BASE_DIR, "config.py")

# ----------------------------------------------------------------------------
# Настройки ТОРГОВОГО ДВИЖКА, изменяемые кнопками (пишутся обратно в config.py)
# ----------------------------------------------------------------------------

EDITABLE_SETTINGS = {
    "PUMP_THRESHOLD_PCT":        {"label": "Порог пампа",             "type": float, "min": 1,    "max": 200,  "step": 1,    "suffix": "%"},
    "LOOKBACK_MINUTES":          {"label": "Окно расчёта",            "type": int,   "min": 5,    "max": 1440, "step": 5,    "suffix": " мин"},
    "POSITION_PCT_OF_EQUITY":    {"label": "Размер позиции",          "type": float, "min": 0.1,  "max": 100,  "step": 0.1,  "suffix": "% от equity"},
    "LEVERAGE":                  {"label": "Плечо",                    "type": int,   "min": 1,    "max": 100,  "step": 1,    "suffix": "x"},
    "TAKE_PROFIT_PCT":           {"label": "Тейк-профит (шорт)",       "type": float, "min": 0.1,  "max": 100,  "step": 0.5,  "suffix": "%"},
    "MAX_OPEN_POSITIONS":        {"label": "Макс. позиций",            "type": int,   "min": 1,    "max": 50,   "step": 1,    "suffix": ""},
    "STALL_CONFIRMATION_TICKS":  {"label": "Тиков без максимума (вход)", "type": int, "min": 1,    "max": 20,   "step": 1,    "suffix": ""},
    "STALL_DROP_PCT":            {"label": "Мин. откат от пика (вход)", "type": float, "min": 0.05, "max": 20,   "step": 0.05, "suffix": "%"},
    "STALL_MIN_SECONDS":         {"label": "Мин. время с пика (вход)", "type": float, "min": 0,    "max": 120,  "step": 0.5,  "suffix": " сек"},
    "STALL_DROP_ADAPTIVE_FACTOR": {"label": "Адапт. откат (× от размера пампа)", "type": float, "min": 0,   "max": 1,    "step": 0.01, "suffix": ""},
    "STALL_DROP_MAX_PCT":        {"label": "Потолок адапт. отката",   "type": float, "min": 0.1,  "max": 50,   "step": 0.5,  "suffix": "%"},
    "WATCH_MAX_MINUTES":         {"label": "Макс. время слежения",     "type": int,   "min": 1,    "max": 240,  "step": 5,    "suffix": " мин"},
    "FIXED_STOP_LOSS_PCT":       {"label": "Стоп-лосс от входа (шорт)", "type": float, "min": 0.05,  "max": 100,    "step": 0.1,   "suffix": "%"},
    "LONG_TAKE_PROFIT_PCT":      {"label": "Тейк-профит (лонг)",       "type": float, "min": 0.1,   "max": 100,    "step": 0.5,   "suffix": "%"},
    "LONG_FIXED_STOP_LOSS_PCT":  {"label": "Стоп-лосс от входа (лонг)", "type": float, "min": 0.05,  "max": 100,    "step": 0.1,   "suffix": "%"},
    "PROFIT_LOCK_TRIGGER_PCT":   {"label": "% движения для защиты (SL)", "type": float, "min": 0.1,   "max": 100,    "step": 0.5,   "suffix": "%"},
    "PROFIT_LOCK_MIN_USDT":      {"label": "Сколько PnL фиксировать",   "type": float, "min": 0.001, "max": 100000, "step": 0.001, "suffix": " USDT"},
    "SMART_EXIT_MIN_PROFIT_USDT": {"label": "Мин. PnL для умн. выхода", "type": float, "min": 0.01,  "max": 100000, "step": 0.5,   "suffix": " USDT"},
    "SMART_EXIT_STALL_TICKS":    {"label": "Тиков без минимума (выход)", "type": int,  "min": 1,    "max": 20,   "step": 1,    "suffix": ""},
    "SMART_EXIT_BOUNCE_PCT":     {"label": "Отскок от дна для выхода", "type": float, "min": 0.05, "max": 20,   "step": 0.05, "suffix": "%"},
    "SMART_EXIT_MIN_SECONDS":    {"label": "Мин. время со дна (выход)", "type": float, "min": 0,   "max": 120,  "step": 0.5,  "suffix": " сек"},
    "COOLDOWN_MINUTES":          {"label": "Cooldown после закрытия",  "type": int,   "min": 0,    "max": 1440, "step": 5,    "suffix": " мин"},
    "HEARTBEAT_MINUTES":         {"label": "Heartbeat-уведомления",    "type": int,   "min": 0,    "max": 1440, "step": 10,   "suffix": " мин"},
    "BREAKOUT_FAIL_MARGIN_PCT":  {"label": "Провал пробоя: откат от хая", "type": float, "min": 0.05, "max": 10,  "step": 0.05, "suffix": "%"},
    "TREND_FILTER_MARGIN_PCT":   {"label": "Порог 'сильного тренда'",  "type": float, "min": 0.1,  "max": 20,   "step": 0.1,  "suffix": "% выше EMA20"},
    "VOLUME_SPIKE_MULTIPLIER":   {"label": "Объёмный спайк, множитель", "type": float, "min": 1.0,  "max": 20,   "step": 0.1,  "suffix": "x"},
    "VOLUME_LOOKBACK_CANDLES":   {"label": "Свечей для среднего объёма", "type": int,  "min": 3,    "max": 100,  "step": 1,    "suffix": ""},
    "VERTICAL_CANDLE_PCT_THRESHOLD": {"label": "Порог вертикальной свечи", "type": float, "min": 0.5, "max": 50, "step": 0.5,  "suffix": "%"},
    "FILTER_REJECT_COOLDOWN_MINUTES": {"label": "Cooldown после отказа фильтра", "type": int, "min": 0, "max": 120, "step": 1, "suffix": " мин"},
    "POST_ONLY_OFFSET_PCT":      {"label": "Post-only: отступ от цены", "type": float, "min": 0.0,  "max": 2,    "step": 0.01, "suffix": "%"},
    "POST_ONLY_TIMEOUT_SEC":     {"label": "Post-only: таймаут ожидания", "type": float, "min": 0.5, "max": 60,  "step": 0.5,  "suffix": " сек"},
    "SHORT_LOW_BOUNCE_PCT":      {"label": "Рост от лоя свечи (шорт)", "type": float, "min": 0.05, "max": 50,   "step": 0.1,  "suffix": "%"},
    "LONG_LOW_BOUNCE_PCT":       {"label": "Рост от лоя свечи (лонг)", "type": float, "min": 0.05, "max": 50,   "step": 0.1,  "suffix": "%"},
}

# Таймфрейм свечи для фильтров "рост от лоя свечи" (шорт/лонг) — отдельные
# кнопки-циклеры (не числовые значения, поэтому не в EDITABLE_SETTINGS выше).
# Значения — минуты строкой, как принято в KLINE_INTERVAL/FILTER_CANDLE_INTERVAL.
SHORT_BOUNCE_INTERVAL_PRESETS = ["1", "3", "5", "15", "30", "60"]
LONG_BOUNCE_INTERVAL_PRESETS = ["1", "3", "5", "15", "30", "60"]

TOGGLE_SETTINGS = {
    "DRY_RUN": "Тестовый режим (без реальных ордеров)",
    "ENABLE_LONG_MODE": "Направление входа: Лонг (выкл = Шорт)",
    "ENABLE_FIXED_STOP_LOSS": "Обычный стоп-лосс (по PnL)",
    "ENABLE_PROFIT_LOCK": "Защита прибыли (авто стоп-лосс)",
    "ENABLE_SMART_EXIT": "Умный выход (ждать конца падения)",
    "ENABLE_MICRO_ANALYSIS": "Микро-анализ разворота (замедление роста)",
    "ENABLE_BREAKOUT_FILTER": "Фильтр: провал пробоя (хай не удержан)",
    "ENABLE_TREND_FILTER": "Фильтр: не шортить сильный тренд",
    "ENABLE_VOLUME_FILTER": "Фильтр: объёмное подтверждение пампа",
    "ENABLE_VOLUME_DECLINE_FILTER": "Фильтр: падение объёма после пампа",
    "ENABLE_VERTICAL_CANDLE_FILTER": "Фильтр: не шортить вертикальную свечу",
    "ENABLE_POST_ONLY_ENTRY": "Вход лимитным post-only ордером",
    "ENABLE_SHORT_LOW_BOUNCE_FILTER": "Фильтр (шорт): рост от лоя свечи",
    "ENABLE_LONG_LOW_BOUNCE_FILTER": "Фильтр (лонг): рост от лоя свечи",
}

_settings_lock = threading.Lock()


def get_trading_setting(key: str):
    return getattr(cfg, key)


def persist_trading_setting(key: str, value) -> None:
    """Потокобезопасно обновляет значение в памяти и переписывает строку в
    config.py, чтобы значение пережило перезапуск."""
    with _settings_lock:
        setattr(cfg, key, value)
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            lines = f.readlines()

        pattern = re.compile(rf"^({re.escape(key)}\s*=\s*)(.+?)(\s*(#.*)?)$")
        new_lines, replaced = [], False
        for line in lines:
            m = pattern.match(line.rstrip("\n"))
            if m:
                prefix, tail = m.group(1), m.group(3)
                new_lines.append(f"{prefix}{value!r}{tail}\n")
                replaced = True
            else:
                new_lines.append(line)

        if replaced:
            tmp_path = CONFIG_PATH + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                f.writelines(new_lines)
            os.replace(tmp_path, CONFIG_PATH)


# ----------------------------------------------------------------------------
# Пресеты для настроек УЧЁТА/ОТЧЁТНОСТИ (хранятся в БД через get_setting)
# ----------------------------------------------------------------------------

LOSS_ALERT_PRESETS = [0, 50, 100, 200, 500, 1000]
PNL_PLUS_PRESETS = [0, 5, 10, 20, 50, 100, 200]
PNL_MINUS_PRESETS = [0, 5, 10, 20, 50, 100, 200]
TIMEZONE_PRESETS = [0, 1, 2, 3, 4, 5, -5]
QUIET_HOURS_PRESETS = ["", "23-7", "0-6", "22-8", "23-9"]
DAILY_REPORT_HOUR_PRESETS = [6, 7, 8, 9, 12, 18, 21]
DB_BACKUP_HOUR_PRESETS = [0, 3, 6, 12, 18, 21]
# Стоп для ручных позиций: от 1% до 10% с шагом 1%.
MANUAL_TRADE_STOP_PERCENT_PRESETS = list(range(1, 11))

def get_manual_stop_percent() -> float:
    """Возвращает допустимый стоп ручных сделок строго в диапазоне 1–10%."""
    try:
        default = float(getattr(cfg, "MANUAL_TRADE_STOP_PERCENT", 6.0))
    except (TypeError, ValueError, OverflowError):
        default = 6.0
    if not math.isfinite(default):
        default = 6.0
    try:
        value = float(get_setting("manual_trade_stop_percent", default))
    except (TypeError, ValueError, OverflowError):
        value = default
    if not math.isfinite(value):
        value = default
    return min(10.0, max(1.0, value))


def _round_stop_price_for_side(value: float, step: float, side: str) -> float:
    """Округляет SL в сторону, не уменьшающую заданную дистанцию риска.

    LONG stop округляется вниз, SHORT stop — вверх. Обычный round_step()
    всегда округляет вниз, что для SHORT могло незаметно уменьшать дистанцию
    стопа и давать цену, отличающуюся от подтверждаемой на бирже.
    """
    normalized_side = str(side or "").strip().upper()
    if normalized_side not in {"LONG", "SHORT"}:
        raise ValueError(f"unknown stop side: {side!r}")
    try:
        price = float(value)
        tick = float(step)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError("stop price and tick size must be numeric") from exc
    if not math.isfinite(price) or price <= 0:
        raise ValueError(f"invalid stop price: {value!r}")
    if not math.isfinite(tick) or tick <= 0:
        raise ValueError(f"invalid tick size: {step!r}")
    rounding = ROUND_DOWN if normalized_side == "LONG" else ROUND_CEILING
    rounded_steps = (Decimal(str(price)) / Decimal(str(tick))).to_integral_value(rounding=rounding)
    rounded = float(rounded_steps * Decimal(str(tick)))
    if not math.isfinite(rounded) or rounded <= 0:
        raise ValueError(f"rounded stop price is invalid: {rounded!r}")
    return rounded


def _calculate_manual_l2_stop(side: str, l2_price: float, stop_percent: float) -> float:
    """Calculate manual SL from the pinned second entry limit (L2).

    stop_percent is always expressed in human percent units (e.g. 6 means 6%,
    never 0.06). This is intentionally shared by initial position capture,
    Telegram setting changes, and post-fill reconciliation so LONG/SHORT formulas
    cannot drift apart. Invalid values fail closed instead of producing an SL.
    """
    normalized_side = str(side or "").strip().upper()
    if normalized_side not in {"LONG", "SHORT"}:
        raise ValueError(f"unknown manual position side: {side!r}")
    try:
        anchor = float(l2_price)
        percent = float(stop_percent)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError("L2 price and stop percent must be numeric") from exc
    if not math.isfinite(anchor) or anchor <= 0:
        raise ValueError(f"invalid L2 price: {l2_price!r}")
    if not math.isfinite(percent) or percent < 1.0 or percent > 10.0:
        raise ValueError(f"stop percent must be finite and between 1 and 10: {stop_percent!r}")
    fraction = percent / 100.0
    result = anchor * (1.0 - fraction) if normalized_side == "LONG" else anchor * (1.0 + fraction)
    if not math.isfinite(result) or result <= 0:
        raise ValueError(f"calculated stop is invalid: {result!r}")
    return result


def get_manual_tp_close_percent() -> int:
    """Возвращает безопасный процент закрытия ручной позиции: 1–100%."""
    default = int(getattr(cfg, "MANUAL_TRADE_TP_CLOSE_PERCENT", 50))
    try:
        value = int(float(get_setting("manual_trade_tp_close_percent", default)))
    except (TypeError, ValueError):
        value = default
    return min(100, max(1, value))


# Мульти-тейки для позиций, открытых самим торговым движком.
# TP1-TP3 закрывают заданную долю исходного объёма, TP4 всегда закрывает
# весь ОСТАТОК позиции. Движение каждой цели считается от фактического
# avgPrice входа, а не от цены, которую бот видел до исполнения.
BOT_TP_CLOSE_DEFAULTS = [25, 25, 25, 100]

def _bot_tp_default_moves() -> List[float]:
    base = float(getattr(cfg, "LONG_TAKE_PROFIT_PCT", getattr(cfg, "TAKE_PROFIT_PCT", 3.0))) if getattr(cfg, "ENABLE_LONG_MODE", False) else float(getattr(cfg, "TAKE_PROFIT_PCT", 3.0))
    base = max(0.4, base)
    return [round(base * 0.25, 6), round(base * 0.50, 6), round(base * 0.75, 6), round(base, 6)]

def get_bot_tp_config() -> Tuple[List[float], List[float]]:
    defaults = _bot_tp_default_moves()
    moves = []
    closes = []
    for i, default in enumerate(defaults, 1):
        try:
            value = float(get_setting(f"bot_tp{i}_move_pct", default))
        except (TypeError, ValueError):
            value = default
        if not math.isfinite(value):
            value = default
        moves.append(max(0.01, min(100.0, value)))
        if i < 4:
            try:
                c = float(get_setting(f"bot_tp{i}_close_pct", BOT_TP_CLOSE_DEFAULTS[i-1]))
            except (TypeError, ValueError):
                c = BOT_TP_CLOSE_DEFAULTS[i-1]
            if not math.isfinite(c):
                c = BOT_TP_CLOSE_DEFAULTS[i-1]
            closes.append(max(0.1, min(99.0, c)))
        else:
            closes.append(100.0)

    # Если БД/закреплённая настройка содержит повреждённый или конфликтующий
    # план, никогда не отправляем его на биржу. Возвращаем безопасные дефолты.
    enabled = [bool(get_setting(f"bot_tp{i}_enabled", True)) for i in range(1, 4)]
    if _bot_tp_validate_moves(moves, enabled) or _bot_tp_validate_closes(closes, enabled):
        return list(defaults), list(BOT_TP_CLOSE_DEFAULTS)
    return moves, closes


def _setting_as_bool(value, default: bool = True) -> bool:
    """Parse SQLite/pinned boolean settings without treating the string '0' as True."""
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        try:
            number = float(value)
        except (TypeError, ValueError, OverflowError):
            return bool(default)
        if not math.isfinite(number):
            return bool(default)
        if number == 0:
            return False
        if number == 1:
            return True
        return bool(default)
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"1", "true", "yes", "on", "enabled", "да", "вкл", "включено"}:
            return True
        if normalized in {"0", "false", "no", "off", "disabled", "нет", "выкл", "выключено", ""}:
            return False
    return bool(default)


def get_bot_tp_enabled() -> List[bool]:
    """Глобальные переключатели TP1-TP3. TP4 всегда включён."""
    enabled = []
    for i in range(1, 4):
        try:
            raw = get_setting(f"bot_tp{i}_enabled", True)
        except Exception:
            raw = True
        enabled.append(_setting_as_bool(raw, default=True))
    return enabled + [True]

def _parse_bot_tp_toggle_callback(data: str) -> Optional[Tuple[int, bool]]:
    """Parse only supported TP1-TP3 on/off callback IDs."""
    if not isinstance(data, str) or not data.startswith("set_bot_tp"):
        return None
    if data.endswith("_on"):
        suffix = "_on"
        enabled = True
    elif data.endswith("_off"):
        suffix = "_off"
        enabled = False
    else:
        return None
    raw_number = data[len("set_bot_tp"):-len(suffix)]
    try:
        tp_no = int(raw_number)
    except (TypeError, ValueError, OverflowError):
        return None
    if tp_no not in (1, 2, 3):
        return None
    return tp_no, enabled


def _bot_tp_rounded_targets_ordered(
    targets: List[float], enabled: List[bool], side: str
) -> bool:
    """Validate only active TP1-TP3 plus TP4 after tick-size rounding."""
    if not isinstance(targets, (list, tuple)) or len(targets) != 4:
        return False
    if not isinstance(enabled, (list, tuple)) or len(enabled) < 3:
        return False
    try:
        prices = [float(x) for x in targets]
    except (TypeError, ValueError, OverflowError):
        return False
    if any(not math.isfinite(x) or x <= 0 for x in prices):
        return False
    active = [prices[i] for i in range(3) if enabled[i]] + [prices[3]]
    normalized_side = str(side or "").upper()
    if normalized_side == "LONG":
        return all(a < b for a, b in zip(active, active[1:]))
    if normalized_side == "SHORT":
        return all(a > b for a, b in zip(active, active[1:]))
    return False


def _bot_tp_protection_ready(
    enabled: List[bool], done: Dict, verified: Dict, tp4_ok: bool
) -> bool:
    """A saved order ID alone is not proof that the exchange order is active."""
    if not tp4_ok:
        return False
    if not isinstance(enabled, (list, tuple)) or len(enabled) < 3:
        return False
    done = done if isinstance(done, dict) else {}
    verified = verified if isinstance(verified, dict) else {}
    return all(
        (not enabled[i]) or bool(done.get(str(i + 1)) or verified.get(str(i + 1)))
        for i in range(3)
    )


def _bot_tp_validate_moves(moves: List[float], enabled: Optional[List[bool]] = None) -> Optional[str]:
    """Проверяет уровни TP1-TP4, включая конечные значения и порядок целей."""
    if not isinstance(moves, (list, tuple)) or len(moves) < 4:
        return "Нужно указать четыре уровня TP1–TP4."
    flags = list(enabled[:3]) if enabled is not None else [True, True, True]
    if len(flags) < 3:
        return "Некорректный список включения TP1–TP3."
    active = []
    for i in range(3):
        if not flags[i]:
            continue
        try:
            value = float(moves[i])
        except (TypeError, ValueError, OverflowError):
            return f"TP{i + 1}: процент должен быть числом."
        if not math.isfinite(value) or value <= 0:
            return f"TP{i + 1}: процент должен быть конечным числом больше 0."
        active.append((i + 1, value))
    try:
        tp4 = float(moves[3])
    except (TypeError, ValueError, OverflowError):
        return "TP4: процент должен быть числом."
    if not math.isfinite(tp4) or tp4 <= 0:
        return "TP4: процент должен быть конечным числом больше 0."
    active.append((4, tp4))
    for (n1, m1), (n2, m2) in zip(active, active[1:]):
        if m1 >= m2:
            return f"TP{n1} должен быть ближе к входу, чем TP{n2}: сейчас {m1:g}% и {m2:g}%."
    return None


def _bot_tp_validate_closes(closes: List[float], enabled: Optional[List[bool]] = None) -> Optional[str]:
    """TP1-TP3 должны закрывать положительные доли, оставляя остаток TP4."""
    if not isinstance(closes, (list, tuple)) or len(closes) < 3:
        return "Нужно указать проценты закрытия для TP1–TP3."
    flags = list(enabled[:3]) if enabled is not None else [True, True, True]
    if len(flags) < 3:
        return "Некорректный список включения TP1–TP3."
    total = 0.0
    for i in range(3):
        if not flags[i]:
            continue
        try:
            value = float(closes[i])
        except (TypeError, ValueError, OverflowError):
            return f"TP{i + 1}: процент закрытия должен быть числом."
        if not math.isfinite(value) or value <= 0 or value >= 100:
            return f"TP{i + 1}: процент закрытия должен быть больше 0 и меньше 100."
        total += value
    if not math.isfinite(total) or total >= 100.0:
        return f"Сумма закрытий TP1–TP3 должна быть меньше 100% (сейчас {total:g}%). TP4 закрывает остаток."
    return None


# Все настройки учёта/отчётности, которые могут меняться кнопками — с их
# типом и значением по умолчанию (из config.py). Используется, чтобы
# сохранить/восстановить их из закреплённого сообщения в Telegram (см.
# UnifiedBot.sync_settings_from_pinned / push_settings_pin ниже) — это
# переживает передеплой на Railway и подобных платформах, где локальный
# диск контейнера каждый раз пересоздаётся с нуля.
REPORT_SETTINGS_SCHEMA = {
    "notify_new_trade": (bool, cfg.NOTIFY_ON_NEW_TRADE),
    "enable_daily_report": (bool, cfg.ENABLE_DAILY_REPORT),
    "daily_report_hour": (int, cfg.DAILY_REPORT_HOUR_UTC),
    "enable_weekly_report": (bool, cfg.ENABLE_WEEKLY_REPORT),
    "max_daily_loss_alert": (float, cfg.MAX_DAILY_LOSS_ALERT),
    "pnl_alert_plus": (float, cfg.PNL_TRADE_ALERT_PLUS),
    "pnl_alert_minus": (float, cfg.PNL_TRADE_ALERT_MINUS),
    "tz_offset": (int, 0),
    "quiet_hours": (str, cfg.QUIET_HOURS),
    "notify_connection_issues": (bool, cfg.NOTIFY_ON_CONNECTION_ISSUES),
    "enable_db_backup": (bool, getattr(cfg, "ENABLE_DB_BACKUP", True)),
    "db_backup_hour": (int, getattr(cfg, "DB_BACKUP_HOUR_UTC", 3)),
    "only_trade_close_notifications": (bool, getattr(cfg, "ONLY_TRADE_CLOSE_NOTIFICATIONS", False)),
    # Ниже — настройки, добавленные позже (посты/сигналы/ручные сделки).
    # ВАЖНО: любая новая настройка через get_setting/set_setting ОБЯЗАНА
    # попасть сюда, иначе она не попадёт в закреплённое сообщение и не
    # переживёт передеплой на Railway без постоянного диска — именно так
    # нашёлся этот баг: несколько настроек тут не хватало.
    "okx_feed_enabled": (bool, getattr(cfg, "OKX_FEED_ENABLED_DEFAULT", False)),
    "manual_trade_management_enabled": (bool, getattr(cfg, "MANUAL_TRADE_MANAGEMENT_ENABLED_DEFAULT", True)),
    "manual_trade_tp_close_percent": (int, getattr(cfg, "MANUAL_TRADE_TP_CLOSE_PERCENT", 50)),
    "manual_trade_stop_percent": (float, getattr(cfg, "MANUAL_TRADE_STOP_PERCENT", 6.0)),
    "manual_limit1_value_usdt": (float, 10.0),
    "manual_limit2_value_usdt": (float, 10.0),
    # Если выключено, бот не меняет qty/стоимость уже выставленных ручных лимиток.
    "manual_limit_value_changes_enabled": (bool, True),
    "bot_tp1_move_pct": (float, _bot_tp_default_moves()[0]),
    "bot_tp1_close_pct": (float, 25),
    "bot_tp2_move_pct": (float, _bot_tp_default_moves()[1]),
    "bot_tp2_close_pct": (float, 25),
    "bot_tp3_move_pct": (float, _bot_tp_default_moves()[2]),
    "bot_tp3_close_pct": (float, 25),
    "bot_tp4_move_pct": (float, _bot_tp_default_moves()[3]),
    "bot_tp4_close_pct": (float, 100),
    "bot_tp1_enabled": (bool, True),
    "bot_tp2_enabled": (bool, True),
    "bot_tp3_enabled": (bool, True),
}

# Настройки-СПИСКИ (не одно скалярное значение, как выше, а список тикеров) —
# хранятся через get_meta/set_meta под этими ключами, и по той же причине
# (пережить передеплой без диска) тоже должны попадать в закреплённое
# сообщение — отдельным разделом payload, см. _build_settings_snapshot.
REPORT_SETTINGS_LIST_KEYS = ("favorite_symbols", "excluded_symbols")

SETTINGS_PIN_MARKER = "SETTINGS_ZLIB_V5:"
SETTINGS_PIN_MARKER_V4 = "SETTINGS_ZLIB_V4:"
SETTINGS_PIN_MARKER_ZLIB_V3 = "SETTINGS_ZLIB_V3:"
SETTINGS_PIN_LISTS_MARKER = "SETTINGS_LISTS_ZLIB_V1:"
SETTINGS_PIN_MARKER_V2 = "SETTINGS_JSON_V2:"
SETTINGS_PIN_MARKER_LEGACY = "SETTINGS_JSON_V1:"
SETTINGS_PIN_MAX_CHARS = 4000

# ----------------------------------------------------------------------------
# Клавиатуры
# ----------------------------------------------------------------------------

BTN_QUICK_STATUS = "⚡ Быстрый статус"
BTN_STATS = "📊 Статистика"
BTN_POSITIONS = "📈 Позиции"
BTN_LIMIT_ORDERS = "📋 Стоимость лимиток"
BTN_CHART = "📉 График капитала"
BTN_TOP_TRADES = "🏆 Топ сделок"
BTN_TABLE = "🧾 Таблица сделок"
BTN_FEES = "💸 Комиссии"
BTN_EXPORT = "📤 Экспорт CSV"
BTN_BALANCE = "💰 Баланс"
BTN_SYNC = "🔄 Синхронизировать"
BTN_HISTORY = "🕘 История (движок)"
BTN_PAUSE = "⏸ Пауза / ▶️ Продолжить"
BTN_STOP = "🔴 Стоп торговли"
BTN_TRADE_SETTINGS = "⚙️ Настройки стратегии"
BTN_REPORT_SETTINGS = "⚙️ Настройки учёта"
BTN_STATUS = "ℹ️ Статус"
BTN_CHECK_CONN = "🩺 Проверить соединение"
BTN_BACKUP = "💾 Резервная копия БД"
BTN_FAVORITES = "⭐ Избранные монеты"


def reply_keyboard(paused: bool) -> types.ReplyKeyboardMarkup:
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    kb.add(types.KeyboardButton(BTN_QUICK_STATUS))
    kb.add(types.KeyboardButton(BTN_STATS), types.KeyboardButton(BTN_POSITIONS))
    kb.add(types.KeyboardButton(BTN_LIMIT_ORDERS))
    kb.add(types.KeyboardButton(BTN_CHART), types.KeyboardButton(BTN_TOP_TRADES))
    kb.add(types.KeyboardButton(BTN_TABLE), types.KeyboardButton(BTN_FEES))
    kb.add(types.KeyboardButton(BTN_EXPORT), types.KeyboardButton(BTN_BALANCE))
    kb.add(types.KeyboardButton(BTN_SYNC), types.KeyboardButton(BTN_HISTORY))
    kb.add(types.KeyboardButton("▶️ Продолжить торговлю" if paused else "⏸ Пауза торговли"))
    kb.add(types.KeyboardButton(BTN_STOP))
    kb.add(types.KeyboardButton(BTN_TRADE_SETTINGS), types.KeyboardButton(BTN_REPORT_SETTINGS))
    kb.add(types.KeyboardButton(BTN_FAVORITES))
    kb.add(types.KeyboardButton(BTN_STATUS), types.KeyboardButton(BTN_CHECK_CONN))
    kb.add(types.KeyboardButton(BTN_BACKUP))
    return kb


def period_menu(prefix: str) -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup(row_width=2)
    buttons = [types.InlineKeyboardButton(name, callback_data=f"{prefix}_{days}") for name, days in PERIODS]
    kb.add(*buttons)
    kb.add(types.InlineKeyboardButton("⬅️ Назад", callback_data="menu_main"))
    return kb


def stats_result_menu(days: int) -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup(row_width=2)
    buttons = [types.InlineKeyboardButton(name, callback_data=f"stats_{d}") for name, d in PERIODS]
    kb.add(*buttons)
    kb.add(types.InlineKeyboardButton("🔄 Обновить", callback_data=f"stats_{days}"), types.InlineKeyboardButton("⬅️ Назад", callback_data="menu_main"))
    return kb


def back_menu() -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("⬅️ Назад", callback_data="menu_main"))
    return kb


def favorites_menu() -> types.InlineKeyboardMarkup:
    enabled = is_favorites_mode_enabled()
    favorites = get_favorite_symbols()
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton(f"⭐ Режим избранного: {'🟢 Вкл.' if enabled else '⚪ Выкл.'}", callback_data="favorites_toggle"))
    kb.add(types.InlineKeyboardButton("➕ Добавить монету", callback_data="favorites_add"))
    if favorites:
        buttons = [types.InlineKeyboardButton(f"❌ {sym}", callback_data=f"favorites_remove:{sym}") for sym in favorites]
        kb.add(*buttons)
    kb.add(types.InlineKeyboardButton("⬅️ Назад", callback_data="menu_main"))
    return kb


def favorites_status_text() -> str:
    enabled = is_favorites_mode_enabled()
    favorites = get_favorite_symbols()
    lines = [
        "⭐ <b>Избранные монеты</b>",
        "━━━━━━━━━━━━━━━",
        f"Режим: <b>{'включён — торгуются только избранные' if enabled else 'выключен — торгуется весь рынок'}</b>",
        "",
    ]
    if favorites:
        lines.append(f"Список ({len(favorites)}): " + ", ".join(favorites))
    else:
        lines.append("Список пуст. Добавь монеты кнопкой ниже — иначе при включённом режиме бот не будет торговать вообще ничего.")
    lines.append("\nНажми на монету ниже (❌), чтобы убрать её из списка.")
    return "\n".join(lines)


def trade_settings_menu() -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup(row_width=1)
    for key, label in TOGGLE_SETTINGS.items():
        value = get_trading_setting(key)
        state = "🟢 Вкл." if value else "⚪ Выкл."
        kb.add(types.InlineKeyboardButton(f"{label}: {state}", callback_data=f"toggle:{key}"))
    for key, meta in EDITABLE_SETTINGS.items():
        value = get_trading_setting(key)
        kb.add(types.InlineKeyboardButton(f"{meta['label']}: {fmt_num(value)}{meta['suffix']}", callback_data=f"set:{key}"))
    bounce_interval = get_trading_setting("SHORT_LOW_BOUNCE_CANDLE_INTERVAL")
    kb.add(types.InlineKeyboardButton(f"Таймфрейм лоя свечи (шорт): {bounce_interval}м", callback_data="cycle_short_bounce_interval"))
    long_bounce_interval = get_trading_setting("LONG_LOW_BOUNCE_CANDLE_INTERVAL")
    kb.add(types.InlineKeyboardButton(f"Таймфрейм лоя свечи (лонг): {long_bounce_interval}м", callback_data="cycle_long_bounce_interval"))
    kb.add(types.InlineKeyboardButton("⬅️ Закрыть меню", callback_data="settings_close"))
    return kb


def value_edit_keyboard(key: str) -> types.InlineKeyboardMarkup:
    meta = EDITABLE_SETTINGS[key]
    step = meta["step"]
    kb = types.InlineKeyboardMarkup(row_width=4)
    kb.add(types.InlineKeyboardButton(f"−{fmt_num(step)}", callback_data=f"adj:{key}:-1"), types.InlineKeyboardButton(f"+{fmt_num(step)}", callback_data=f"adj:{key}:1"))
    kb.add(types.InlineKeyboardButton("✏️ Ввести своё значение", callback_data=f"typein:{key}"))
    kb.add(types.InlineKeyboardButton("⬅️ Назад к настройкам стратегии", callback_data="trade_settings_back"))
    return kb


def report_settings_menu() -> types.InlineKeyboardMarkup:
    notify = get_setting("notify_new_trade", cfg.NOTIFY_ON_NEW_TRADE)
    daily = get_setting("enable_daily_report", cfg.ENABLE_DAILY_REPORT)
    weekly = get_setting("enable_weekly_report", cfg.ENABLE_WEEKLY_REPORT)
    loss_limit = get_setting("max_daily_loss_alert", cfg.MAX_DAILY_LOSS_ALERT)
    tz_offset = get_setting("tz_offset", 0)
    conn_notify = get_setting("notify_connection_issues", cfg.NOTIFY_ON_CONNECTION_ISSUES)
    quiet_hours = get_setting("quiet_hours", cfg.QUIET_HOURS)
    pnl_plus = get_setting("pnl_alert_plus", cfg.PNL_TRADE_ALERT_PLUS)
    pnl_minus = get_setting("pnl_alert_minus", cfg.PNL_TRADE_ALERT_MINUS)
    okx_feed = get_setting("okx_feed_enabled", cfg.OKX_FEED_ENABLED_DEFAULT)
    db_backup = get_setting("enable_db_backup", getattr(cfg, "ENABLE_DB_BACKUP", True))
    db_backup_hour = get_setting("db_backup_hour", getattr(cfg, "DB_BACKUP_HOUR_UTC", 3))
    only_trade_close = get_setting("only_trade_close_notifications", getattr(cfg, "ONLY_TRADE_CLOSE_NOTIFICATIONS", False))
    manual_mgmt = get_setting("manual_trade_management_enabled", getattr(cfg, "MANUAL_TRADE_MANAGEMENT_ENABLED_DEFAULT", True))
    manual_tp2_pct = get_manual_tp_close_percent()
    manual_stop_pct = get_manual_stop_percent()

    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton(
        f"🔕 Только уведомления о закрытии сделок: {'Вкл ✅' if only_trade_close else 'Выкл ⛔'}",
        callback_data="toggle_only_trade_close",
    ))
    kb.add(types.InlineKeyboardButton(f"🔔 Уведомления о сделках: {'Вкл ✅' if notify else 'Выкл ⛔'}", callback_data="toggle_notify"))
    kb.add(types.InlineKeyboardButton(f"🌙 Тихие часы: {quiet_hours if quiet_hours else 'Выкл'}", callback_data="cycle_quiet_hours"))
    kb.add(types.InlineKeyboardButton(f"🔌 Уведомления о проблемах связи: {'Вкл ✅' if conn_notify else 'Выкл ⛔'}", callback_data="toggle_conn_notify"))
    kb.add(types.InlineKeyboardButton(f"🗓 Ежедневный отчёт: {'Вкл ✅' if daily else 'Выкл ⛔'}", callback_data="toggle_daily"))
    kb.add(types.InlineKeyboardButton(f"🕐 Час ежедневного отчёта: {get_setting('daily_report_hour', cfg.DAILY_REPORT_HOUR_UTC)}:00 UTC", callback_data="cycle_daily_hour"))
    kb.add(types.InlineKeyboardButton(f"📅 Еженедельный отчёт: {'Вкл ✅' if weekly else 'Выкл ⛔'}", callback_data="toggle_weekly"))
    kb.add(types.InlineKeyboardButton(f"⚠️ Риск-алерт (сутки суммарно): {(str(loss_limit) + ' USDT/сутки') if loss_limit > 0 else 'Выкл'}", callback_data="cycle_loss_alert"))
    kb.add(types.InlineKeyboardButton(f"🟢 Алерт на прибыль (сделка): {(f'от +{pnl_plus:g} USDT') if pnl_plus else 'Выкл'}", callback_data="cycle_pnl_plus"))
    kb.add(types.InlineKeyboardButton(f"🔴 Алерт на убыток (сделка): {(f'от −{pnl_minus:g} USDT') if pnl_minus else 'Выкл'}", callback_data="cycle_pnl_minus"))
    kb.add(types.InlineKeyboardButton(f"🕓 Часовой пояс отчётов: UTC{tz_offset:+d}", callback_data="cycle_timezone"))
    kb.add(types.InlineKeyboardButton(f"💾 Автобэкап БД в Telegram: {'Вкл ✅' if db_backup else 'Выкл ⛔'}", callback_data="toggle_db_backup"))
    kb.add(types.InlineKeyboardButton(f"📢 Посты трейдера OKX: {'Вкл ✅' if okx_feed else 'Выкл ⛔'}", callback_data="toggle_okx_feed"))
    bot_tp_moves, bot_tp_closes = get_bot_tp_config()
    bot_tp_enabled = get_bot_tp_enabled()
    for _i in range(3):
        kb.add(
            types.InlineKeyboardButton(f"TP{_i+1} ВКЛ {'✅' if bot_tp_enabled[_i] else ''}", callback_data=f"set_bot_tp{_i+1}_on"),
            types.InlineKeyboardButton(f"TP{_i+1} ВЫКЛ {'⛔' if not bot_tp_enabled[_i] else ''}", callback_data=f"set_bot_tp{_i+1}_off"),
        )
        kb.add(types.InlineKeyboardButton(
            f"✏️ TP{_i+1}: +{fmt_num(bot_tp_moves[_i])}% / {fmt_num(bot_tp_closes[_i])}%",
            callback_data=f"edit_bot_tp{_i+1}",
        ))
    kb.add(types.InlineKeyboardButton(
        f"🏁 TP4 (бот + ручные): +{fmt_num(bot_tp_moves[3])}% / 100% остатка",
        callback_data="edit_bot_tp4",
    ))
    kb.add(types.InlineKeyboardButton("📋 Активные сделки бота (посты)", callback_data="view_bot_signal_orders"))
    kb.add(types.InlineKeyboardButton(f"👀 Управление ручными сделками: {'Вкл ✅' if manual_mgmt else 'Выкл ⛔'}", callback_data="toggle_manual_trade_mgmt"))
    kb.add(types.InlineKeyboardButton(f"🛑 Стоп (ручные сделки): {fmt_num(manual_stop_pct)}%", callback_data="cycle_manual_stop_pct"))
    kb.add(types.InlineKeyboardButton("✏️ Ввести процент стопа вручную", callback_data="set_manual_stop_pct"))
    limit_changes_enabled = bool(get_setting("manual_limit_value_changes_enabled", True))
    kb.add(types.InlineKeyboardButton(
        f"🔧 Автоизменение стоимости лимиток: {'Вкл ✅' if limit_changes_enabled else 'Выкл ⛔'}",
        # Explicit desired state makes duplicate/double-click callbacks
        # idempotent: two callbacks for the same old keyboard can't toggle
        # the setting off and then accidentally turn it back on.
        callback_data=f"set_manual_limit_value_changes:{0 if limit_changes_enabled else 1}",
    ))
    kb.add(types.InlineKeyboardButton(f"💰 1-я лимитка: {fmt_num(get_setting('manual_limit1_value_usdt', 10.0))} USDT", callback_data="set_manual_limit1_value"))
    kb.add(types.InlineKeyboardButton(f"💰 2-я лимитка: {fmt_num(get_setting('manual_limit2_value_usdt', 10.0))} USDT", callback_data="set_manual_limit2_value"))
    kb.add(types.InlineKeyboardButton("🚫 Монеты-исключения", callback_data="manage_excluded_symbols"))
    kb.add(types.InlineKeyboardButton(f"🕓 Час автобэкапа БД: {int(db_backup_hour)}:00 UTC", callback_data="cycle_db_backup_hour"))
    kb.add(types.InlineKeyboardButton("📤 Прислать бэкап БД сейчас", callback_data="backup_now"))
    kb.add(types.InlineKeyboardButton("🧪 Тест PnL-алерта", callback_data="test_pnl_alert"))
    kb.add(types.InlineKeyboardButton("🔔 Тестовое уведомление", callback_data="test_notify"))
    kb.add(types.InlineKeyboardButton("📜 Журнал уведомлений", callback_data="notification_log"))
    kb.add(types.InlineKeyboardButton("⬅️ Закрыть меню", callback_data="settings_close"))
    return kb


# ----------------------------------------------------------------------------
# Единый бот
# ----------------------------------------------------------------------------

class UnifiedBot:
    def __init__(self, logger):
        self.log = logger
        self.bot = telebot.TeleBot(cfg.TELEGRAM_BOT_TOKEN, parse_mode="HTML", threaded=True)
        self.chat_id = cfg.TELEGRAM_CHAT_ID

        # Telegram ограничивает обычное текстовое сообщение 4096 символами.
        # В этом боте отчёты/журналы и список настроек могут стать длиннее,
        # поэтому перехватываем ВСЕ send_message/edit_message_text и безопасно
        # разбиваем длинный текст на несколько сообщений. Разбивка сначала
        # идёт по переводам строк, чтобы не ломать HTML-теги в большинстве
        # обычных сообщений. Очень длинную одиночную строку режем только как
        # запасной вариант.
        _tg_send_message = self.bot.send_message
        _tg_edit_message_text = self.bot.edit_message_text

        def _split_telegram_text(text, limit=3900):
            text = str(text or "")
            if len(text) <= limit:
                return [text]
            parts = []
            current = []
            current_len = 0
            for line in text.split("\n"):
                add_len = len(line) + (1 if current else 0)
                if current and current_len + add_len > limit:
                    parts.append("\n".join(current))
                    current = []
                    current_len = 0
                if len(line) > limit:
                    if current:
                        parts.append("\n".join(current))
                        current = []
                        current_len = 0
                    while len(line) > limit:
                        parts.append(line[:limit])
                        line = line[limit:]
                    if line:
                        current = [line]
                        current_len = len(line)
                elif line:
                    current.append(line)
                    current_len += add_len
                elif current:
                    # сохраняем пустую строку, если она помещается
                    if current_len + 1 <= limit:
                        current.append("")
                        current_len += 1
            if current or not parts:
                parts.append("\n".join(current))
            return [p for p in parts if p != ""]

        def _safe_send_message(chat_id, text, *args, **kwargs):
            chunks = _split_telegram_text(text)
            first = None
            for idx, chunk in enumerate(chunks):
                call_kwargs = dict(kwargs)
                # Кнопки прикрепляем только к последней части: так меню не
                # дублируется и остаётся на сообщении, с которым работает UI.
                if idx != len(chunks) - 1:
                    call_kwargs.pop("reply_markup", None)
                sent = _tg_send_message(chat_id, chunk, *args, **call_kwargs)
                if first is None:
                    first = sent
            return first

        def _safe_edit_message_text(text, chat_id=None, message_id=None, *args, **kwargs):
            chunks = _split_telegram_text(text)
            if len(chunks) == 1:
                return _tg_edit_message_text(chunks[0], chat_id, message_id, *args, **kwargs)

            # Первую часть редактируем в исходном сообщении, остальные
            # отправляем отдельными сообщениями. Reply-клавиатура остаётся
            # только на первой части редактируемого сообщения.
            result = _tg_edit_message_text(chunks[0], chat_id, message_id, *args, **kwargs)
            send_kwargs = dict(kwargs)
            send_kwargs.pop("reply_markup", None)
            for chunk in chunks[1:]:
                _tg_send_message(chat_id, chunk, *args, **send_kwargs)
            return result

        self.bot.send_message = _safe_send_message
        self.bot.edit_message_text = _safe_edit_message_text

        self._state_lock = threading.Lock()
        self._paused = False
        self._running = True
        self._awaiting_input_key = None   # ключ параметра стратегии, ожидающего ручной ввод
        self._awaiting_stats_input = None  # ("pnl_alert_plus"/"pnl_alert_minus", label) для учёта
        self._awaiting_favorite_add = False  # ждём текст с монетами для добавления в избранное
        self._awaiting_excluded_add = False  # ждём текст с монетами для добавления в исключения
        self._excluded_add_mode = "add"  # "add" или "remove" — что делать с монетами из следующего сообщения
        self._awaiting_signal_margin: Optional[Dict] = None  # разобранный сигнал, ждём сумму (маржу) в USDT
        self._pending_signal: Optional[Dict] = None  # разобранный пост-сигнал, ждущий подтверждения
        self._pending_signal_side_confirm: Optional[Dict] = None  # угаданное направление, ждём подтверждения LONG/SHORT

        self.engine = None    # trading_engine.ShortPumpBot — присоединяется позже
        self.reports = None   # reports.ReportsEngine — присоединяется позже

        # Уведомления шлём через очередь в отдельном потоке-воркере, а не
        # напрямую из notify(). send_message — это блокирующий сетевой вызов
        # к Telegram (от десятков мс до секунд при плохой сети/лимитах), и
        # раньше он выполнялся прямо в торговом потоке — например, ровно
        # перед отправкой ордера на открытие позиции. Каждое уведомление
        # держало сделку заложником сети до Telegram. Очередь с одним
        # воркером убирает эту задержку из горячего пути ПОЛНОСТЬЮ, сохраняя
        # при этом порядок сообщений (FIFO), в отличие от "поток на каждое
        # уведомление".
        self._notify_queue: "queue.Queue[str]" = queue.Queue()
        threading.Thread(target=self._notify_worker, daemon=True, name="tg-notify-worker").start()

        # id закреплённого сообщения с настройками (см. sync_settings_from_pinned
        # / push_settings_pin) — источник истины для настроек, переживающий
        # передеплой на платформах с эфемерной файловой системой (Railway и т.п.)
        self._settings_pin_message_id = None
        self._settings_pin_lock = threading.Lock()
        # Сериализуем сетевые обновления pinned-настроек, чтобы устаревший
        # снимок от параллельного callback не перезаписал более новый.
        self._settings_pin_update_lock = threading.Lock()

        self._register_handlers()
        self._polling_thread = None

    # ---- состояние -----------------------------------------------------

    @property
    def paused(self) -> bool:
        with self._state_lock:
            return self._paused

    @paused.setter
    def paused(self, value: bool):
        with self._state_lock:
            self._paused = value

    @property
    def running(self) -> bool:
        with self._state_lock:
            return self._running

    @running.setter
    def running(self, value: bool):
        with self._state_lock:
            self._running = value

    @property
    def recently_closed_ids(self):
        return self.engine.recently_closed_ids if self.engine else set()

    @property
    def known_symbols(self):
        return set(self.engine._symbols) if self.engine else set()

    def attach(self, engine, reports):
        self.engine = engine
        self.reports = reports

    # ------------------------------------------------------------------
    # Настройки, "приколотые" (pinned) в Telegram — источник истины,
    # переживающий передеплой на Railway (там локальный диск контейнера
    # каждый раз пересоздаётся заново, поэтому переписывание config.py и
    # запись в SQLite не переживают redeploy). Telegram-чат — переживает.
    # ------------------------------------------------------------------

    def _build_settings_snapshot(self) -> Tuple[str, dict]:
        """Возвращает (человекочитаемый_текст, json_с_настройками)."""
        trading = {}
        for key in EDITABLE_SETTINGS:
            trading[key] = get_trading_setting(key)
        for key in TOGGLE_SETTINGS:
            trading[key] = get_trading_setting(key)

        reports_settings = {}
        for key, (py_type, default) in REPORT_SETTINGS_SCHEMA.items():
            reports_settings[key] = get_setting(key, default)

        list_settings = {
            "favorite_symbols": get_favorite_symbols(),
            "excluded_symbols": get_excluded_symbols(),
        }

        payload = {"trading": trading, "reports": reports_settings, "lists": list_settings}

        # Машиночитаемый JSON ставим В НАЧАЛО сообщения. Это важно: общий
        # Telegram-wrapper может разбить длинное сообщение на несколько частей,
        # а закреплённой остаётся первая часть. sync_settings_from_pinned()
        # использует raw_decode(), поэтому после JSON может безопасно идти
        # обычный человекочитаемый текст.
        settings_json = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
        lines = [
            f"{SETTINGS_PIN_MARKER}{settings_json}",
            "📌 <b>Настройки бота (не удаляй и не редактируй вручную это сообщение!)</b>",
            "Бот хранит здесь свои текущие настройки, чтобы они не терялись при "
            "передеплое на Railway. Меняй настройки только через меню бота — "
            "оно само обновит это сообщение.",
            "",
            "⚙️ <b>Стратегия:</b>",
        ]
        for key, meta in EDITABLE_SETTINGS.items():
            lines.append(f"  {meta['label']}: {fmt_num(trading[key])}{meta['suffix']}")
        for key, label in TOGGLE_SETTINGS.items():
            lines.append(f"  {label}: {'вкл' if trading[key] else 'выкл'}")
        lines.append("")
        lines.append("⚙️ <b>Учёт и отчётность:</b>")
        lines.append(f"  Уведомления о сделках: {'вкл' if reports_settings['notify_new_trade'] else 'выкл'}")
        lines.append(f"  Ежедневный отчёт: {'вкл в ' + str(int(reports_settings['daily_report_hour'])) + ':00 UTC' if reports_settings['enable_daily_report'] else 'выкл'}")
        lines.append(f"  Еженедельный отчёт: {'вкл' if reports_settings['enable_weekly_report'] else 'выкл'}")
        lines.append(f"  Риск-алерт (сутки): {reports_settings['max_daily_loss_alert']:g} USDT" if reports_settings["max_daily_loss_alert"] else "  Риск-алерт (сутки): выкл")
        lines.append(f"  Алерт по прибыли/сделке: {reports_settings['pnl_alert_plus']:g} USDT" if reports_settings["pnl_alert_plus"] else "  Алерт по прибыли/сделке: выкл")
        lines.append(f"  Алерт по убытку/сделке: {reports_settings['pnl_alert_minus']:g} USDT" if reports_settings["pnl_alert_minus"] else "  Алерт по убытку/сделке: выкл")
        lines.append(f"  Тихие часы: {reports_settings['quiet_hours'] or 'выкл'}")
        lines.append(f"  Часовой пояс отчётов: UTC{int(reports_settings['tz_offset']):+d}")
        lines.append(f"  Уведомления о проблемах связи: {'вкл' if reports_settings['notify_connection_issues'] else 'выкл'}")
        lines.append(f"  Автобэкап БД в Telegram: {'вкл в ' + str(int(reports_settings['db_backup_hour'])) + ':00 UTC' if reports_settings['enable_db_backup'] else 'выкл'}")
        lines.append(f"  Только уведомления о закрытии сделок: {'вкл' if reports_settings['only_trade_close_notifications'] else 'выкл'}")
        lines.append(f"  Ручные сделки: стоп {fmt_num(reports_settings['manual_trade_stop_percent'])}%")
        lines.append(f"  Номинал 1-й ручной лимитки: {fmt_num(reports_settings['manual_limit1_value_usdt'])} USDT (max-плечо)")
        lines.append(f"  Номинал 2-й ручной лимитки: {fmt_num(reports_settings['manual_limit2_value_usdt'])} USDT (max-плечо)")
        bot_tp_moves, bot_tp_closes = get_bot_tp_config()
        lines.append("  4 тейка (бот + ручные): " + " · ".join(f"TP{i+1} +{fmt_num(bot_tp_moves[i])}% / {fmt_num(bot_tp_closes[i])}%" if i < 3 else f"TP4 +{fmt_num(bot_tp_moves[i])}% / 100% остатка" for i in range(4)))
        lines.append(f"  Избранные монеты: {', '.join(list_settings['favorite_symbols']) or 'нет'}")
        lines.append(f"  Монеты-исключения: {', '.join(list_settings['excluded_symbols']) or 'нет'}")
        lines.append("")
        text = "\n".join(lines)
        return text, payload

    def _apply_settings_payload(self, payload: dict):
        trading = payload.get("trading", {}) or {}
        for key, value in trading.items():
            try:
                if key in EDITABLE_SETTINGS:
                    meta = EDITABLE_SETTINGS[key]
                    persist_trading_setting(key, meta["type"](value))
                elif key in TOGGLE_SETTINGS:
                    persist_trading_setting(key, bool(value))
            except Exception:
                self.log.exception(f"Не удалось восстановить настройку стратегии {key} из закреплённого сообщения")

        reports_settings = payload.get("reports", {}) or {}
        list_settings = payload.get("lists", {}) or {}
        updates = {}
        for key, value in reports_settings.items():
            if key not in REPORT_SETTINGS_SCHEMA:
                continue
            try:
                py_type, _default = REPORT_SETTINGS_SCHEMA[key]
                if key == "manual_trade_stop_percent":
                    value = min(10.0, max(1.0, float(value)))
                elif key == "manual_trade_tp_close_percent":
                    value = min(100, max(1, int(float(value))))
                elif key.startswith("bot_tp"):
                    # Preserve explicit False; never numeric-clamp an enabled flag.
                    if key.endswith("_enabled"):
                        if isinstance(value, str):
                            value = value.strip().lower() in {"1", "true", "yes", "on", "вкл", "включен", "включён"}
                        else:
                            value = bool(value)
                    else:
                        value = max(0.01, min(100.0, float(value)))
                        if key == "bot_tp4_close_pct":
                            value = 100.0
                if py_type is bool:
                    parsed_bool = _parse_bool_setting_value(value, None)
                    if parsed_bool is None:
                        raise ValueError(f"ожидалось булево значение, получено {value!r}")
                    value = parsed_bool
                else:
                    value = py_type(value)
                    if isinstance(value, float) and not math.isfinite(value):
                        raise ValueError(f"числовая настройка не конечна: {value!r}")
                updates[f"setting_{key}"] = str(value)
            except Exception:
                self.log.exception("Не удалось разобрать настройку учёта %s из закреплённого сообщения", key)

        try:
            if "favorite_symbols" in list_settings:
                seen = []
                for item in list_settings["favorite_symbols"]:
                    item = str(item).upper().strip()
                    if item and item not in seen:
                        seen.append(item)
                updates["favorite_symbols"] = json.dumps(seen)
            if "excluded_symbols" in list_settings:
                seen = []
                for item in list_settings["excluded_symbols"]:
                    item = str(item).upper().strip()
                    if item and item not in seen:
                        seen.append(item)
                updates["excluded_symbols"] = json.dumps(seen)
        except Exception:
            self.log.exception("Не удалось разобрать списки монет из закреплённого сообщения")

        if updates:
            last_error = None
            for attempt in range(1, 4):
                try:
                    with _db_lock:
                        if _conn.in_transaction:
                            _conn.rollback()
                        _conn.execute("BEGIN IMMEDIATE")
                        _conn.executemany(
                            "INSERT INTO meta(key,value) VALUES(?,?) "
                            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                            list(updates.items()),
                        )
                        _conn.commit()
                    break
                except Exception as exc:
                    last_error = exc
                    try:
                        with _db_lock:
                            _conn.rollback()
                    except Exception:
                        pass
                    self.log.exception("Не удалось атомарно сохранить настройки/списки в SQLite (попытка %s/3)", attempt)
                    if attempt < 3:
                        time.sleep(0.2 * attempt)
            else:
                raise RuntimeError("Не удалось сохранить настройки/списки из закреплённого сообщения в SQLite") from last_error

    def _settings_persistence_text(self) -> str:
        """Формирует компактный V5-снимок настроек.

        Первая строка содержит сжатые scalar-настройки, вторая — отдельно
        сжатые списки монет. Разделение блоков даёт больший запас по лимиту
        Telegram и позволяет хранить большой список исключений.
        """
        _text, payload = self._build_settings_snapshot()

        quote = str(getattr(cfg, "QUOTE_COIN", "USDT")).upper()
        def _compact_symbol(symbol: str) -> str:
            value = str(symbol).upper().strip()
            if value.endswith(quote) and len(value) > len(quote):
                return value[:-len(quote)]
            return "=" + value

        scalar_payload = {
            "v": 5,
            "trading": payload.get("trading", {}),
            "reports": payload.get("reports", {}),
        }
        lists_payload = {
            "q": quote,
            "favorites": [_compact_symbol(x) for x in payload.get("lists", {}).get("favorite_symbols", [])],
            "excluded": [_compact_symbol(x) for x in payload.get("lists", {}).get("excluded_symbols", [])],
        }

        scalar_json = json.dumps(scalar_payload, ensure_ascii=False, separators=(",", ":"))
        lists_json = json.dumps(lists_payload, ensure_ascii=False, separators=(",", ":"))
        scalar_packed = base64.urlsafe_b64encode(zlib.compress(scalar_json.encode("utf-8"), level=9)).decode("ascii")
        lists_packed = base64.urlsafe_b64encode(zlib.compress(lists_json.encode("utf-8"), level=9)).decode("ascii")

        header = f"{SETTINGS_PIN_MARKER}{scalar_packed}"
        lists_line = f"{SETTINGS_PIN_LISTS_MARKER}{lists_packed}"

        excluded = get_excluded_symbols()
        summary = (
            "📌 <b>Сохранённые настройки</b>\n"
            f"🛑 Стоп {fmt_num(get_manual_stop_percent())}% · "
            f"✂️ TP {get_manual_tp_close_percent()}% · "
            f"🚫 Исключений {len(excluded)}"
        )
        result = f"{header}\n{lists_line}\n{summary}"
        if len(result) > SETTINGS_PIN_MAX_CHARS:
            raise ValueError(
                f"Снимок настроек слишком большой: {len(result)} символов "
                f"(лимит безопасного блока {SETTINGS_PIN_MAX_CHARS})"
            )
        return result

    def _apply_pinned_settings_text(self, text: str) -> bool:
        """Восстанавливает V5/V4/V3 compressed либо старые V2/V1 JSON-снимки."""
        if SETTINGS_PIN_MARKER in text:
            lines = text.splitlines()
            first = lines[0].strip()
            scalar_packed = first.split(SETTINGS_PIN_MARKER, 1)[1].strip()
            scalar_raw = zlib.decompress(
                base64.urlsafe_b64decode(scalar_packed.encode("ascii"))
            ).decode("utf-8")
            scalar_payload, _end_idx = json.JSONDecoder().raw_decode(scalar_raw)

            lists_payload = {"q": getattr(cfg, "QUOTE_COIN", "USDT"), "favorites": [], "excluded": []}
            for line in lines[1:]:
                if line.startswith(SETTINGS_PIN_LISTS_MARKER):
                    lists_packed = line.split(SETTINGS_PIN_LISTS_MARKER, 1)[1].strip()
                    lists_raw = zlib.decompress(
                        base64.urlsafe_b64decode(lists_packed.encode("ascii"))
                    ).decode("utf-8")
                    lists_payload, _lists_end = json.JSONDecoder().raw_decode(lists_raw)
                    break

            quote = str(lists_payload.get("q") or getattr(cfg, "QUOTE_COIN", "USDT")).upper()
            def _expand_symbol(value: str) -> str:
                value = str(value).upper().strip()
                if value.startswith("="):
                    return value[1:]
                return value + quote

            payload = {
                "trading": scalar_payload.get("trading", {}),
                "reports": scalar_payload.get("reports", {}),
                "lists": {
                    "favorite_symbols": [_expand_symbol(x) for x in lists_payload.get("favorites", [])],
                    "excluded_symbols": [_expand_symbol(x) for x in lists_payload.get("excluded", [])],
                },
            }
        elif SETTINGS_PIN_MARKER_V4 in text:
            payload_part = text.split(SETTINGS_PIN_MARKER_V4, 1)[1]
            packed = payload_part.splitlines()[0].strip()
            raw_json = zlib.decompress(
                base64.urlsafe_b64decode(packed.encode("ascii"))
            ).decode("utf-8")
            payload, _end_idx = json.JSONDecoder().raw_decode(raw_json)
            if isinstance(payload, dict) and payload.get("v") == 4 and ("favorites" in payload or "excluded" in payload):
                quote = str(payload.get("q") or getattr(cfg, "QUOTE_COIN", "USDT")).upper()
                def _expand_symbol(value: str) -> str:
                    value = str(value).upper().strip()
                    return value[1:] if value.startswith("=") else value + quote
                payload = {
                    "trading": payload.get("trading", {}),
                    "reports": payload.get("reports", {}),
                    "lists": {
                        "favorite_symbols": [_expand_symbol(x) for x in payload.get("favorites", [])],
                        "excluded_symbols": [_expand_symbol(x) for x in payload.get("excluded", [])],
                    },
                }
        elif SETTINGS_PIN_MARKER_ZLIB_V3 in text:
            payload_part = text.split(SETTINGS_PIN_MARKER_ZLIB_V3, 1)[1]
            packed = payload_part.splitlines()[0].strip()
            raw_json = zlib.decompress(
                base64.urlsafe_b64decode(packed.encode("ascii"))
            ).decode("utf-8")
            payload, _end_idx = json.JSONDecoder().raw_decode(raw_json)
        else:
            marker = (
                SETTINGS_PIN_MARKER_V2 if SETTINGS_PIN_MARKER_V2 in text
                else SETTINGS_PIN_MARKER_LEGACY if SETTINGS_PIN_MARKER_LEGACY in text
                else None
            )
            if not marker:
                return False
            json_part = text.split(marker, 1)[1].strip()
            payload, _end_idx = json.JSONDecoder().raw_decode(json_part)

        if not isinstance(payload, dict):
            raise ValueError("закреплённый снимок настроек имеет неверный формат")
        self._apply_settings_payload(payload)
        return True

    def sync_settings_from_pinned(self):
        """Вызывается один раз при старте. Восстанавливает настройки из
        закреплённого сообщения Telegram. Поддерживает и старый V1, чтобы
        уже существующие настройки не потерялись при первом обновлении.
        """
        if not self.chat_id:
            return
        try:
            chat = self.bot.get_chat(self.chat_id)
            pinned = getattr(chat, "pinned_message", None)
            if pinned is None:
                self.log.info("Закреплённого сообщения с настройками не найдено (первый запуск) — создаю новое.")
                return

            text = pinned.text or pinned.caption or ""
            if not self._apply_pinned_settings_text(text):
                self.log.info("Закреплённое сообщение не содержит настроек бота — будет создано новое.")
                return

            with self._settings_pin_lock:
                self._settings_pin_message_id = pinned.message_id
            self.log.info("Настройки восстановлены из закреплённого сообщения в Telegram.")
        except Exception:
            # Не падаем на старте из-за повреждённого/старого pin. После этого
            # main() вызовет push_settings_pin(), который создаст корректный
            # компактный V4-снимок.
            with self._settings_pin_lock:
                self._settings_pin_message_id = None
            self.log.exception("Не удалось прочитать закреплённые настройки из Telegram (будет создан новый снимок)")

    def push_settings_pin(self) -> bool:
        """Сохраняет актуальные настройки в закреплённом сообщении Telegram.

        True возвращается только после подтверждённого обновления/создания pin.
        Параллельные обновления сериализованы, чтобы устаревший снимок не
        перезаписал более новый после задержки сети.
        """
        with self._settings_pin_update_lock:
            return self._push_settings_pin_serialized()

    def _push_settings_pin_serialized(self) -> bool:
        if not self.chat_id:
            return False

        try:
            text = self._settings_persistence_text()
        except Exception:
            self.log.exception("Не удалось подготовить компактный снимок настроек для Telegram")
            return False

        with self._settings_pin_lock:
            message_id = self._settings_pin_message_id

        if message_id is not None:
            try:
                # Используем один короткий текст, поэтому наш общий wrapper
                # не сможет разделить JSON на несколько сообщений.
                self.bot.edit_message_text(text, self.chat_id, message_id)
                return True
            except Exception as e:
                if "not modified" in str(e).lower():
                    return True
                self.log.info("Не удалось обновить старое закреплённое сообщение — создаю новое: %s", e)
                with self._settings_pin_lock:
                    self._settings_pin_message_id = None

        try:
            sent = self.bot.send_message(self.chat_id, text)
            self.bot.pin_chat_message(self.chat_id, sent.message_id, disable_notification=True)
            with self._settings_pin_lock:
                self._settings_pin_message_id = sent.message_id
            return True
        except Exception:
            self.log.exception("Не удалось создать/закрепить сообщение с настройками")
            return False

    def notify(self, text: str, important: bool = False):
        if not self.chat_id:
            return
        if not important and get_setting("only_trade_close_notifications", getattr(cfg, "ONLY_TRADE_CLOSE_NOTIFICATIONS", False)):
            # Режим "только уведомления о закрытии сделок" — всё остальное
            # (heartbeat, вход в сделку, отчёты, риск-алерты и т.п.) молчит.
            return
        # Не блокируем вызывающий поток на сетевом походе к Telegram — просто
        # кладём сообщение в очередь, реальную отправку делает _notify_worker.
        self._notify_queue.put(text)

    def _notify_worker(self):
        while True:
            text = self._notify_queue.get()
            try:
                self.bot.send_message(self.chat_id, text)
                log_notification(text)
            except Exception:
                self.log.warning("Не удалось отправить сообщение в Telegram")
            finally:
                self._notify_queue.task_done()

    def flush_notifications(self, timeout: float = 3.0):
        """Ждёт, пока очередь уведомлений опустеет (с таймаутом). Вызывается
        перед завершением процесса (сигнал остановки, передеплой) — иначе
        последнее сообщение ("бот остановлен" и т.п.) рискует потеряться:
        _notify_worker — демон-поток, и его убьют вместе с процессом раньше,
        чем он успеет отправить то, что уже лежит в очереди."""
        done = threading.Event()

        def _joiner():
            self._notify_queue.join()
            done.set()

        threading.Thread(target=_joiner, daemon=True, name="notify-flush").start()
        done.wait(timeout)

    def is_allowed(self, chat_id) -> bool:
        if not self.chat_id:
            return True
        return str(chat_id) == str(self.chat_id)

    def _safe(self, handler_fn):
        def wrapper(*args, **kwargs):
            try:
                handler_fn(*args, **kwargs)
            except Exception as e:
                self.log.exception("Ошибка в обработчике Telegram")
                try:
                    chat_id = args[0].chat.id if hasattr(args[0], "chat") else args[0].message.chat.id
                    self.bot.send_message(chat_id, f"⚠️ Внутренняя ошибка: {e}")
                except Exception:
                    pass
        return wrapper

    # ---- рендеры, общие для нескольких кнопок --------------------------

    def _render_status(self) -> str:
        state = "⏸ <b>На паузе</b>" if self.paused else ("🟢 <b>Работает</b>" if self.running else "🔴 <b>Остановлен</b>")
        mode = "🧪 Testnet" if cfg.TESTNET else "🔥 Боевой рынок"
        dry = "да (ордера не отправляются)" if cfg.DRY_RUN else "нет (реальная торговля)"
        summary = self.engine.build_status_summary() if self.engine else "движок ещё не готов"
        return f"📊 <b>Статус торгового движка</b>\n━━━━━━━━━━━━━━━\nСостояние: {state}\nРежим: {mode}\nDry-run: {dry}\n\n<b>Параметры стратегии:</b>\n{summary}"

    def _render_history(self) -> str:
        records = read_trade_history(limit=10)
        if not records:
            return "🕘 <b>История сделок движка</b>\n━━━━━━━━━━━━━━━\nПока нет закрытых сделок."
        priced = [r for r in records if r.get("pnl") is not None]
        wins = sum(1 for r in priced if r["pnl"] > 0)
        total_pnl = sum(r["pnl"] for r in priced)
        pending_note = f" (+{len(records) - len(priced)} ждут уточнения)" if len(priced) < len(records) else ""
        lines = ["🕘 <b>История сделок движка</b> (последние 10)", "━━━━━━━━━━━━━━━", f"Винрейт: <b>{wins}/{len(priced)}</b> · Суммарный PnL: <b>{total_pnl:.2f} USDT</b>{pending_note}\n"]
        for r in reversed(records):
            pnl = r.get("pnl")
            if pnl is None:
                lines.append(f"⏳ <b>{r['symbol']}</b>: PnL уточняется (появится после синхронизации)")
                continue
            emoji = "🟢" if pnl >= 0 else "🔴"
            exit_type = {"tp_or_manual": "TP/вручную", "profit_lock": "защита прибыли", "smart_exit": "умный выход", "stop_loss": "стоп-лосс"}.get(r.get("exit_type"), r.get("exit_type", "?"))
            lines.append(f"{emoji} <b>{r['symbol']}</b>: {pnl:.2f} USDT ({exit_type})")
        return "\n".join(lines)

    # ---- регистрация хендлеров ------------------------------------------

    def _register_handlers(self):
        bot = self.bot

        @bot.message_handler(commands=["start", "help", "menu"])
        @self._safe
        def _start(message):
            if not self.is_allowed(message.chat.id):
                return
            # На случай, если пользователь застрял в ожидании ввода (число
            # для настройки, тикеры для избранного и т.п.) — /start всегда
            # должен возвращать в чистое состояние, а не тихо ждать ввод,
            # который человек уже не собирается присылать.
            self._awaiting_input_key = None
            self._awaiting_stats_input = None
            self._awaiting_favorite_add = False
            self._awaiting_excluded_add = False
            self._awaiting_signal_margin = None
            self._pending_signal_side_confirm = None
            self._pending_signal = None
            bot.send_message(
                message.chat.id,
                "Привет! Я объединённый бот: торгую по стратегии «памп → шорт» и веду учёт сделок Bybit "
                "с отчётами и алертами.\n\n"
                f"Твой chat_id: <code>{message.chat.id}</code>\n\n"
                "Кнопки снизу — быстрый доступ.",
                reply_markup=reply_keyboard(self.paused),
            )

        @bot.message_handler(commands=["cancel"])
        @self._safe
        def _cancel(message):
            if not self.is_allowed(message.chat.id):
                return
            was_waiting = self._awaiting_input_key is not None or self._awaiting_stats_input is not None or self._awaiting_favorite_add or self._awaiting_excluded_add or self._awaiting_signal_margin is not None or self._pending_signal_side_confirm is not None or self._pending_signal is not None
            self._awaiting_input_key = None
            self._awaiting_stats_input = None
            self._awaiting_favorite_add = False
            self._awaiting_excluded_add = False
            self._awaiting_signal_margin = None
            self._pending_signal_side_confirm = None
            self._pending_signal = None
            bot.send_message(message.chat.id, "Отменено." if was_waiting else "Нечего отменять.", reply_markup=reply_keyboard(self.paused))

        @bot.message_handler(func=lambda m: (
            self._awaiting_input_key is None and self._awaiting_stats_input is None
            and not self._awaiting_favorite_add and not self._awaiting_excluded_add and self._awaiting_signal_margin is None
            and self._pending_signal_side_confirm is None and self._pending_signal is None
            and parse_signal_post(m.text or "") is not None
        ))
        @self._safe
        def _signal_post(message):
            if not self.is_allowed(message.chat.id):
                return
            self._handle_signal_post(message)

        @bot.message_handler(func=lambda m: m.text in {
            BTN_QUICK_STATUS, BTN_STATS, BTN_POSITIONS, BTN_LIMIT_ORDERS, BTN_CHART, BTN_TOP_TRADES, BTN_TABLE, BTN_FEES, BTN_EXPORT,
            BTN_BALANCE, BTN_SYNC, BTN_HISTORY, BTN_STATUS, BTN_CHECK_CONN, BTN_BACKUP,
            BTN_TRADE_SETTINGS, BTN_REPORT_SETTINGS, BTN_FAVORITES, "⏸ Пауза торговли", "▶️ Продолжить торговлю",
        })
        @self._safe
        def _reply_kb(message):
            if not self.is_allowed(message.chat.id):
                return
            chat_id = message.chat.id
            text = message.text

            if text == BTN_QUICK_STATUS:
                bot.send_message(chat_id, "Считаю быстрый статус...")
                bot.send_message(chat_id, self.reports.build_quick_status_message(), reply_markup=back_menu())
            elif text == BTN_STATS:
                bot.send_message(chat_id, "За какой период показать статистику?", reply_markup=period_menu("stats"))
            elif text == BTN_POSITIONS:
                bot.send_message(chat_id, "Загружаю позиции...")
                bot.send_message(chat_id, self.reports.build_open_positions_message(), reply_markup=back_menu())
            elif text == BTN_LIMIT_ORDERS:
                bot.send_message(chat_id, "Считываю открытые лимитки с Bybit...")
                report = self.reports.build_open_limit_orders_message()
                # Telegram ограничивает одно сообщение примерно 4096 символами.
                # Делим только по строкам, чтобы не разрывать HTML-теги/записи.
                chunks = []
                current = ""
                for line in report.splitlines():
                    candidate = (current + "\n" + line) if current else line
                    if len(candidate) > 3800 and current:
                        chunks.append(current)
                        current = line
                    else:
                        current = candidate
                if current:
                    chunks.append(current)
                for index, chunk in enumerate(chunks):
                    bot.send_message(chat_id, chunk, parse_mode="HTML", reply_markup=back_menu() if index == len(chunks) - 1 else None)
            elif text == BTN_CHART:
                bot.send_message(chat_id, "За какой период построить график капитала?", reply_markup=period_menu("chart"))
            elif text == BTN_TOP_TRADES:
                bot.send_message(chat_id, "За какой период показать топ сделок?", reply_markup=period_menu("top"))
            elif text == BTN_TABLE:
                bot.send_message(chat_id, "За какой период показать таблицу сделок?", reply_markup=period_menu("table"))
            elif text == BTN_FEES:
                bot.send_message(chat_id, "За какой период показать комиссии?", reply_markup=period_menu("fees"))
            elif text == BTN_EXPORT:
                bot.send_message(chat_id, "За какой период выгрузить CSV?", reply_markup=period_menu("export"))
            elif text == BTN_BALANCE:
                bot.send_message(chat_id, self.reports.get_balance_message(), reply_markup=back_menu())
            elif text == BTN_SYNC:
                saved = self.reports.sync_trades(silent_notify=True)
                total = total_trade_count()
                bot.send_message(chat_id, f"✅ Готово.\nНовых сделок сохранено: {saved}\nВсего в базе: {total}", reply_markup=back_menu())
            elif text == BTN_HISTORY:
                bot.send_message(chat_id, self._render_history(), reply_markup=back_menu())
            elif text == "⏸ Пауза торговли" or text == "▶️ Продолжить торговлю":
                self.paused = not self.paused
                txt = "⏸ <b>Пауза включена.</b>\nНовые позиции открываться не будут, уже открытые продолжаю вести." if self.paused else "▶️ <b>Продолжаю торговлю.</b>"
                bot.send_message(chat_id, txt, reply_markup=reply_keyboard(self.paused))
            elif text == BTN_STATUS:
                bot.send_message(chat_id, self._render_status() + "\n\n" + self.reports.build_status_message(), reply_markup=back_menu())
            elif text == BTN_CHECK_CONN:
                bot.send_message(chat_id, "Проверяю...")
                bot.send_message(chat_id, self.reports.check_connection(), reply_markup=back_menu())
            elif text == BTN_BACKUP:
                self.reports.send_db_backup(caption="💾 Бэкап базы сделок по запросу", reply_markup=back_menu())
            elif text == BTN_TRADE_SETTINGS:
                bot.send_message(chat_id, "⚙️ <b>Настройки стратегии</b>\n\nНажми на параметр, чтобы изменить значение:", reply_markup=trade_settings_menu())
            elif text == BTN_REPORT_SETTINGS:
                bot.send_message(chat_id, "⚙️ <b>Настройки учёта и уведомлений</b>", reply_markup=report_settings_menu())
            elif text == BTN_FAVORITES:
                bot.send_message(chat_id, favorites_status_text(), reply_markup=favorites_menu())

        @bot.message_handler(func=lambda m: m.text == BTN_STOP)
        @bot.message_handler(commands=["stop"])
        @self._safe
        def _stop(message):
            if not self.is_allowed(message.chat.id):
                return
            kb = types.InlineKeyboardMarkup()
            kb.add(types.InlineKeyboardButton("✅ Да, остановить торговлю", callback_data="confirm_stop"), types.InlineKeyboardButton("❌ Отмена", callback_data="cancel_stop"))
            bot.send_message(message.chat.id, "❗ Точно остановить торговый движок полностью? (учёт/отчёты продолжат работать)", reply_markup=kb)

        @bot.message_handler(func=lambda m: self._awaiting_input_key is not None or self._awaiting_stats_input is not None or self._awaiting_favorite_add or self._awaiting_excluded_add or self._awaiting_signal_margin is not None)
        @self._safe
        def _handle_typed_value(message):
            if not self.is_allowed(message.chat.id):
                return
            if self._awaiting_input_key is not None:
                self._process_typed_trading_value(message)
            elif self._awaiting_stats_input is not None:
                self._process_typed_stats_value(message)
            elif self._awaiting_favorite_add:
                self._process_favorite_add(message)
            elif self._awaiting_excluded_add:
                self._process_excluded_add(message)
            elif self._awaiting_signal_margin is not None:
                self._process_signal_margin_input(message)

        @bot.callback_query_handler(func=lambda call: True)
        @self._safe
        def _handle_callback(call):
            if not self.is_allowed(call.message.chat.id):
                return
            self._dispatch_callback(call)

    # ---- ручной ввод: параметр стратегии --------------------------------

    def _process_typed_trading_value(self, message):
        key = self._awaiting_input_key
        self._awaiting_input_key = None
        meta = EDITABLE_SETTINGS[key]
        try:
            raw = message.text.strip().replace(",", ".")
            new_value = meta["type"](float(raw))
        except (ValueError, TypeError):
            self.bot.send_message(message.chat.id, "⚠️ Не понял значение, попробуй ещё раз через «⚙️ Настройки стратегии».")
            return
        if not (meta["min"] <= new_value <= meta["max"]):
            self.bot.send_message(message.chat.id, f"⚠️ Значение должно быть в диапазоне {fmt_num(meta['min'])}–{fmt_num(meta['max'])}{meta['suffix']}.")
            return
        persist_trading_setting(key, new_value)
        self.push_settings_pin()
        self.bot.send_message(message.chat.id, f"✅ <b>{meta['label']}</b> изменено на <b>{fmt_num(new_value)}{meta['suffix']}</b>", reply_markup=reply_keyboard(self.paused))

    # ---- ручной ввод: добавление избранных монет -------------------------

    def _process_favorite_add(self, message):
        self._awaiting_favorite_add = False
        chat_id = message.chat.id
        text = (message.text or "").strip()
        if text.startswith("/cancel"):
            self.bot.send_message(chat_id, "Отменено.", reply_markup=favorites_menu())
            return

        raw_tokens = [t for t in re.split(r"[,\s]+", text.upper()) if t]
        if not raw_tokens:
            self.bot.send_message(chat_id, "⚠️ Не понял список монет. Пришли тикеры через запятую или пробел, например: <code>BTC, ETH, SOLUSDT</code>", reply_markup=favorites_menu())
            return

        added = add_favorite_symbols(raw_tokens)
        self.push_settings_pin()

        # Сверяем с реальным списком торгуемых на бирже пар — просто для
        # предупреждения, добавляем в избранное в любом случае (например,
        # список пар у бота мог ещё не обновиться).
        known_symbols = self.known_symbols
        unknown = [s for s in added if known_symbols and s not in known_symbols]

        if added:
            msg = f"✅ Добавлено в избранное: {', '.join(added)}"
            if unknown:
                msg += f"\n\n⚠️ Не нашёл на бирже как бессрочный USDT-контракт: {', '.join(unknown)} — проверь тикер, если это не опечатка, бот всё равно будет пытаться его торговать."
        else:
            msg = "Все перечисленные монеты уже в избранном."
        self.bot.send_message(chat_id, msg + "\n\n" + favorites_status_text(), reply_markup=favorites_menu())

    # ---- ручной ввод: добавление монет-исключений -------------------------

    def _process_excluded_add(self, message):
        self._awaiting_excluded_add = False
        mode = getattr(self, "_excluded_add_mode", "add")
        chat_id = message.chat.id
        text = (message.text or "").strip()
        if text.startswith("/cancel"):
            self.bot.send_message(chat_id, "Отменено.", reply_markup=report_settings_menu())
            return

        raw_tokens = [t for t in re.split(r"[,\s]+", text.upper()) if t]
        if not raw_tokens:
            self.bot.send_message(chat_id, "⚠️ Не понял список монет. Пришли тикеры через запятую или пробел, например: <code>BTC, ETH, SOLUSDT</code>", reply_markup=report_settings_menu())
            return

        if mode == "remove":
            removed = remove_excluded_symbols(raw_tokens)
            current = get_excluded_symbols()
            msg = f"✅ Убрано из исключений: {', '.join(removed)}" if removed else "Ни одной из перечисленных монет не было в исключениях."
        else:
            added = add_excluded_symbols(raw_tokens)
            current = get_excluded_symbols()
            if added:
                msg = f"🚫 Добавлено в исключения: {', '.join(added)}\n\nБот больше не будет ставить тейки/стопы и брать под управление эти монеты ни по постам, ни вручную открытые."
            else:
                msg = "Все перечисленные монеты уже в исключениях."
        # Важно: список исключений меняется динамически и должен сразу попасть
        # в закреплённый снимок, иначе после redeploy восстановится старый список.
        self.push_settings_pin()
        msg += "\n\nТекущий список исключений: " + (", ".join(current) if current else "пусто")
        self.bot.send_message(chat_id, msg, reply_markup=report_settings_menu())

    # ---- ручной ввод: порог PnL-алерта учёта -----------------------------

    def _process_typed_stats_value(self, message):
        setting_name, label = self._awaiting_stats_input
        self._awaiting_stats_input = None
        chat_id = message.chat.id
        text = (message.text or "").strip().replace(",", ".")
        if text.startswith("/cancel"):
            self.bot.send_message(chat_id, "Отменено.", reply_markup=report_settings_menu())
            return

        # Ручная настройка 4 тейков: TP1-TP3 принимают пару
        # «движение% закрытия%». TP4 принимает движение; его закрытие всегда
        # 100% остатка, чтобы последняя цель гарантированно завершала сделку.
        if setting_name.endswith("_pair"):
            try:
                parts = text.split()
                if len(parts) != 2:
                    raise ValueError
                tp_no = int(setting_name[len("bot_tp")])
                move = float(parts[0])
                close = float(parts[1])
                if not (0.01 <= move <= 100.0 and 0.1 <= close <= 99.0):
                    raise ValueError
                moves, closes = get_bot_tp_config()
                moves[tp_no-1] = move
                closes[tp_no-1] = close
                err = _bot_tp_validate_moves(moves, get_bot_tp_enabled()) or _bot_tp_validate_closes(closes, get_bot_tp_enabled())
                if err:
                    raise ValueError(err)
                set_setting(f"bot_tp{tp_no}_move_pct", move)
                set_setting(f"bot_tp{tp_no}_close_pct", close)
            except ValueError as e:
                self._awaiting_stats_input = (setting_name, label)
                msg = str(e) if str(e) else "Формат: движение% закрытия%, например <code>1.0 25</code>."
                self.bot.send_message(chat_id, f"⚠️ {msg}\nПопробуй ещё раз или /cancel.")
                return
            self.push_settings_pin()
            updated, failed = (self.reports.apply_manual_settings_to_open_positions(reason=f"изменён план TP{tp_no}") if self.reports else (0, 0))
            suffix = f" Применено к {updated} открытым ручным позициям." + (f" Ошибок: {failed}." if failed else "")
            self.bot.send_message(chat_id, f"✅ TP{tp_no}: движение +{fmt_num(move)}%, закрытие {fmt_num(close)}% исходной позиции.{suffix}", reply_markup=report_settings_menu())
            return

        if setting_name == "manual_trade_stop_percent":
            try:
                # Подсказка Telegram разрешает десятичную запятую; нормализуем
                # ровно её, сохраняя строгий отказ для строк с несколькими разделителями.
                normalized_stop_text = str(text).strip().replace(",", ".")
                value = float(normalized_stop_text)
                if not math.isfinite(value) or not (1.0 <= value <= 10.0):
                    raise ValueError
                set_setting("manual_trade_stop_percent", value)
                persisted_stop = get_manual_stop_percent()
                if not math.isfinite(persisted_stop) or abs(persisted_stop - value) > 1e-9:
                    raise RuntimeError(
                        f"проверка чтения настройки вернула {persisted_stop!r}, ожидалось {value}"
                    )
            except ValueError:
                self._awaiting_stats_input = (setting_name, label)
                self.bot.send_message(
                    chat_id,
                    "⚠️ Введи число от <b>1 до 10%</b>, например <code>2.5</code> или <code>4,25</code>.\n"
                    "Значение за пределами диапазона не принято. Попробуй ещё раз или /cancel."
                )
                return
            except Exception as exc:
                self.log.exception("Не удалось сохранить процент стопа ручных сделок")
                self.bot.send_message(
                    chat_id,
                    f"⛔ Не удалось подтвердить сохранение процента стопа в SQLite. Стопы на бирже не менялись. Ошибка: {exc}",
                    reply_markup=report_settings_menu(),
                )
                return
            pin_saved = self.push_settings_pin()
            if self.reports:
                try:
                    updated, failed = self.reports.apply_manual_settings_to_open_positions(
                        reason=f"ручной ввод стопа {value:g}%", force_stop_from_l2=True
                    )
                    updated, failed = max(0, int(updated)), max(0, int(failed))
                except Exception:
                    # Сохранённая настройка остаётся в SQLite, но сбой применения
                    # не должен молча лишать пользователя результата операции.
                    updated, failed = 0, 1
                    self.log.exception("Не удалось применить вручную введённый процент стопа к открытым позициям")
            else:
                updated, failed = 0, 1
                self.log.error("Нельзя применить введённый ручной стоп: менеджер ручных сделок недоступен")
            suffix = f" Применено к {updated} открытым ручным позициям."
            if failed:
                suffix += f" Ошибок применения: {failed}. Проверь позиции и стопы на бирже."
            if not pin_saved:
                suffix += " ⚠️ SQLite сохранена, но закреплённый снимок настроек не обновился."
            self.bot.send_message(
                chat_id,
                f"✅ Процент стопа ручных сделок установлен: <b>{value:g}%</b>." + suffix,
                reply_markup=report_settings_menu(),
            )
            return

        if setting_name in ("manual_limit1_value_usdt", "manual_limit2_value_usdt"):
            try:
                value = float(text)
                if not (0.01 <= value <= 100000.0):
                    raise ValueError
            except ValueError:
                self._awaiting_stats_input = (setting_name, "Стоимость 1-й лимитки" if setting_name.endswith("1_value_usdt") else "Стоимость 2-й лимитки")
                self.bot.send_message(chat_id, "⚠️ Введи номинал ордера от 0.01 до 100000 USDT, например <code>100</code> или <code>250.5</code>, либо /cancel.")
                return
            # Сериализуем конкурирующие изменения L1/L2. Событие о смене
            # номинала выставляется ДО ожидания текущего amend; так старый проход
            # не успевает применить устаревшее значение к следующим монетам.
            reports = self.reports
            amend_lock = getattr(reports, "_manual_limit_amend_lock", None) if reports else None
            target_update_event = getattr(reports, "_manual_limit_target_update_requested", None) if reports else None
            target_update_lock = getattr(reports, "_manual_limit_target_update_lock", None) if reports else None
            if target_update_lock is not None:
                target_update_lock.acquire()
            save_error = None
            try:
                if target_update_event is not None:
                    target_update_event.set()
                try:
                    if amend_lock is not None:
                        with amend_lock:
                            set_setting(setting_name, value)
                    else:
                        set_setting(setting_name, value)
                except Exception as exc:
                    save_error = exc
                else:
                    if target_update_event is not None:
                        target_update_event.clear()
            finally:
                if target_update_lock is not None:
                    target_update_lock.release()
            if save_error is not None:
                # При неопределённом результате записи не разрешаем старому
                # сканеру менять следующие ордера до повторного ввода настройки.
                # Event остаётся установленным, пока запись не повторится успешно.
                self.log.error(
                    "Не удалось сохранить стоимость ручной лимитки %s: %s",
                    setting_name, save_error,
                    exc_info=(type(save_error), save_error, save_error.__traceback__),
                )
                # Если возможно, также сохраняем глобальное отключение. Если
                # БД недоступна и это не удалось, Event всё равно блокирует amend
                # в текущем процессе, а пользователь получает явное предупреждение.
                try:
                    set_setting("manual_limit_value_changes_enabled", False)
                    self.push_settings_pin()
                except Exception:
                    self.log.exception("Не удалось дополнительно сохранить аварийное отключение автоизменения")
                try:
                    self.bot.send_message(
                        chat_id,
                        "⛔ Не удалось подтвердить сохранение стоимости лимитки в SQLite. "
                        "Автоматические изменения приостановлены до повторного ввода настройки. "
                        f"Ошибка: {save_error}",
                    )
                except Exception:
                    self.log.exception("Не удалось отправить ошибку сохранения номинала лимитки")
                return
            pin_saved = self.push_settings_pin()
            if bool(get_setting("manual_limit_value_changes_enabled", True)):
                changed, skipped, failed, errors = (self.reports.apply_manual_limit_values_to_open_orders(reason=f"изменена стоимость {'1-й' if setting_name.endswith('1_value_usdt') else '2-й'} лимитки") if self.reports else (0, 0, 0, []))
                suffix = f" Изменено ордеров: {changed}; уже соответствовали: {skipped}; ошибок: {failed}."
                if errors:
                    suffix += "\n" + "\n".join(f"⚠️ {e}" for e in errors[:10])
            else:
                suffix = " Автоизменение выключено: существующие ордера не тронуты; новое значение сохранено только для будущей автоматической обработки после включения переключателя."
            if not pin_saved:
                suffix += " ⚠️ Настройка записана в SQLite, но резервный снимок Telegram не обновился; при эфемерном диске перед redeploy проверь сохранение."
            self.bot.send_message(chat_id, f"✅ Стоимость {'1-й' if setting_name.endswith('1_value_usdt') else '2-й'} лимитки установлен: <b>{value:g} USDT</b> номинал ордера при максимальном плече монеты.{suffix}", reply_markup=report_settings_menu())
            return

        if setting_name == "bot_tp4_move_pct":
            try:
                parts = text.split()
                if len(parts) not in (1, 2):
                    raise ValueError
                move = float(parts[0])
                if not (0.01 <= move <= 100.0):
                    raise ValueError
                if len(parts) == 2 and abs(float(parts[1]) - 100.0) > 1e-9:
                    raise ValueError("Для TP4 процент закрытия всегда должен быть 100% остатка.")
                moves, closes = get_bot_tp_config()
                moves[3] = move
                closes[3] = 100.0
                err = _bot_tp_validate_moves(moves)
                if err:
                    raise ValueError(err)
                set_setting("bot_tp4_move_pct", move)
                set_setting("bot_tp4_close_pct", 100.0)
            except ValueError as e:
                self._awaiting_stats_input = (setting_name, label)
                msg = str(e) if str(e) else "Формат: <code>3</code> или <code>3 100</code>. Движение 0.01–100%, TP4 всегда закрывает 100% остатка."
                self.bot.send_message(chat_id, f"⚠️ {msg}\nПопробуй ещё раз или /cancel.")
                return
            self.push_settings_pin()
            updated, failed = (self.reports.apply_manual_settings_to_open_positions(reason="изменён план TP4") if self.reports else (0, 0))
            suffix = f" Применено к {updated} открытым ручным позициям." + (f" Ошибок: {failed}." if failed else "")
            self.bot.send_message(chat_id, f"✅ TP4: движение +{fmt_num(move)}%, закрытие 100% остатка.{suffix}", reply_markup=report_settings_menu())
            return

        try:
            value = abs(float(text))
        except ValueError:
            self._awaiting_stats_input = (setting_name, label)
            self.bot.send_message(chat_id, "⚠️ Не похоже на число. Введи значение ещё раз (например 20 или 20.5), или /cancel для отмены.")
            return
        set_setting(setting_name, value)
        self.push_settings_pin()
        status = f"{value:g} USDT" if value else "выключен"
        self.bot.send_message(chat_id, f"✅ Готово. Алерт на {label} по одной сделке: <b>{status}</b>", reply_markup=report_settings_menu())

    # ---- пост-сигнал: разбор, запрос суммы, подтверждение, открытие ------

    def _handle_signal_post(self, message):
        chat_id = message.chat.id
        parsed = parse_signal_post(message.text or "")
        if parsed is None:
            return
        self._handle_parsed_signal(chat_id, parsed)

    def _handle_parsed_signal(self, chat_id: int, parsed: Dict):
        if parsed.get("dual_zone"):
            # Пост с двумя независимыми зонами (шорт выше, лонг ниже) — цена
            # сейчас ни в одной из них, направление за пользователя не
            # угадываем, а показываем обе зоны и ждём выбора кнопкой.
            self._pending_signal_side_confirm = parsed
            long_txt = " / ".join(fmt_num(e) for e in parsed["long_entries"])
            short_txt = " / ".join(fmt_num(e) for e in parsed["short_entries"])
            kb = types.InlineKeyboardMarkup()
            kb.add(
                types.InlineKeyboardButton(f"🔼 LONG ({long_txt})", callback_data="sigdir_long"),
                types.InlineKeyboardButton(f"🔽 SHORT ({short_txt})", callback_data="sigdir_short"),
            )
            kb.add(types.InlineKeyboardButton("❌ Отмена", callback_data="sigdir_cancel"))
            self.bot.send_message(
                chat_id,
                f"📩 <b>Распознан пост-разбор по {parsed['symbol']}</b>\n"
                f"В посте две независимые зоны — выбери, какую торговать:\n"
                f"🔼 LONG-зона: {long_txt}\n"
                f"🔽 SHORT-зона: {short_txt}\n\n"
                f"Стоп будет рассчитан автоматически как {getattr(cfg, 'SIGNAL_ZONE_AUTO_STOP_PERCENT', 7)}% от крайней (дальней) цены выбранной зоны.",
                reply_markup=kb,
            )
            return

        if parsed.get("unknown_zone"):
            # Зона входа найдена (например, "Зона интереса 96.94-95.46"), но
            # ни явного SHORT/LONG, ни узнаваемого контекста (накопление/
            # распределение) в посте нет — направление за пользователя не
            # угадываем, показываем ту же зону и ждём выбора кнопкой.
            self._pending_signal_side_confirm = parsed
            zone_txt = " / ".join(fmt_num(e) for e in parsed["zone_entries"])
            kb = types.InlineKeyboardMarkup()
            kb.add(
                types.InlineKeyboardButton("🔼 LONG", callback_data="sigdir_long"),
                types.InlineKeyboardButton("🔽 SHORT", callback_data="sigdir_short"),
            )
            kb.add(types.InlineKeyboardButton("❌ Отмена", callback_data="sigdir_cancel"))
            self.bot.send_message(
                chat_id,
                f"📩 <b>Распознан пост-разбор по {parsed['symbol']}</b>\n"
                f"Зона: {zone_txt}\n\n"
                f"В посте не написано, LONG это или SHORT — выбери сам.\n"
                f"Стоп будет рассчитан автоматически как {getattr(cfg, 'SIGNAL_ZONE_AUTO_STOP_PERCENT', 7)}% от крайней цены зоны.",
                reply_markup=kb,
            )
            return

        if not parsed.get("side_explicit", True):
            # В посте нет явного слова SHORT/LONG — направление бот угадал по
            # смыслу текста, но это ненадёжно, поэтому просим подтвердить.
            self._pending_signal_side_confirm = parsed
            entries_txt = " / ".join(fmt_num(e) for e in parsed["entries"])
            kb = types.InlineKeyboardMarkup()
            kb.add(
                types.InlineKeyboardButton("🔼 LONG", callback_data="sigdir_long"),
                types.InlineKeyboardButton("🔽 SHORT", callback_data="sigdir_short"),
            )
            kb.add(types.InlineKeyboardButton("❌ Отмена", callback_data="sigdir_cancel"))
            self.bot.send_message(
                chat_id,
                f"📩 <b>Распознан пост-сигнал по {parsed['symbol']}</b>\n"
                f"Входы: {entries_txt}\n\n"
                f"В посте явно не написано SHORT или LONG — я предположил "
                f"<b>{parsed['side']}</b> по смыслу текста, но лучше подтверди сам:",
                reply_markup=kb,
            )
            return

        self._present_signal_for_confirmation(chat_id, parsed)

    def _present_signal_for_confirmation(self, chat_id: int, parsed: Dict):
        if parsed["symbol"] in get_excluded_symbols():
            self.bot.send_message(chat_id, f"🚫 <b>{parsed['symbol']}</b> в списке исключений — бот не открывает по ней сделки. Убери её из исключений в настройках, если это ошибка.")
            return
        avg_entry = sum(parsed["entries"]) / len(parsed["entries"])
        if parsed["side"] == "SHORT" and parsed["stop"] <= avg_entry:
            self.bot.send_message(chat_id, f"⚠️ Не похоже на корректный SHORT: стоп ({fmt_num(parsed['stop'])}) должен быть ВЫШЕ средней цены входа ({fmt_num(avg_entry)}). Проверь пост и пришли заново.")
            return
        if parsed["side"] == "LONG" and parsed["stop"] >= avg_entry:
            self.bot.send_message(chat_id, f"⚠️ Не похоже на корректный LONG: стоп ({fmt_num(parsed['stop'])}) должен быть НИЖЕ средней цены входа ({fmt_num(avg_entry)}). Проверь пост и пришли заново.")
            return
        # Цели из исходного поста больше НЕ используются как отдельные тейки.
        # Сигнальная сделка после исполнения входа получает единый TP1-TP4
        # план из общих настроек бота. Стоп из сигнала сохраняется.
        moves, closes = get_bot_tp_config()
        enabled = get_bot_tp_enabled()
        lines = [
            "📩 <b>Распознан пост-сигнал</b>",
            "━━━━━━━━━━━━━━━",
            f"Пара: <b>{parsed['symbol']}</b>",
            f"Направление: <b>{parsed['side']}</b>",
            f"Входы (лимитные ордера): {' / '.join(fmt_num(e) for e in parsed['entries'])}",
            *([f"⚠️ В посте цен входа больше {len(parsed['entries'])}: беру первые {len(parsed['entries'])}, "
               f"пропущено: {' / '.join(fmt_num(e) for e in parsed['entries_dropped'])}"]
              if parsed.get("entries_dropped") else []),
            f"Стоп: {fmt_num(parsed['stop'])}" + (f" (авто-расчёт: {getattr(cfg, 'SIGNAL_AUTO_STOP_PERCENT', 12)}% от первой цены входа)" if parsed.get('stop_auto') else ""),
            "Плечо будет выставлено максимальное, доступное этой монете на бирже.",
        ]
        tp_parts = []
        for i in range(1, 5):
            if i == 4 or enabled[i - 1]:
                close_txt = "100% остатка" if i == 4 else f"{closes[i-1]:g}% исходного объёма"
                state_txt = "включён" if i == 4 or enabled[i-1] else "выключен"
                tp_parts.append(f"TP{i}: +{moves[i-1]:g}% / {close_txt} ({state_txt})")
        lines.append(
            "После исполнения входа исходные цели из поста игнорируются. "
            "Выставлю единый план TP1–TP4 от фактической средней цены:\n"
            + "\n".join(tp_parts)
            + "\nTP4 всегда закрывает 100% оставшегося объёма."
        )
        lines.append(
            "После исполнения TP1 оставшийся отслеживаемый вход будет отменён, "
            "а стоп перенесён на +0.5% от фактического входа для LONG / −0.5% для SHORT."
            if parsed["breakeven_after_tp1"] else
            "Перенос стопа после TP1 отключён для этого сигнала."
        )
        lines.append("\n✏️ Впиши итоговую сумму сделки в USDT одним числом (это будет объём ордеров вместе, не маржа) — например <code>20</code>. Или /cancel, чтобы отменить.")

        self._awaiting_signal_margin = parsed
        self.bot.send_message(chat_id, "\n".join(lines))

    def _process_signal_margin_input(self, message):
        parsed = self._awaiting_signal_margin
        self._awaiting_signal_margin = None
        chat_id = message.chat.id
        text = (message.text or "").strip()

        if text.startswith("/cancel"):
            self.bot.send_message(chat_id, "Отменено.", reply_markup=reply_keyboard(self.paused))
            return

        try:
            order_usdt = float(text.replace(",", "."))
            # nan/inf проходили проверку «> 0» и ломали расчёт объёма дальше.
            if not math.isfinite(order_usdt) or order_usdt <= 0:
                raise ValueError
        except ValueError:
            self._awaiting_signal_margin = parsed
            self.bot.send_message(chat_id, "⚠️ Не похоже на число. Впиши итоговую сумму сделки в USDT ещё раз (например 20), или /cancel для отмены.")
            return

        try:
            client = self.reports.client
            leverage = client.get_max_leverage(parsed["symbol"])
            # Тот же расчёт, что и при реальной постановке ордеров: пользователь
            # подтверждает именно те числа, которые уйдут на биржу.
            sizing = client.compute_signal_entry_sizing(
                parsed["symbol"], parsed["side"], parsed["entries"], parsed["stop"], order_usdt,
            )
            qty_total = sizing["qty_total"]
            qty_each = sizing["qty_each"]
            notional_total = sizing["notional_total"]
        except ValueError as e:
            # Размер не проходит биржевые лимиты — сообщаем сразу и просим другую
            # сумму, вместо ошибки уже после нажатия «Да, открыть».
            self._awaiting_signal_margin = parsed
            self.bot.send_message(chat_id, f"⚠️ {e}\nВпиши другую сумму в USDT, или /cancel для отмены.")
            return
        except Exception as e:
            self.log.exception("Не удалось посчитать предварительный объём по сигналу")
            self.bot.send_message(chat_id, f"⚠️ Не удалось посчитать объём: {e}")
            return

        parsed = {**parsed, "order_usdt": order_usdt}
        self._pending_signal = parsed

        required_margin = notional_total / leverage if leverage else notional_total
        tp_line = f"Тейк (на весь объём): {fmt_num(parsed['targets'][-1])}" if parsed.get("targets") else "Тейк: не указан в посте — не будет выставлен"
        lines = [
            "📩 <b>Проверь перед открытием</b>",
            "━━━━━━━━━━━━━━━",
            f"Пара: <b>{parsed['symbol']}</b> · {parsed['side']}",
            f"Сумма ордеров (вместе): {fmt_num(order_usdt)} USDT (фактически ≈{fmt_num(notional_total)} USDT после округления объёма)",
            f"Макс. плечо монеты: {fmt_num(leverage)}x → под эту сумму нужна маржа ≈{fmt_num(required_margin)} USDT",
            f"Объём на каждый из {len(parsed['entries'])} вход(ов): ≈{fmt_num(qty_each)} (суммарно ≈{fmt_num(qty_total)})",
            f"Стоп: {fmt_num(parsed['stop'])}",
            tp_line,
            "\nОткрыть лимитными ордерами со стопом и тейком?",
        ]
        kb = types.InlineKeyboardMarkup()
        kb.add(
            types.InlineKeyboardButton("✅ Да, открыть", callback_data="confirm_signal"),
            types.InlineKeyboardButton("❌ Отмена", callback_data="cancel_signal"),
        )
        self.bot.send_message(chat_id, "\n".join(lines), reply_markup=kb)

    def _format_bot_signal_orders(self) -> str:
        """Список всех сделок/лимиток, которые бот сам открыл по постам —
        и уже открытых (позиция есть), и ещё ожидающих исполнения входа."""
        positions = get_all_open_signal_positions()
        if not positions:
            return "Сейчас нет активных сделок, открытых ботом по постам."

        lines = ["📋 <b>Активные сделки бота по постам</b>", "━━━━━━━━━━━━━━━"]
        for symbol, sp in positions.items():
            entry_ids = sp.get("entry_order_ids", [])
            open_ids = self.reports.client.get_open_order_ids(symbol)
            if open_ids is not None:
                still_pending = len(set(entry_ids) & open_ids)
                fill_status = f"исполнено {len(entry_ids) - still_pending}/{len(entry_ids)}"
            else:
                fill_status = "статус входов неизвестен (сбой запроса)"

            entries_txt = " / ".join(fmt_num(e) for e in sp.get("entries", []))
            targets_txt = " / ".join(fmt_num(t) for t in sp.get("manual_tp_targets", [])) or "рассчитываются от фактического входа"
            tp_state = []
            tp_done = sp.get("manual_tp_done") or {}
            for i in range(1, 5):
                if i == 4:
                    tp_state.append("TP4: Full")
                elif get_bot_tp_enabled()[i-1]:
                    tp_state.append(f"TP{i}: {'готов' if tp_done.get(str(i)) else 'активен'}")
            tp_status = " · ".join(tp_state)
            stop_note = " (после TP1 перенесён)" if sp.get("breakeven_done") else ""

            lines.append(
                f"\n<b>{symbol}</b> · {sp['side']} · {sp['status']}\n"
                f"Входы: {entries_txt} ({fill_status})\n"
                f"Стоп: {fmt_num(sp['stop_price'])}{stop_note}\n"
                f"TP1–TP4: {targets_txt}\n"
                f"Тейки на бирже: {tp_status}"
            )
        return "\n".join(lines)

    def _execute_signal_position(self, chat_id: int, parsed: Dict):
        # Refuse duplicate/conflicting active symbols BEFORE placing exchange
        # orders. create_signal_position() also guards its UPSERT, but that
        # check runs after order placement and alone could leave live entries
        # with no durable DB tracker.
        existing = get_signal_position(str(parsed.get("symbol") or ""))
        if _active_signal_position_conflict(existing, {
            "side": parsed.get("side"),
            "source": "post",
        }):
            self.bot.send_message(
                chat_id,
                f"⚠️ {parsed.get('symbol')}: уже есть активная запись сделки в БД. "
                "Новые лимитные ордера не размещены, чтобы не потерять состояние TP/SL.",
            )
            self.log.warning(
                "[%s] Отклонён повторный сигнал до размещения ордеров: в БД уже есть активная запись",
                parsed.get("symbol"),
            )
            return
        try:
            result = self.reports.client.open_signal_position(
                parsed["symbol"], parsed["side"], parsed["entries"], parsed["stop"], parsed["order_usdt"],
                targets=parsed.get("targets"), single_target_is_partial=bool(parsed.get("single_target_is_partial")),
            )
        except Exception as e:
            self.log.exception("Не удалось открыть позицию по сигналу")
            self.bot.send_message(chat_id, f"⚠️ Не удалось открыть позицию по сигналу: {e}")
            return

        try:
            create_signal_position({
                "symbol": parsed["symbol"],
                "side": parsed["side"],
                "entries": parsed["entries"],
                "targets": parsed["targets"],
                # Стоп, фактически ушедший на биржу (после округления к тику), а не
                # сырое число из поста: иначе монитор видит расхождение с биржей.
                "stop_price": result.get("stop_price", parsed["stop"]),
                "avg_entry_price": result["avg_entry"],
                "qty_total": result["qty_total"],
                "entry_order_ids": result["order_ids"],
                "breakeven_after_tp1": parsed["breakeven_after_tp1"],
                "source": "post",
            })
        except Exception as persist_error:
            # A failure after exchange orders were accepted must never be
            # silently ignored. First check whether the DB commit succeeded
            # but a later audit-event write failed.
            try:
                saved = get_signal_position(parsed["symbol"])
            except Exception:
                saved = None
            expected_order_ids = {
                str(x) for x in (result.get("order_ids") or []) if x
            }
            saved_order_ids = {
                str(x) for x in ((saved or {}).get("entry_order_ids") or []) if x
            }
            saved_matches_this_entry = bool(
                saved
                and str(saved.get("status") or "").lower() in {"pending", "open"}
                and str(saved.get("side") or "").upper() == str(parsed.get("side") or "").upper()
                and str(saved.get("source") or "post").lower() == "post"
                and expected_order_ids == saved_order_ids
            )
            if saved_matches_this_entry:
                self.log.exception(
                    "[%s] Ошибка после записи signal_positions; запись с теми же order ID найдена, входные ордера оставлены под контролем",
                    parsed["symbol"],
                )
            else:
                cancel_errors = []
                for entry_order_id in result.get("order_ids") or []:
                    try:
                        self.reports.client.session.cancel_order(
                            category=cfg.CATEGORY,
                            symbol=parsed["symbol"],
                            orderId=str(entry_order_id),
                        )
                    except Exception as cancel_error:
                        cancel_errors.append(f"{entry_order_id}: {cancel_error}")
                self.log.exception(
                    "[%s] Не удалось сохранить сигнал в SQLite после размещения входов. "
                    "Отмена незаполненных входов запрошена; состояние исполнения требует сверки с биржей. Ошибки отмены: %s",
                    parsed["symbol"], "; ".join(cancel_errors) or "нет",
                )
                try:
                    self.bot.send_message(
                        chat_id,
                        f"🚨 <b>{parsed['symbol']}</b>: ордера на вход были отправлены, но состояние сделки не удалось сохранить в БД. "
                        "Запрошена отмена оставшихся входов; обязательно проверь позицию и защитные ордера на Bybit. "
                        "Автоматически считать сделку безопасной нельзя."
                        + (f" Ошибки отмены: {'; '.join(cancel_errors)}" if cancel_errors else ""),
                    )
                except Exception:
                    self.log.exception("[%s] Не удалось отправить аварийное уведомление о сбое записи SQLite", parsed["symbol"])
            return

        # Если один из лимитных входов уже успел исполниться до записи позиции
        # в БД, не ждём следующего 10-секундного цикла: сразу запускаем полный
        # контроль TP1-TP4. Если позиция ещё pending, проверка безопасно выйдет.
        try:
            self.reports._check_signal_position(parsed["symbol"], get_signal_position(parsed["symbol"]) or {})
        except Exception:
            self.log.exception(f"[{parsed['symbol']}] Не удалось выполнить немедленную проверку TP1-TP4 после постановки входов")

        breakeven_note = (
            " TP1-TP4 установятся сразу после фактического исполнения входа; после TP1 стоп перенесётся на ±0.5% от фактического входа."
            if parsed["breakeven_after_tp1"] else
            " TP1-TP4 установятся после фактического исполнения входа; перенос стопа после TP1 отключён."
        )
        tp_note = " Старые цели из поста не используются."
        warn_note = ""
        if result.get("errors"):
            placed_n = len(result["order_ids"])
            total_n = len(parsed["entries"])
            warn_note = f"\n⚠️ Встало только {placed_n} из {total_n} ордеров — часть не прошла: {'; '.join(result['errors'])}"
        self.bot.send_message(
            chat_id,
            f"✅ <b>{parsed['symbol']}</b>: выставлено {len(result['order_ids'])} лимитных ордера(ов) на вход "
            f"по {fmt_num(result['qty_each'])} (суммарно {fmt_num(result['qty_total'])}), "
            f"сумма ордеров ≈{fmt_num(result.get('notional_total', result['order_usdt']))} USDT, плечо {fmt_num(result['leverage'])}x "
            f"(маржа под сделку ≈{fmt_num(result['required_margin'])} USDT), "
            f"стоп {fmt_num(parsed['stop'])}{tp_note}.{breakeven_note}{warn_note}",
        )

    # ---- callback-и -------------------------------------------------------

    def _dispatch_callback(self, call):
        bot = self.bot
        data = call.data or ""
        chat_id = call.message.chat.id
        msg_id = call.message.message_id

        if data == "confirm_signal":
            parsed = self._pending_signal
            self._pending_signal = None
            if parsed is None:
                bot.answer_callback_query(call.id, "Сигнал устарел")
                bot.edit_message_text("⚠️ Сигнал устарел или уже обработан — пришли пост ещё раз.", chat_id, msg_id)
                return
            bot.answer_callback_query(call.id, "Открываю...")
            bot.edit_message_text("⏳ Открываю позицию по сигналу...", chat_id, msg_id)
            self._execute_signal_position(chat_id, parsed)
            return
        if data == "cancel_signal":
            self._pending_signal = None
            bot.answer_callback_query(call.id, "Отменено")
            bot.edit_message_text("Отменено.", chat_id, msg_id)
            return

        if data in ("sigdir_long", "sigdir_short"):
            parsed = self._pending_signal_side_confirm
            self._pending_signal_side_confirm = None
            if parsed is None:
                bot.answer_callback_query(call.id, "Сигнал устарел")
                bot.edit_message_text("⚠️ Сигнал устарел или уже обработан — пришли пост ещё раз.", chat_id, msg_id)
                return
            chosen_side = "LONG" if data == "sigdir_long" else "SHORT"

            if parsed.get("dual_zone"):
                # Из двух независимых зон выбрали одну — собираем обычный
                # parsed-сигнал из выбранной зоны: стоп на SIGNAL_ZONE_AUTO_STOP_PERCENT
                # % от крайней (самой дальней) цены зоны, тейк на 50% (кнопкой
                # регулируется) на SIGNAL_ZONE_TP_PERCENT % от ПЕРВОЙ цены зоны —
                # целей в самом посте нет, их неоткуда взять, поэтому фиксированный
                # процент. Как только цена дойдёт до этого тейка — стоп уйдёт в
                # безубыток, а вторая (ещё не исполненная) лимитка снимется —
                # тот же механизм, что и для обычных постов с 2+ целями.
                entries = parsed["long_entries"] if chosen_side == "LONG" else parsed["short_entries"]
                zone_stop_pct = getattr(cfg, "SIGNAL_ZONE_AUTO_STOP_PERCENT", 7) / 100.0
                zone_tp_pct = getattr(cfg, "SIGNAL_ZONE_TP_PERCENT", 3) / 100.0
                far_entry, first_entry = entries[-1], entries[0]
                stop = far_entry * (1 - zone_stop_pct) if chosen_side == "LONG" else far_entry * (1 + zone_stop_pct)
                tp = first_entry * (1 + zone_tp_pct) if chosen_side == "LONG" else first_entry * (1 - zone_tp_pct)
                parsed = {
                    "symbol": parsed["symbol"],
                    "side": chosen_side,
                    "side_explicit": True,
                    "leverage": None,
                    "entries": entries,
                    "targets": [tp],
                    "single_target_is_partial": True,
                    "stop": stop,
                    "stop_auto": True,
                    "breakeven_after_tp1": True,
                }
            elif parsed.get("unknown_zone"):
                # Направление неизвестно было из текста вообще — та же зона
                # (одна и та же цена входа) используется для любого выбора,
                # разница только в формулах стопа/тейка под выбранную сторону.
                entries = parsed["zone_entries"]
                zone_stop_pct = getattr(cfg, "SIGNAL_ZONE_AUTO_STOP_PERCENT", 7) / 100.0
                zone_tp_pct = getattr(cfg, "SIGNAL_ZONE_TP_PERCENT", 3) / 100.0
                far_entry, first_entry = entries[-1], entries[0]
                stop = far_entry * (1 - zone_stop_pct) if chosen_side == "LONG" else far_entry * (1 + zone_stop_pct)
                tp = first_entry * (1 + zone_tp_pct) if chosen_side == "LONG" else first_entry * (1 - zone_tp_pct)
                parsed = {
                    "symbol": parsed["symbol"],
                    "side": chosen_side,
                    "side_explicit": True,
                    "leverage": None,
                    "entries": entries,
                    "targets": [tp],
                    "single_target_is_partial": True,
                    "stop": stop,
                    "stop_auto": True,
                    "breakeven_after_tp1": True,
                }
            elif chosen_side != parsed["side"] and parsed.get("stop_auto"):
                # автостоп считался от исходного (угаданного) направления —
                # если пользователь выбрал другое, пересчитываем стоп.
                auto_pct = getattr(cfg, "SIGNAL_AUTO_STOP_PERCENT", 12) / 100.0
                first_entry = parsed["entries"][0]
                parsed["stop"] = first_entry * (1 - auto_pct) if chosen_side == "LONG" else first_entry * (1 + auto_pct)

            parsed["side"] = chosen_side
            parsed["side_explicit"] = True
            bot.answer_callback_query(call.id, f"Направление: {chosen_side}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=None)
            self._present_signal_for_confirmation(chat_id, parsed)
            return
        if data == "sigdir_cancel":
            self._pending_signal_side_confirm = None
            bot.answer_callback_query(call.id, "Отменено")
            bot.edit_message_text("Отменено.", chat_id, msg_id)
            return

        if data == "menu_main":
            bot.answer_callback_query(call.id)
            bot.edit_message_text("Выбери действие снизу или в этом меню:", chat_id, msg_id, reply_markup=back_menu())
            return

        if data == "confirm_stop":
            self.running = False
            bot.answer_callback_query(call.id, "Останавливаю торговый движок...")
            bot.edit_message_text("🔴 Торговый движок остановлен по команде. Учёт/отчёты продолжают работать.", chat_id, msg_id)
            return
        if data == "cancel_stop":
            bot.answer_callback_query(call.id, "Отменено")
            bot.edit_message_text("Остановка отменена.", chat_id, msg_id)
            return

        if data == "settings_close":
            bot.answer_callback_query(call.id)
            bot.delete_message(chat_id, msg_id)
            return

        # ---- избранные монеты ----
        if data == "favorites_toggle":
            new_value = not is_favorites_mode_enabled()
            set_favorites_mode_enabled(new_value)
            bot.answer_callback_query(call.id, f"Режим избранного: {'включён' if new_value else 'выключен'}")
            bot.edit_message_text(favorites_status_text(), chat_id, msg_id, reply_markup=favorites_menu())
            return
        if data == "favorites_add":
            self._awaiting_favorite_add = True
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "Пришли тикеры монет через запятую или пробел (например: <code>BTC, ETH, SOLUSDT</code>). Или /cancel, чтобы отменить.")
            return
        if data.startswith("favorites_remove:"):
            symbol = data.split(":", 1)[1]
            removed = remove_favorite_symbol(symbol)
            if removed:
                self.push_settings_pin()
            bot.answer_callback_query(call.id, f"{symbol} убран из избранного" if removed else "Уже не в списке")
            bot.edit_message_text(favorites_status_text(), chat_id, msg_id, reply_markup=favorites_menu())
            return

        # ---- настройки стратегии ----
        if data == "trade_settings_back":
            self._awaiting_input_key = None
            bot.answer_callback_query(call.id)
            bot.edit_message_text("⚙️ <b>Настройки стратегии</b>\n\nНажми на параметр, чтобы изменить значение:", chat_id, msg_id, reply_markup=trade_settings_menu())
            return
        # ---- отдельные переключатели TP1-TP3 ----------------------------
        # Кнопки меню report_settings_menu() используют callback_data
        # set_bot_tpN_on/off. Раньше сами кнопки создавались, но обработчика
        # этих callback-ов здесь не было — Telegram нажимал кнопку, а настройка
        # фактически не менялась.
        #
        # ВАЖНО: get_bot_tp_enabled() читает значения через get_setting(),
        # то есть источник истины для этих флагов — SQLite meta, а не cfg.*.
        # Поэтому здесь намеренно используется set_setting(), а не
        # persist_trading_setting(). Это гарантирует сохранение значения в
        # trades.db и восстановление после перезапуска.
        if data.startswith("set_bot_tp") and (data.endswith("_on") or data.endswith("_off")):
            m = re.fullmatch(r"set_bot_tp([1-3])_(on|off)", data)
            if not m:
                bot.answer_callback_query(call.id, "Некорректная кнопка TP")
                return

            tp_no = int(m.group(1))
            new_value = m.group(2) == "on"
            key = f"bot_tp{tp_no}_enabled"

            # Сохраняем именно в SQLite. Запись синхронная: после возврата
            # set_setting() новое значение уже находится в БД.
            set_setting(key, new_value)

            # Немедленно проверяем, что именно записалось и что следующий
            # вызов торговой логики увидит новое состояние.
            saved_value = bool(get_setting(key, True))
            if saved_value != new_value:
                bot.answer_callback_query(call.id, "⚠️ Не удалось сохранить настройку TP")
                self.log.error("Не удалось подтвердить сохранение %s=%s в SQLite", key, new_value)
                return

            # Закреплённый снимок настроек тоже обновляем, чтобы настройка
            # пережила redeploy Railway даже при потере локального файла БД.
            self.push_settings_pin()

            state_text = "ВКЛЮЧЁН ✅" if saved_value else "ВЫКЛЮЧЕН ⛔"
            bot.answer_callback_query(call.id, f"TP{tp_no}: {state_text}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())

            # Не трогаем уже исполненные TP и не создаём ордера прямо из
            # Telegram callback. Торговый guard сам подхватит изменение:
            # отключённый TP будет отменён, включённый — восстановлен/создан
            # при следующей TP-реконсиляции. Это сохраняет единую торговую
            # логику и исключает двойную постановку ордеров.
            return

        if data.startswith("toggle:"):
            key = data.split(":", 1)[1]
            new_value = not get_trading_setting(key)
            persist_trading_setting(key, new_value)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"{TOGGLE_SETTINGS[key]}: {'включено' if new_value else 'выключено'}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=trade_settings_menu())
            return
        if data.startswith("set:"):
            key = data.split(":", 1)[1]
            meta = EDITABLE_SETTINGS[key]
            value = get_trading_setting(key)
            bot.answer_callback_query(call.id)
            bot.edit_message_text(f"🔧 <b>{meta['label']}</b>\nТекущее значение: <b>{fmt_num(value)}{meta['suffix']}</b>\n\nИзмени кнопками шага или введи своё значение.", chat_id, msg_id, reply_markup=value_edit_keyboard(key))
            return
        if data.startswith("adj:"):
            _, key, direction = data.split(":")
            meta = EDITABLE_SETTINGS[key]
            value = get_trading_setting(key)
            delta = meta["step"] * (1 if direction == "1" else -1)
            new_value = meta["type"](round(value + delta, 6))
            new_value = max(meta["min"], min(meta["max"], new_value))
            persist_trading_setting(key, new_value)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"{meta['label']}: {fmt_num(new_value)}{meta['suffix']}")
            bot.edit_message_text(f"🔧 <b>{meta['label']}</b>\nТекущее значение: <b>{fmt_num(new_value)}{meta['suffix']}</b>\n\nИзмени кнопками шага или введи своё значение.", chat_id, msg_id, reply_markup=value_edit_keyboard(key))
            return
        if data.startswith("typein:"):
            key = data.split(":", 1)[1]
            meta = EDITABLE_SETTINGS[key]
            self._awaiting_input_key = key
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, f"Введи новое значение для «{meta['label']}» (диапазон {fmt_num(meta['min'])}–{fmt_num(meta['max'])}{meta['suffix']}):")
            return
        if data == "cycle_short_bounce_interval":
            cur = str(get_trading_setting("SHORT_LOW_BOUNCE_CANDLE_INTERVAL"))
            idx = SHORT_BOUNCE_INTERVAL_PRESETS.index(cur) if cur in SHORT_BOUNCE_INTERVAL_PRESETS else 0
            new_val = SHORT_BOUNCE_INTERVAL_PRESETS[(idx + 1) % len(SHORT_BOUNCE_INTERVAL_PRESETS)]
            persist_trading_setting("SHORT_LOW_BOUNCE_CANDLE_INTERVAL", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Таймфрейм лоя свечи (шорт): {new_val}м")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=trade_settings_menu())
            return
        if data == "cycle_long_bounce_interval":
            cur = str(get_trading_setting("LONG_LOW_BOUNCE_CANDLE_INTERVAL"))
            idx = LONG_BOUNCE_INTERVAL_PRESETS.index(cur) if cur in LONG_BOUNCE_INTERVAL_PRESETS else 0
            new_val = LONG_BOUNCE_INTERVAL_PRESETS[(idx + 1) % len(LONG_BOUNCE_INTERVAL_PRESETS)]
            persist_trading_setting("LONG_LOW_BOUNCE_CANDLE_INTERVAL", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Таймфрейм лоя свечи (лонг): {new_val}м")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=trade_settings_menu())
            return

        # ---- статистика/периоды ----
        if data.startswith("stats_"):
            days = int(data.split("_", 1)[1])
            period_name = dict(PERIODS).get(days) or next((n for n, d in PERIODS if d == days), f"{days} дней")
            bot.answer_callback_query(call.id)
            bot.edit_message_text(self.reports.build_stats_message(period_name, days), chat_id, msg_id, reply_markup=stats_result_menu(days))
            return
        if data.startswith("chart_"):
            days = int(data.split("_", 1)[1])
            bot.answer_callback_query(call.id, "Строю график...")
            chart = self.reports.build_equity_chart(days)
            if chart is None:
                bot.send_message(chat_id, "📭 За этот период нет закрытых сделок.", reply_markup=back_menu())
            else:
                bot.send_photo(chat_id, chart, reply_markup=back_menu())
            return
        if data.startswith("top_"):
            days = int(data.split("_", 1)[1])
            bot.answer_callback_query(call.id)
            bot.edit_message_text(self.reports.build_top_trades_message(days), chat_id, msg_id, reply_markup=back_menu())
            return
        if data.startswith("table_"):
            days = int(data.split("_", 1)[1])
            bot.answer_callback_query(call.id, "Строю таблицу...")
            img, total = self.reports.build_trades_table_image(days)
            if img is None:
                bot.send_message(chat_id, "📭 За этот период нет закрытых сделок.", reply_markup=back_menu())
            else:
                bot.send_photo(chat_id, img, reply_markup=back_menu())
            return
        if data.startswith("fees_"):
            days = int(data.split("_", 1)[1])
            period_name = next((n for n, d in PERIODS if d == days), f"{days} дней")
            bot.answer_callback_query(call.id, "Считаю...")
            bot.edit_message_text(self.reports.build_fees_message(period_name, days), chat_id, msg_id, reply_markup=back_menu())
            return
        if data.startswith("export_"):
            days = int(data.split("_", 1)[1])
            bot.answer_callback_query(call.id, "Готовлю файл...")
            csv_data = self.reports.build_csv_export(days)
            if csv_data is None:
                bot.send_message(chat_id, "📭 За этот период нет закрытых сделок.", reply_markup=back_menu())
            else:
                csv_data.name = f"trades_{days}d.csv"
                bot.send_document(chat_id, csv_data, reply_markup=back_menu())
            return
        if data.startswith("symstat_"):
            symbol = data.split("_", 1)[1]
            bot.answer_callback_query(call.id)
            bot.edit_message_text(self.reports.build_stats_message("всё время", 3650, symbol=symbol), chat_id, msg_id, reply_markup=back_menu())
            return

        # ---- настройки учёта ----
        if data == "toggle_only_trade_close":
            cur = get_setting("only_trade_close_notifications", getattr(cfg, "ONLY_TRADE_CLOSE_NOTIFICATIONS", False))
            set_setting("only_trade_close_notifications", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, "Теперь только уведомления о закрытии сделок" if not cur else "Все уведомления снова включены")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "toggle_notify":
            cur = get_setting("notify_new_trade", cfg.NOTIFY_ON_NEW_TRADE)
            set_setting("notify_new_trade", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, "Готово")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "toggle_daily":
            cur = get_setting("enable_daily_report", cfg.ENABLE_DAILY_REPORT)
            set_setting("enable_daily_report", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, "Готово")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "toggle_weekly":
            cur = get_setting("enable_weekly_report", cfg.ENABLE_WEEKLY_REPORT)
            set_setting("enable_weekly_report", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, "Готово")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "toggle_conn_notify":
            cur = get_setting("notify_connection_issues", cfg.NOTIFY_ON_CONNECTION_ISSUES)
            set_setting("notify_connection_issues", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, "Готово")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "cycle_loss_alert":
            cur = get_setting("max_daily_loss_alert", cfg.MAX_DAILY_LOSS_ALERT)
            idx = LOSS_ALERT_PRESETS.index(cur) if cur in LOSS_ALERT_PRESETS else 0
            new_val = LOSS_ALERT_PRESETS[(idx + 1) % len(LOSS_ALERT_PRESETS)]
            set_setting("max_daily_loss_alert", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Риск-алерт: {new_val if new_val else 'выкл'}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "cycle_pnl_plus":
            key = "pnl_alert_plus"
            self._awaiting_stats_input = (key, "ПРИБЫЛЬ")
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "Введи порог алерта на ПРИБЫЛЬ по одной сделке в USDT (0 — выключить), или /cancel:")
            return
        if data == "cycle_pnl_minus":
            key = "pnl_alert_minus"
            self._awaiting_stats_input = (key, "УБЫТОК")
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "Введи порог алерта на УБЫТОК по одной сделке в USDT (0 — выключить), или /cancel:")
            return
        if data == "cycle_timezone":
            cur = get_setting("tz_offset", 0)
            idx = TIMEZONE_PRESETS.index(cur) if cur in TIMEZONE_PRESETS else 0
            new_val = TIMEZONE_PRESETS[(idx + 1) % len(TIMEZONE_PRESETS)]
            set_setting("tz_offset", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Часовой пояс: UTC{new_val:+d}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "cycle_quiet_hours":
            cur = get_setting("quiet_hours", cfg.QUIET_HOURS)
            idx = QUIET_HOURS_PRESETS.index(cur) if cur in QUIET_HOURS_PRESETS else 0
            new_val = QUIET_HOURS_PRESETS[(idx + 1) % len(QUIET_HOURS_PRESETS)]
            set_setting("quiet_hours", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Тихие часы: {new_val if new_val else 'выключены'}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "cycle_daily_hour":
            cur = get_setting("daily_report_hour", cfg.DAILY_REPORT_HOUR_UTC)
            idx = DAILY_REPORT_HOUR_PRESETS.index(cur) if cur in DAILY_REPORT_HOUR_PRESETS else 0
            new_val = DAILY_REPORT_HOUR_PRESETS[(idx + 1) % len(DAILY_REPORT_HOUR_PRESETS)]
            set_setting("daily_report_hour", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Час отчёта: {new_val}:00 UTC")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "toggle_db_backup":
            cur = get_setting("enable_db_backup", getattr(cfg, "ENABLE_DB_BACKUP", True))
            set_setting("enable_db_backup", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Автобэкап БД: {'включён' if not cur else 'выключен'}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "toggle_okx_feed":
            cur = get_setting("okx_feed_enabled", cfg.OKX_FEED_ENABLED_DEFAULT)
            set_setting("okx_feed_enabled", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Посты трейдера OKX: {'включены' if not cur else 'выключены'}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data in ("toggle_bot_tp1", "toggle_bot_tp2", "toggle_bot_tp3"):
            # Совместимость со старой кнопкой-переключателем.
            tp_no = int(data[-1])
            key = f"bot_tp{tp_no}_enabled"
            cur = bool(get_setting(key, True))
            set_setting(key, not cur)
            self.push_settings_pin()
            state = "включён" if not cur else "выключен"
            bot.answer_callback_query(call.id, f"TP{tp_no}: {state}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return

        tp_toggle = _parse_bot_tp_toggle_callback(data)
        if tp_toggle is not None:
            tp_no, enabled_value = tp_toggle
            set_setting(f"bot_tp{tp_no}_enabled", enabled_value)
            self.push_settings_pin()
            updated, failed = (
                self.reports.apply_manual_settings_to_open_positions(
                    reason=f"TP{tp_no} {'включён' if enabled_value else 'выключен'}"
                ) if self.reports else (0, 0)
            )
            suffix = f"; ручных позиций обновлено: {updated}"
            if failed:
                suffix += f", ошибок: {failed}"
            bot.answer_callback_query(
                call.id,
                f"TP{tp_no}: {'включён' if enabled_value else 'выключен'}{suffix}"
            )
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return

        if data.startswith("edit_bot_tp") and data[-1:].isdigit():
            tp_no = int(data[-1])
            moves, closes = get_bot_tp_config()
            if tp_no == 4:
                self._awaiting_stats_input = (f"bot_tp4_move_pct", "Движение TP4")
                bot.answer_callback_query(call.id)
                bot.send_message(chat_id, f"Введи движение TP4 и при желании 100% закрытия через пробел. Сейчас: +{fmt_num(moves[3])}% / 100% остатка. Например: <code>3 100</code>. Или /cancel")
            else:
                self._awaiting_stats_input = (f"bot_tp{tp_no}_pair", f"TP{tp_no}")
                bot.answer_callback_query(call.id)
                bot.send_message(chat_id, f"TP{tp_no}: сейчас +{fmt_num(moves[tp_no-1])}% / {fmt_num(closes[tp_no-1])}%. Введи ДВА числа через пробел: движение% закрытия%. Например: 1.0 25. Или /cancel")
            return

        if data == "view_bot_signal_orders":
            bot.answer_callback_query(call.id, "Собираю список...")
            bot.send_message(chat_id, self._format_bot_signal_orders())
            return
        if data == "toggle_manual_limit_value_changes" or data.startswith("set_manual_limit_value_changes:"):
            # Новая кнопка передаёт желаемое состояние (идемпотентно). Старый
            # callback toggle оставлен для кнопок из уже отправленных сообщений.
            # В случае ошибки сохранения включение автоизменений не разрешаем.
            toggle_lock = getattr(self.reports, "_manual_limit_toggle_lock", None) if self.reports else None
            amend_lock = getattr(self.reports, "_manual_limit_amend_lock", None) if self.reports else None
            disable_event = getattr(self.reports, "_manual_limit_disable_requested", None) if self.reports else None
            desired_state = None
            if data.startswith("set_manual_limit_value_changes:"):
                raw_state = data.partition(":")[2].strip()
                if raw_state not in {"0", "1"}:
                    bot.answer_callback_query(call.id, "Некорректное состояние кнопки; обнови меню настроек.")
                    self.log.warning("Получен неизвестный callback автоизменения лимиток: %r", data)
                    return
                desired_state = raw_state == "1"
            bot.answer_callback_query(call.id, "Переключаю автоизменение; текущий запрос ордера завершится…")
            try:
                if toggle_lock is not None:
                    with toggle_lock:
                        cur = bool(get_setting("manual_limit_value_changes_enabled", True))
                        enabled_now = (not cur) if desired_state is None else desired_state
                        # Сразу блокируем новые amend, до ожидания уже начатого запроса.
                        if not enabled_now and disable_event is not None:
                            disable_event.set()
                        if amend_lock is not None:
                            with amend_lock:
                                set_setting("manual_limit_value_changes_enabled", enabled_now)
                                if enabled_now and disable_event is not None:
                                    disable_event.clear()
                        else:
                            set_setting("manual_limit_value_changes_enabled", enabled_now)
                            if enabled_now and disable_event is not None:
                                disable_event.clear()
                else:
                    cur = bool(get_setting("manual_limit_value_changes_enabled", True))
                    enabled_now = (not cur) if desired_state is None else desired_state
                    if not enabled_now and disable_event is not None:
                        disable_event.set()
                    if amend_lock is not None:
                        with amend_lock:
                            set_setting("manual_limit_value_changes_enabled", enabled_now)
                            if enabled_now and disable_event is not None:
                                disable_event.clear()
                    else:
                        set_setting("manual_limit_value_changes_enabled", enabled_now)
            except Exception as exc:
                # Ошибка БД при выключении: Event остаётся установленным. При
                # любой неопределённости сохраняем fail-closed до перезапуска.
                if disable_event is not None:
                    disable_event.set()
                self.log.exception("Не удалось сохранить переключатель стоимости лимиток")
                # Повторная fail-closed запись: первичная ошибка может быть
                # временной. Если и она не удастся, runtime Event остаётся set.
                try:
                    set_setting("manual_limit_value_changes_enabled", False)
                    self.push_settings_pin()
                except Exception:
                    self.log.exception("Не удалось дополнительно сохранить аварийное отключение автоизменения")
                try:
                    bot.send_message(
                        chat_id,
                        "⛔ Не удалось подтвердить сохранение настройки в SQLite. "
                        "Автоизменение заблокировано в текущем процессе в целях безопасности. "
                        f"Проверь БД и настройку после перезапуска. Ошибка: {exc}",
                    )
                except Exception:
                    self.log.exception("Не удалось отправить сообщение об ошибке переключателя стоимости лимиток")
                return

            pin_saved = self.push_settings_pin()
            state_text = (
                "Автоизменение стоимости лимиток включено" if enabled_now
                else "Автоизменение выключено — ручные размеры ордеров сохраняются"
            )
            try:
                bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            except Exception:
                self.log.exception("Не удалось обновить кнопку переключателя стоимости лимиток")
            if not pin_saved:
                state_text += ". ВНИМАНИЕ: SQLite обновлена, но закреплённое сообщение Telegram не обновилось; перед redeploy проверь настройки."
                try:
                    bot.send_message(chat_id, "⚠️ " + state_text)
                except Exception:
                    self.log.exception("Не удалось отправить предупреждение о сохранении переключателя")
            else:
                try:
                    bot.send_message(chat_id, "✅ " + state_text)
                except Exception:
                    self.log.exception("Не удалось отправить подтверждение переключателя")
            return

        if data == "toggle_manual_trade_mgmt":
            cur = get_setting("manual_trade_management_enabled", getattr(cfg, "MANUAL_TRADE_MANAGEMENT_ENABLED_DEFAULT", True))
            set_setting("manual_trade_management_enabled", not cur)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Управление ручными сделками: {'включено' if not cur else 'выключено'}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "manage_excluded_symbols":
            current = get_excluded_symbols()
            text = "🚫 <b>Монеты-исключения</b>\nБот не ставит тейки/стопы и не берёт под управление эти монеты — ни по постам, ни ручные.\n\nТекущий список: " + (", ".join(current) if current else "пусто")
            kb2 = types.InlineKeyboardMarkup(row_width=1)
            kb2.add(types.InlineKeyboardButton("➕ Добавить монету(ы)", callback_data="excluded_add_prompt"))
            if current:
                kb2.add(types.InlineKeyboardButton("➖ Убрать монету(ы)", callback_data="excluded_remove_prompt"))
            kb2.add(types.InlineKeyboardButton("‹ Назад в настройки", callback_data="back_to_settings"))
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, text, reply_markup=kb2)
            return
        if data == "excluded_add_prompt":
            self._awaiting_excluded_add = True
            self._excluded_add_mode = "add"
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "Пришли тикер(ы) через запятую или пробел, например: <code>BTC, ETH, SOLUSDT</code>. Или /cancel.")
            return
        if data == "excluded_remove_prompt":
            self._awaiting_excluded_add = True
            self._excluded_add_mode = "remove"
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "Пришли тикер(ы), которые убрать из исключений, через запятую или пробел. Или /cancel.")
            return
        if data == "back_to_settings":
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "⚙️ Настройки учёта", reply_markup=report_settings_menu())
            return
        if data in ("set_manual_limit1_value", "set_manual_limit2_value"):
            slot = 1 if data.endswith("1_value") else 2
            key = f"manual_limit{slot}_value_usdt"
            value = float(get_setting(key, 10.0))
            self._awaiting_stats_input = (key, f"Стоимость {slot}-й лимитки")
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, f"💰 Введи номинал {slot}-й лимитки в USDT. При отсутствии открытой позиции бот выставит максимальное плечо монеты.\nТекущее значение: <b>{value:g} USDT</b>\nДиапазон: 0.01–100000 USDT.\n/cancel — отмена.")
            return

        if data == "set_manual_stop_pct":
            self._awaiting_stats_input = ("manual_trade_stop_percent", "Процент стопа ручных сделок")
            bot.answer_callback_query(call.id)
            bot.send_message(
                chat_id,
                "✏️ Введи процент стопа от цены 2-й ближайшей лимитки для ручных сделок. "
                "Допустимый диапазон: <b>1–10%</b>, можно дробное значение, например <code>2.5</code> или <code>4,25</code>.\n"
                "Изменение сохранится в SQLite и будет применено к открытым ручным позициям до TP1. После TP1 сохраняется существующая логика переноса стопа на +0,5% / −0,5%.\n"
                "/cancel — отмена."
            )
            return

        if data == "cycle_manual_stop_pct":
            cur = get_manual_stop_percent()
            presets = MANUAL_TRADE_STOP_PERCENT_PRESETS
            # Если в старой БД вдруг лежит дробное/устаревшее значение,
            # начинаем цикл с ближайшего элемента, сохраняя диапазон 1–10%.
            try:
                idx = presets.index(int(cur)) if float(cur).is_integer() and int(cur) in presets else -1
            except (TypeError, ValueError):
                idx = -1
            if not (0 <= idx < len(presets)):
                idx = -1
            new_val = presets[(idx + 1) % len(presets)]
            try:
                set_setting("manual_trade_stop_percent", float(new_val))
                persisted_stop = get_manual_stop_percent()
                if not math.isfinite(persisted_stop) or abs(persisted_stop - float(new_val)) > 1e-9:
                    raise RuntimeError(
                        f"проверка чтения настройки вернула {persisted_stop!r}, ожидалось {new_val}"
                    )
            except Exception as exc:
                self.log.exception("Не удалось подтвердить сохранение процента стопа ручных сделок")
                bot.answer_callback_query(
                    call.id,
                    "Ошибка сохранения стопа в SQLite. Стопы на бирже не менялись; повтори попытку.",
                    show_alert=True,
                )
                return
            # Сначала сохраняем отображаемые настройки. SQLite уже подтверждена;
            # если Telegram pin не обновится, торговую операцию всё равно пробуем
            # применить и отдельно сообщаем о проблеме восстановления настроек.
            pin_saved = self.push_settings_pin()
            if self.reports:
                try:
                    updated, failed = self.reports.apply_manual_settings_to_open_positions(
                        reason=f"изменён стоп на {new_val}%", force_stop_from_l2=True
                    )
                    updated, failed = max(0, int(updated)), max(0, int(failed))
                except Exception:
                    updated, failed = 0, 1
                    self.log.exception("Не удалось применить новый процент ручного стопа к открытым позициям")
            else:
                updated, failed = 0, 1
                self.log.error("Нельзя применить новый ручной стоп: менеджер отчётности/ручных сделок недоступен")
            suffix = f"; применено к {updated} открытым ручным позициям"
            if failed:
                suffix += f", ошибок: {failed}"
            if not pin_saved:
                suffix += "; предупреждение: закреплённое сообщение не обновлено"
            bot.answer_callback_query(call.id, f"Стоп ручных сделок: {new_val}%{suffix}")
            try:
                bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            except Exception:
                self.log.exception("Не удалось обновить меню после изменения процента ручного стопа")
            if not pin_saved:
                try:
                    bot.send_message(chat_id, "⚠️ Процент стопа сохранён в SQLite, но закреплённое сообщение настроек не обновлено. Перед повторным запуском проверь восстановление настроек.")
                except Exception:
                    self.log.exception("Не удалось уведомить о неуспешном обновлении закреплённых настроек")
            return

        if data == "cycle_manual_tp2_pct":
            cur = get_manual_tp_close_percent()
            idx = SIGNAL_TP2_CLOSE_PERCENT_PRESETS.index(cur) if cur in SIGNAL_TP2_CLOSE_PERCENT_PRESETS else 0
            new_val = SIGNAL_TP2_CLOSE_PERCENT_PRESETS[(idx + 1) % len(SIGNAL_TP2_CLOSE_PERCENT_PRESETS)]
            set_setting("manual_trade_tp_close_percent", new_val)
            # Сначала фиксируем новое значение в закреплённом сообщении — это
            # источник восстановления после redeploy. Затем перестраиваем живые TP.
            self.push_settings_pin()
            updated, failed = (self.reports.apply_manual_settings_to_open_positions(reason=f"изменён размер тейка на {new_val}%")
                               if self.reports else (0, 0))
            suffix = f"; применено к {updated} открытым ручным позициям"
            if failed:
                suffix += f", ошибок: {failed}"
            bot.answer_callback_query(call.id, f"На ручных сделках теперь закрываем {new_val}% объёма на тейке{suffix}")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "cycle_db_backup_hour":
            cur = int(get_setting("db_backup_hour", getattr(cfg, "DB_BACKUP_HOUR_UTC", 3)))
            idx = DB_BACKUP_HOUR_PRESETS.index(cur) if cur in DB_BACKUP_HOUR_PRESETS else 0
            new_val = DB_BACKUP_HOUR_PRESETS[(idx + 1) % len(DB_BACKUP_HOUR_PRESETS)]
            set_setting("db_backup_hour", new_val)
            self.push_settings_pin()
            bot.answer_callback_query(call.id, f"Час автобэкапа: {new_val}:00 UTC")
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=report_settings_menu())
            return
        if data == "backup_now":
            bot.answer_callback_query(call.id, "Отправляю бэкап...")
            self.reports.send_db_backup(caption="💾 Бэкап базы сделок по запросу")
            return
        if data == "test_notify":
            bot.answer_callback_query(call.id, "Отправляю...")
            muted = get_setting("only_trade_close_notifications", getattr(cfg, "ONLY_TRADE_CLOSE_NOTIFICATIONS", False))
            note = "\n\n(сейчас включён режим «только закрытие сделок» — обычные уведомления молчат, но тестовое всегда доходит)" if muted else ""
            self.notify(f"🔔 Это тестовое уведомление. Если ты его видишь — уведомления работают исправно.{note}", important=True)
            return
        if data == "test_pnl_alert":
            bot.answer_callback_query(call.id)
            row = last_trade_row()
            if not row:
                bot.send_message(chat_id, "В базе пока нет ни одной сделки — нечего проверять.", reply_markup=report_settings_menu())
            else:
                plus_th = get_setting("pnl_alert_plus", cfg.PNL_TRADE_ALERT_PLUS)
                minus_th = get_setting("pnl_alert_minus", cfg.PNL_TRADE_ALERT_MINUS)
                pnl = row["closed_pnl"]
                would = (plus_th and pnl >= abs(plus_th)) or (minus_th and pnl <= -abs(minus_th))
                text = f"Последняя сделка: {row['symbol']}, PnL={pnl:+.2f} USDT.\n"
                if would:
                    text += "✅ Превышает порог — шлю тестовый алерт отдельным сообщением."
                    self.reports.check_trade_pnl_threshold_alert({"closedPnl": pnl, "symbol": row["symbol"], "side": row["side"], "qty": row["qty"]})
                else:
                    text += "ℹ️ Порог не превышен — по ней алерт закономерно не приходил."
                bot.send_message(chat_id, text, reply_markup=report_settings_menu())
            return
        if data == "notification_log":
            bot.answer_callback_query(call.id)
            entries = get_notification_log(15)
            if not entries:
                bot.edit_message_text("📜 <b>Журнал уведомлений</b>\n\nПока пусто.", chat_id, msg_id, reply_markup=back_menu())
            else:
                tz_offset = get_setting("tz_offset", 0)
                lines = ["📜 <b>Журнал уведомлений</b> (последние 15)\n"]
                for e in entries:
                    dt = datetime.fromtimestamp(e["sent_at"] / 1000, tz=timezone.utc) + timedelta(hours=tz_offset)
                    short_text = e["text"].split("\n")[0][:60]
                    lines.append(f"<code>{dt.strftime('%d.%m %H:%M')}</code> — {short_text}")
                bot.edit_message_text("\n".join(lines), chat_id, msg_id, reply_markup=back_menu())
            return

        bot.answer_callback_query(call.id)

    # ---- запуск поллинга -------------------------------------------------

    def start_polling(self):
        def _run():
            self.log.info("Telegram-поллинг запущен.")
            while True:
                try:
                    try:
                        self.bot.remove_webhook()
                    except Exception:
                        pass
                    self.bot.infinity_polling(timeout=30, long_polling_timeout=30, skip_pending=True)
                    break
                except telebot.apihelper.ApiTelegramException as e:
                    if getattr(e, "error_code", None) == 409:
                        time.sleep(30)
                    else:
                        self.log.warning(f"Telegram-поллинг упал (API), перезапуск через 5 сек: {e}")
                        time.sleep(5)
                except Exception as e:
                    self.log.warning(f"Telegram-поллинг упал, перезапуск через 5 сек: {e}")
                    time.sleep(5)

        self._polling_thread = threading.Thread(target=_run, daemon=True, name="telegram")
        self._polling_thread.start()


# ============================================================================
# ТОЧКА ВХОДА
# ============================================================================

PLACEHOLDER_VALUES = {
    "ВСТАВЬ_СВОЙ_API_KEY", "ВСТАВЬ_СВОЙ_API_SECRET",
    "ВСТАВЬ_ТОКЕН_ОТ_BOTFATHER", "ВСТАВЬ_СВОЙ_CHAT_ID",
}


def setup_logging() -> logging.Logger:
    logger = logging.getLogger("merged_bybit_bot")
    logger.setLevel(logging.INFO)
    logger.propagate = False
    if logger.handlers:
        # setup_logging() вызван повторно (например, в тестах) — не плодим
        # дублирующиеся хендлеры, иначе каждая строка будет логироваться N раз.
        return logger

    fmt = logging.Formatter("%(asctime)s | %(levelname)-7s | %(threadName)-10s | %(message)s", "%Y-%m-%d %H:%M:%S")

    try:
        fh = RotatingFileHandler(resolve_path(cfg.LOG_FILE), maxBytes=cfg.LOG_MAX_BYTES, backupCount=cfg.LOG_BACKUP_COUNT, encoding="utf-8")
        fh.setFormatter(fmt)
        logger.addHandler(fh)
    except OSError as e:
        # Некоторые контейнерные окружения дают только read-only файловую
        # систему кроме определённых директорий — не роняем весь бот из-за
        # невозможности писать лог-файл, продолжаем хотя бы с логом в stdout.
        print(f"[WARN] Не удалось открыть лог-файл ({e}), логирую только в stdout.", file=sys.stderr)

    ch = logging.StreamHandler(sys.stdout)
    ch.setFormatter(fmt)
    logger.addHandler(ch)
    return logger


def validate_config(logger: logging.Logger) -> bool:
    problems = []
    if cfg.API_KEY in PLACEHOLDER_VALUES or not cfg.API_KEY:
        problems.append("API_KEY не задан.")
    if cfg.API_SECRET in PLACEHOLDER_VALUES or not cfg.API_SECRET:
        problems.append("API_SECRET не задан.")
    if cfg.TELEGRAM_BOT_TOKEN in PLACEHOLDER_VALUES or not cfg.TELEGRAM_BOT_TOKEN:
        problems.append("TELEGRAM_BOT_TOKEN не задан.")
    if not cfg.TELEGRAM_CHAT_ID:
        logger.warning("TELEGRAM_CHAT_ID пуст — бот будет отвечать в ЛЮБОМ чате. Рекомендуется задать после первого /start.")
    if cfg.MAX_OPEN_POSITIONS < 1:
        problems.append("MAX_OPEN_POSITIONS должен быть >= 1.")
    if cfg.LEVERAGE < 1:
        problems.append("LEVERAGE должен быть >= 1.")
    if cfg.POSITION_PCT_OF_EQUITY <= 0:
        problems.append("POSITION_PCT_OF_EQUITY должен быть > 0.")
    if cfg.PROFIT_LOCK_TRIGGER_PCT <= 0:
        problems.append("PROFIT_LOCK_TRIGGER_PCT должен быть > 0.")
    if cfg.PROFIT_LOCK_MIN_USDT <= 0:
        problems.append("PROFIT_LOCK_MIN_USDT должен быть > 0.")
    if getattr(cfg, "ENABLE_FIXED_STOP_LOSS", False) and getattr(cfg, "FIXED_STOP_LOSS_PCT", 0) <= 0:
        problems.append("FIXED_STOP_LOSS_PCT должен быть > 0, если ENABLE_FIXED_STOP_LOSS включён.")
    if getattr(cfg, "ENABLE_LONG_MODE", False):
        if getattr(cfg, "LONG_TAKE_PROFIT_PCT", 0) <= 0:
            problems.append("LONG_TAKE_PROFIT_PCT должен быть > 0.")
        if getattr(cfg, "ENABLE_FIXED_STOP_LOSS", False) and getattr(cfg, "LONG_FIXED_STOP_LOSS_PCT", 0) <= 0:
            problems.append("LONG_FIXED_STOP_LOSS_PCT должен быть > 0, если ENABLE_FIXED_STOP_LOSS включён.")
    if getattr(cfg, "ENABLE_VOLUME_FILTER", False) and getattr(cfg, "VOLUME_SPIKE_MULTIPLIER", 1) < 1:
        problems.append("VOLUME_SPIKE_MULTIPLIER должен быть >= 1, если ENABLE_VOLUME_FILTER включён.")
    if getattr(cfg, "ENABLE_SHORT_LOW_BOUNCE_FILTER", False) and getattr(cfg, "SHORT_LOW_BOUNCE_PCT", 0) <= 0:
        problems.append("SHORT_LOW_BOUNCE_PCT должен быть > 0, если ENABLE_SHORT_LOW_BOUNCE_FILTER включён.")
    if getattr(cfg, "ENABLE_LONG_LOW_BOUNCE_FILTER", False) and getattr(cfg, "LONG_LOW_BOUNCE_PCT", 0) <= 0:
        problems.append("LONG_LOW_BOUNCE_PCT должен быть > 0, если ENABLE_LONG_LOW_BOUNCE_FILTER включён.")
    if getattr(cfg, "VOLUME_LOOKBACK_CANDLES", 1) < 1:
        problems.append("VOLUME_LOOKBACK_CANDLES должен быть >= 1.")
    if getattr(cfg, "ENABLE_POST_ONLY_ENTRY", False) and getattr(cfg, "POST_ONLY_TIMEOUT_SEC", 0) <= 0:
        problems.append("POST_ONLY_TIMEOUT_SEC должен быть > 0, если ENABLE_POST_ONLY_ENTRY включён.")
    if getattr(cfg, "POST_ONLY_OFFSET_PCT", 0) < 0:
        problems.append("POST_ONLY_OFFSET_PCT должен быть >= 0.")
    if getattr(cfg, "FILTER_REJECT_COOLDOWN_MINUTES", 0) < 0:
        problems.append("FILTER_REJECT_COOLDOWN_MINUTES должен быть >= 0.")
    if cfg.SMART_EXIT_MIN_PROFIT_USDT <= 0:
        problems.append("SMART_EXIT_MIN_PROFIT_USDT должен быть > 0.")
    if cfg.STALL_MIN_SECONDS < 0 or cfg.SMART_EXIT_MIN_SECONDS < 0:
        problems.append("STALL_MIN_SECONDS и SMART_EXIT_MIN_SECONDS должны быть >= 0.")
    if cfg.STALL_DROP_ADAPTIVE_FACTOR < 0:
        problems.append("STALL_DROP_ADAPTIVE_FACTOR должен быть >= 0.")
    if cfg.STALL_DROP_MAX_PCT < cfg.STALL_DROP_PCT:
        problems.append("STALL_DROP_MAX_PCT должен быть >= STALL_DROP_PCT.")
    if cfg.MAX_RETRIES < 1:
        problems.append("MAX_RETRIES должен быть >= 1.")
    if cfg.REQUEST_TIMEOUT_SEC <= 0:
        problems.append("REQUEST_TIMEOUT_SEC должен быть > 0.")
    if cfg.POLL_INTERVAL_SEC <= 0:
        problems.append("POLL_INTERVAL_SEC должен быть > 0.")
    if cfg.SYNC_INTERVAL_SEC <= 0:
        problems.append("SYNC_INTERVAL_SEC должен быть > 0.")
    if cfg.LOOKBACK_MINUTES <= 0:
        problems.append("LOOKBACK_MINUTES должен быть > 0.")
    if cfg.WATCH_MAX_MINUTES <= 0:
        problems.append("WATCH_MAX_MINUTES должен быть > 0.")

    if problems:
        logger.error("Конфигурация некорректна, бот не запущен:")
        for p in problems:
            logger.error(f"  - {p}")
        return False
    return True


def get_external_ip() -> str:
    try:
        import requests
        return requests.get("https://api.ipify.org", timeout=5).text
    except Exception:
        return "неизвестен"


def supervised_thread(target, name: str, notifier: UnifiedBot, logger: logging.Logger):
    """Оборачивает фоновую функцию: если она упадёт — залогирует, уведомит
    администратора и перезапустит через паузу вместо того, чтобы тихо
    погибнуть и оставить бота без синхронизации/отчётов/торговли."""

    def wrapper():
        while True:
            try:
                target()
                break  # функция сама решила завершиться штатно
            except Exception as e:
                logger.exception("Поток '%s' упал", name)
                notifier.notify(
                    f"⚠️ <b>Внутренний сбой</b>\n\nФоновый процесс «{name}» упал с ошибкой и будет перезапущен через 15 секунд:\n<code>{e}</code>"
                )
                time.sleep(15)

    t = threading.Thread(target=wrapper, name=name, daemon=True)
    t.start()
    return t


def setup_graceful_shutdown(notifier: UnifiedBot, engine: ShortPumpBot, logger: logging.Logger):
    def handler(signum, frame):
        sig_name = signal.Signals(signum).name
        logger.info("Получен сигнал %s — бот останавливается.", sig_name)
        notifier.notify(f"🛑 <b>Бот остановлен</b> (сигнал {sig_name}) — обычно это плановый передеплой.")
        notifier.flush_notifications()  # дожидаемся реальной отправки, иначе сообщение теряется вместе с процессом
        engine.stop()
        raise SystemExit(0)

    try:
        signal.signal(signal.SIGTERM, handler)
        signal.signal(signal.SIGINT, handler)
    except Exception:
        pass


def main():
    logger = setup_logging()

    if not validate_config(logger):
        sys.exit(1)

    logger.info("Внешний IP этого сервера: %s", get_external_ip())

    init_db()

    client = BybitClient(logger)
    tg = UnifiedBot(logger)

    # ВАЖНО: восстанавливаем настройки из закреплённого в Telegram сообщения
    # ДО создания движка и репортера — так они читают уже актуальные (а не
    # дефолтные из свежего config.py/пустой БД) значения при старте после
    # передеплоя на платформах с эфемерным диском (Railway и т.п.).
    logger.info("Синхронизирую настройки с закреплённым сообщением в Telegram...")
    tg.sync_settings_from_pinned()

    engine = ShortPumpBot(logger, client, tg)
    reports = ReportsEngine(logger, client, tg)
    tg.attach(engine, reports)

    # Восстанавливаем отслеживание сделок по постам с биржи — на случай,
    # если локальная база потерялась при редеплое (например, Railway без
    # постоянного диска пересоздаёт контейнер с нуля). Делается ДО запуска
    # фонового мониторинга, чтобы тот сразу видел восстановленные позиции.
    logger.info("Сверяю сигнальные позиции с биржей (восстановление после возможного редеплоя)...")
    reports.reconcile_signal_positions_from_exchange()

    # Пересобираем и закрепляем сообщение с настройками — либо создаём его
    # впервые, либо обновляем уже существующее актуальным содержимым.
    tg.push_settings_pin()

    setup_graceful_shutdown(tg, engine, logger)

    # Telegram-поллинг — своим потоком, сразу
    tg.start_polling()

    # Фоновые процессы учёта/отчётности
    supervised_thread(reports.sync_loop, "Синхронизация сделок (REST)", tg, logger)
    supervised_thread(reports.open_positions_pnl_alert_loop, "PnL-алерт открытых позиций", tg, logger)
    supervised_thread(reports.daily_report_loop, "Ежедневный отчёт", tg, logger)
    supervised_thread(reports.weekly_report_loop, "Еженедельный отчёт", tg, logger)
    supervised_thread(reports.db_backup_loop, "Автобэкап БД в Telegram", tg, logger)
    supervised_thread(reports.signal_positions_monitor_loop, "Мониторинг сигнальных позиций", tg, logger)
    supervised_thread(reports.okx_feed_monitor_loop, "Мониторинг постов трейдера OKX", tg, logger)
    supervised_thread(reports.manual_positions_scan_loop, "Сканирование ручных позиций", tg, logger)

    logger.info("Бот запущен. Ожидаю команды...")
    tg.notify("✅ <b>Объединённый бот запущен</b> (торговля + учёт) и готов к работе 24/7.")

    # Торговый движок — в главном потоке, с автоперезапуском при сбое.
    # Задержка между попытками растёт с числом ПОДРЯД идущих сбоев и
    # сбрасывается только после того, как движок отработал достаточно долго
    # (иначе быстро сменяющиеся сбои не будут давать бирже/сети время на
    # восстановление, а будут долбить перезапусками каждые 5 секунд).
    restart_count = 0
    max_delay = 300
    min_healthy_run_sec = 120
    while True:
        run_started_at = time.time()
        try:
            if restart_count > 0:
                tg.notify(f"🔁 <b>Повторно запускаю торговый движок</b> (попытка №{restart_count + 1})...")
            engine.run()
            break  # engine.run() завершился штатно (Стоп из Telegram)
        except Exception as e:
            run_duration = time.time() - run_started_at
            if run_duration >= min_healthy_run_sec:
                # движок успел проработать нормально какое-то время, прежде
                # чем упасть — это не "шторм" сбоев подряд, сбрасываем счётчик
                restart_count = 0
            restart_count += 1
            delay = min(5 * restart_count, max_delay)
            logger.exception("Торговый движок упал (попытка №%s), перезапуск через %sс", restart_count, delay)
            tg.notify(f"🔴 <b>Торговый движок упал и перезапускается</b>\n\nПопытка №{restart_count}, повтор через {delay} сек:\n<code>{e}</code>")
            time.sleep(delay)
            tg.running = True  # engine.run() выходит из цикла, если tg.running стал False только по /stop


if __name__ == "__main__":
    # Последний рубеж для истинной работы 24/7: даже если main() упадёт
    # целиком ДО того, как заработал собственный (более умный) механизм
    # перезапуска торгового движка внутри main() — например, кратковременный
    # сбой сети при самом старте, ошибка инициализации БД и т.п. — процесс
    # не умирает насовсем, а откатывается назад и пробует снова с задержкой.
    # Осознанный sys.exit(1) из validate_config() (битый конфиг, чинить
    # руками) — исключение: его не перезапускаем бесконечно.
    _startup_attempt = 0
    _max_startup_delay = 300
    while True:
        try:
            main()
            break  # main() завершился штатно (например, дошли до конца без ошибок)
        except SystemExit:
            raise
        except KeyboardInterrupt:
            raise
        except Exception:
            _startup_attempt += 1
            delay = min(30 * _startup_attempt, _max_startup_delay)
            print(
                f"[FATAL] main() упал целиком (попытка №{_startup_attempt}), "
                f"перезапускаю процесс через {delay} сек:",
                file=sys.stderr,
            )
            traceback.print_exc()
            time.sleep(delay)
