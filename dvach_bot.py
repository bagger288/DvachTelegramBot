#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Telegram-бот для отслеживания и постинга в треды 2ch (Двач).
Версия: 3.0 (с отправкой ответов прямо из Telegram, вложениями и решением визуальной EmojiCaptcha).
"""

import asyncio
import base64
import http.server
import io
import json
import logging
import os
import re
import secrets
import socketserver
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import requests
from bs4 import BeautifulSoup
from PIL import Image, ImageDraw
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, InputMediaVideo, Message, Update
from telegram._message import parse_message_entities
from telegram.constants import ParseMode
from telegram.error import BadRequest, RetryAfter
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ------------------------- CONFIG -------------------------

def _int_env(name: str, default: str) -> int:
    raw = (os.environ.get(name) or "").strip()
    if not raw:
        raw = default
    try:
        return int(raw)
    except ValueError:
        raise SystemExit(f"Переменная {name} должна быть целым числом, получено: {raw!r}")


def _float_env(name: str, default: str) -> float:
    raw = (os.environ.get(name) or "").strip()
    if not raw:
        raw = default
    try:
        return float(raw)
    except ValueError:
        raise SystemExit(f"Переменная {name} должна быть числом, получено: {raw!r}")


BOT_TOKEN = os.environ.get("DVACH_BOT_TOKEN", "").strip()
USER_ID = _int_env("DVACH_USER_ID", "0")
POLL_INTERVAL = _int_env("DVACH_POLL_INTERVAL", "15")

# Задержки между отправками постов для защиты от Telegram Flood Control (429 Too Many Requests)
HISTORY_SEND_DELAY = _float_env("DVACH_HISTORY_DELAY", "2.5")  # сек при выгрузке /watch <url> all
LIVE_SEND_DELAY = _float_env("DVACH_LIVE_DELAY", "1.5")        # сек при получении пачки новых постов

# Порт встроенного веб-сервера health-check (0 чтобы отключить, либо 8080 для облачного хостинга):
PORT = int(os.environ.get("PORT") or os.environ.get("DVACH_HEALTH_PORT") or "8080")

def _normalize_domain(d: str) -> str:
    d = d.strip().rstrip("/")
    if not re.match(r"^https?://", d, re.IGNORECASE):
        d = f"https://{d}"
    return d


PRIMARY_DOMAIN = _normalize_domain(os.environ.get("DVACH_DOMAIN", "https://2ch.su"))
FALLBACK_DOMAINS = [
    PRIMARY_DOMAIN,
    "https://2ch.life",
    "https://2ch.hk",
    "https://2ch.org",
]
DOMAINS = list(dict.fromkeys(FALLBACK_DOMAINS))

STATE_FILE = Path(__file__).with_name("state.json")
START_TIME = time.time()

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

TELEGRAM_ALLOWED_TAGS = {"b", "strong", "i", "em", "u", "s", "strike", "del", "code", "pre", "tg-spoiler"}
THREAD_URL_RE = re.compile(r"2ch\.\w+/([a-z0-9]+)/res/(\d+)")
MAX_MSG_IDS_PER_THREAD = 1000


class _PendingPostFilter(filters.MessageFilter):
    """Матчит сообщение, только если для этого чата сейчас ждём текст/медиа нового поста
    (после нажатия кнопки "✏️ Новый пост"). Проверяется динамически при каждом апдейте,
    поэтому когда ожидания нет — просто не матчится, и сообщение уходит другим хэндлерам."""

    def filter(self, message):
        return message.chat_id in PENDING_POST


PENDING_POST_FILTER = _PendingPostFilter()


class _PendingUnwatchFilter(filters.MessageFilter):
    """Матчит сообщение, только если для этого чата сейчас ждём номер треда для удаления
    (после /unwatch без аргументов) и сообщение — это просто число."""

    def filter(self, message):
        text = (message.text or "").strip()
        return message.chat_id in PENDING_UNWATCH and text.isdigit()


PENDING_UNWATCH_FILTER = _PendingUnwatchFilter()


class _PendingDraftFieldFilter(filters.MessageFilter):
    """Матчит сообщение, только если для этого чата сейчас ждём текст для поля
    черновика поста (имя или тема) — после нажатия соответствующей кнопки на
    экране настроек перед капчей."""

    def filter(self, message):
        return message.chat_id in PENDING_DRAFT_FIELD


PENDING_DRAFT_FIELD_FILTER = _PendingDraftFieldFilter()

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger("dvach_bot")


# ------------------------- STATE -------------------------
#
# Два режима хранения state.json:
#   1. Локальный файл (по умолчанию) — как было всегда, для VPS/Termux, где
#      файловая система персистентна между перезапусками.
#   2. GitHub Gist — включается заданием DVACH_GIST_TOKEN (Personal Access
#      Token со скоупом "gist"). Нужен для хостинга на Render и подобных
#      платформах с эфемерной файловой системой (файлы стираются при каждом
#      передеплое/рестарте). DVACH_GIST_ID можно не указывать при самом
#      первом запуске — бот создаст новый приватный (secret) гист сам и
#      выведет его ID в лог; это значение ОБЯЗАТЕЛЬНО нужно потом сохранить
#      в переменную окружения DVACH_GIST_ID, иначе при следующем перезапуске
#      состояние потеряется и создастся ещё один новый гист вместо этого же.

GITHUB_API = "https://api.github.com"
GIST_TOKEN = os.environ.get("DVACH_GIST_TOKEN", "").strip()
GIST_ID = os.environ.get("DVACH_GIST_ID", "").strip()
GIST_FILENAME = "state.json"
USE_GIST_BACKEND = bool(GIST_TOKEN)


def _gist_headers() -> dict:
    return {
        "Authorization": f"token {GIST_TOKEN}",
        "Accept": "application/vnd.github+json",
        "User-Agent": USER_AGENT,
    }


def _create_new_gist() -> str:
    payload = {
        "description": "dvach_bot state.json (auto-created)",
        "public": False,
        "files": {GIST_FILENAME: {"content": json.dumps({"mode": "preview", "threads": {}}, indent=2)}},
    }
    resp = requests.post(f"{GITHUB_API}/gists", headers=_gist_headers(), json=payload, timeout=15)
    resp.raise_for_status()
    return resp.json()["id"]


def _load_state_from_gist() -> dict:
    default = {"mode": "preview", "threads": {}}
    global GIST_ID

    if not GIST_ID:
        try:
            GIST_ID = _create_new_gist()
            logger.warning(
                "\n" + "=" * 72 +
                "\nСоздан новый Gist для хранения состояния бота: %s\n"
                "ОБЯЗАТЕЛЬНО сохрани этот ID в переменную окружения DVACH_GIST_ID —\n"
                "иначе при следующем перезапуске состояние потеряется и создастся\n"
                "ЕЩЁ ОДИН новый гист вместо использования уже созданного.\n" + "=" * 72,
                GIST_ID,
            )
        except Exception as e:
            logger.error("Не удалось создать новый Gist для состояния: %s", e)
            return default

    try:
        resp = requests.get(f"{GITHUB_API}/gists/{GIST_ID}", headers=_gist_headers(), timeout=15)
        if resp.status_code != 200:
            logger.error("Не удалось загрузить состояние из Gist (HTTP %s): %s", resp.status_code, resp.text[:300])
            return default
        file_info = resp.json().get("files", {}).get(GIST_FILENAME)
        if not file_info:
            logger.info("В Gist %s ещё нет файла %s — стартуем с пустого состояния.", GIST_ID, GIST_FILENAME)
            return default
        content = file_info.get("content", "")
        if file_info.get("truncated") and file_info.get("raw_url"):
            # Gist API отдаёт content целиком только для файлов примерно до 1МБ;
            # для больших файлов нужно отдельно забирать содержимое по raw_url.
            content = requests.get(file_info["raw_url"], headers=_gist_headers(), timeout=15).text
        data = json.loads(content) if content.strip() else default
        data.setdefault("mode", "preview")
        data.setdefault("threads", {})
        return data
    except Exception as e:
        logger.error("Ошибка при загрузке состояния из Gist: %s", e)
        return default


def _save_state_to_gist(state: dict) -> None:
    if not GIST_ID:
        return  # создание гиста при старте не удалось — уже залогировано, не пишем в никуда
    try:
        payload = {"files": {GIST_FILENAME: {"content": json.dumps(state, ensure_ascii=False, indent=2)}}}
        resp = requests.patch(f"{GITHUB_API}/gists/{GIST_ID}", headers=_gist_headers(), json=payload, timeout=15)
        if resp.status_code != 200:
            logger.error("Не удалось сохранить состояние в Gist (HTTP %s): %s", resp.status_code, resp.text[:300])
    except Exception as e:
        logger.error("Ошибка при сохранении состояния в Gist: %s", e)


def load_state() -> dict:
    if USE_GIST_BACKEND:
        return _load_state_from_gist()

    if STATE_FILE.exists():
        try:
            data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
            data.setdefault("mode", "preview")
            data.setdefault("threads", {})
            return data
        except json.JSONDecodeError:
            pass
    return {
        "mode": "preview",
        "threads": {},
    }


def save_state(state: dict) -> None:
    if USE_GIST_BACKEND:
        _save_state_to_gist(state)
        return
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


STATE = load_state()

# Словарь активных фоновых задач выгрузки истории тредов: key -> asyncio.Task
ACTIVE_HISTORY_TASKS: dict = {}

# Треды, для которых сейчас ждём "следующее сообщение = новый пост" после нажатия
# кнопки "✏️ Новый пост": chat_id -> {"board": ..., "thread": ...}
PENDING_POST: Dict[int, dict] = {}

# Список тредов, показанный по /unwatch без аргументов, в порядке нумерации.
# chat_id -> список ключей тредов (thread_key), номер N в сообщении соответствует
# элементу с индексом N-1.
PENDING_UNWATCH: Dict[int, dict] = {}

# Буфер частей альбома (Telegram присылает несколько фото одним альбомом как
# НЕСКОЛЬКО отдельных сообщений с общим media_group_id, а не одним сообщением
# со списком файлов) — см. collect_media_group_messages().
MEDIA_GROUP_BUFFERS: Dict[str, List] = {}
MEDIA_GROUP_DELAY = 1.5  # сек — пауза ожидания "остальных частей" альбома
MAX_FILES_PER_POST = 4  # 2ch отбрасывает лишние файлы сверх этого лимита на пост

# Черновики поста, ожидающие экрана настроек (имя/тема/sage/оригинальное имя файла)
# перед запросом капчи. session_id -> {board, thread, comment, files_data, name,
# subject, sage, keep_original_filename, can_keep_original, chat_id, settings_msg_id}.
POST_DRAFTS: Dict[str, dict] = {}

# Ожидание текстового ввода для поля черновика (имя/тема), после нажатия
# соответствующей кнопки на экране настроек: chat_id -> {"session_id":..., "field": "name"|"subject"}
PENDING_DRAFT_FIELD: Dict[int, dict] = {}

# Очищаем устаревший флаг loading_history при перезапуске бота
for _t_info in STATE.get("threads", {}).values():
    if _t_info.get("loading_history"):
        _t_info["loading_history"] = False


def thread_key(board: str, thread: str) -> str:
    return f"{board}:{thread}"


def parse_thread_url(text: str) -> Optional[Tuple[str, str]]:
    m = THREAD_URL_RE.search(text.strip())
    if not m:
        return None
    return m.group(1), m.group(2)


POST_FLAG_RE = re.compile(r"--(name|subject)\b\s*", re.IGNORECASE)


def extract_post_flags(text: str) -> Tuple[str, str, str]:
    """Достаёт необязательные --name и --subject из текста поста.

    Флаги ставятся В КОНЦЕ сообщения, после самого текста поста, например:
        Текст поста --name Аноним2 --subject Заголовок треда
    Значение каждого флага — всё до следующего флага или до конца строки.
    Если флагов нет вообще, возвращает исходный текст без изменений.

    Возвращает (name, subject, оставшийся_текст_поста).
    """
    matches = list(POST_FLAG_RE.finditer(text))
    if not matches:
        return "", "", text

    comment = text[: matches[0].start()].strip()
    name, subject = "", ""
    for i, m in enumerate(matches):
        flag = m.group(1).lower()
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        value = text[start:end].strip()
        if flag == "name":
            name = value
        elif flag == "subject":
            subject = value
    return name, subject, comment


def get_internal_chat_id() -> Optional[str]:
    s = str(USER_ID)
    if s.startswith("-100"):
        return s[4:]
    return None


# ------------------------- HTML → TELEGRAM HTML -------------------------

def clean_comment(raw_html: str, resolve_ref=None) -> str:
    if not raw_html:
        return ""

    soup = BeautifulSoup(raw_html, "html.parser")

    for br in soup.find_all("br"):
        br.replace_with("\n")

    for a in soup.find_all("a"):
        classes = a.get("class") or []
        href = a.get("href", "")
        if "post-reply-link" in classes:
            data_num = a.get("data-num")
            url = resolve_ref(data_num) if (resolve_ref and data_num) else None
            if url:
                a.attrs = {"href": url}
            else:
                a.replace_with(a.get_text())
        elif href.startswith("/"):
            a.replace_with(a.get_text())
        else:
            a.attrs = {"href": href}

    for span in soup.find_all("span"):
        classes = span.get("class") or []
        if "spoiler" in classes:
            span.name = "tg-spoiler"
            span.attrs = {}
        elif "s" in classes:
            span.name = "s"
            span.attrs = {}
        elif "u" in classes:
            span.name = "u"
            span.attrs = {}
        else:
            span.unwrap()

    for tag in soup.find_all(True):
        if tag.name == "strong":
            tag.name = "b"
        elif tag.name == "em":
            tag.name = "i"
        elif tag.name not in TELEGRAM_ALLOWED_TAGS and tag.name != "a":
            tag.unwrap()

    return str(soup).strip()


def extract_referenced_nums(raw_html: str) -> List[str]:
    if not raw_html:
        return []
    soup = BeautifulSoup(raw_html, "html.parser")
    nums = []
    for a in soup.find_all("a", class_="post-reply-link"):
        data_num = a.get("data-num")
        if data_num and data_num.isdigit():
            nums.append(data_num)
    return nums


# ------------------------- 2CH API & MIRRORS -------------------------

# Последний домен, с которого удалось успешно получить тред — пробуем его первым
# при следующих запросах, чтобы не тратить время на заведомо недоступное основное
# зеркало при каждом опросе (актуально при длительных блокировках).
_LAST_WORKING_DOMAIN: Optional[str] = None


def _domain_order() -> List[str]:
    if _LAST_WORKING_DOMAIN and _LAST_WORKING_DOMAIN in DOMAINS:
        return [_LAST_WORKING_DOMAIN] + [d for d in DOMAINS if d != _LAST_WORKING_DOMAIN]
    return list(DOMAINS)


def fetch_thread(board: str, thread: str) -> Optional[dict]:
    global _LAST_WORKING_DOMAIN
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
    for domain in _domain_order():
        url = f"{domain}/{board}/res/{thread}.json"
        try:
            resp = requests.get(url, timeout=12, headers=headers)
            if resp.status_code == 200:
                if domain != _LAST_WORKING_DOMAIN:
                    logger.info("Рабочее зеркало для запросов треда переключено на %s", domain)
                    _LAST_WORKING_DOMAIN = domain
                return resp.json()
        except requests.RequestException as e:
            logger.debug("Сбой запроса к %s: %s", url, e)
    logger.warning("Не удалось получить тред %s/%s ни с одного зеркала", board, thread)
    return None


def get_posts(thread_json: dict) -> List[dict]:
    try:
        return thread_json["threads"][0]["posts"]
    except (KeyError, IndexError):
        return []


def is_video(file_obj: dict) -> bool:
    name = file_obj.get("name", "") or file_obj.get("fullname", "")
    return name.lower().endswith((".webm", ".mp4"))


def is_full_video_send(file_obj: dict, mode: str) -> bool:
    """
    В режиме full для видео (.mp4 или .webm) нужно слать сам видеофайл через
    send_video/InputMediaVideo, а не пытаться отправить его как фото.
    """
    return mode == "full" and is_video(file_obj)


def file_url(file_obj: dict, mode: str) -> str:
    domain = DOMAINS[0]
    if is_video(file_obj) and mode == "preview":
        return f"{domain}{file_obj['thumbnail']}"
    path = file_obj["thumbnail"] if mode == "preview" else file_obj["path"]
    return f"{domain}{path}"


# ------------------------- ОТПРАВКА ПОСТА -------------------------

async def _send_with_reply_fallback(send_coro_factory, reply_to: Optional[int], max_retries: int = 4):
    for attempt in range(max_retries):
        target_reply = reply_to if attempt == 0 else None
        try:
            return await send_coro_factory(reply_to_message_id=target_reply)
        except RetryAfter as e:
            wait_s = float(e.retry_after) + 1.0
            logger.warning(
                "Telegram Flood limit (429 RetryAfter)! Ожидание %s сек (попытка %s/%s)...",
                wait_s,
                attempt + 1,
                max_retries,
            )
            await asyncio.sleep(wait_s)
        except BadRequest as e:
            if reply_to and "reply" in str(e).lower():
                logger.info("Не удалось сделать reply на %s (%s), отправляю без reply", reply_to, e)
                try:
                    return await send_coro_factory(reply_to_message_id=None)
                except RetryAfter as retry_err:
                    wait_s = float(retry_err.retry_after) + 1.0
                    logger.warning("Telegram Flood limit при повторе: ожидание %s сек...", wait_s)
                    await asyncio.sleep(wait_s)
                    return await send_coro_factory(reply_to_message_id=None)
            else:
                raise
        except Exception as e:
            if "Too Many Requests" in str(e) or "retry after" in str(e).lower():
                logger.warning("Перехвачена ошибка 429: %s. Пауза 5 сек перед повтором...", e)
                await asyncio.sleep(5.0)
            else:
                raise
    return None


def _remember_msg_id(msg_ids: dict, num, message_id: int) -> None:
    msg_ids[str(num)] = message_id
    if len(msg_ids) > MAX_MSG_IDS_PER_THREAD:
        oldest_key = next(iter(msg_ids))
        del msg_ids[oldest_key]


def _build_caption(board: str, thread: str, post: dict, msg_ids: dict, internal_chat_id: Optional[str]) -> str:
    num = post.get("num")
    raw_comment = post.get("comment", "")

    def resolve_ref(data_num: str) -> Optional[str]:
        target_msg_id = msg_ids.get(data_num)
        if target_msg_id and internal_chat_id:
            return f"https://t.me/c/{internal_chat_id}/{target_msg_id}"
        return f"{DOMAINS[0]}/{board}/res/{thread}.html#{data_num}"

    comment = clean_comment(raw_comment, resolve_ref=resolve_ref)
    link = f"{DOMAINS[0]}/{board}/res/{thread}.html#{num}"

    # Имя автора (по умолчанию Аноним)
    name = clean_comment((post.get("name") or "Аноним").strip()) or "Аноним"

    # Дата и время (например: 31/08/26 Пнд 23:56:15)
    date_str = (post.get("date") or "").strip()
    date_part = f" {date_str}" if date_str else ""

    # Порядковый номер поста в треде (1-600)
    seq = post.get("number")
    seq_str = f" {seq}" if seq is not None else ""

    # Тема (если есть)
    subject = (post.get("subject") or "").strip()
    subject_part = f"<b>{clean_comment(subject)}</b> " if subject else ""

    header = f'{subject_part}{name}{date_part} <a href="{link}">№{num}</a>{seq_str}'.strip()
    caption = f"{header}\n\n{comment}".strip() if comment else header
    return caption or header


def build_show_full_markup(board: str, thread: str, num) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton("🔍 Показать оригинал", callback_data=f"full:{board}:{thread}:{num}")]]
    )


def build_newpost_markup(board: str, thread: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton("✏️ Новый пост", callback_data=f"newpost:{board}:{thread}")]]
    )


async def _delete_message_silently(context: ContextTypes.DEFAULT_TYPE, chat_id: int, message_id: Optional[int]) -> None:
    """Удаляет сообщение по chat_id/message_id, полностью игнорируя ошибки (уже
    удалено вручную, нет прав, слишком старое и т.п.). Общий хелпер для всех мест,
    где бот подчищает за собой служебные сообщения."""
    if not message_id:
        return
    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
    except Exception:
        pass


async def _delete_own_message_silently(message) -> None:
    """Удаляет входящее сообщение пользователя (саму команду или служебный ответ)
    сразу после обработки — молча, если это не получится."""
    try:
        await message.delete()
    except Exception:
        pass


async def refresh_newpost_button(context: ContextTypes.DEFAULT_TYPE, board: str, thread: str, info: dict) -> None:
    """Переносит кнопку "✏️ Новый пост" в самый низ треда: удаляет старое сообщение
    с кнопкой (если было) и присылает новое, уже после самого последнего поста.
    Вызывать один раз ПОСЛЕ отправки очередной пачки новых постов, а не на каждый пост."""
    old_id = info.get("newpost_msg_id")
    if old_id:
        await _delete_message_silently(context, USER_ID, old_id)

    try:
        sent = await context.bot.send_message(
            chat_id=USER_ID,
            text=f"— /{board}/{thread} —",
            reply_markup=build_newpost_markup(board, thread),
            disable_notification=True,  # это служебная кнопка-якорь, отдельный пуш ни к чему
        )
        info["newpost_msg_id"] = sent.message_id
        save_state(STATE)
    except Exception as e:
        logger.warning("Не удалось обновить кнопку 'Новый пост' для %s/%s: %s", board, thread, e)


async def remove_newpost_button(context: ContextTypes.DEFAULT_TYPE, info: dict) -> None:
    """Убирает сообщение с кнопкой "Новый пост", например при /unwatch."""
    msg_id = info.get("newpost_msg_id")
    if not msg_id:
        return
    await _delete_message_silently(context, USER_ID, msg_id)


SERVICE_MESSAGE_TTL = 10.0  # сек — через сколько самоудаляются служебные подтверждения бота


def schedule_message_deletion(context: ContextTypes.DEFAULT_TYPE, chat_id: int, message_id: int,
                               delay: float = SERVICE_MESSAGE_TTL) -> None:
    """Ставит служебное сообщение бота (приглашение/подтверждение) на самоудаление
    через delay секунд. Fire-and-forget — не блокирует обработку и не мешает, если
    сообщение к тому моменту уже удалено вручную или недоступно."""
    async def _worker():
        await asyncio.sleep(delay)
        await _delete_message_silently(context, chat_id, message_id)

    asyncio.create_task(_worker())


async def send_post(context: ContextTypes.DEFAULT_TYPE, board: str, thread: str, post: dict, mode: str, info: dict) -> None:
    msg_ids = info.setdefault("msg_ids", {})
    num = post.get("num")
    raw_comment = post.get("comment", "")
    internal_chat_id = get_internal_chat_id()
    caption = _build_caption(board, thread, post, msg_ids, internal_chat_id)

    # Кнопку "показать оригинал" имеет смысл предлагать только когда пост
    # реально отправлен превьюшками — в режиме full и так шлём оригиналы.
    files_for_button = post.get("files") or []
    show_full_markup = build_show_full_markup(board, thread, num) if (mode == "preview" and files_for_button) else None

    reply_to = None
    for ref_num in extract_referenced_nums(raw_comment):
        if ref_num in msg_ids:
            reply_to = msg_ids[ref_num]
            break

    files = post.get("files") or []

    # 1. Пост без вложений
    if not files:
        sent = await _send_with_reply_fallback(
            lambda reply_to_message_id: context.bot.send_message(
                chat_id=USER_ID, text=caption, parse_mode=ParseMode.HTML,
                disable_web_page_preview=True, reply_to_message_id=reply_to_message_id,
            ),
            reply_to,
        )
        if sent:
            _remember_msg_id(msg_ids, num, sent.message_id)
        return

    # 2. Одно вложение
    if len(files) == 1:
        f = files[0]
        url = file_url(f, mode)
        if is_full_video_send(f, mode):
            try:
                sent = await _send_with_reply_fallback(
                    lambda reply_to_message_id: context.bot.send_video(
                        chat_id=USER_ID, video=url, caption=caption,
                        parse_mode=ParseMode.HTML, reply_to_message_id=reply_to_message_id,
                        reply_markup=show_full_markup,
                    ),
                    reply_to,
                )
                if sent:
                    _remember_msg_id(msg_ids, num, sent.message_id)
                return
            except Exception as e:
                logger.warning("Не удалось отправить видео %s, фолбэк на превью-картинку: %s", url, e)
                url = f"{DOMAINS[0]}{f['thumbnail']}"  # фолбэк на превью, а не на тот же .webm/.mp4 как фото

        try:
            sent = await _send_with_reply_fallback(
                lambda reply_to_message_id: context.bot.send_photo(
                    chat_id=USER_ID, photo=url, caption=caption,
                    parse_mode=ParseMode.HTML, reply_to_message_id=reply_to_message_id,
                    reply_markup=show_full_markup,
                ),
                reply_to,
            )
            if sent:
                _remember_msg_id(msg_ids, num, sent.message_id)
            return
        except Exception as e:
            logger.warning("Не удалось отправить фото %s: %s", url, e)
            sent = await context.bot.send_message(chat_id=USER_ID, text=f"{caption}\n{url}", parse_mode=ParseMode.HTML)
            if sent:
                _remember_msg_id(msg_ids, num, sent.message_id)
            return

    # 3. Несколько вложений -> send_media_group (Альбом)
    chunk_size = 10
    chunks = [files[i : i + chunk_size] for i in range(0, len(files), chunk_size)]

    for chunk_idx, chunk in enumerate(chunks):
        media_group = []
        for file_idx, f in enumerate(chunk):
            url = file_url(f, mode)
            item_caption = caption if (chunk_idx == 0 and file_idx == 0) else None
            parse_mode = ParseMode.HTML if item_caption else None

            if is_full_video_send(f, mode):
                media_group.append(InputMediaVideo(media=url, caption=item_caption, parse_mode=parse_mode))
            else:
                media_group.append(InputMediaPhoto(media=url, caption=item_caption, parse_mode=parse_mode))

        try:
            current_reply = reply_to if chunk_idx == 0 else None
            sent_msgs = await _send_with_reply_fallback(
                lambda reply_to_message_id: context.bot.send_media_group(
                    chat_id=USER_ID, media=media_group, reply_to_message_id=reply_to_message_id,
                ),
                current_reply,
            )
            if sent_msgs and chunk_idx == 0:
                _remember_msg_id(msg_ids, num, sent_msgs[0].message_id)
                # Для точечного показа оригиналов (editMessageMedia бьёт только по
                # одному message_id за раз) запоминаем ID КАЖДОГО сообщения альбома,
                # в том же порядке, что и files — понадобится в on_show_full.
                album_map = info.setdefault("album_msg_ids", {})
                album_map[str(num)] = [m.message_id for m in sent_msgs]
                if len(album_map) > MAX_MSG_IDS_PER_THREAD:
                    del album_map[next(iter(album_map))]
                # Telegram не позволяет прикрепить inline-кнопку к самому альбому,
                # поэтому для доступа к оригиналам шлём отдельное служебное сообщение-реплай.
                if show_full_markup:
                    try:
                        await context.bot.send_message(
                            chat_id=USER_ID,
                            text=f"🖼 Файлов в посте: {len(files)}",
                            reply_to_message_id=sent_msgs[0].message_id,
                            reply_markup=show_full_markup,
                            disable_notification=True,  # служебная кнопка, уведомление от самого альбома уже было
                        )
                    except Exception as e:
                        logger.warning("Не удалось отправить кнопку 'показать оригинал' для альбома: %s", e)
        except Exception as e:
            logger.warning("Не удалось отправить media_group: %s. Отправляю фолбэк-текстом.", e)
            file_links = "\n".join(file_url(f, mode) for f in chunk)
            sent = await context.bot.send_message(
                chat_id=USER_ID, text=f"{caption}\n\nФайлы:\n{file_links}", parse_mode=ParseMode.HTML,
            )
            if sent and chunk_idx == 0:
                _remember_msg_id(msg_ids, num, sent.message_id)


# ------------------------- ПЕРИОДИЧЕСКАЯ ПРОВЕРКА -------------------------

async def check_new_posts(context: ContextTypes.DEFAULT_TYPE) -> None:
    if not STATE["threads"]:
        return

    mode = STATE.get("mode", "preview")
    changed = False

    for key, info in list(STATE["threads"].items()):
        if info.get("loading_history"):
            continue

        board, thread = info["board"], info["thread"]
        thread_json = await asyncio.to_thread(fetch_thread, board, thread)
        if thread_json is None:
            continue

        posts = get_posts(thread_json)
        if not posts:
            continue

        last_num = info.get("last_num")

        if last_num is None:
            info["last_num"] = posts[-1]["num"]
            info.setdefault("msg_ids", {})
            changed = True
            logger.info("Инициализация треда %s: последний пост #%s", key, info["last_num"])
            continue

        new_posts = [p for p in posts if p.get("num", 0) > last_num]
        if not new_posts:
            continue

        thread_still_tracked = True
        for post in new_posts:
            if key not in STATE.get("threads", {}):
                logger.info("Тред %s был удалён через /unwatch во время отправки новых постов. Прерываю.", key)
                thread_still_tracked = False
                break
            await send_post(context, board, thread, post, mode, info)
            info["last_num"] = post["num"]
            changed = True
            await asyncio.sleep(LIVE_SEND_DELAY)
            if key not in STATE.get("threads", {}):
                logger.info("Тред %s был удалён через /unwatch во время паузы. Прерываю.", key)
                thread_still_tracked = False
                break

        # Переносим кнопку "✏️ Новый пост" под самый последний из только что отправленных
        # постов — один раз на всю пачку, а не на каждый пост.
        if thread_still_tracked and key in STATE.get("threads", {}):
            await refresh_newpost_button(context, board, thread, info)

    if changed:
        save_state(STATE)


# ------------------------- КОМАНДЫ -------------------------

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        "👋 <b>Бот для отслеживания и постинга в треды 2ch (Двач)</b>\n\n"
        "<b>Чтение и мониторинг:</b>\n"
        "• /watch &lt;ссылка&gt; — начать следить за тредом (только новые посты)\n"
        f"• /watch &lt;ссылка&gt; all — выгрузить всю историю треда ({HISTORY_SEND_DELAY}с пауза)\n"
        "• /unwatch — показать список тредов с номерами и выбрать, какой убрать\n"
        "• /unwatch &lt;ссылка или all&gt; — убрать конкретный тред (или все сразу)\n"
        "• /list — список отслеживаемых тредов\n"
        "• /mode preview|full — режим качества медиа\n"
        "• /status — статус работы и аптайм бота\n"
        "• /chatid — узнать ID текущего чата\n\n"
        "<b>✍️ Публикация ответов на Двач:</b>\n"
        "• <b>Быстрый ответ:</b> сделайте <b>Reply</b> на любое сообщение бота с постом из треда (текст или фото)\n"
        "• <code>/reply Текст вашего ответа</code> — цитата &gt;&gt;номер подставится автоматически\n"
        "• <code>/post &lt;ссылка&gt; Текст</code> — создать пост в указанном треде\n"
        "• <b>✏️ Новый пост</b> — кнопка под последним постом треда: нажмите и просто "
        "отправьте следующее сообщение (текст/фото/видео) — оно уйдёт постом. "
        "<code>/cancel</code> отменяет ожидание\n"
        "• Имя и тема поста — флагами в конце текста: "
        "<code>Текст поста --name Аноним2 --subject Заголовок</code>\n"
        "<i>Капча решается прямо в Telegram нажатием на кнопки [ 1 ]..[ 8 ] под картинкой!</i>",
        parse_mode=ParseMode.HTML,
    )


async def cmd_chatid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    is_supergroup = chat.type in ("supergroup", "channel")
    extra = (
        "✅ <b>Это супергруппа!</b> Кликабельные ссылки вида <code>t.me/c/...</code> будут работать идеально."
        if is_supergroup
        else "ℹ️ <i>Это личный чат или базовая группа.</i> Ссылки внутри поста будут вести на сайт 2ch."
    )
    await update.message.reply_text(
        f"<b>ID этого чата:</b> <code>{chat.id}</code>\n"
        f"<b>Тип:</b> {chat.type}\n\n"
        f"{extra}\n\n"
        f"Чтобы бот слал посты сюда, укажи <code>DVACH_USER_ID={chat.id}</code>.",
        parse_mode=ParseMode.HTML,
    )


async def load_history_worker(
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int,
    board: str,
    thread: str,
    posts: list,
    mode: str,
) -> None:
    """Фоновая задача последовательной выгрузки истории треда с поддержкой мгновенной остановки через /unwatch."""
    key = thread_key(board, thread)
    try:
        for post in posts:
            # 1. Проверяем, не был ли тред удалён через /unwatch
            if key not in STATE.get("threads", {}):
                logger.info("Выгрузка истории треда %s прервана: тред удален через /unwatch", key)
                return

            info = STATE["threads"][key]
            try:
                await send_post(context, board, thread, post, mode, info)
                if key in STATE.get("threads", {}):
                    STATE["threads"][key]["last_num"] = post["num"]
            except Exception as e:
                logger.warning("Ошибка при отправке поста #%s из истории: %s", post.get("num"), e)

            # Задержка между постами во избежание Flood Control 429
            await asyncio.sleep(HISTORY_SEND_DELAY)

            # 2. Проверяем ещё раз после паузы (пользователь мог вызвать /unwatch во время сна)
            if key not in STATE.get("threads", {}):
                logger.info("Выгрузка истории треда %s прервана после паузы: тред удален через /unwatch", key)
                return

        # Если дошли до конца и тред всё ещё в списке
        if key in STATE.get("threads", {}):
            STATE["threads"][key]["loading_history"] = False
            save_state(STATE)
            await refresh_newpost_button(context, board, thread, STATE["threads"][key])
            try:
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=(
                        f"✅ Вся история треда <b>/{board}/{thread}</b> ({len(posts)} постов) успешно отправлена!\n"
                        f"Бот перешёл в режим отслеживания новых постов."
                    ),
                    parse_mode=ParseMode.HTML,
                )
            except Exception as e:
                logger.warning("Не удалось отправить уведомление о завершении выгрузки: %s", e)

    except asyncio.CancelledError:
        logger.info("Задача выгрузки истории треда %s была принудительно отменена через /unwatch.", key)
        if key in STATE.get("threads", {}):
            STATE["threads"][key]["loading_history"] = False
            save_state(STATE)
    finally:
        ACTIVE_HISTORY_TASKS.pop(key, None)


async def cmd_watch(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    # Команда — служебное действие, само сообщение с ней в чате не нужно.
    await _delete_own_message_silently(update.message)

    if not context.args:
        await context.bot.send_message(
            chat_id=chat_id,
            text=(
                "<b>Использование:</b>\n"
                "• <code>/watch &lt;ссылка на тред&gt;</code> — отслеживать только новые посты\n"
                "• <code>/watch &lt;ссылка на тред&gt; all</code> — загрузить тред целиком (всю историю)\n\n"
                "<i>Пример:</i> <code>/watch https://2ch.su/b/res/123456.html all</code>"
            ),
            parse_mode=ParseMode.HTML,
        )
        return

    raw_args = context.args
    load_all = any(arg.lower() == "all" for arg in raw_args)
    url_candidates = [arg for arg in raw_args if arg.lower() != "all"]
    url_text = " ".join(url_candidates) if url_candidates else " ".join(raw_args)

    parsed = parse_thread_url(url_text)
    if not parsed:
        await context.bot.send_message(
            chat_id=chat_id,
            text="Не удалось распознать ссылку. Нужен формат: <code>https://2ch.su/доска/res/номер.html</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    board, thread = parsed
    key = thread_key(board, thread)

    if key in STATE["threads"]:
        await context.bot.send_message(
            chat_id=chat_id, text=f"Тред <b>{board}/{thread}</b> уже отслеживается.", parse_mode=ParseMode.HTML,
        )
        return

    thread_json = await asyncio.to_thread(fetch_thread, board, thread)
    posts = get_posts(thread_json) if thread_json else []
    if not posts:
        await context.bot.send_message(
            chat_id=chat_id,
            text=f"❌ Не удалось получить тред <b>{board}/{thread}</b>. Проверь ссылку или статус треда на 2ch.",
            parse_mode=ParseMode.HTML,
        )
        return

    mode = STATE.get("mode", "preview")

    if load_all:
        # Отменяем предыдущую задачу выгрузки для этого треда, если она уже шла
        if key in ACTIVE_HISTORY_TASKS:
            old_task = ACTIVE_HISTORY_TASKS.pop(key)
            if not old_task.done():
                old_task.cancel()

        STATE["threads"][key] = {
            "board": board,
            "thread": thread,
            "last_num": posts[0]["num"] if posts else 0,
            "msg_ids": {},
            "loading_history": True,
        }
        save_state(STATE)

        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=(
                f"⏳ Тред <b>/{board}/{thread}</b> добавлен!\n"
                f"Запущена выгрузка всей истории (<b>{len(posts)}</b> постов) с интервалом {HISTORY_SEND_DELAY} сек.\n"
                f"<i>Для прерывания выгрузки в любой момент используйте:</i> <code>/unwatch /{board}/{thread}</code>"
            ),
            parse_mode=ParseMode.HTML,
        )
        schedule_message_deletion(context, sent.chat_id, sent.message_id)

        task = asyncio.create_task(
            load_history_worker(context, chat_id, board, thread, posts, mode)
        )
        ACTIVE_HISTORY_TASKS[key] = task
    else:
        # Если для этого треда была активна выгрузка истории, отменяем
        if key in ACTIVE_HISTORY_TASKS:
            old_task = ACTIVE_HISTORY_TASKS.pop(key)
            if not old_task.done():
                old_task.cancel()

        STATE["threads"][key] = {
            "board": board,
            "thread": thread,
            "last_num": posts[-1]["num"],
            "msg_ids": {},
        }
        save_state(STATE)

        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=(
                f"✅ Добавлен тред <b>/{board}/{thread}</b>.\n"
                f"Начинаю следить с поста <b>#{posts[-1]['num']}</b> (всего в треде: {len(posts)} постов).\n\n"
                f"<i>Подсказка:</i> Чтобы загрузить все посты треда с самого начала, используй:\n"
                f"<code>/watch https://2ch.su/{board}/res/{thread}.html all</code>"
            ),
            parse_mode=ParseMode.HTML,
        )
        schedule_message_deletion(context, sent.chat_id, sent.message_id)
        await refresh_newpost_button(context, board, thread, STATE["threads"][key])


async def _unwatch_thread_by_key(context: ContextTypes.DEFAULT_TYPE, key: str) -> Tuple[bool, bool]:
    """Удаляет тред по ключу: отменяет фоновую выгрузку истории (если идёт) и убирает
    из STATE. Возвращает (removed, was_loading)."""
    was_loading = False
    if key in ACTIVE_HISTORY_TASKS:
        task = ACTIVE_HISTORY_TASKS.pop(key)
        if not task.done():
            task.cancel()
            was_loading = True

    if key not in STATE["threads"]:
        return False, was_loading

    removed_info = STATE["threads"].pop(key)
    await remove_newpost_button(context, removed_info)
    save_state(STATE)
    return True, was_loading


async def cmd_unwatch(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id

    # Команда — это просто служебное действие, само сообщение с ней не нужно хранить в чате.
    await _delete_own_message_silently(update.message)

    if not context.args:
        threads = STATE.get("threads", {})
        if not threads:
            sent = await context.bot.send_message(chat_id=chat_id, text="Список пуст — нечего отменять отслеживание.")
            schedule_message_deletion(context, sent.chat_id, sent.message_id)
            return

        keys = list(threads.keys())

        lines = ["<b>Какой тред убрать из отслеживания?</b>\nОтправьте номер:\n"]
        for i, k in enumerate(keys, start=1):
            info = threads[k]
            last = info.get("last_num", "—")
            lines.append(f"{i}. /{info['board']}/{info['thread']} (пост #{last})")
        lines.append("\nИли <code>/unwatch all</code>, или конкретную ссылку/доску+номер. Отменить: /cancel")

        sent = await context.bot.send_message(chat_id=chat_id, text="\n".join(lines), parse_mode=ParseMode.HTML)
        # Список НЕ на таймере — убираем его явно только после удаления треда или /cancel.
        PENDING_UNWATCH[chat_id] = {"keys": keys, "list_msg_id": sent.message_id}
        return

    joined = " ".join(context.args).strip()

    # Массовая остановка
    if joined.lower() == "all":
        cancelled_count = 0
        for k, task in list(ACTIVE_HISTORY_TASKS.items()):
            if not task.done():
                task.cancel()
                cancelled_count += 1
        ACTIVE_HISTORY_TASKS.clear()

        for info in STATE.get("threads", {}).values():
            await remove_newpost_button(context, info)

        count = len(STATE.get("threads", {}))
        STATE["threads"] = {}
        save_state(STATE)
        pending = PENDING_UNWATCH.pop(chat_id, None)
        if pending and pending.get("list_msg_id"):
            await _delete_message_silently(context, chat_id, pending["list_msg_id"])
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=(
                f"🗑 Все треды ({count}) удалены из отслеживания.\n"
                f"🛑 Активных выгрузок истории прервано: {cancelled_count}."
            ),
            parse_mode=ParseMode.HTML,
        )
        schedule_message_deletion(context, sent.chat_id, sent.message_id)
        return

    parsed = parse_thread_url(joined)
    if not parsed and len(context.args) == 2:
        parsed = (context.args[0], context.args[1])

    if not parsed:
        sent = await context.bot.send_message(chat_id=chat_id, text="Не удалось разобрать ссылку или доску/номер.")
        schedule_message_deletion(context, sent.chat_id, sent.message_id)
        return

    board, thread = parsed
    key = thread_key(board, thread)
    removed, was_loading = await _unwatch_thread_by_key(context, key)
    pending = PENDING_UNWATCH.pop(chat_id, None)
    if pending and pending.get("list_msg_id"):
        await _delete_message_silently(context, chat_id, pending["list_msg_id"])

    if not removed:
        if was_loading:
            sent = await context.bot.send_message(
                chat_id=chat_id,
                text=f"🛑 Выгрузка истории треда <b>/{board}/{thread}</b> немедленно остановлена.",
                parse_mode=ParseMode.HTML,
            )
            schedule_message_deletion(context, sent.chat_id, sent.message_id)
            return
        sent = await context.bot.send_message(
            chat_id=chat_id, text=f"Тред <b>{board}/{thread}</b> не отслеживается.", parse_mode=ParseMode.HTML,
        )
        schedule_message_deletion(context, sent.chat_id, sent.message_id)
        return

    msg = f"🗑 Тред <b>/{board}/{thread}</b> удалён из списка."
    if was_loading:
        msg += "\n🛑 Фоновая выгрузка постов немедленно прервана!"
    sent = await context.bot.send_message(chat_id=chat_id, text=msg, parse_mode=ParseMode.HTML)
    schedule_message_deletion(context, sent.chat_id, sent.message_id)


async def on_pending_unwatch_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Ловит число, отправленное после /unwatch без аргументов, и удаляет
    соответствующий по порядку тред из показанного списка."""
    chat_id = update.effective_chat.id
    pending = PENDING_UNWATCH.pop(chat_id, None)
    if not pending:
        return  # на всякий случай — не должно случаться благодаря фильтру

    # Реплай с номером — это тоже просто служебный ввод, само сообщение в чате не нужно.
    await _delete_own_message_silently(update.message)

    keys = pending.get("keys") or []
    list_msg_id = pending.get("list_msg_id")

    idx = int(update.message.text.strip()) - 1
    if not (0 <= idx < len(keys)):
        # Некорректный ввод — список НЕ удаляем (только после реального удаления треда
        # или /cancel), просто просим начать заново.
        await context.bot.send_message(
            chat_id=chat_id,
            text=f"Нет треда с номером {idx + 1} в показанном списке. Отправьте /unwatch ещё раз, чтобы обновить список.",
        )
        return

    key = keys[idx]
    if key not in STATE["threads"]:
        await context.bot.send_message(
            chat_id=chat_id,
            text="Этот тред уже был удалён (список успел устареть). Отправьте /unwatch ещё раз.",
        )
        return

    info = STATE["threads"][key]
    board, thread = info["board"], info["thread"]
    removed, was_loading = await _unwatch_thread_by_key(context, key)

    if removed and list_msg_id:
        await _delete_message_silently(context, chat_id, list_msg_id)

    msg = f"🗑 Тред <b>/{board}/{thread}</b> удалён из списка." if removed else f"Тред <b>/{board}/{thread}</b> не найден."
    if was_loading:
        msg += "\n🛑 Фоновая выгрузка постов немедленно прервана!"
    sent = await context.bot.send_message(chat_id=chat_id, text=msg, parse_mode=ParseMode.HTML)
    if removed:
        schedule_message_deletion(context, sent.chat_id, sent.message_id)


async def cmd_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    # Команда — служебное действие, само сообщение с ней в чате не нужно.
    await _delete_own_message_silently(update.message)

    threads = STATE.get("threads", {})
    if not threads:
        await context.bot.send_message(
            chat_id=chat_id, text="Список пуст. Добавь тред: <code>/watch &lt;ссылка&gt;</code>", parse_mode=ParseMode.HTML,
        )
        return

    lines = ["<b>📋 Отслеживаемые треды:</b>\n"]
    for info in threads.values():
        link = f"{DOMAINS[0]}/{info['board']}/res/{info['thread']}.html"
        last = info.get("last_num", "—")
        k = thread_key(info["board"], info["thread"])
        status_tag = ""
        if k in ACTIVE_HISTORY_TASKS and not ACTIVE_HISTORY_TASKS[k].done():
            status_tag = " <i>(⏳ идёт выгрузка истории...)</i>"
        lines.append(f"• <a href=\"{link}\">/{info['board']}/{info['thread']}</a> (пост #{last}){status_tag}")

    await context.bot.send_message(
        chat_id=chat_id, text="\n".join(lines), parse_mode=ParseMode.HTML, disable_web_page_preview=True,
    )


async def cmd_mode(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not context.args or context.args[0] not in ("preview", "full"):
        await update.message.reply_text(
            f"Текущий режим: <b>{STATE.get('mode', 'preview')}</b>\n"
            "Использование:\n"
            "• <code>/mode preview</code> — быстрые сжатые превью (thumbnails)\n"
            "• <code>/mode full</code> — оригинальные файлы высокого качества",
            parse_mode=ParseMode.HTML,
        )
        return

    STATE["mode"] = context.args[0]
    save_state(STATE)
    desc = "сжатые превью (быстро и экономно)" if STATE["mode"] == "preview" else "полноразмерные оригиналы"
    await update.message.reply_text(f"✅ Режим переключен на: <b>{STATE['mode']}</b> ({desc})", parse_mode=ParseMode.HTML)


NEWPOST_CLICK_DEBOUNCE_SEC = 2.0
_LAST_NEWPOST_CLICK: Dict[int, float] = {}


async def on_newpost_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Нажатие кнопки '✏️ Новый пост' под последним постом треда: включаем режим
    ожидания — следующее обычное сообщение (текст и/или медиа) от пользователя
    уйдёт постом именно в этот тред, без необходимости писать /post каждый раз."""
    query = update.callback_query

    try:
        _, board, thread = query.data.split(":", 2)
    except ValueError:
        await query.answer("Некорректные данные кнопки.", show_alert=True)
        return

    chat_id = query.message.chat_id
    now = time.time()

    existing = PENDING_POST.get(chat_id)
    same_target = existing and existing.get("board") == board and existing.get("thread") == thread

    # Дебаунс: пользователь дважды тапнул по той же кнопке почти одновременно
    # (случайный двойной клик / повторная доставка callback) — не дублируем сообщение.
    last_click = _LAST_NEWPOST_CLICK.get(chat_id, 0)
    if same_target and (now - last_click) < NEWPOST_CLICK_DEBOUNCE_SEC:
        await query.answer("Уже жду ваше сообщение для этого треда 👍")
        return
    _LAST_NEWPOST_CLICK[chat_id] = now

    if same_target:
        # Не двойной клик, но ожидание для этого же треда уже активно — просто подтверждаем.
        await query.answer("Уже жду ваше сообщение для этого треда 👍")
        return

    if existing:
        # Было ожидание для ДРУГОГО треда — явно сообщаем, что цель переключилась,
        # чтобы не улетело туда, куда пользователь не ожидает.
        await query.answer(f"Переключено на тред /{board}/{thread}")
        old_invite_id = existing.get("invite_msg_id")
        if old_invite_id:
            await _delete_message_silently(context, chat_id, old_invite_id)
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=(
                f"🔀 Ожидание переключено: пишу теперь в тред <b>/{board}/{thread}</b> "
                f"вместо <b>/{existing['board']}/{existing['thread']}</b>.\n"
                f"Отправьте текст, фото или видео. Отменить: /cancel"
            ),
            parse_mode=ParseMode.HTML,
        )
        PENDING_POST[chat_id] = {"board": board, "thread": thread, "invite_msg_id": sent.message_id}
        return

    await query.answer()

    sent = await context.bot.send_message(
        chat_id=chat_id,
        text=(
            f"✍️ Жду текст, фото или видео для нового поста в тред <b>/{board}/{thread}</b>.\n"
            f"Просто отправьте следующее сообщение — как обычно, перед публикацией нужно "
            f"будет решить капчу, так что случайно ничего не улетит.\n\n"
            f"Чтобы отменить ожидание: /cancel"
        ),
        parse_mode=ParseMode.HTML,
    )
    # Само приглашение НЕ на таймере — удаляем его явно, когда пользователь либо
    # реально ответит постом (on_pending_post_message), либо нажмёт /cancel.
    PENDING_POST[chat_id] = {"board": board, "thread": thread, "invite_msg_id": sent.message_id}


async def on_pending_post_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Ловит первое же не-командное сообщение после нажатия '✏️ Новый пост' и отправляет
    его на публикацию в заранее известный тред (см. PENDING_POST_FILTER)."""
    chat_id = update.effective_chat.id
    if chat_id not in PENDING_POST:
        return  # на всякий случай — не должно случаться благодаря фильтру

    messages = await collect_media_group_messages(update)
    if messages is None:
        return  # не последняя часть альбома — обработку продолжит "победивший" вызов

    pending = PENDING_POST.pop(chat_id, None)
    if not pending:
        return  # уже забрано параллельным вызовом (например, другой частью того же альбома)

    invite_msg_id = pending.get("invite_msg_id")
    if invite_msg_id:
        await _delete_message_silently(context, chat_id, invite_msg_id)

    primary = _pick_caption_message(messages)
    text = _build_formatted_comment(primary).strip()
    extra = [m for m in messages if m is not primary]

    await _run_post_flow_safe(
        update, context, "pending post",
        explicit_text=text, forced_board=pending["board"], forced_thread=pending["thread"],
        extra_messages=extra, primary_message=primary,
    )


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    cancelled_post = PENDING_POST.pop(chat_id, None)
    cancelled_unwatch = PENDING_UNWATCH.pop(chat_id, None)
    cancelled_field = PENDING_DRAFT_FIELD.pop(chat_id, None)

    # Приглашение "Жду текст..." не на таймере — раз отменяем ожидание, убираем его сразу же.
    if cancelled_post:
        invite_msg_id = cancelled_post.get("invite_msg_id")
        if invite_msg_id:
            await _delete_message_silently(context, chat_id, invite_msg_id)

    # Список тредов от /unwatch тоже не на таймере — убираем сразу при отмене.
    if cancelled_unwatch:
        list_msg_id = cancelled_unwatch.get("list_msg_id")
        if list_msg_id:
            await _delete_message_silently(context, chat_id, list_msg_id)

    # Отменяем только ожидание текста для поля (имя/тема) — сам черновик поста и
    # экран настроек остаются как были, отменить их целиком можно кнопкой "❌ Отмена".
    if cancelled_field:
        draft = POST_DRAFTS.get(cancelled_field["session_id"])
        if draft:
            prompt_id = draft.pop("field_prompt_msg_id", None)
            if prompt_id:
                await _delete_message_silently(context, chat_id, prompt_id)

    # Своё же сообщение с командой /cancel тоже убираем — не отвечаем на него reply_text,
    # чтобы не зависеть от уже удалённого message_id.
    await _delete_own_message_silently(update.message)

    if cancelled_post and cancelled_unwatch:
        sent = await context.bot.send_message(chat_id=chat_id, text="❌ Ожидание нового поста и выбор треда для удаления отменены.")
    elif cancelled_post:
        sent = await context.bot.send_message(chat_id=chat_id, text="❌ Ожидание нового поста отменено.")
    elif cancelled_unwatch:
        sent = await context.bot.send_message(chat_id=chat_id, text="❌ Выбор треда для удаления отменён.")
    elif cancelled_field:
        sent = await context.bot.send_message(chat_id=chat_id, text="❌ Ввод отменён, настройки поста не изменены.")
    else:
        sent = await context.bot.send_message(chat_id=chat_id, text="Нечего отменять — не было активного ожидания.")
    schedule_message_deletion(context, sent.chat_id, sent.message_id)


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uptime_sec = int(time.time() - START_TIME)
    h, m, s = uptime_sec // 3600, (uptime_sec % 3600) // 60, uptime_sec % 60
    server_info = f"порт {PORT}" if PORT else "выключен"
    if USE_GIST_BACKEND:
        state_backend = f"GitHub Gist (<code>{GIST_ID or 'ещё не создан!'}</code>)"
    else:
        state_backend = "локальный файл"

    await update.message.reply_text(
        "<b>📊 Статус бота:</b>\n\n"
        f"• <b>Активных тредов:</b> {len(STATE.get('threads', {}))}\n"
        f"• <b>Режим вложений:</b> {STATE.get('mode', 'preview')} (группировка в альбомы)\n"
        f"• <b>Интервал опроса:</b> {POLL_INTERVAL} сек.\n"
        f"• <b>Задержка отправки:</b> {LIVE_SEND_DELAY}с (лайв) / {HISTORY_SEND_DELAY}с (история)\n"
        f"• <b>Health-сервер:</b> {server_info}\n"
        f"• <b>Хранение состояния:</b> {state_backend}\n"
        f"• <b>Аптайм:</b> {h}ч {m}м {s}с\n"
        f"• <b>Основное зеркало:</b> {DOMAINS[0]}",
        parse_mode=ParseMode.HTML,
    )


# ------------------------- ПОСТИНГ И EMOJI-КАПЧА 2CH -------------------------

CAPTCHA_SESSIONS: Dict[str, dict] = {}


def clean_expired_captcha_sessions() -> None:
    now = time.time()
    expired = [sid for sid, s in CAPTCHA_SESSIONS.items() if now - s.get("created_at", now) > 600]
    for sid in expired:
        CAPTCHA_SESSIONS.pop(sid, None)


def find_post_by_message_id(reply_msg_id: int) -> Optional[Tuple[str, str, int]]:
    for key, info in STATE.get("threads", {}).items():
        msg_ids = info.get("msg_ids", {})
        for post_num_str, m_id in msg_ids.items():
            if m_id == reply_msg_id:
                try:
                    return info["board"], info["thread"], int(post_num_str)
                except ValueError:
                    return info["board"], info["thread"], 0
    return None


def get_dvach_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({
        "User-Agent": USER_AGENT,
        "Accept": "*/*",
        "Accept-Language": "ru,en-US;q=0.9,en;q=0.8",
    })
    for d in [".2ch.su", ".2ch.org", ".2ch.life", ".2ch.hk"]:
        s.cookies.set("ageallow", "1", domain=d)
    return s


def fetch_emoji_captcha(domain: str, session: requests.Session) -> dict:
    url_id = f"{domain}/api/captcha/emoji/id"
    r = session.get(url_id, timeout=15)
    if r.status_code != 200:
        return {"error": f"Ошибка запроса ID капчи: HTTP {r.status_code}"}

    try:
        data = r.json()
    except Exception as e:
        return {"error": f"Некорректный ответ сервера капчи: {e}"}

    result = data.get("result")
    if result == 2:
        return {"vip": True}
    if result == 3:
        return {"disabled": True}

    cap_id = data.get("id")
    if not cap_id:
        return {"error": data.get("message") or "Не получен id токена капчи"}

    url_show = f"{domain}/api/captcha/emoji/show?id={cap_id}"
    show_r = session.get(url_show, timeout=15)
    if show_r.status_code != 200:
        return {"error": f"Ошибка загрузки изображений капчи: HTTP {show_r.status_code}"}

    try:
        show_data = show_r.json()
    except Exception as e:
        return {"error": f"Некорректный JSON показа капчи: {e}"}

    return {
        "id": cap_id,
        "image": show_data.get("image"),
        "keyboard": show_data.get("keyboard", []),
    }


def click_emoji_captcha(domain: str, session: requests.Session, cap_id: str, emoji_number: int) -> dict:
    payload = {"captchaTokenID": cap_id, "emojiNumber": emoji_number}
    r = session.post(f"{domain}/api/captcha/emoji/click", json=payload, timeout=15)
    try:
        return r.json()
    except Exception as e:
        return {"error": f"Ошибка ответа при клике: {e}"}


def compose_emoji_captcha_image(challenge_b64: str, keyboard_b64_list: list, selected_b64_list: Optional[list] = None) -> bytes:
    selected_b64_list = selected_b64_list or []

    challenge_img = Image.open(io.BytesIO(base64.b64decode(challenge_b64))).convert("RGB")
    c_w, c_h = challenge_img.size

    target_cw = 480
    target_ch = max(int(c_h * (target_cw / c_w)), 120)
    challenge_scaled = challenge_img.resize((target_cw, target_ch), Image.Resampling.LANCZOS)

    icons = [Image.open(io.BytesIO(base64.b64decode(k))).convert("RGBA") for k in keyboard_b64_list]
    num_icons = len(icons)
    cols = 4
    rows = max((num_icons + cols - 1) // cols, 1)

    cell_w, cell_h = 120, 68
    margin = 14
    gap = 8
    total_w = margin * 2 + cols * cell_w + (cols - 1) * gap
    header_h = 28
    grid_h = rows * cell_h + (rows - 1) * gap

    # строка уже выбранных (правильно угаданных на прошлых шагах) иконок — как на самом сайте 2ch
    selected_icons = [Image.open(io.BytesIO(base64.b64decode(s))).convert("RGBA") for s in selected_b64_list]
    selected_h = 0
    selected_header_h = 0
    sel_icon_size = 48
    if selected_icons:
        selected_header_h = 22
        selected_h = sel_icon_size + 10

    total_h = margin + selected_header_h + selected_h + target_ch + 10 + header_h + grid_h + margin

    canvas = Image.new("RGB", (total_w, total_h), (242, 244, 248))
    draw = ImageDraw.Draw(canvas)

    cursor_y = margin

    if selected_icons:
        draw.text((margin, cursor_y), f"Уже угадано ({len(selected_icons)}):", fill=(40, 130, 60))
        cursor_y += selected_header_h
        sx = margin
        for icon in selected_icons:
            icon_small = icon.resize((sel_icon_size, sel_icon_size), Image.Resampling.LANCZOS)
            draw.rectangle([sx - 2, cursor_y - 2, sx + sel_icon_size + 2, cursor_y + sel_icon_size + 2],
                           outline=(60, 170, 90), width=2)
            canvas.paste(icon_small, (sx, cursor_y), icon_small)
            sx += sel_icon_size + 8
        cursor_y += selected_h

    cw_x = (total_w - target_cw) // 2
    cw_y = cursor_y
    canvas.paste(challenge_scaled, (cw_x, cw_y))
    draw.rectangle([cw_x - 1, cw_y - 1, cw_x + target_cw, cw_y + target_ch], outline=(170, 175, 190), width=2)

    text_y = cw_y + target_ch + 10
    draw.text((margin, text_y), "Нажмите кнопки с иконками, которые есть на картинке выше:", fill=(40, 45, 55))

    grid_y = text_y + header_h
    for idx, icon in enumerate(icons):
        r_idx = idx // cols
        c_idx = idx % cols
        cx = margin + c_idx * (cell_w + gap)
        cy = grid_y + r_idx * (cell_h + gap)

        draw.rectangle([cx, cy, cx + cell_w, cy + cell_h], fill=(255, 255, 255), outline=(200, 205, 220), width=1)

        badge_size = 24
        bx = cx + 8
        by = cy + (cell_h - badge_size) // 2
        draw.rectangle([bx, by, bx + badge_size, by + badge_size], fill=(36, 129, 238))
        draw.text((bx + 8, by + 5), str(idx + 1), fill=(255, 255, 255))

        iw, ih = icon.size
        ix = cx + badge_size + 12 + (cell_w - badge_size - 18 - iw) // 2
        iy = cy + (cell_h - ih) // 2
        canvas.paste(icon, (ix, iy), icon)

    out = io.BytesIO()
    canvas.save(out, format="PNG")
    return out.getvalue()


def build_captcha_keyboard(session_id: str, num_icons: int) -> InlineKeyboardMarkup:
    keyboard = []
    row1 = []
    row2 = []
    for i in range(num_icons):
        btn = InlineKeyboardButton(f"[ {i + 1} ]", callback_data=f"cap:{session_id}:{i}")
        if i < 4:
            row1.append(btn)
        else:
            row2.append(btn)
    if row1:
        keyboard.append(row1)
    if row2:
        keyboard.append(row2)

    keyboard.append([
        InlineKeyboardButton("🔄 Обновить капчу", callback_data=f"cap_refresh:{session_id}"),
        InlineKeyboardButton("❌ Отмена", callback_data=f"cap_cancel:{session_id}"),
    ])
    return InlineKeyboardMarkup(keyboard)


def submit_post_to_2ch(
    session: requests.Session,
    domain: str,
    board: str,
    thread: str,
    comment: str,
    captcha_key: str = "",
    files_data: Optional[List[Tuple[bytes, Optional[str], bool]]] = None,
    name: str = "",
    subject: str = "",
    sage: bool = False,
    keep_original_filename: bool = False,
) -> dict:
    """
    Структура запроса подтверждена реальным cURL, снятым через DevTools при
    отправке поста с сайта 2ch.org (эндпоинт /user/posting, multipart/form-data).
    captcha_key: финальное значение поля emoji_captcha_id (токен успеха капчи,
    response.success из /api/captcha/emoji/click).
    files_data: список (file_data, file_name, has_original_name) — 2ch принимает
    несколько файлов на пост через повторяющееся поле "file[]" (макс. обычно 4,
    сервер сам обрежет лишнее).
    keep_original_filename: если True — для файлов, у которых has_original_name=True,
    используется их настоящее имя вместо сгенерированного по unix time. Для файлов
    без настоящего имени (сжатые фото — Telegram стирает его ещё на своей стороне)
    ничего не меняется в любом случае, генерируется имя как обычно.
    """
    headers = {
        "User-Agent": USER_AGENT,
        "Origin": domain,
        "Referer": f"{domain}/{board}/res/{thread}.html",
        "Accept": "*/*",
    }
    data = {
        "task": "post",
        "board": board,
        "thread": str(thread),
        "usercode": "",
        "code": "",
        "email": "sage" if sage else "",
        "name": name,
        "submit": "Ответ",
        "subject": subject,
        "comment": comment,
        "makaka_id": "",
        "makaka_answer": "",
    }
    if captcha_key:
        data["captcha_type"] = "emoji_captcha"
        data["emoji_captcha_id"] = captcha_key

    # requests не даёт повторяющиеся ключи в dict, поэтому multipart-поля собираем
    # списком пар (имя_поля, значение) — так можно добавить несколько "file[]" подряд.
    multipart_fields: List[Tuple[str, Any]] = [(k, (None, str(v))) for k, v in data.items()]

    for file_data, file_name, has_original_name in (files_data or []):
        if not file_data:
            continue
        orig_name = file_name or "image.png"
        low = orig_name.lower()
        if low.endswith(".png"):
            mime, ext = "image/png", ".png"
        elif low.endswith(".gif"):
            mime, ext = "image/gif", ".gif"
        elif low.endswith(".webm"):
            mime, ext = "video/webm", ".webm"
        elif low.endswith(".mp4"):
            mime, ext = "video/mp4", ".mp4"
        else:
            mime, ext = "image/jpeg", ".jpg"

        if keep_original_filename and has_original_name:
            # Настоящее имя реально есть (видео/gif/документ с именем от Telegram) —
            # используем его как есть, только вырезаем path-разделители на всякий случай.
            fn = re.sub(r"[\\/]+", "_", orig_name).strip() or orig_name
        else:
            # По умолчанию (и всегда для сжатых фото, у которых оригинала попросту
            # нет) — исходное имя файла может содержать метаданные (модель устройства,
            # дату съёмки и т.п.), заменяем на unix time в миллисекундах. Добавляем
            # счётчик в конец, чтобы у нескольких файлов в одном посте не совпали имена.
            fn = f"{int(time.time() * 1000)}_{len(multipart_fields)}{ext}"
        multipart_fields.append(("file[]", (fn, file_data, mime)))

    try:
        resp = session.post(
            f"{domain}/user/posting", headers=headers, files=multipart_fields, timeout=30,
        )
        logger.info("Ответ /user/posting: HTTP %s, тело: %s", resp.status_code, resp.text[:500])

        if resp.status_code == 200:
            try:
                res_json = resp.json()
            except Exception:
                # не JSON — возможно, HTML-страница с ошибкой или редирект-заглушка
                low_text = resp.text.lower()
                if "успешно" in low_text or "отправлен" in low_text:
                    return {"ok": True, "num": None, "raw": resp.text[:500]}
                return {"ok": False, "error": "Сервер вернул не-JSON ответ", "raw": resp.text[:500]}

            # разбираем разные возможные форматы ответа (пока не знаем точный формат
            # именно для /user/posting — подстраиваемся по фактическим логам)
            error_field = res_json.get("Error")
            result_field = res_json.get("result")
            status_field = res_json.get("Status")

            is_ok = (
                (error_field is not None and error_field in (False, 0, "")) or
                (status_field == "OK") or
                (result_field in (1, True)) or
                (error_field is None and any(k in res_json for k in ("Target", "Num", "num", "id")))
            )

            if is_ok:
                num = res_json.get("Target") or res_json.get("Num") or res_json.get("num") or res_json.get("id")
                return {"ok": True, "num": num, "raw": res_json}

            err = (
                res_json.get("Reason")
                or (res_json.get("error") if isinstance(res_json.get("error"), str) else (res_json.get("error") or {}).get("message"))
                or res_json.get("message")
                or "Неизвестная ошибка 2ch"
            )
            return {"ok": False, "error": str(err), "raw": res_json}
        else:
            try:
                res_json = resp.json()
                err = (
                    res_json.get("Reason")
                    or (res_json.get("error") if isinstance(res_json.get("error"), str) else (res_json.get("error") or {}).get("message"))
                    or res_json.get("message")
                    or f"HTTP {resp.status_code}"
                )
                return {"ok": False, "error": str(err), "raw": res_json}
            except Exception:
                return {"ok": False, "error": f"HTTP {resp.status_code}: {resp.text[:300]}"}
    except Exception as e:
        return {"ok": False, "error": str(e)}


async def handle_post_flow(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    reply_msg_id: Optional[int] = None,
    explicit_text: str = "",
    forced_board: Optional[str] = None,
    forced_thread: Optional[str] = None,
    extra_messages: Optional[list] = None,
    primary_message=None,
) -> None:
    clean_expired_captcha_sessions()

    # "Главное" сообщение для reply_text/извлечения медиа — обычно update.message,
    # но при альбоме (media_group) это может быть НЕ то сообщение, что реально
    # содержит подпись/текст (см. collect_media_group_messages + _pick_caption_message
    # в точках входа). update.message в PTB v20+ неизменяем, поэтому вместо мутации
    # update просто используем отдельную переменную здесь и далее по функции.
    msg = primary_message or update.message

    target_info = None
    if reply_msg_id:
        target_info = find_post_by_message_id(reply_msg_id)

    board, thread, ref_num = None, None, None
    name, subject, comment = extract_post_flags(explicit_text.strip())

    if forced_board and forced_thread:
        # Пришли из режима "ожидания нового поста" после кнопки "✏️ Новый пост" —
        # доска и тред уже точно известны, никакой >>ref-подстановки не нужно.
        board, thread = forced_board, forced_thread
    elif target_info:
        board, thread, ref_num = target_info
        if ref_num and not comment.startswith(f">>{ref_num}") and f">>{ref_num}" not in comment:
            comment = f">>{ref_num}\n{comment}".strip()
    else:
        parts = comment.split(None, 1)
        if parts:
            parsed = parse_thread_url(parts[0])
            if parsed:
                board, thread = parsed
                comment = parts[1] if len(parts) > 1 else ""
            elif len(parts) >= 2 and parts[0].isalnum() and parts[1].split(None, 1)[0].isdigit():
                board = parts[0]
                rest = parts[1].split(None, 1)
                thread = rest[0]
                comment = rest[1] if len(rest) > 1 else ""

        if not board or not thread:
            tracked_keys = list(STATE.get("threads", {}).keys())
            if len(tracked_keys) == 1:
                t_info = STATE["threads"][tracked_keys[0]]
                board, thread = t_info["board"], t_info["thread"]

    if not board or not thread:
        await msg.reply_text(
            "<b>✍️ Как отправить пост на Двач:</b>\n\n"
            "1. <b>Ответом (Reply):</b> ответьте на любое сообщение треда в этом чате:\n"
            "   <code>/reply Текст вашего ответа</code> (номер &gt;&gt;12345 подставится сам!)\n\n"
            "2. <b>По ссылке на тред:</b>\n"
            "   <code>/post https://2ch.su/доска/res/номер.html Текст сообщения</code>\n\n"
            "<i>К сообщению можно прикрепить картинку. Имя и тему можно указать флагами "
            "в конце текста: --name Аноним2 --subject Заголовок</i>",
            parse_mode=ParseMode.HTML,
        )
        return

    # Извлечение прикреплённого медиа (фото, видео, gif, документ) — из основного
    # сообщения и из всех остальных частей альбома, если это был media_group (см.
    # collect_media_group_messages в точках входа выше по цепочке).
    files_data: List[Tuple[bytes, str, bool]] = []
    for one_msg in [msg] + list(extra_messages or []):
        extracted = await _extract_one_file(context, one_msg)
        if extracted:
            files_data.append(extracted)

    truncated_notice = ""
    if len(files_data) > MAX_FILES_PER_POST:
        truncated_notice = (
            f"\n⚠️ В посте {len(files_data)} файлов, 2ch принимает не больше "
            f"{MAX_FILES_PER_POST} — лишние не отправлены."
        )
        files_data = files_data[:MAX_FILES_PER_POST]

    if not comment and not files_data:
        await msg.reply_text("Введите текст сообщения для публикации на Дваче.")
        return

    # Оригинальное имя есть только у видео/gif/документов, которые Telegram передал
    # с настоящим file_name — у сжатых фото такого имени в принципе не существует.
    can_keep_original = any(has_orig for _, _, has_orig in files_data)

    sid = secrets.token_hex(4)
    draft = {
        "board": board,
        "thread": thread,
        "comment": comment,
        "files_data": files_data,
        "truncated_notice": truncated_notice,
        "name": name,
        "subject": subject,
        "sage": False,
        "keep_original_filename": False,
        "can_keep_original": can_keep_original,
        "chat_id": msg.chat_id,
    }
    POST_DRAFTS[sid] = draft

    sent = await msg.reply_text(
        _render_draft_text(draft), parse_mode=ParseMode.HTML, reply_markup=_render_draft_markup(sid, draft),
    )
    draft["settings_msg_id"] = sent.message_id


def _render_draft_text(draft: dict) -> str:
    board, thread = draft["board"], draft["thread"]
    lines = [f"<b>⚙️ Настройки поста в /{board}/{thread}</b>\n"]
    lines.append(f"Имя: <b>{draft['name'] or '(по умолчанию)'}</b>")
    lines.append(f"Тема: <b>{draft['subject'] or '(нет)'}</b>")
    lines.append(f"Sage: <b>{'вкл' if draft['sage'] else 'выкл'}</b>")
    if draft["can_keep_original"]:
        lines.append(
            f"Оригинальное имя файла: <b>{'вкл' if draft['keep_original_filename'] else 'выкл'}</b>"
        )
    n_files = len(draft["files_data"])
    if n_files:
        lines.append(f"\nФайлов: {n_files}")
    lines.append("\n<i>Когда всё готово — жмите «Продолжить», откроется капча.</i>")
    return "\n".join(lines)


def _render_draft_markup(sid: str, draft: dict) -> InlineKeyboardMarkup:
    rows = [[
        InlineKeyboardButton("✏️ Имя", callback_data=f"draftname:{sid}"),
        InlineKeyboardButton("📝 Тема", callback_data=f"draftsubject:{sid}"),
    ]]
    sage_label = "⬇️ Sage: вкл ✅" if draft["sage"] else "⬇️ Sage: выкл"
    rows.append([InlineKeyboardButton(sage_label, callback_data=f"draftsage:{sid}")])
    if draft["can_keep_original"]:
        orig_label = "🖼 Оригинал. имя: вкл ✅" if draft["keep_original_filename"] else "🖼 Оригинал. имя: выкл"
        rows.append([InlineKeyboardButton(orig_label, callback_data=f"draftorig:{sid}")])
    rows.append([
        InlineKeyboardButton("✅ Продолжить", callback_data=f"draftgo:{sid}"),
        InlineKeyboardButton("❌ Отмена", callback_data=f"draftcancel:{sid}"),
    ])
    return InlineKeyboardMarkup(rows)


async def on_draft_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Кнопки Sage / Оригинальное имя файла на экране настроек — переключают
    значение и перерисовывают то же сообщение."""
    query = update.callback_query
    field, sid = query.data.split(":", 1)
    draft = POST_DRAFTS.get(sid)
    if not draft:
        await query.answer("Черновик устарел или уже обработан.", show_alert=True)
        return

    if field == "draftsage":
        draft["sage"] = not draft["sage"]
    elif field == "draftorig":
        draft["keep_original_filename"] = not draft["keep_original_filename"]

    await query.answer()
    await query.edit_message_text(
        _render_draft_text(draft), parse_mode=ParseMode.HTML, reply_markup=_render_draft_markup(sid, draft),
    )


async def on_draft_edit_field(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Кнопки "Имя"/"Тема" — включают ожидание текстового ввода для этого поля."""
    query = update.callback_query
    prefix, sid = query.data.split(":", 1)
    field = "name" if prefix == "draftname" else "subject"
    draft = POST_DRAFTS.get(sid)
    if not draft:
        await query.answer("Черновик устарел или уже обработан.", show_alert=True)
        return

    await query.answer()
    chat_id = draft["chat_id"]
    PENDING_DRAFT_FIELD[chat_id] = {"session_id": sid, "field": field}
    label = "имя" if field == "name" else "тему"
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text=f"✍️ Введите {label} (или отправьте «-», чтобы очистить поле). Отменить: /cancel",
    )
    draft["field_prompt_msg_id"] = sent.message_id


async def on_pending_draft_field_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    pending = PENDING_DRAFT_FIELD.pop(chat_id, None)
    if not pending:
        return

    prompt_id = None
    draft = POST_DRAFTS.get(pending["session_id"])
    if draft:
        prompt_id = draft.pop("field_prompt_msg_id", None)

    await _delete_own_message_silently(update.message)
    if prompt_id:
        await _delete_message_silently(context, chat_id, prompt_id)

    if not draft:
        sent = await context.bot.send_message(chat_id=chat_id, text="Черновик устарел или уже обработан.")
        schedule_message_deletion(context, sent.chat_id, sent.message_id)
        return

    value = (update.message.text or "").strip()
    if value == "-":
        value = ""
    draft[pending["field"]] = value

    sid = pending["session_id"]
    settings_msg_id = draft.get("settings_msg_id")
    if settings_msg_id:
        try:
            await context.bot.edit_message_text(
                chat_id=chat_id, message_id=settings_msg_id,
                text=_render_draft_text(draft), parse_mode=ParseMode.HTML,
                reply_markup=_render_draft_markup(sid, draft),
            )
        except Exception as e:
            logger.warning("Не удалось обновить экран настроек поста: %s", e)


async def on_draft_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    sid = query.data.split(":", 1)[1]
    draft = POST_DRAFTS.pop(sid, None)
    await query.answer()
    if draft:
        PENDING_DRAFT_FIELD.pop(draft["chat_id"], None)
    try:
        await query.edit_message_text("❌ Публикация поста отменена.")
    except Exception:
        pass


async def on_draft_continue(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    sid = query.data.split(":", 1)[1]
    draft = POST_DRAFTS.pop(sid, None)
    if not draft:
        await query.answer("Черновик устарел или уже обработан.", show_alert=True)
        return

    await query.answer()
    PENDING_DRAFT_FIELD.pop(draft["chat_id"], None)

    board, thread = draft["board"], draft["thread"]
    comment = draft["comment"]
    name, subject = draft["name"], draft["subject"]
    sage = draft["sage"]
    keep_original_filename = draft["keep_original_filename"]
    files_data = draft["files_data"]
    truncated_notice = draft.get("truncated_notice", "")
    chat_id = draft["chat_id"]

    domain = DOMAINS[0]
    http_s = get_dvach_session()

    status_msg = await query.edit_message_text(
        f"⏳ Запрашиваю капчу с 2ch для треда <b>/{board}/{thread}</b>...",
        parse_mode=ParseMode.HTML,
    )

    try:
        cap_data = await asyncio.to_thread(fetch_emoji_captcha, domain, http_s)
    except Exception as e:
        logger.exception("Ошибка при запросе капчи: %s", e)
        await status_msg.edit_text(f"❌ Не удалось связаться с 2ch: {e}")
        return

    if cap_data.get("vip") or cap_data.get("disabled"):
        await status_msg.edit_text("⚡ Капча не требуется (пасскод или отключена). Публикую пост...")
        try:
            post_res = await asyncio.to_thread(
                submit_post_to_2ch,
                session=http_s,
                domain=domain,
                board=board,
                thread=thread,
                comment=comment,
                captcha_key="",
                files_data=files_data,
                name=name,
                subject=subject,
                sage=sage,
                keep_original_filename=keep_original_filename,
            )
        except Exception as e:
            logger.exception("Необработанная ошибка при публикации поста (VIP/без капчи): %s", e)
            post_res = {"ok": False, "error": f"Внутренняя ошибка бота: {e}"}
        if post_res.get("ok"):
            post_num = post_res.get("num")
            num_str = f"#{post_num}" if post_num else "создан"
            link = f"{domain}/{board}/res/{thread}.html" + (f"#{post_num}" if post_num else "")
            sent = await status_msg.edit_text(
                f"✅ <b>Пост опубликован!</b>\n\n"
                f"• Тред: <b>/{board}/{thread}</b>\n"
                f"• Номер: <b>{num_str}</b>\n"
                f"• Ссылка: <a href=\"{link}\">Открыть на 2ch</a>"
                f"{truncated_notice}",
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True,
            )
            schedule_message_deletion(context, sent.chat_id, sent.message_id)
        else:
            err = post_res.get("error", "Неизвестная ошибка")
            await status_msg.edit_text(f"❌ Ошибка публикации: <code>{err}</code>", parse_mode=ParseMode.HTML)
        return

    if cap_data.get("error") or not cap_data.get("image") or not cap_data.get("keyboard"):
        err = cap_data.get("error") or "Не удалось загрузить капчу"
        await status_msg.edit_text(f"❌ Ошибка получения капчи: <code>{err}</code>", parse_mode=ParseMode.HTML)
        return

    session_id = secrets.token_hex(4)
    CAPTCHA_SESSIONS[session_id] = {
        "board": board,
        "thread": thread,
        "comment": comment,
        "name": name,
        "subject": subject,
        "sage": sage,
        "keep_original_filename": keep_original_filename,
        "files_data": files_data,
        "truncated_notice": truncated_notice,
        "domain": domain,
        "http_session": http_s,
        "captcha_id": cap_data["id"],
        "image": cap_data["image"],
        "keyboard": cap_data["keyboard"],
        "step": 1,
        "selected_emojis": [],
        "created_at": time.time(),
    }

    try:
        img_bytes = compose_emoji_captcha_image(cap_data["image"], cap_data["keyboard"])
    except Exception as e:
        logger.error("Ошибка при отрисовке капчи: %s", e)
        await status_msg.edit_text(f"❌ Ошибка рендеринга изображения капчи: {e}")
        return

    markup = build_captcha_keyboard(session_id, len(cap_data["keyboard"]))
    caption = (
        f"🧩 <b>Капча 2ch (EmojiCaptcha)</b>\n"
        f"Тред: <b>/{board}/{thread}</b>\n\n"
        f"<i>Посмотрите на верхнюю картинку и нажмите кнопки с соответствующими символами:</i>"
    )

    try:
        await status_msg.delete()
    except Exception:
        pass

    await context.bot.send_photo(
        chat_id=chat_id,
        photo=img_bytes,
        caption=caption,
        parse_mode=ParseMode.HTML,
        reply_markup=markup,
    )


async def collect_media_group_messages(update: Update, delay: float = MEDIA_GROUP_DELAY) -> Optional[list]:
    """Если сообщение — часть альбома (media_group_id), копит все его части в буфере
    и ждёт паузу, чтобы дать долететь остальным. Как только за время паузы не пришло
    ничего нового — эта копия функции забирает и возвращает ВЕСЬ накопленный список
    сообщений альбома, а все "проигравшие" (более ранние) копии возвращают None,
    сигнализируя вызывающему коду просто выйти и ничего не делать.

    Если сообщение не часть альбома — возвращает [update.message] сразу же, без
    задержки (обычный текст/одиночное фото не тормозятся ни на миллисекунду).
    """
    message = update.message
    group_id = message.media_group_id
    if not group_id:
        return [message]

    buf = MEDIA_GROUP_BUFFERS.setdefault(group_id, [])
    buf.append(message)
    await asyncio.sleep(delay)

    if not buf or buf[-1] is not message:
        return None  # за время нашего ожидания пришла более новая часть — она и заберёт буфер

    return MEDIA_GROUP_BUFFERS.pop(group_id, [])


def _pick_caption_message(messages: list):
    """Среди частей альбома подпись (text/caption) обычно есть только у ОДНОЙ —
    возвращает именно её (для остальных текст будет пустым)."""
    for m in messages:
        if (m.text or m.caption or "").strip():
            return m
    return messages[0]


async def _extract_one_file(context: ContextTypes.DEFAULT_TYPE, message) -> Optional[Tuple[bytes, str, bool]]:
    """Достаёт файл (фото/видео/gif/подходящий документ) из ОДНОГО Telegram-сообщения,
    если он там есть. Возвращает (file_data, file_name, has_original_name) или None.
    has_original_name=True только если Telegram реально передал исходное имя файла —
    у сжатых фото (PhotoSize) такого имени нет в принципе, Telegram стирает все
    метаданные на своей стороне ещё до того, как что-либо попадает к боту."""
    if message.photo:
        largest = message.photo[-1]
        tg_file = await context.bot.get_file(largest.file_id)
        data = bytes(await tg_file.download_as_bytearray())
        return data, f"photo_{int(time.time())}.jpg", False
    if message.video:
        vid = message.video
        tg_file = await context.bot.get_file(vid.file_id)
        data = bytes(await tg_file.download_as_bytearray())
        return data, (vid.file_name or f"video_{int(time.time())}.mp4"), bool(vid.file_name)
    if message.video_note:
        # Кружок — физически обычное mp4-видео, круглая маска/приближение это чисто
        # визуальный эффект клиента Telegram, самого файла это не касается. Имени
        # файла Telegram для video_note не передаёт вообще (в отличие от video/
        # document) — оригинала тут нет, has_original_name всегда False.
        note = message.video_note
        tg_file = await context.bot.get_file(note.file_id)
        data = bytes(await tg_file.download_as_bytearray())
        return data, f"video_note_{int(time.time())}.mp4", False
    if message.animation:
        anim = message.animation
        tg_file = await context.bot.get_file(anim.file_id)
        data = bytes(await tg_file.download_as_bytearray())
        return data, (anim.file_name or f"animation_{int(time.time())}.mp4"), bool(anim.file_name)
    if message.document:
        doc = message.document
        doc_mime = (doc.mime_type or "").lower()
        doc_name = (doc.file_name or "").lower()
        allowed_exts = (".png", ".jpg", ".jpeg", ".gif", ".webm", ".mp4")
        if doc_mime.startswith("image/") or doc_mime.startswith("video/") or any(doc_name.endswith(ext) for ext in allowed_exts):
            tg_file = await context.bot.get_file(doc.file_id)
            data = bytes(await tg_file.download_as_bytearray())
            return data, (doc.file_name or f"file_{int(time.time())}.png"), bool(doc.file_name)
    return None


async def _run_post_flow_safe(update: Update, context: ContextTypes.DEFAULT_TYPE, label: str, **kwargs) -> None:
    """Общая обёртка для вызова handle_post_flow из разных точек входа
    (/post, /reply, реплай на пост, "Новый пост"): гарантирует, что любая
    необработанная ошибка попадёт в лог и будет видна пользователю, а не
    тихо потеряется."""
    try:
        await handle_post_flow(update, context, **kwargs)
    except Exception as e:
        logger.exception("Необработанная ошибка в handle_post_flow (%s): %s", label, e)
        await update.message.reply_text(f"❌ Внутренняя ошибка бота: <code>{e}</code>", parse_mode=ParseMode.HTML)


async def _finish_captcha_message(query, text: str, reply_markup: Optional[InlineKeyboardMarkup] = None) -> None:
    """Пытается заменить капшен сообщения с капчей на финальный текст (успех/ошибка).
    Если сообщение больше нельзя редактировать (например, слишком старое) —
    отправляет тот же текст новым сообщением.
    ВАЖНО: edit_message_caption не поддерживает disable_web_page_preview (в отличие
    от reply_text) — раньше эта разница приводила к тому, что edit всегда падал
    с TypeError и код тихо проваливался в fallback, даже когда редактирование
    было бы возможно."""
    try:
        await query.edit_message_caption(caption=text, parse_mode=ParseMode.HTML, reply_markup=reply_markup)
    except Exception:
        await query.message.reply_text(
            text, parse_mode=ParseMode.HTML, disable_web_page_preview=True, reply_markup=reply_markup,
        )


def _tg_html_to_dvach_markup(html_text: str) -> str:
    """Конвертирует HTML-разметку в стиле Telegram Bot API (результат Message._parse_html)
    в BBCode-подобную разметку 2ch: [b][/b], [i][/i], [u][/u], [s][/s], [SPOILER][/SPOILER],
    цитаты (>текст) для blockquote. Тег <code>/<pre> — у 2ch нет прямого аналога,
    просто разворачиваем в обычный текст."""
    if not html_text:
        return ""

    soup = BeautifulSoup(html_text, "html.parser")

    def walk(node) -> str:
        parts = []
        for child in node.children:
            if isinstance(child, str):
                parts.append(child)
                continue
            inner = walk(child)
            name = child.name
            classes = child.get("class") or []
            if name in ("b", "strong"):
                parts.append(f"[b]{inner}[/b]")
            elif name in ("i", "em"):
                parts.append(f"[i]{inner}[/i]")
            elif name == "u":
                parts.append(f"[u]{inner}[/u]")
            elif name in ("s", "strike", "del"):
                parts.append(f"[s]{inner}[/s]")
            elif name == "tg-spoiler" or (name == "span" and "tg-spoiler" in classes):
                parts.append(f"[SPOILER]{inner}[/SPOILER]")
            elif name == "blockquote":
                lines = inner.split("\n")
                parts.append("\n".join(f"> {line}" if line else ">" for line in lines))
            elif name == "a":
                href = child.get("href", "")
                if href and inner and href != inner:
                    parts.append(f"{inner} ({href})")
                else:
                    parts.append(inner or href)
            else:
                # code/pre/tg-emoji и всё остальное — просто текст без обёртки
                parts.append(inner)
        return "".join(parts)

    return walk(soup)


def _entities_to_dvach_markup(text: str, entities) -> str:
    """text + список MessageEntity (как у Message.entities/caption_entities или
    TextQuote.entities) -> текст с BBCode-разметкой 2ch."""
    if not text:
        return ""
    if not entities:
        return text
    html = Message._parse_html(text, parse_message_entities(text, entities), urled=False)
    return _tg_html_to_dvach_markup(html or text)


def _build_formatted_comment(message) -> str:
    """Строит текст для отправки на 2ch из Telegram-сообщения: сохраняет форматирование
    (жирный/курсив/подчёркнутый/зачёркнутый/спойлер, цитаты) в виде BBCode 2ch. Если
    сообщение отправлено через "Reply with Quote" с выделением текста — выделенный
    фрагмент добавляется сверху в виде цитаты (> текст)."""
    text = message.text or message.caption or ""
    entities = message.entities or message.caption_entities or []
    own_part = _entities_to_dvach_markup(text, entities)

    quote = getattr(message, "quote", None)
    if quote and quote.text:
        quoted_bbcode = _entities_to_dvach_markup(quote.text, quote.entities or [])
        quoted_lines = "\n".join(f"> {line}" if line else ">" for line in quoted_bbcode.split("\n"))
        own_part = f"{quoted_lines}\n{own_part}" if own_part else quoted_lines

    return own_part


async def cmd_post(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    messages = await collect_media_group_messages(update)
    if messages is None:
        return  # не последняя часть альбома — обработку продолжит "победивший" вызов

    primary = _pick_caption_message(messages)
    extra = [m for m in messages if m is not primary]

    formatted = _build_formatted_comment(primary)
    cmd_match = re.match(r"^/(?:post|reply)(?:@\w+)?\s*", formatted, re.IGNORECASE)
    body = formatted[cmd_match.end():].strip() if cmd_match else formatted.strip()
    reply_msg_id = primary.reply_to_message.message_id if primary.reply_to_message else None
    await _run_post_flow_safe(
        update, context, "cmd_post", reply_msg_id=reply_msg_id, explicit_text=body,
        extra_messages=extra, primary_message=primary,
    )


async def on_reply_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message or not update.message.reply_to_message:
        return

    messages = await collect_media_group_messages(update)
    if messages is None:
        return  # не последняя часть альбома — обработку продолжит "победивший" вызов

    primary = _pick_caption_message(messages)
    extra = [m for m in messages if m is not primary]

    text = _build_formatted_comment(primary).strip()
    reply_msg_id = update.message.reply_to_message.message_id
    if not find_post_by_message_id(reply_msg_id):
        return
    await _run_post_flow_safe(
        update, context, "on_reply_message", reply_msg_id=reply_msg_id, explicit_text=text,
        extra_messages=extra, primary_message=primary,
    )


async def on_captcha_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query

    parts = query.data.split(":")
    if len(parts) != 3:
        await query.answer()
        return

    _, session_id, idx_str = parts
    session = CAPTCHA_SESSIONS.get(session_id)
    if not session:
        await query.answer("Сессия капчи истекла или не найдена.", show_alert=True)
        try:
            await query.edit_message_caption(
                caption="⚠️ Сессия капчи истекла. Отправьте <code>/reply</code> или <code>/post</code> снова.",
                parse_mode=ParseMode.HTML,
            )
        except Exception:
            pass
        return

    try:
        idx = int(idx_str)
    except ValueError:
        await query.answer()
        return

    domain = session["domain"]
    http_s = session["http_session"]
    cap_id = session["captcha_id"]

    try:
        click_res = await asyncio.to_thread(click_emoji_captcha, domain, http_s, cap_id, idx)
    except Exception as e:
        logger.exception("Ошибка при отправке клика капчи: %s", e)
        await query.answer("Ошибка связи с сервером 2ch при клике", show_alert=True)
        return

    # --- Успех: все нужные иконки угаданы, капча решена целиком ---
    if click_res.get("success"):
        await query.answer("✅ Капча решена!")
        captcha_token = click_res["success"]
        try:
            await query.edit_message_caption(
                caption="⏳ <b>Капча успешно решена!</b> Отправляю пост на Двач...",
                parse_mode=ParseMode.HTML,
            )
        except Exception:
            pass

        board = session["board"]
        thread = session["thread"]
        comment = session["comment"]
        name = session.get("name", "")
        subject = session.get("subject", "")
        sage = session.get("sage", False)
        keep_original_filename = session.get("keep_original_filename", False)
        files_data = session.get("files_data") or []
        truncated_notice = session.get("truncated_notice", "")

        try:
            post_res = await asyncio.to_thread(
                submit_post_to_2ch,
                session=http_s,
                domain=domain,
                board=board,
                thread=thread,
                comment=comment,
                captcha_key=captcha_token,
                files_data=files_data,
                name=name,
                subject=subject,
                sage=sage,
                keep_original_filename=keep_original_filename,
            )
        except Exception as e:
            logger.exception("Необработанная ошибка при публикации поста на 2ch: %s", e)
            post_res = {"ok": False, "error": f"Внутренняя ошибка бота: {e}"}

        if post_res.get("ok"):
            CAPTCHA_SESSIONS.pop(session_id, None)
            chat_id = query.message.chat_id
            try:
                await query.message.delete()
            except Exception as e:
                logger.warning("Не удалось удалить сообщение с капчей: %s", e)
            sent = await context.bot.send_message(
                chat_id=chat_id,
                text=f"✅ <b>Пост успешно опубликован!</b>{truncated_notice}",
                parse_mode=ParseMode.HTML,
            )
            schedule_message_deletion(context, chat_id, sent.message_id)
        else:
            # Сессию НЕ удаляем — 2ch мог отклонить именно токен капчи (просрочен между
            # кликом и отправкой поста), при этом сам текст/файлы поста никуда не делись.
            # Даём кнопки "Обновить капчу"/"Отмена" — они уже умеют работать с этой сессией.
            err_msg = post_res.get("error", "Неизвестная ошибка")
            logger.warning("Ошибка публикации на 2ch. Сырой ответ сервера: %s", post_res.get("raw"))
            fail_text = (
                f"❌ <b>Ошибка при публикации поста на 2ch:</b>\n"
                f"<code>{err_msg}</code>\n\n"
                f"<i>Часто помогает просто обновить капчу и попробовать снова —\n"
                f"текст и файлы поста никуда не делись.</i>"
            )
            retry_markup = InlineKeyboardMarkup([[
                InlineKeyboardButton("🔄 Обновить капчу", callback_data=f"cap_refresh:{session_id}"),
                InlineKeyboardButton("❌ Отмена", callback_data=f"cap_cancel:{session_id}"),
            ]])
            await _finish_captcha_message(query, fail_text, reply_markup=retry_markup)
        return

    # --- Правильная иконка, но капча ещё не решена целиком: сервер прислал следующий шаг ---
    new_image = click_res.get("image")
    new_keyboard = click_res.get("keyboard")
    if new_image and new_keyboard:
        await query.answer("✅ Верно! Следующий шаг")

        # запоминаем картинку иконки, которую только что угадали (она была под этим idx
        # в ПРЕДЫДУЩЕЙ клавиатуре — берём её до перезаписи session["keyboard"])
        old_keyboard = session.get("keyboard") or []
        if 0 <= idx < len(old_keyboard):
            session.setdefault("selected_emojis", []).append(old_keyboard[idx])

        session["image"] = new_image
        session["keyboard"] = new_keyboard
        session["step"] = session.get("step", 1) + 1

        img_bytes = compose_emoji_captcha_image(
            new_image, new_keyboard, session.get("selected_emojis", [])
        )
        markup = build_captcha_keyboard(session_id, len(new_keyboard))
        caption = (
            f"🧩 <b>Капча 2ch (Шаг {session['step']})</b>\n"
            f"Тред: <b>/{session['board']}/{session['thread']}</b>\n\n"
            f"<i>Нажмите следующую иконку с картинки выше:</i>"
        )
        try:
            await query.edit_message_media(
                media=InputMediaPhoto(media=img_bytes, caption=caption, parse_mode=ParseMode.HTML),
                reply_markup=markup,
            )
        except Exception as e:
            logger.warning("Не удалось обновить фото капчи: %s", e)
        return

    # --- Ни success, ни новый шаг: клик мимо (эта иконка не подходит) ---
    # Так же ведёт себя и сам сайт 2ch — клавиатура и картинка не меняются,
    # просто пробуем другую иконку.
    await query.answer("Мимо 🙅 Попробуйте другую иконку")


async def on_show_full(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Обработка кнопки '🔍 Показать оригинал' под превью-постом.

    Правит уже отправленное сообщение (или все сообщения альбома) НА МЕСТЕ через
    editMessageMedia — ничего не улетает новым сообщением в конец чата, оригинал
    остаётся частью того же сообщения и его можно скачать/переслать в любой
    момент, сколько угодно раз. Кнопка после показа убирается — переключаться
    обратно на превью незачем.
    """
    query = update.callback_query

    try:
        _, board, thread, num_str = query.data.split(":", 3)
    except ValueError:
        await query.answer("Некорректные данные кнопки.", show_alert=True)
        return

    await query.answer("Загружаю оригинал...")

    key = thread_key(board, thread)
    info = STATE.get("threads", {}).get(key)
    if not info:
        await query.message.reply_text("❌ Этот тред больше не отслеживается.")
        return

    thread_json = await asyncio.to_thread(fetch_thread, board, thread)
    if not thread_json:
        await query.message.reply_text("❌ Не удалось получить тред с 2ch (возможно, удалён или недоступен).")
        return

    post = next((p for p in get_posts(thread_json) if str(p.get("num")) == num_str), None)
    if not post:
        await query.message.reply_text(f"❌ Пост №{num_str} не найден в треде (возможно, был удалён).")
        return

    files = post.get("files") or []
    if not files:
        await query.message.reply_text("В этом посте больше нет вложений.")
        return

    # editMessageMedia стирает caption, если явно не передать его заново —
    # поэтому пересобираем тот же самый текст, что был при первой отправке поста.
    msg_ids = info.get("msg_ids", {})
    internal_chat_id = get_internal_chat_id()
    caption = _build_caption(board, thread, post, msg_ids, internal_chat_id)

    def _full_media(f: dict, with_caption: bool = False):
        url = file_url(f, "full")
        kwargs: dict = {"media": url}
        if with_caption:
            kwargs["caption"] = caption
            kwargs["parse_mode"] = ParseMode.HTML
        return InputMediaVideo(**kwargs) if is_full_video_send(f, "full") else InputMediaPhoto(**kwargs)

    album_msg_ids = (info.get("album_msg_ids") or {}).get(num_str)

    try:
        if album_msg_ids:
            # Альбом на самом деле состоит из НЕСКОЛЬКИХ отдельных сообщений
            # (общий media_group_id) — у editMessageMedia нет "массового" режима,
            # редактируем каждое своим отдельным вызовом. Небольшая пауза между
            # вызовами — чтобы не словить flood-limit на серию правок в один чат.
            # Caption у альбома изначально был только на самом первом сообщении —
            # возвращаем его туда же, остальные части были и остаются без подписи.
            for i, msg_id in enumerate(album_msg_ids):
                if i >= len(files):
                    break
                await context.bot.edit_message_media(
                    chat_id=USER_ID, message_id=msg_id, media=_full_media(files[i], with_caption=(i == 0)),
                )
                if i < len(album_msg_ids) - 1:
                    await asyncio.sleep(0.4)
            # Кнопка жила на отдельном служебном сообщении под альбомом ("Файлов в
            # посте: N") — она своё отслужила, убираем его целиком.
            try:
                await query.message.delete()
            except Exception:
                pass
        else:
            # Один файл — кнопка висит прямо на этом сообщении, редактируем медиа
            # (с сохранением caption) и убираем клавиатуру одним и тем же вызовом.
            await context.bot.edit_message_media(
                chat_id=USER_ID, message_id=query.message.message_id,
                media=_full_media(files[0], with_caption=True), reply_markup=None,
            )
    except Exception as e:
        logger.warning("Не удалось показать оригинал поста #%s: %s", num_str, e)
        links = "\n".join(file_url(f, "full") for f in files)
        await query.message.reply_text(f"❌ Не удалось загрузить оригинал напрямую. Ссылки:\n{links}")


async def on_captcha_refresh(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query

    session_id = query.data.split(":", 1)[1]
    session = CAPTCHA_SESSIONS.get(session_id)
    if not session:
        await query.answer("Сессия истекла", show_alert=True)
        return

    domain = session["domain"]
    http_s = session["http_session"]

    try:
        cap_data = await asyncio.to_thread(fetch_emoji_captcha, domain, http_s)
    except Exception as e:
        logger.exception("Ошибка при обновлении капчи: %s", e)
        await query.answer(f"Ошибка связи с 2ch: {e}", show_alert=True)
        return

    if cap_data.get("error"):
        await query.answer(f"Ошибка: {cap_data['error']}", show_alert=True)
        return

    await query.answer("Обновлено")

    session["captcha_id"] = cap_data["id"]
    session["image"] = cap_data["image"]
    session["keyboard"] = cap_data["keyboard"]
    session["step"] = 1
    session["selected_emojis"] = []

    img_bytes = compose_emoji_captcha_image(cap_data["image"], cap_data["keyboard"])
    markup = build_captcha_keyboard(session_id, len(cap_data["keyboard"]))
    caption = (
        f"🧩 <b>Капча 2ch (Обновлена)</b>\n"
        f"Тред: <b>/{session['board']}/{session['thread']}</b>\n\n"
        f"<i>Посмотрите на верхнюю картинку и нажмите кнопки с соответствующими символами:</i>"
    )
    try:
        await query.edit_message_media(
            media=InputMediaPhoto(media=img_bytes, caption=caption, parse_mode=ParseMode.HTML),
            reply_markup=markup,
        )
    except Exception as e:
        logger.warning("Ошибка при обновлении капчи: %s", e)


async def on_captcha_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()

    session_id = query.data.split(":", 1)[1]
    CAPTCHA_SESSIONS.pop(session_id, None)

    try:
        edited = await query.edit_message_caption(
            caption="❌ <b>Публикация поста отменена.</b>",
            parse_mode=ParseMode.HTML,
        )
        schedule_message_deletion(context, edited.chat_id, edited.message_id)
    except Exception:
        pass


# ------------------------- HEALTH CHECK HTTP SERVER -------------------------

class _HealthHandler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.end_headers()
        payload = {
            "status": "ok",
            "bot": "dvach_telegram_bot",
            "threads_count": len(STATE.get("threads", {})),
            "uptime_seconds": int(time.time() - START_TIME),
        }
        self.wfile.write(json.dumps(payload).encode("utf-8"))

    def log_message(self, format, *args):
        pass


def start_health_server(port: int):
    try:
        server = socketserver.TCPServer(("0.0.0.0", port), _HealthHandler)
        t = threading.Thread(target=server.serve_forever, daemon=True)
        t.start()
        logger.info("Healthcheck HTTP сервер запущен на порту %s", port)
    except Exception as e:
        logger.error("Не удалось запустить healthcheck сервер на порту %s: %s", port, e)


# ------------------------- MAIN -------------------------

def main() -> None:
    if not BOT_TOKEN or BOT_TOKEN == "ВСТАВЬ_СЮДА_ТОКЕН_БОТА":
        raise SystemExit(
            "Ошибка: Не указан токен бота!\n"
            "Задай переменную окружения DVACH_BOT_TOKEN или пропиши токен в BOT_TOKEN в начале файла."
        )

    if not USER_ID:
        raise SystemExit(
            "Ошибка: Не указан DVACH_USER_ID (твой Telegram ID или chat_id супергруппы вида -100...)!\n"
            "Узнать chat_id можно, написав боту /chatid."
        )

    if PORT > 0:
        start_health_server(PORT)

    app = Application.builder().token(BOT_TOKEN).concurrent_updates(True).build()

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("chatid", cmd_chatid))
    app.add_handler(CommandHandler("watch", cmd_watch))
    app.add_handler(CommandHandler("unwatch", cmd_unwatch))
    app.add_handler(CommandHandler("list", cmd_list))
    app.add_handler(CommandHandler("mode", cmd_mode))
    app.add_handler(CommandHandler("status", cmd_status))
    app.add_handler(CommandHandler("post", cmd_post))
    app.add_handler(CommandHandler("reply", cmd_post))
    app.add_handler(CommandHandler("cancel", cmd_cancel))

    # Режим "ожидания текста для поля черновика поста" (имя/тема) после нажатия
    # кнопки на экране настроек перед капчей.
    app.add_handler(MessageHandler(PENDING_DRAFT_FIELD_FILTER, on_pending_draft_field_message))

    # Режим "ожидания номера треда для удаления" после /unwatch без аргументов:
    # следующее сообщение-число убирает соответствующий по порядку тред.
    app.add_handler(MessageHandler(PENDING_UNWATCH_FILTER, on_pending_unwatch_message))

    # Режим "ожидания нового поста" после кнопки "✏️ Новый пост": ловим ПЕРВОЕ же
    # не-командное сообщение (текст/фото/видео/gif/документ) для чата, у которого
    # сейчас есть запись в PENDING_POST. Фильтр динамический — когда ожидания нет,
    # просто не матчится, и апдейт уходит дальше остальным хэндлерам.
    pending_post_media_filter = (
        filters.TEXT | filters.PHOTO | filters.VIDEO | filters.VIDEO_NOTE | filters.ANIMATION
        | filters.Document.IMAGE | filters.Document.VIDEO
    )
    app.add_handler(MessageHandler(
        PENDING_POST_FILTER & pending_post_media_filter & ~filters.COMMAND, on_pending_post_message
    ))

    # CommandHandler матчится только по message.text и не видит команды,
    # написанные в подписи (caption) к фото/видео/документу — Telegram Bot API
    # не помечает caption entity как bot_command для CommandHandler'а python-telegram-bot.
    # Поэтому "/post <текст>" в подписи к фото отдельно ловим тут и явно зовём cmd_post,
    # который уже сам умеет доставать текст и из caption, и резать префикс команды.
    post_caption_filter = (
        filters.PHOTO | filters.VIDEO | filters.ANIMATION | filters.Document.IMAGE | filters.Document.VIDEO
    ) & filters.CaptionRegex(r"(?i)^/(?:post|reply)(?:@\w+)?(\s|$)")
    app.add_handler(MessageHandler(post_caption_filter, cmd_post))

    app.add_handler(CallbackQueryHandler(on_captcha_callback, pattern=r"^cap:"))
    app.add_handler(CallbackQueryHandler(on_captcha_refresh, pattern=r"^cap_refresh:"))
    app.add_handler(CallbackQueryHandler(on_captcha_cancel, pattern=r"^cap_cancel:"))
    app.add_handler(CallbackQueryHandler(on_show_full, pattern=r"^full:"))
    app.add_handler(CallbackQueryHandler(on_newpost_button, pattern=r"^newpost:"))
    app.add_handler(CallbackQueryHandler(on_draft_edit_field, pattern=r"^draft(?:name|subject):"))
    app.add_handler(CallbackQueryHandler(on_draft_toggle, pattern=r"^draft(?:sage|orig):"))
    app.add_handler(CallbackQueryHandler(on_draft_continue, pattern=r"^draftgo:"))
    app.add_handler(CallbackQueryHandler(on_draft_cancel, pattern=r"^draftcancel:"))

    reply_media_filter = (
        filters.TEXT
        | filters.PHOTO
        | filters.VIDEO
        | filters.VIDEO_NOTE
        | filters.ANIMATION
        | filters.Document.IMAGE
        | filters.Document.VIDEO
    )
    app.add_handler(MessageHandler(filters.REPLY & reply_media_filter & ~filters.COMMAND, on_reply_message))

    app.job_queue.run_repeating(check_new_posts, interval=POLL_INTERVAL, first=5)

    logger.info(
        "Бот запущен. Опрос каждые %s сек. Тредов в базе: %s. Chat ID: %s",
        POLL_INTERVAL,
        len(STATE["threads"]),
        USER_ID,
    )
    app.run_polling()


if __name__ == "__main__":
    main()
