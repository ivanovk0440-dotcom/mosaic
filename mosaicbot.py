from __future__ import annotations

import asyncio
import gzip
import html
import json
import logging
import math
import os
import re
import secrets
import shutil
import subprocess
import sys
import time
import unicodedata
import zipfile
from contextlib import asynccontextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Optional, Sequence

import aiofiles
import aiosqlite
from PIL import Image, ImageDraw, ImageFont

try:  # Pillow 10.1+
    _DEFAULT_FONT = ImageFont.load_default(size=22)
except Exception:  # pragma: no cover - старые версии Pillow
    _DEFAULT_FONT = ImageFont.load_default()

try:  # Pillow 10.1+
    _SMALL_FONT = ImageFont.load_default(size=16)
except Exception:  # pragma: no cover
    _SMALL_FONT = ImageFont.load_default()

try:
    from aiogram import Bot, Dispatcher, F, Router
    from aiogram.client.default import DefaultBotProperties
    from aiogram.enums import ChatAction, ParseMode
    from aiogram.exceptions import (
        TelegramAPIError, TelegramBadRequest, TelegramNetworkError,
        TelegramRetryAfter, TelegramUnauthorizedError,
    )
    from aiogram.filters import Command, CommandStart, StateFilter
    from aiogram.fsm.context import FSMContext
    aiogram_version = "3"
except Exception as _exc:  # pragma: no cover
    raise SystemExit(
        "Не найден aiogram 3. Установите зависимости: pip install -r requirements.txt"
    ) from _exc

from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    CallbackQuery,
    FSInputFile,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputSticker,
    Message,
    Sticker,
)


# =====================================================================
# 1. КОНФИГУРАЦИЯ
# =====================================================================

APP_TITLE = "Sticker & Emoji Studio"
APP_VERSION = "1.0.0"

BASE_DIR = Path(__file__).resolve().parent
STORAGE_DIR = BASE_DIR / "storage"
ORIGINALS_DIR = STORAGE_DIR / "originals"
FRAGMENTS_DIR = STORAGE_DIR / "fragments"
PREVIEWS_DIR = STORAGE_DIR / "previews"
STICKERS_DIR = STORAGE_DIR / "stickers"
TEMPORARY_DIR = STORAGE_DIR / "temporary"
DB_PATH = BASE_DIR / "database.db"
LOG_DIR = BASE_DIR / "logs"
LOG_PATH = LOG_DIR / "bot.log"

STORAGE_SUBDIRS = (ORIGINALS_DIR, FRAGMENTS_DIR, PREVIEWS_DIR, STICKERS_DIR, TEMPORARY_DIR)

# Лимиты Telegram Bot API и собственные ограничения проекта.
MAX_DOWNLOAD_MB = 20                 # Bot API: бот может скачать файл до 20 МБ
MAX_DOWNLOAD_BYTES = MAX_DOWNLOAD_MB * 1024 * 1024
MAX_MOSAIC_ITEMS = 200               # лимит Custom Emoji набора
MAX_EMOJI_PACK_ITEMS = 200           # лимит Custom Emoji набора
MAX_STATIC_PACK_ITEMS = 120          # лимит обычного набора
MAX_ANIMATED_PACK_ITEMS = 50         # лимит TGS набора
MAX_VIDEO_PACK_ITEMS = 50            # лимит WebM набора
MAX_PACK_TITLE = 64
MAX_PACK_NAME = 64
MAX_IMAGE_PIXELS = 32_000_000        # защита от декомпрессионной бомбы
MAX_USER_STORAGE_MB = 300
MAX_TOTAL_STORAGE_MB = 4096
MAX_HEAVY_JOBS = 2
TEMP_TTL_HOURS = 12
ORIGINAL_TTL_HOURS = 24
RESULT_TTL_HOURS = 24 * 7
CLEANUP_INTERVAL_SECONDS = 1800
PACK_LINK_PREFIX = "https://t.me/addstickers/"
TELEGRAM_FLOOD_PADDING = 0.35

STICKER_SIZE = 512
EMOJI_SIZE = 512
STATIC_STICKER_MAX_BYTES = 512 * 1024
EMOJI_STICKER_MAX_BYTES = 256 * 1024
TGS_MAX_BYTES = 64 * 1024
WEBM_MAX_BYTES = 256 * 1024
WEBM_MAX_SECONDS = 3.0
GIF_MAX_BYTES = 20 * 1024 * 1024

# Палитра emoji для мозаичных наборов: Telegram требует emoji_list для каждого стикера.
MOSAIC_EMOJI_PALETTE = [
    "🟥", "🟧", "🟨", "🟩", "🟦", "🟪", "🟫", "⬛", "⬜",
    "🔶", "🔷", "🔸", "🔹", "🔺", "🔻", "💠", "🔲", "🔳",
    "🔴", "🟠", "🟡", "🟢", "🔵", "🟣", "🟤", "⚫", "⚪",
    "🖍", "🖊", "🖌", "-marker", "🖼",
]
MOSAIC_EMOJI_PALETTE = [e for e in MOSAIC_EMOJI_PALETTE if e != "-marker"]

IMAGE_EXT = {".jpg", ".jpeg", ".png", ".webp", ".bmp", ".gif", ".tif", ".tiff"}
STATIC_STICKER_EXT = {".png", ".webp", ".jpg", ".jpeg"}
VIDEO_EXT = {".mp4", ".mov", ".m4v", ".avi", ".mkv", ".webm", ".gif"}
ANIM_EXT = {".gif", ".mp4", ".mov", ".m4v", ".webm"}

MIME_BY_EXT = {
    ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".png": "image/png",
    ".webp": "image/webp", ".gif": "image/gif", ".mp4": "video/mp4",
    ".mov": "video/quicktime", ".m4v": "video/mp4", ".webm": "video/webm",
    ".tgs": "application/x-tgsticker", ".zip": "application/zip",
}


# =====================================================================
# 2. ЛОГИРОВАНИЕ
# =====================================================================

class SecretFilter(logging.Filter):
    """Не пропускает в логи токен бота и похожие на него строки."""

    def __init__(self) -> None:
        super().__init__()
        self.secrets: list[str] = []

    def add_secret(self, value: str) -> None:
        if value and len(value) >= 8 and value not in self.secrets:
            self.secrets.append(value)

    def filter(self, record: logging.LogRecord) -> bool:
        try:
            message = record.getMessage()
        except Exception:
            return True
        for secret in self.secrets:
            if secret and secret in message:
                record.msg = message.replace(secret, "***")
                record.args = ()
                break
        return True


SECRET_FILTER = SecretFilter()


def setup_logging() -> logging.Logger:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    logger = logging.getLogger("emoji_mosaic")
    logger.setLevel(logging.INFO)
    logger.handlers.clear()

    fmt = logging.Formatter("%(asctime)s | %(levelname)-8s | %(name)s | %(message)s")

    stream = logging.StreamHandler(sys.stdout)
    stream.setFormatter(fmt)
    stream.addFilter(SECRET_FILTER)

    file_handler = logging.FileHandler(LOG_PATH, encoding="utf-8")
    file_handler.setFormatter(fmt)
    file_handler.addFilter(SECRET_FILTER)

    logger.addHandler(stream)
    logger.addHandler(file_handler)
    logger.propagate = False

    logging.getLogger("aiogram").setLevel(logging.WARNING)
    return logger


LOG = setup_logging()


# =====================================================================
# 3. ЛОКАЛИЗАЦИЯ
# =====================================================================

TEXTS: dict[str, dict[str, str]] = {
"ru": {
    # ---------- Общее ----------
    "welcome_new": "👋 <b>Sticker &amp; Emoji Studio</b>\n\nЯ создаю мозаики из Custom Emoji, собираю наборы стикеров и конвертирую стикеры в картинки и GIF.\n\n👇 Выберите язык интерфейса:",
    "welcome_back": "👋 <b>С возвращением!</b>\n\nЧем займёмся?",
    "main_title": "🏠 <b>Главное меню</b>\n\nВыберите действие 👇",
    "lang_saved": "✅ Язык интерфейса: <b>русский</b>.",
    "lang_saved_en": "✅ Interface language: <b>English</b>.",
    "cancelled": "🚫 Действие отменено.",
    "done_ok": "✅ Готово.",

    # ---------- Кнопки ----------
    "btn_mosaic": "🧩 Создать мозаику",
    "btn_emoji_pack": "⭐ Custom Emoji Pack",
    "btn_sticker_pack": "🎨 Создать стикерпак",
    "btn_to_png": "🖼 Стикер в картинку",
    "btn_to_gif": "🎞 Стикер в GIF",
    "btn_my_packs": "📁 Мои наборы",
    "btn_history": "🕘 История",
    "btn_settings": "⚙️ Настройки",
    "btn_help": "❓ Помощь",
    "btn_back": "⬅️ Назад",
    "btn_home": "🏠 Главное меню",
    "btn_cancel": "❌ Отмена",
    "btn_confirm": "✅ Подтвердить",
    "btn_create": "🚀 Создать",
    "btn_change_grid": "🔄 Изменить сетку",
    "btn_manual_grid": "✏️ Свой размер",
    "btn_done": "✅ Готово",
    "btn_add_more": "➕ Добавить ещё",
    "btn_delete": "🗑 Удалить",
    "btn_link": "🔗 Открыть набор",
    "btn_details": "ℹ️ Подробнее",
    "btn_more": "➡️ Ещё",
    "btn_ru": "🇷🇺 Русский",
    "btn_en": "🇬🇧 English",
    "btn_download": "💾 Скачать",
    "btn_yes": "✅ Да, удалить",
    "btn_no": "❌ Нет, отмена",
    "btn_continue": "▶️ Продолжить",

    # ---------- Мозаика ----------
    "mos_intro": "🧩 <b>Мозаика из Custom Emoji</b>\n\nОтправьте фотографию. Я разрежу её на квадратные фрагменты и соберу настоящий набор Telegram Custom Emoji.\n\n📷 Фото можно отправить картинкой или документом.\n💾 Максимальный размер файла: <b>{max} МБ</b>.\n\n💡 Документ (без сжатия) сохраняет максимум качества.",
    "mos_downloading": "⏳ Скачиваю фотографию…",
    "mos_analyzing": "🔎 Анализирую изображение…",
    "mos_photo_info": "📷 <b>Фото получено</b>\n\nРазмер: <b>{w} × {h}</b> px\nПропорции: <b>{ratio}</b>\nФормат: <b>{fmt}</b>\n\nВыберите сетку: количество столбцов и строк.\nКаждый фрагмент будет квадратным.",
    "mos_grid_chosen": "Сетка: <b>{cols} × {rows}</b> · фрагментов: <b>{total}</b>",
    "mos_manual_prompt": "✏️ Введите размер сетки.\n\nФормат: <code>столбцы строк</code>\nНапример: <code>8 10</code> или <code>8x10</code>\n\nМаксимум: <b>{max}</b> фрагментов.\nМинимум: 2 × 2.",
    "mos_manual_bad": "🤔 Не понял размер. Введите два числа через пробел, например <code>8 10</code>.",
    "mos_manual_too_many": "⚠️ Слишком много фрагментов: {total}. Максимум <b>{max}</b>.\n\nВыберите сетку поменьше.",
    "mos_building_preview": "⏳ Нарезаю изображение и собираю предпросмотр…",
    "mos_preview_caption": "🖼 <b>Предпросмотр мозаики</b>\n\n📏 Сетка: <b>{cols} × {rows}</b>\n🧩 Фрагментов: <b>{total}</b>\n🔹 Каждый фрагмент: 512 × 512 px\n{crop}\nПодтвердите создание набора.",
    "mos_crop_line": "✂️ Для квадратных фрагментов изображение обрезано по центру: {w} × {h} px.",
    "mos_crop_none": "✂️ Обрезка не потребовалась: пропорции совпали.",
    "mos_creating": "⏳ <b>Создаю набор Custom Emoji…</b>\n\nЗагружено фрагментов: <b>{done}</b> из <b>{total}</b>",
    "mos_done": "🎉 <b>Мозаика готова!</b>\n\n📏 Сетка: {cols} × {rows}\n🧩 Элементов: {total}\n🔗 Ссылка: {link}\n\n1. Нажмите «Открыть набор» и добавьте его в Telegram.\n2. Мозаика из Custom Emoji отправлена отдельным сообщением. Точный вид на картинке выше.\n\nℹ️ Custom Emoji в чате отображаются крупно, поэтому длинные строки могут переноситься.",
    "mos_emoji_sent": "🧩 <b>Ваша мозаика из Custom Emoji</b>\n\nℹ️ Если строки перенеслись, это особенность отображения Telegram. Точный вариант смотрите на картинке.",
    "mos_emoji_blocked": "⚠️ Telegram не разрешил этому боту отправить мозаику из Custom Emoji. Набор создан и доступен по ссылке, а точный вид мозаики на картинке выше.",
    "mos_too_small": "📐 Изображение слишком маленькое для такой сетки. Выберите сетку поменьше или отправьте фото в большем разрешении.",
    "mos_saved": "💾 Мозаика сохранена в разделе «Мои наборы».",

    # ---------- Custom Emoji Pack ----------
    "ep_intro": "⭐ <b>Создание Custom Emoji Pack</b>\n\nОтправьте изображения PNG, WebP или JPG. Я подготовлю их под требования Telegram и создам настоящий набор.\n\n📸 Можно отправлять по одному или альбомом.\n🧩 Максимум: <b>{max}</b> элементов.\n\nКогда закончите, нажмите «Готово».",
    "ep_count": "🧩 Элементов в наборе: <b>{n}</b>",
    "ep_item": "Элемент #{i}",
    "ep_added": "➕ Добавлен элемент #{i}. Элементов: <b>{n}</b>",
    "ep_add_more_hint": "Отправьте ещё изображения или нажмите «Готово».",
    "ep_empty": "📭 Список пуст. Добавьте хотя бы одно изображение.",
    "ep_emoji_prompt": "😀 Введите emoji для элемента #{i}.\n\nОдин символ, например <code>😀</code>.",
    "ep_emoji_bad": "🤔 Это не похоже на emoji. Отправьте один символ, например <code>😀</code>.",
    "ep_emoji_saved": "✅ Emoji для элемента #{i}: {emoji}",
    "ep_title_prompt": "📝 Введите название набора.\n\nДо 64 символов. Например: <code>Мои смайлики</code>",
    "ep_title_bad": "⚠️ Название должно быть от 1 до 64 символов.",
    "ep_short_prompt": "🔗 Введите короткое имя для ссылки.\n\nТолько латинские буквы, цифры и «_». До 64 символов.\nЯ автоматически добавлю суффикс <code>_by_{bot}</code>.\n\nНапример: <code>my_emoji</code>",
    "ep_short_bad": "⚠️ Короткое имя не подходит.\n\nИспользуйте латинские буквы, цифры и «_». Начните с буквы.",
    "ep_preview_caption": "👀 <b>Предпросмотр набора</b>\n\n📝 Название: {title}\n🔗 Имя: <code>{short}</code>\n🧩 Элементов: <b>{n}</b>\n⭐ Тип: Custom Emoji\n\nПодтвердите создание набора.",
    "ep_creating": "⏳ <b>Создаю Custom Emoji Pack…</b>\n\nЗагружено: <b>{done}</b> из <b>{total}</b>",
    "ep_done": "🎉 <b>Набор готов!</b>\n\n⭐ {title}\n🧩 Элементов: {n}\n🔗 {link}\n\nНажмите «Открыть набор» и добавьте его в Telegram.",

    # ---------- Sticker Maker ----------
    "sp_intro": "🎨 <b>Sticker Maker</b>\n\nВыберите тип набора:",
    "sp_type_static": "🖼 Статичные\nPNG, WebP",
    "sp_type_animated": "🎞 Анимированные\nTGS",
    "sp_type_video": "🎥 Видео\nWebM",
    "sp_add_static": "🖼 <b>Статичные стикеры</b>\n\nОтправьте изображения PNG, WebP или JPG.\nПрозрачность сохраняется, пропорции не искажаются.\n\n🧩 Максимум: <b>{max}</b> стикеров.",
    "sp_add_animated": "🎞 <b>Анимированные стикеры</b>\n\nОтправьте файлы <b>.tgs</b> документами. Это формат Telegram на основе Lottie.\n\n🧩 Максимум: <b>{max}</b> стикеров.\nℹ️ Создать TGS из GIF или видео нельзя: это векторный формат. Возьмите готовый .tgs из редактора или набора @Stickers.",
    "sp_add_video": "🎥 <b>Видео-стикеры</b>\n\nОтправьте файл <b>.webm</b> документом или короткое видео MP4/MOV, я сконвертирую его в WebM.\n\n🧩 Максимум: <b>{max}</b> стикеров.\nℹ️ Длина до 3 секунд, 512 × 512 px, без звука. Прозрачность нужна в исходнике.",
    "sp_count": "🧩 Стикеров в наборе: <b>{n}</b>",
    "sp_added": "➕ Добавлен стикер #{i}. Стикеров: <b>{n}</b>",
    "ep_not_image": "🚫 Это не изображение. Отправьте PNG, WebP или JPG.",
    "sp_not_tgs": "🚫 Это не TGS. Отправьте файл .tgs документом.",
    "sp_not_video": "🚫 Это не видео. Отправьте .webm документом или видео MP4/MOV.",
    "sp_emoji_prompt": "😀 Введите emoji для стикера #{i}.\n\nМожно 1-20 emoji через пробел, например <code>😀 😎</code>",
    "sp_emoji_saved": "✅ Emoji для стикера #{i}: {emoji}",
    "sp_title_prompt": "📝 Введите название набора.\n\nДо 64 символов. Например: <code>Мои стикеры</code>",
    "sp_title_bad": "⚠️ Название должно быть от 1 до 64 символов.",
    "sp_short_prompt": "🔗 Введите короткое имя для ссылки.\n\nТолько латинские буквы, цифры и «_». До 64 символов.\nСуффикс <code>_by_{bot}</code> я добавлю автоматически.\n\nНапример: <code>my_stickers</code>",
    "sp_short_bad": "⚠️ Короткое имя не подходит.\n\nИспользуйте латинские буквы, цифры и «_». Начните с буквы.",
    "sp_preview_caption": "👀 <b>Предпросмотр набора</b>\n\n📝 Название: {title}\n🔗 Имя: <code>{short}</code>\n🎨 Тип: {type}\n🧩 Стикеров: <b>{n}</b>\n\nПодтвердите создание набора.",
    "sp_creating": "⏳ <b>Создаю стикерпак…</b>\n\nЗагружено: <b>{done}</b> из <b>{total}</b>",
    "sp_done": "🎉 <b>Стикерпак готов!</b>\n\n🎨 {title}\n🧩 Стикеров: {n}\n🔗 {link}\n\nНажмите «Открыть набор» и добавьте его в Telegram.",
    "sp_type_static_short": "статичный",
    "sp_type_animated_short": "анимированный",
    "sp_type_video_short": "видео",
    "sp_converting_video": "⏳ Конвертирую видео в WebM…",

    # ---------- Конвертер ----------
    "cv_png_intro": "🖼 <b>Стикер в картинку</b>\n\nОтправьте стикер или пересланное сообщение со стикером.\nЯ определю тип и предложу варианты.\n\nПоддерживаются WebP, TGS и WebM.",
    "cv_gif_intro": "🎞 <b>Стикер в GIF</b>\n\nОтправьте стикер.\nАнимированные (TGS) и видео (WebM) конвертируются в GIF.\n\nℹ️ GIF ограничен 256 цветами, поэтому возможна небольшая потеря качества.",
    "cv_processing": "⏳ Обрабатываю стикер…",
    "cv_static_title": "🖼 <b>Статичный стикер</b>\n\nWebP → PNG. Прозрачность сохраняется.",
    "cv_animated_title": "🎞 <b>Анимированный стикер (TGS)</b>\n\nВыберите результат:",
    "cv_video_title": "🎥 <b>Видео-стикер (WebM)</b>\n\nВыберите результат:",
    "cv_btn_gif": "🎞 GIF",
    "cv_btn_png": "🖼 PNG",
    "cv_btn_first_frame": "📷 Первый кадр",
    "cv_btn_all_frames": "📦 Все кадры (ZIP)",
    "cv_btn_source_video": "🎥 Исходное видео",
    "cv_btn_again": "🔄 Ещё раз",
    "cv_quality_title": "⚙️ <b>Настройки GIF</b>\n\nВыберите качество:",
    "cv_q_normal": "🙂 Обычное",
    "cv_q_high": "✨ Высокое",
    "cv_q_small": "📦 Минимальный размер",
    "cv_no_animation": "ℹ️ У этого стикера нет анимации. Отправляю PNG.",
    "cv_png_caption": "✅ <b>WebP → PNG</b>\n\nПрозрачность сохранена.\n📁 {size}",
    "cv_gif_caption": "✅ <b>{src} → GIF</b>\n\n🎨 Качество: {q}\n📁 {size}\n\nℹ️ GIF ограничен 256 цветами на кадр.",
    "cv_frame_caption": "✅ <b>Первый кадр извлечён</b>\n\n📷 PNG · {size}",
    "cv_frames_caption": "✅ <b>Кадры извлечены</b>\n\n📦 {n} кадров в архиве\n📁 {size}",
    "cv_mp4_caption": "✅ <b>Исходное видео</b>\n\n🎥 MP4 · {size}\nℹ️ Прозрачность в MP4 не сохраняется.",
    "cv_too_many_frames": "⚠️ Слишком много кадров. Отправляю первые {n}.",
    "cv_done": "✅ Готово. Что дальше?",

    # ---------- Мои наборы ----------
    "mp_title": "📁 <b>Мои наборы</b>\n\nЗдесь хранятся ваши мозаики и наборы.\nВыберите запись, чтобы увидеть подробности.",
    "mp_empty": "📭 Пока пусто.\n\nСоздайте первую мозаику или набор! 🚀",
    "mp_item_title": "{icon} <b>{title}</b>\n{type} · {n} эл. · {date}",
    "mp_mosaic": "🧩 Мозаика",
    "mp_emoji": "⭐ Custom Emoji",
    "mp_sticker": "🎨 Стикерпак",
    "mp_detail": "📄 <b>Информация о наборе</b>\n\n📝 {title}\n🏷 Тип: {type}\n🧩 Элементов: {n}\n📅 {date}\n🔗 {link}\n\n⚠️ Telegram не позволяет редактировать или удалять опубликованный набор через Bot API. Можно удалить только локальную запись и файлы на сервере.",
    "mp_deleted": "🗑 Локальная запись удалена, файлы очищены.",
    "mp_deleted_remote": "🗑 Набор удалён из Telegram, локальная запись тоже удалена.",
    "mp_delete_confirm": "⚠️ <b>Удалить набор?</b>\n\n{title}\n\nЭто удалит набор из Telegram для всех пользователей. Действие нельзя отменить.",
    "mp_delete_local": "🗑 Удалить только запись",
    "mp_delete_remote": "⚠️ Удалить набор из Telegram",
    "mp_delete_title": "⚠️ <b>Удалить запись?</b>\n\n{title}\n\nФайлы на сервере будут удалены. Набор в Telegram останется доступен по ссылке.",
    "mp_clear_files": "🗑 Удалить файлы на сервере",
    "mp_page": "Страница {page} из {pages}",

    # ---------- История ----------
    "hist_title": "🕘 <b>История операций</b>\n\nПоследние действия с наборами и конвертациями.",
    "hist_empty": "📭 История пуста.",
    "status_processing": "⏳ В обработке",
    "status_done": "✅ Успешно",
    "status_error": "❌ Ошибка",
    "status_cancelled": "🚫 Отменено",
    "op_mosaic": "🧩 Мозаика",
    "op_emoji_pack": "⭐ Custom Emoji Pack",
    "op_sticker_pack": "🎨 Стикерпак",
    "op_png": "🖼 Стикер в PNG",
    "op_gif": "🎞 Стикер в GIF",
    "op_frames": "📦 Извлечение кадров",

    # ---------- Настройки ----------
    "st_title": "⚙️ <b>Настройки</b>\n\nИнтерфейс, язык и хранилище.",
    "st_lang": "🌐 Язык: {language}",
    "st_choose_lang": "🌐 <b>Выберите язык</b>",
    "st_storage": "💾 <b>Хранилище</b>\n\nЗанято: <b>{size}</b>\nФайлов: <b>{n}</b>\n\nВременные файлы удаляются автоматически.",
    "st_clear_confirm": "⚠️ <b>Удалить все файлы?</b>\n\nБудут удалены оригиналы, фрагменты и результаты с сервера.\nОпубликованные наборы в Telegram останутся доступными.\n\nПродолжить?",
    "st_cleared": "✅ Файлы удалены с сервера.",
    "st_clear_files": "🗑 Удалить мои файлы",
    "st_stats": "📊 <b>Статистика</b>\n\n👤 Пользователей: {users}\n📁 Наборов: {packs}\n🖼 Конвертаций: {conversions}\n💾 Хранилище: {size}",

    # ---------- Помощь ----------
    "help_title": "❓ <b>Помощь</b>\n\nКратко о возможностях бота.",
    "help_text": (
        "❓ <b>Как работает бот</b>\n\n"
        "🧩 <b>Мозаика</b>\n"
        "Отправьте фото, выберите сетку, подтвердите. Бот нарежет фото на квадратные фрагменты и создаст набор Custom Emoji. "
        "Исходник не редактируется: только нарезка и техническое масштабирование.\n\n"
        "⭐ <b>Custom Emoji Pack</b>\n"
        "Отправьте изображения, задайте emoji, название и короткое имя. Бот создаст настоящий набор через Bot API.\n\n"
        "🎨 <b>Sticker Maker</b>\n"
        "Статичные (PNG/WebP), анимированные (TGS) и видео (WebM) наборы. Можно менять порядок, удалять элементы и назначать emoji.\n\n"
        "🖼 <b>Конвертер</b>\n"
        "WebP → PNG, TGS → GIF, WebM → GIF, первый кадр и архив кадров.\n\n"
        "⚠️ <b>Важные ограничения</b>\n"
        "• Custom Emoji могут использовать только Telegram Premium.\n"
        "• Отправка мозаики из Custom Emoji работает не у всех ботов: Telegram разрешает это при наличии Premium у владельца бота. Набор и картинка-предпросмотр доступны всегда.\n"
        "• Custom Emoji в чате крупные: длинные строки переносятся.\n"
        "• TGS создаётся только в векторных редакторах, из GIF его не сделать.\n"
        "• GIF ограничен 256 цветами и 1-битной прозрачностью.\n"
        "• Набор нельзя отредактировать после публикации, но можно удалить через бота.\n\n"
        "📁 <b>Мои наборы</b>\n"
        "Список ваших наборов, ссылки и удаление записей.\n\n"
        "🔒 <b>Приватность</b>\n"
        "Файлы хранятся на сервере бота и удаляются автоматически. Доступ к файлам есть только у их владельца."
    ),
    "help_limits": "📊 <b>Лимиты</b>\n\n🧩 Мозаика: до {mosaic} фрагментов\n⭐ Custom Emoji: до {emoji} элементов\n🖼 Статичный набор: до {static} стикеров\n🎞 TGS набор: до {anim} стикеров\n🎥 WebM набор: до {video} стикеров\n📎 Файл: до {mb} МБ\n💾 Хранилище: до {storage} МБ на пользователя",

    # ---------- Ошибки ----------
    "err_generic": "😣 Что-то пошло не так. Попробуйте ещё раз или вернитесь в меню.",
    "err_too_big": "📎 Файл слишком большой. Максимум <b>{max} МБ</b>.",
    "err_bad_format": "🚫 Неподдерживаемый формат.\n\n{expected}",
    "err_bad_image": "🖼 Не удалось прочитать изображение. Возможно, файл повреждён.",
    "err_bad_file": "📎 Не удалось обработать файл. Возможно, он повреждён.",
    "err_disk": "💾 Недостаточно места на сервере. Попробуйте позже.",
    "err_busy": "⏳ Уже выполняется другая операция. Подождите немного.",
    "err_cancel": "🚫 Операция отменена.",
    "err_pack": "⚠️ Не удалось создать набор.\n\n{reason}",
    "err_pack_name_taken": "⚠️ Не удалось создать набор.\n\nTelegram: имя набора уже занято. Попробуйте другое короткое имя.",
    "err_pack_flood": "🐢 Слишком много запросов к Telegram. Попробуйте через минуту.",
    "err_name": "✏️ Некорректное короткое имя. Используйте латинские буквы, цифры и «_».",
    "err_title": "✏️ Название должно быть от 1 до 64 символов.",
    "err_no_items": "📭 Список пуст. Добавьте хотя бы один элемент.",
    "err_too_many_items": "⚠️ Слишком много элементов. Максимум <b>{max}</b>.",
    "err_no_ffmpeg": "⚠️ FFmpeg не найден на сервере. Обратитесь к администратору бота.",
    "err_no_tgs": "⚠️ Модуль рендеринга TGS не установлен на сервере. Обратитесь к администратору.",
    "err_no_anim": "ℹ️ У этого стикера нет анимации.",
    "err_telegram": "⚠️ Telegram вернул ошибку. Попробуйте позже.",
    "err_rate": "🐢 Слишком много запросов. Подождите {sec} сек.",
    "err_timeout": "⏱ Время обработки истекло. Попробуйте файл поменьше.",
    "err_no_sticker": "🚫 Отправьте стикер или пересланное сообщение со стикером.",
    "err_no_photo": "🚫 Отправьте фотографию или документ с изображением.",
    "err_no_video": "🚫 Отправьте видео или .webm документ.",
    "err_no_tgs_file": "🚫 Отправьте .tgs файл документом.",
    "err_too_small_image": "📐 Изображение слишком маленькое. Отправьте файл в большем разрешении.",
    "err_pixel_limit": "📐 Изображение слишком большое по разрешению. Максимум 32 мегапикселя.",
    "err_send_sticker": "⚠️ Не удалось отправить стикер.",
    "err_sticker_download": "⚠️ Не удалось скачать стикер. Попробуйте ещё раз.",
    "err_quota": "💾 Превышен лимит хранилища. Удалите старые файлы в настройках.",
    "err_video_convert": "⚠️ Не удалось сконвертировать видео в WebM.",
    "err_not_found": "🤷 Запись не найдена.",
    "err_wrong_state": "🤔 Не понимаю, что делать. Нажмите кнопку в меню.",
    "err_no_keyboard": "⚠️ Не удалось показать меню. Отправьте /menu.",

    # ---------- Прочее ----------
    "status_working": "⏳ Работаю…",
    "status_uploading": "⏳ Загружаю…",
    "nav_back": "⬅️ Назад",
    "confirm_delete": "🗑 Удалить",
    "storage_empty": "0 Б",
    "items_word": "эл.",
    "unknown": "неизвестно",
},
"en": {
    # ---------- Common ----------
    "welcome_new": "👋 <b>Sticker &amp; Emoji Studio</b>\n\nI create mosaics from Custom Emoji, build sticker packs and convert stickers into images and GIFs.\n\n👇 Choose your interface language:",
    "welcome_back": "👋 <b>Welcome back!</b>\n\nWhat shall we do?",
    "main_title": "🏠 <b>Main menu</b>\n\nChoose an action 👇",
    "lang_saved": "✅ Interface language: <b>English</b>.",
    "lang_saved_en": "✅ Interface language: <b>English</b>.",
    "cancelled": "🚫 Action cancelled.",
    "done_ok": "✅ Done.",

    # ---------- Buttons ----------
    "btn_mosaic": "🧩 Create Mosaic",
    "btn_emoji_pack": "⭐ Custom Emoji Pack",
    "btn_sticker_pack": "🎨 Create Sticker Pack",
    "btn_to_png": "🖼 Sticker to Image",
    "btn_to_gif": "🎞 Sticker to GIF",
    "btn_my_packs": "📁 My Packs",
    "btn_history": "🕘 History",
    "btn_settings": "⚙️ Settings",
    "btn_help": "❓ Help",
    "btn_back": "⬅️ Back",
    "btn_home": "🏠 Main menu",
    "btn_cancel": "❌ Cancel",
    "btn_confirm": "✅ Confirm",
    "btn_create": "🚀 Create",
    "btn_change_grid": "🔄 Change grid",
    "btn_manual_grid": "✏️ Custom size",
    "btn_done": "✅ Done",
    "btn_add_more": "➕ Add more",
    "btn_delete": "🗑 Delete",
    "btn_link": "🔗 Open pack",
    "btn_details": "ℹ️ Details",
    "btn_more": "➡️ More",
    "btn_ru": "🇷🇺 Русский",
    "btn_en": "🇬🇧 English",
    "btn_download": "💾 Download",
    "btn_yes": "✅ Yes, delete",
    "btn_no": "❌ No, cancel",
    "btn_continue": "▶️ Continue",

    # ---------- Mosaic ----------
    "mos_intro": "🧩 <b>Custom Emoji Mosaic</b>\n\nSend me a photo. I will slice it into square fragments and build a real Telegram Custom Emoji pack.\n\n📷 Send it as a photo or as a document.\nfilesize 💾 Max file size: <b>{max} MB</b>.\n\n💡 A document (uncompressed) keeps the best quality.",
    "mos_downloading": "⏳ Downloading the photo…",
    "mos_analyzing": "🔎 Analyzing the image…",
    "mos_photo_info": "📷 <b>Photo received</b>\n\nSize: <b>{w} × {h}</b> px\nAspect ratio: <b>{ratio}</b>\nFormat: <b>{fmt}</b>\n\nChoose a grid: columns and rows.\nEvery fragment will be square.",
    "mos_grid_chosen": "Grid: <b>{cols} × {rows}</b> · fragments: <b>{total}</b>",
    "mos_manual_prompt": "✏️ Enter the grid size.\n\nFormat: <code>columns rows</code>\nFor example: <code>8 10</code> or <code>8x10</code>\n\nMaximum: <b>{max}</b> fragments.\nMinimum: 2 × 2.",
    "mos_manual_bad": "🤔 I could not parse that. Send two numbers separated by a space, for example <code>8 10</code>.",
    "mos_manual_too_many": "⚠️ Too many fragments: {total}. Maximum is <b>{max}</b>.\n\nChoose a smaller grid.",
    "mos_building_preview": "⏳ Slicing the image and building the preview…",
    "mos_preview_caption": "🖼 <b>Mosaic preview</b>\n\n📏 Grid: <b>{cols} × {rows}</b>\n🧩 Fragments: <b>{total}</b>\n🔹 Each fragment: 512 × 512 px\n{crop}\nConfirm to create the pack.",
    "mos_crop_line": "✂️ To keep fragments square, the image was cropped at the center: {w} × {h} px.",
    "mos_crop_none": "✂️ No cropping was needed: the aspect ratio already matched.",
    "mos_creating": "⏳ <b>Creating the Custom Emoji pack…</b>\n\nUploaded fragments: <b>{done}</b> of <b>{total}</b>",
    "mos_done": "🎉 <b>Your mosaic is ready!</b>\n\n📏 Grid: {cols} × {rows}\n🧩 Items: {total}\n🔗 Link: {link}\n\n1. Tap “Open pack” and add it in Telegram.\n2. The Custom Emoji mosaic was sent as a separate message. The exact look is in the picture above.\n\nℹ️ Custom Emoji are rendered large in chats, so long rows may wrap.",
    "mos_emoji_sent": "🧩 <b>Your Custom Emoji mosaic</b>\n\nℹ️ If the rows wrapped, that is how Telegram renders them. See the exact version in the picture.",
    "mos_emoji_blocked": "⚠️ Telegram did not allow this bot to send a Custom Emoji mosaic. The pack is created and available by the link, and the exact look is in the picture above.",
    "mos_too_small": "📐 The image is too small for this grid. Choose a smaller grid or send a larger photo.",
    "mos_saved": "💾 The mosaic was saved to “My Packs”.",

    # ---------- Custom Emoji Pack ----------
    "ep_intro": "⭐ <b>Create a Custom Emoji Pack</b>\n\nSend PNG, WebP or JPG images. I will prepare them for Telegram and create a real pack.\n\n📸 Send them one by one or as an album.\n🧩 Maximum: <b>{max}</b> items.\n\nWhen you finish, tap “Done”.",
    "ep_count": "🧩 Items in the pack: <b>{n}</b>",
    "ep_item": "Item #{i}",
    "ep_added": "➕ Item #{i} added. Items: <b>{n}</b>",
    "ep_add_more_hint": "Send more images or tap “Done”.",
    "ep_empty": "📭 The list is empty. Add at least one image.",
    "ep_emoji_prompt": "😀 Send an emoji for item #{i}.\n\nOne character, for example <code>😀</code>.",
    "ep_emoji_bad": "🤔 That does not look like an emoji. Send one character, for example <code>😀</code>.",
    "ep_emoji_saved": "✅ Emoji for item #{i}: {emoji}",
    "ep_title_prompt": "📝 Send the pack title.\n\nUp to 64 characters. For example: <code>My emoji</code>",
    "ep_title_bad": "⚠️ The title must be 1 to 64 characters long.",
    "ep_short_prompt": "🔗 Send a short name for the link.\n\nLatin letters, digits and “_” only. Up to 64 characters.\nI will add the <code>_by_{bot}</code> suffix automatically.\n\nFor example: <code>my_emoji</code>",
    "ep_short_bad": "⚠️ That short name is invalid.\n\nUse Latin letters, digits and “_”. Start with a letter.",
    "ep_preview_caption": "👀 <b>Pack preview</b>\n\n📝 Title: {title}\n🔗 Name: <code>{short}</code>\n🧩 Items: <b>{n}</b>\n⭐ Type: Custom Emoji\n\nConfirm to create the pack.",
    "ep_creating": "⏳ <b>Creating the Custom Emoji pack…</b>\n\nUploaded: <b>{done}</b> of <b>{total}</b>",
    "ep_done": "🎉 <b>Pack is ready!</b>\n\n⭐ {title}\n🧩 Items: {n}\n🔗 {link}\n\nTap “Open pack” to add it in Telegram.",

    # ---------- Sticker Maker ----------
    "sp_intro": "🎨 <b>Sticker Maker</b>\n\nChoose the pack type:",
    "sp_type_static": "🖼 Static\nPNG, WebP",
    "sp_type_animated": "🎞 Animated\nTGS",
    "sp_type_video": "🎥 Video\nWebM",
    "sp_add_static": "🖼 <b>Static stickers</b>\n\nSend PNG, WebP or JPG images.\nTransparency is preserved and proportions are not distorted.\n\n🧩 Maximum: <b>{max}</b> stickers.",
    "sp_add_animated": "🎞 <b>Animated stickers</b>\n\nSend <b>.tgs</b> files as documents. It is the Telegram Lottie-based format.\n\n🧩 Maximum: <b>{max}</b> stickers.\nℹ️ A TGS cannot be made from a GIF or video: it is a vector format. Use a ready .tgs from an editor or from @Stickers.",
    "sp_add_video": "🎥 <b>Video stickers</b>\n\nSend a <b>.webm</b> document or a short MP4/MOV video, and I will convert it to WebM.\n\n🧩 Maximum: <b>{max}</b> stickers.\nℹ️ Up to 3 seconds, 512 × 512 px, no audio. Transparency must be in the source.",
    "sp_count": "🧩 Stickers in the pack: <b>{n}</b>",
    "sp_added": "➕ Sticker #{i} added. Stickers: <b>{n}</b>",
    "ep_not_image": "🚫 That is not an image. Send PNG, WebP or JPG.",
    "sp_not_tgs": "🚫 That is not a TGS file. Send a .tgs file as a document.",
    "sp_not_video": "🚫 That is not a video. Send a .webm document or an MP4/MOV video.",
    "sp_emoji_prompt": "😀 Send an emoji for sticker #{i}.\n\nYou can send 1-20 emoji separated by spaces, for example <code>😀 😎</code>",
    "sp_emoji_saved": "✅ Emoji for sticker #{i}: {emoji}",
    "sp_title_prompt": "📝 Send the pack title.\n\nUp to 64 characters. For example: <code>My stickers</code>",
    "sp_title_bad": "⚠️ The title must be 1 to 64 characters long.",
    "sp_short_prompt": "🔗 Send a short name for the link.\n\nLatin letters, digits and “_” only. Up to 64 characters.\nThe <code>_by_{bot}</code> suffix is added automatically.\n\nFor example: <code>my_stickers</code>",
    "sp_short_bad": "⚠️ That short name is invalid.\n\nUse Latin letters, digits and “_”. Start with a letter.",
    "sp_preview_caption": "👀 <b>Pack preview</b>\n\n📝 Title: {title}\n🔗 Name: <code>{short}</code>\n🎨 Type: {type}\n🧩 Stickers: <b>{n}</b>\n\nConfirm to create the pack.",
    "sp_creating": "⏳ <b>Creating the sticker pack…</b>\n\nUploaded: <b>{done}</b> of <b>{total}</b>",
    "sp_done": "🎉 <b>Sticker pack is ready!</b>\n\n🎨 {title}\n🧩 Stickers: {n}\n🔗 {link}\n\nTap “Open pack” to add it in Telegram.",
    "sp_type_static_short": "static",
    "sp_type_animated_short": "animated",
    "sp_type_video_short": "video",
    "sp_converting_video": "⏳ Converting the video to WebM…",

    # ---------- Converter ----------
    "cv_png_intro": "🖼 <b>Sticker to Image</b>\n\nSend a sticker or a forwarded message with a sticker.\nI will detect its type and offer options.\n\nWebP, TGS and WebM are supported.",
    "cv_gif_intro": "🎞 <b>Sticker to GIF</b>\n\nSend a sticker.\nAnimated (TGS) and video (WebM) stickers are converted to GIF.\n\nℹ️ GIF is limited to 256 colors, so some quality loss is possible.",
    "cv_processing": "⏳ Processing the sticker…",
    "cv_static_title": "🖼 <b>Static sticker</b>\n\nWebP → PNG. Transparency is preserved.",
    "cv_animated_title": "🎞 <b>Animated sticker (TGS)</b>\n\nChoose the result:",
    "cv_video_title": "🎥 <b>Video sticker (WebM)</b>\n\nChoose the result:",
    "cv_btn_gif": "🎞 GIF",
    "cv_btn_png": "🖼 PNG",
    "cv_btn_first_frame": "📷 First frame",
    "cv_btn_all_frames": "📦 All frames (ZIP)",
    "cv_btn_source_video": "🎥 Source video",
    "cv_btn_again": "🔄 Again",
    "cv_quality_title": "⚙️ <b>GIF settings</b>\n\nChoose quality:",
    "cv_q_normal": "🙂 Normal",
    "cv_q_high": "✨ High",
    "cv_q_small": "📦 Smallest size",
    "cv_no_animation": "ℹ️ This sticker has no animation. Sending a PNG instead.",
    "cv_png_caption": "✅ <b>WebP → PNG</b>\n\nTransparency preserved.\n📁 {size}",
    "cv_gif_caption": "✅ <b>{src} → GIF</b>\n\n🎨 Quality: {q}\n📁 {size}\n\nℹ️ GIF is limited to 256 colors per frame.",
    "cv_frame_caption": "✅ <b>First frame extracted</b>\n\n📷 PNG · {size}",
    "cv_frames_caption": "✅ <b>Frames extracted</b>\n\n📦 {n} frames in the archive\n📁 {size}",
    "cv_mp4_caption": "✅ <b>Source video</b>\n\n🎥 MP4 · {size}\nℹ️ Transparency is not preserved in MP4.",
    "cv_too_many_frames": "⚠️ Too many frames. Sending the first {n}.",
    "cv_done": "✅ Done. What is next?",

    # ---------- My Packs ----------
    "mp_title": "📁 <b>My Packs</b>\n\nYour mosaics and packs are stored here.\nSelect an entry to see the details.",
    "mp_empty": "📭 Nothing here yet.\n\nCreate your first mosaic or pack! 🚀",
    "mp_item_title": "{icon} <b>{title}</b>\n{type} · {n} items · {date}",
    "mp_mosaic": "🧩 Mosaic",
    "mp_emoji": "⭐ Custom Emoji",
    "mp_sticker": "🎨 Sticker pack",
    "mp_detail": "📄 <b>Pack information</b>\n\n📝 {title}\n🏷 Type: {type}\n🧩 Items: {n}\n📅 {date}\n🔗 {link}\n\n⚠️ Telegram does not allow editing or deleting a published pack through the Bot API. Only the local record and server files can be removed.",
    "mp_deleted": "🗑 Local record removed, files cleaned up.",
    "mp_deleted_remote": "🗑 The pack was deleted from Telegram and the local record was removed.",
    "mp_delete_confirm": "⚠️ <b>Delete the pack?</b>\n\n{title}\n\nThis deletes the pack from Telegram for all users. This cannot be undone.",
    "mp_delete_local": "🗑 Delete local record only",
    "mp_delete_remote": "⚠️ Delete pack from Telegram",
    "mp_delete_title": "⚠️ <b>Delete the record?</b>\n\n{title}\n\nServer files will be removed. The pack stays available in Telegram by its link.",
    "mp_clear_files": "🗑 Delete server files",
    "mp_page": "Page {page} of {pages}",

    # ---------- History ----------
    "hist_title": "🕘 <b>Operation history</b>\n\nRecent pack and conversion operations.",
    "hist_empty": "📭 History is empty.",
    "status_processing": "⏳ Processing",
    "status_done": "✅ Success",
    "status_error": "❌ Error",
    "status_cancelled": "🚫 Cancelled",
    "op_mosaic": "🧩 Mosaic",
    "op_emoji_pack": "⭐ Custom Emoji Pack",
    "op_sticker_pack": "🎨 Sticker pack",
    "op_png": "🖼 Sticker to PNG",
    "op_gif": "🎞 Sticker to GIF",
    "op_frames": "📦 Frame extraction",

    # ---------- Settings ----------
    "st_title": "⚙️ <b>Settings</b>\n\nInterface, language and storage.",
    "st_lang": "🌐 Language: {language}",
    "st_choose_lang": "🌐 <b>Choose a language</b>",
    "st_storage": "💾 <b>Storage</b>\n\nUsed: <b>{size}</b>\nFiles: <b>{n}</b>\n\nTemporary files are removed automatically.",
    "st_clear_confirm": "⚠️ <b>Delete all files?</b>\n\nOriginals, fragments and results will be removed from the server.\nPublished packs stay available in Telegram.\n\nContinue?",
    "st_cleared": "✅ Files removed from the server.",
    "st_clear_files": "🗑 Delete my files",
    "st_stats": "📊 <b>Statistics</b>\n\n👤 Users: {users}\n📁 Packs: {packs}\n🖼 Conversions: {conversions}\n💾 Storage: {size}",

    # ---------- Help ----------
    "help_title": "❓ <b>Help</b>\n\nA short overview of what the bot can do.",
    "help_text": (
        "❓ <b>How the bot works</b>\n\n"
        "🧩 <b>Mosaic</b>\n"
        "Send a photo, choose a grid and confirm. The bot slices the photo into square fragments and creates a Custom Emoji pack. "
        "The source is never edited: only slicing and technical scaling.\n\n"
        "⭐ <b>Custom Emoji Pack</b>\n"
        "Send images, assign emoji, set a title and a short name. The bot creates a real pack through the Bot API.\n\n"
        "🎨 <b>Sticker Maker</b>\n"
        "Static (PNG/WebP), animated (TGS) and video (WebM) packs. Reorder, delete items and assign emoji.\n\n"
        "🖼 <b>Converter</b>\n"
        "WebP → PNG, TGS → GIF, WebM → GIF, first frame and a ZIP with all frames.\n\n"
        "⚠️ <b>Important limits</b>\n"
        "• Only Telegram Premium users can use Custom Emoji.\n"
        "• Sending a Custom Emoji mosaic does not work for every bot: Telegram allows it when the bot owner has Premium. The pack and the preview picture are always available.\n"
        "• Custom Emoji are large in chats: long rows wrap.\n"
        "• TGS is made in vector editors only, it cannot be produced from a GIF.\n"
        "• GIF is limited to 256 colors and 1-bit transparency.\n"
        "• A published pack cannot be edited, but it can be deleted by the bot.\n\n"
        "📁 <b>My Packs</b>\n"
        "The list of your packs, links and record deletion.\n\n"
        "🔒 <b>Privacy</b>\n"
        "Files are stored on the bot server and removed automatically. Only the owner can access them."
    ),
    "help_limits": "📊 <b>Limits</b>\n\n🧩 Mosaic: up to {mosaic} fragments\n⭐ Custom Emoji: up to {emoji} items\n🖼 Static pack: up to {static} stickers\n🎞 TGS pack: up to {anim} stickers\n🎥 WebM pack: up to {video} stickers\n📎 File: up to {mb} MB\n💾 Storage: up to {storage} MB per user",

    # ---------- Errors ----------
    "err_generic": "😣 Something went wrong. Try again or go back to the menu.",
    "err_too_big": "📎 The file is too large. Maximum is <b>{max} MB</b>.",
    "err_bad_format": "🚫 Unsupported format.\n\n{expected}",
    "err_bad_image": "🖼 Could not read the image. The file may be corrupted.",
    "err_bad_file": "📎 Could not process the file. It may be corrupted.",
    "err_disk": "💾 Not enough disk space on the server. Try again later.",
    "err_busy": "⏳ Another operation is already running. Please wait.",
    "err_cancel": "🚫 Operation cancelled.",
    "err_pack": "⚠️ Could not create the pack.\n\n{reason}",
    "err_pack_name_taken": "⚠️ Could not create the pack.\n\nTelegram: this pack name is already taken. Try another short name.",
    "err_pack_flood": "🐢 Too many requests to Telegram. Try again in a minute.",
    "err_name": "✏️ Invalid short name. Use Latin letters, digits and “_”.",
    "err_title": "✏️ The title must be 1 to 64 characters long.",
    "err_no_items": "📭 The list is empty. Add at least one item.",
    "err_too_many_items": "⚠️ Too many items. Maximum is <b>{max}</b>.",
    "err_no_ffmpeg": "⚠️ FFmpeg was not found on the server. Contact the bot administrator.",
    "err_no_tgs": "⚠️ The TGS rendering module is not installed on the server. Contact the bot administrator.",
    "err_no_anim": "ℹ️ This sticker has no animation.",
    "err_telegram": "⚠️ Telegram returned an error. Try again later.",
    "err_rate": "🐢 Too many requests. Wait {sec} sec.",
    "err_timeout": "⏱ Processing timed out. Try a smaller file.",
    "err_no_sticker": "🚫 Send a sticker or a forwarded message with a sticker.",
    "err_no_photo": "🚫 Send a photo or a document with an image.",
    "err_no_video": "🚫 Send a video or a .webm document.",
    "err_no_tgs_file": "🚫 Send a .tgs file as a document.",
    "err_too_small_image": "📐 The image is too small. Send a larger file.",
    "err_pixel_limit": "📐 The image resolution is too high. Maximum is 32 megapixels.",
    "err_send_sticker": "⚠️ Could not send the sticker.",
    "err_sticker_download": "⚠️ Could not download the sticker. Try again.",
    "err_quota": "💾 Storage limit exceeded. Delete old files in the settings.",
    "err_video_convert": "⚠️ Could not convert the video to WebM.",
    "err_not_found": "🤷 Record not found.",
    "err_wrong_state": "🤔 I am not sure what to do. Use a menu button.",
    "err_no_keyboard": "⚠️ Could not show the menu. Send /menu.",

    # ---------- Misc ----------
    "status_working": "⏳ Working…",
    "status_uploading": "⏳ Uploading…",
    "nav_back": "⬅️ Back",
    "confirm_delete": "🗑 Delete",
    "storage_empty": "0 B",
    "items_word": "items",
    "unknown": "unknown",
},
}


def t(lang: str, key: str, **kwargs: Any) -> str:
    """Возвращает локализованную строку с подстановкой параметров."""
    lang = lang if lang in TEXTS else "ru"
    text = TEXTS[lang].get(key)
    if text is None:
        text = TEXTS["ru"].get(key) or TEXTS["en"].get(key) or key
    if kwargs:
        try:
            text = text.format(**kwargs)
        except Exception:
            pass
    return text


def esc(value: Any) -> str:
    """Экранирует пользовательский текст для HTML-разметки Telegram."""
    return html.escape(str(value), quote=False)


def human_size(num: float) -> str:
    num = float(num)
    for unit in ("B", "KB", "MB", "GB"):
        if num < 1024 or unit == "GB":
            if unit == "B":
                return f"{int(num)} {unit}"
            return f"{num:.1f} {unit}"
        num /= 1024
    return f"{num:.1f} GB"


def ratio_text(w: int, h: int) -> str:
    g = math.gcd(int(w), int(h))
    if g == 0:
        return "1:1"
    a, b = int(w) // g, int(h) // g
    if a > 40 or b > 40:
        return f"{w/h:.3f}"
    return f"{a}:{b}"


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def format_date(value: str | None) -> str:
    if not value:
        return "-"
    try:
        dt = datetime.strptime(value[:19], "%Y-%m-%d %H:%M:%S")
        return dt.strftime("%d.%m.%Y %H:%M")
    except Exception:
        return value


# =====================================================================
# 4. ИСКЛЮЧЕНИЯ И ГЛОБАЛЬНОЕ СОСТОЯНИЕ
# =====================================================================

class BotError(Exception):
    """Ошибка с ключом локализации. Показывается пользователю без трассировки."""

    def __init__(self, key: str, **kwargs: Any) -> None:
        self.key = key
        self.kwargs = kwargs
        super().__init__(key)


class BusyError(BotError):
    def __init__(self) -> None:
        super().__init__("err_busy")


class CancelledByUser(Exception):
    """Пользователь отменил операцию."""


class Runtime:
    """Глобальное состояние процесса: бот, база, ffmpeg, кэш языков."""

    def __init__(self) -> None:
        self.bot: Optional[Bot] = None
        self.bot_username: str = ""
        self.db: Optional["Database"] = None
        self.ffmpeg: Optional[str] = None
        self.started_at: float = time.time()
        self.busy_users: set[int] = set()
        self.lang_cache: dict[int, str] = {}
        self.semaphore = asyncio.Semaphore(MAX_HEAVY_JOBS)
        self.last_callback: dict[int, float] = {}
        self.tasks: set[asyncio.Task] = set()


RT = Runtime()


@asynccontextmanager
async def heavy_job(user_id: int):
    """Защита от параллельных тяжёлых операций одного пользователя."""
    if user_id in RT.busy_users:
        raise BusyError()
    RT.busy_users.add(user_id)
    try:
        async with RT.semaphore:
            yield
    finally:
        RT.busy_users.discard(user_id)


async def run_blocking(func: Callable[..., Any], *args: Any, **kwargs: Any) -> Any:
    """Выполняет блокирующую работу (Pillow, ffmpeg) в пуле потоков."""
    return await asyncio.to_thread(func, *args, **kwargs)


# =====================================================================
# 5. ФАЙЛЫ И ХРАНИЛИЩЕ
# =====================================================================

def ensure_storage() -> None:
    for directory in STORAGE_SUBDIRS:
        directory.mkdir(parents=True, exist_ok=True)


def user_subdir(base: Path, user_id: int) -> Path:
    directory = base / str(int(user_id))
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def new_file_path(directory: Path, prefix: str, ext: str) -> Path:
    ext = ext.lower()
    if ext and not ext.startswith("."):
        ext = "." + ext
    if ext not in (".jpg", ".jpeg", ".png", ".webp", ".gif", ".mp4", ".mov", ".webm", ".tgs", ".zip", ".json", ".bin"):
        ext = ".bin"
    name = f"{prefix}_{int(time.time())}_{secrets.token_hex(4)}{ext}"
    return directory / name


def sniff_format(path: Path) -> str:
    """Определяет реальный формат файла по сигнатуре, а не по расширению."""
    try:
        with open(path, "rb") as fh:
            head = fh.read(16)
    except OSError:
        return "UNKNOWN"
    if head.startswith(b"\xff\xd8\xff"):
        return "JPEG"
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return "PNG"
    if head.startswith(b"GIF87a") or head.startswith(b"GIF89a"):
        return "GIF"
    if head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return "WEBP"
    if head.startswith(b"\x1f\x8b"):
        return "TGS"
    if head.startswith(b"\x1a\x45\xdf\xa3"):
        return "WEBM"
    if head[4:8] == b"ftyp":
        return "MP4"
    if head.startswith(b"PK\x03\x04"):
        return "ZIP"
    if head.startswith(b"BM"):
        return "BMP"
    if head.startswith(b"II*\x00") or head.startswith(b"MM\x00*"):
        return "TIFF"
    return "UNKNOWN"


def ext_for_format(fmt: str) -> str:
    return {
        "JPEG": ".jpg", "PNG": ".png", "GIF": ".gif", "WEBP": ".webp",
        "TGS": ".tgs", "WEBM": ".webm", "MP4": ".mp4", "ZIP": ".zip",
        "BMP": ".bmp", "TIFF": ".tiff",
    }.get(fmt, ".bin")


def file_size_ok(path: Path, limit: int) -> bool:
    try:
        return path.stat().st_size <= limit
    except OSError:
        return False


def cleanup_path(path: Path | str | None) -> None:
    if not path:
        return
    try:
        p = Path(path)
        if p.is_file():
            p.unlink(missing_ok=True)
    except Exception:
        LOG.debug("Не удалось удалить файл %s", path)


def cleanup_dir(path: Path | str | None) -> None:
    if not path:
        return
    try:
        p = Path(path)
        if p.is_dir():
            shutil.rmtree(p, ignore_errors=True)
    except Exception:
        LOG.debug("Не удалось удалить каталог %s", path)


# =====================================================================
# 6. ПРОВЕРКА ВВОДА
# =====================================================================

EMOJI_CHAR_RE = re.compile(
    "[\U0001F000-\U0001FAFF\u2190-\u21FF\u2300-\u23FF\u2460-\u24FF\u25A0-\u25FF"
    "\u2600-\u27BF\u2B00-\u2BFF\u2B50\u2B55\u00A9\u00AE\u203C\u2049\u2122\u2139"
    "\u231A-\u231B\u2328\u23CF\u23E9-\u23FA\u24C2\u25AA-\u25FE\u2934\u2935"
    "\u3030\u303D\u3297\u3299\uFE0F\u200D\u20E3]"
)


def is_emoji_token(token: str) -> bool:
    token = token.strip()
    if not token or len(token) > 20:
        return False
    core = "".join(ch for ch in token if ch not in ("\u200d", "\ufe0f"))
    if not core:
        return False
    return all(EMOJI_CHAR_RE.match(ch) for ch in core)


def parse_emoji_list(text: str, max_items: int = 20) -> list[str]:
    tokens = text.split()
    result: list[str] = []
    for token in tokens:
        if is_emoji_token(token):
            result.append(token)
        if len(result) >= max_items:
            break
    return result


def normalize_title(raw: str, max_len: int = MAX_PACK_TITLE) -> str:
    title = re.sub(r"\s+", " ", str(raw)).strip()
    return title[:max_len]


def sanitize_short_name(raw: str, bot_username: str) -> str:
    """Приводит короткое имя к требованиям Bot API и добавляет суффикс бота."""
    ascii_text = unicodedata.normalize("NFKD", str(raw)).encode("ascii", "ignore").decode("ascii")
    name = re.sub(r"[^a-zA-Z0-9_]", "_", ascii_text).lower()
    name = re.sub(r"_+", "_", name).strip("_")
    if not name:
        return ""
    if name[0].isdigit():
        name = "pack_" + name
    suffix = f"_by_{bot_username.lower()}" if bot_username else ""
    max_base = max(1, MAX_PACK_NAME - len(suffix))
    name = name[:max_base].strip("_")
    if not name:
        return ""
    if name[0].isdigit():
        name = "pack_" + name
    return name + suffix


def parse_grid(text: str) -> Optional[tuple[int, int]]:
    numbers = re.findall(r"\d+", text)
    if len(numbers) != 2:
        return None
    cols, rows = int(numbers[0]), int(numbers[1])
    if cols < 2 or rows < 2:
        return None
    return cols, rows


def validate_grid(cols: int, rows: int, max_items: int) -> Optional[tuple[int, int]]:
    if cols < 2 or rows < 2:
        return None
    if cols * rows > max_items:
        return None
    return cols, rows


def compute_crop(w: int, h: int, cols: int, rows: int) -> tuple[int, int, int, int]:
    """Квадратные ячейки требуют соотношения cols:rows. Обрезаем по центру."""
    target = cols / rows
    current = w / h
    if abs(current - target) < 1e-9:
        return 0, 0, w, h
    if current > target:
        new_w = max(1, min(w, round(h * target)))
        x = (w - new_w) // 2
        return x, 0, x + new_w, h
    new_h = max(1, min(h, round(w / target)))
    y = (h - new_h) // 2
    return 0, y, w, y + new_h


def suggest_grids(w: int, h: int, max_items: int) -> list[tuple[int, int]]:
    """Подбирает несколько сеток с соотношением сторон, близким к фото."""
    aspect = max(0.05, min(w / max(1, h), 20.0))
    targets = [12, 20, 30, 48, 80, 120]
    result: list[tuple[int, int]] = []
    for total in targets:
        rows = max(2, round(math.sqrt(total / aspect)))
        cols = max(2, round(rows * aspect))
        while cols * rows > max_items and (cols > 2 or rows > 2):
            if cols >= rows and cols > 2:
                cols -= 1
            elif rows > 2:
                rows -= 1
            else:
                break
        if cols * rows <= max_items and (cols, rows) not in result:
            result.append((cols, rows))
    return result[:6]


# =====================================================================
# 7. БАЗА ДАННЫХ SQLITE
# =====================================================================

class Database:
    """Асинхронная обёртка над aiosqlite. Все запросы идут через один коннект."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.conn: Optional[aiosqlite.Connection] = None
        self._lock = asyncio.Lock()

    async def init(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = await aiosqlite.connect(str(self.path))
        self.conn.row_factory = aiosqlite.Row
        await self.conn.execute("PRAGMA journal_mode=WAL")
        await self.conn.execute("PRAGMA synchronous=NORMAL")
        await self.conn.execute("PRAGMA busy_timeout=5000")
        await self.conn.execute("PRAGMA foreign_keys=ON")
        await self._create_schema()
        await self.conn.commit()
        LOG.info("База данных готова: %s", self.path)

    async def close(self) -> None:
        if self.conn:
            await self.conn.close()
            self.conn = None

    async def _create_schema(self) -> None:
        assert self.conn is not None
        await self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT,
                language TEXT NOT NULL DEFAULT 'ru',
                registration_date TEXT NOT NULL,
                premium INTEGER NOT NULL DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS mosaics (
                mosaic_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                columns INTEGER NOT NULL,
                rows INTEGER NOT NULL,
                total_fragments INTEGER NOT NULL,
                pack_name TEXT NOT NULL,
                pack_link TEXT NOT NULL,
                title TEXT NOT NULL DEFAULT '',
                files TEXT NOT NULL DEFAULT '[]',
                created_at TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'done'
            );
            CREATE INDEX IF NOT EXISTS idx_mosaics_user ON mosaics(user_id, created_at DESC);

            CREATE TABLE IF NOT EXISTS sticker_packs (
                pack_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                pack_name TEXT NOT NULL,
                pack_type TEXT NOT NULL,
                pack_link TEXT NOT NULL,
                title TEXT NOT NULL DEFAULT '',
                total_items INTEGER NOT NULL DEFAULT 0,
                files TEXT NOT NULL DEFAULT '[]',
                created_at TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'done'
            );
            CREATE INDEX IF NOT EXISTS idx_packs_user ON sticker_packs(user_id, created_at DESC);

            CREATE TABLE IF NOT EXISTS conversions (
                conversion_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                source_type TEXT NOT NULL,
                result_type TEXT NOT NULL,
                file_path TEXT,
                status TEXT NOT NULL DEFAULT 'done',
                created_at TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_conv_user ON conversions(user_id, created_at DESC);

            CREATE TABLE IF NOT EXISTS history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                op_type TEXT NOT NULL,
                title TEXT NOT NULL,
                status TEXT NOT NULL,
                details TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_history_user ON history(user_id, created_at DESC);

            CREATE TABLE IF NOT EXISTS files (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                path TEXT NOT NULL UNIQUE,
                kind TEXT NOT NULL,
                size INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL,
                expires_at INTEGER NOT NULL
            );
            CREATE INDEX IF NOT EXISTS idx_files_user ON files(user_id);
            CREATE INDEX IF NOT EXISTS idx_files_expires ON files(expires_at);
            """
        )

    async def execute(self, sql: str, args: Sequence[Any] = ()) -> None:
        assert self.conn is not None
        async with self._lock:
            await self.conn.execute(sql, tuple(args))
            await self.conn.commit()

    async def fetchone(self, sql: str, args: Sequence[Any] = ()) -> Optional[dict[str, Any]]:
        assert self.conn is not None
        async with self._lock:
            async with self.conn.execute(sql, tuple(args)) as cursor:
                row = await cursor.fetchone()
        return dict(row) if row else None

    async def fetchall(self, sql: str, args: Sequence[Any] = ()) -> list[dict[str, Any]]:
        assert self.conn is not None
        async with self._lock:
            async with self.conn.execute(sql, tuple(args)) as cursor:
                rows = await cursor.fetchall()
        return [dict(row) for row in rows]

    # ---------- пользователи ----------
    async def get_user(self, user_id: int) -> Optional[dict[str, Any]]:
        return await self.fetchone("SELECT * FROM users WHERE user_id = ?", (user_id,))

    async def upsert_user(self, user_id: int, username: str | None, language: str = "ru") -> None:
        await self.execute(
            """
            INSERT INTO users (user_id, username, language, registration_date, premium)
            VALUES (?, ?, ?, ?, 0)
            ON CONFLICT(user_id) DO UPDATE SET username = excluded.username
            """,
            (user_id, (username or "")[:64], language, utc_now_iso()),
        )

    async def set_language(self, user_id: int, language: str) -> None:
        await self.execute("UPDATE users SET language = ? WHERE user_id = ?", (language, user_id))

    async def count_users(self) -> int:
        row = await self.fetchone("SELECT COUNT(*) AS n FROM users")
        return int(row["n"]) if row else 0

    # ---------- мозаики ----------
    async def add_mosaic(self, user_id: int, cols: int, rows: int, total: int,
                         pack_name: str, pack_link: str, title: str,
                         files: Optional[Sequence[str]] = None) -> int:
        await self.execute(
            """
            INSERT INTO mosaics (user_id, columns, rows, total_fragments, pack_name, pack_link, title, files, created_at, status)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 'done')
            """,
            (user_id, cols, rows, total, pack_name, pack_link, title,
             json.dumps(list(files or [])), utc_now_iso()),
        )
        row = await self.fetchone("SELECT last_insert_rowid() AS id")
        return int(row["id"]) if row else 0

    async def list_mosaics(self, user_id: int, limit: int, offset: int) -> list[dict[str, Any]]:
        return await self.fetchall(
            """
            SELECT mosaic_id AS id, 'mosaic' AS kind, title, total_fragments AS total,
            columns, rows, pack_name, pack_link, created_at, status
            FROM mosaics WHERE user_id = ? ORDER BY created_at DESC LIMIT ? OFFSET ?
            """,
            (user_id, limit, offset),
        )

    async def count_mosaics(self, user_id: int) -> int:
        row = await self.fetchone("SELECT COUNT(*) AS n FROM mosaics WHERE user_id = ?", (user_id,))
        return int(row["n"]) if row else 0

    async def get_mosaic(self, user_id: int, mosaic_id: int) -> Optional[dict[str, Any]]:
        return await self.fetchone(
            """
            SELECT mosaic_id AS id, 'mosaic' AS kind, title, total_fragments AS total,
            columns, rows, pack_name, pack_link, files, created_at, status
            FROM mosaics WHERE user_id = ? AND mosaic_id = ?
            """,
            (user_id, mosaic_id),
        )

    async def delete_mosaic(self, user_id: int, mosaic_id: int) -> None:
        await self.execute("DELETE FROM mosaics WHERE user_id = ? AND mosaic_id = ?", (user_id, mosaic_id))

    # ---------- наборы ----------
    async def add_sticker_pack(self, user_id: int, pack_name: str, pack_type: str,
                               pack_link: str, title: str, total_items: int,
                               files: Optional[Sequence[str]] = None) -> int:
        await self.execute(
            """
            INSERT INTO sticker_packs (user_id, pack_name, pack_type, pack_link, title, total_items, files, created_at, status)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'done')
            """,
            (user_id, pack_name, pack_type, pack_link, title, total_items,
             json.dumps(list(files or [])), utc_now_iso()),
        )
        row = await self.fetchone("SELECT last_insert_rowid() AS id")
        return int(row["id"]) if row else 0

    async def list_sticker_packs(self, user_id: int, limit: int, offset: int) -> list[dict[str, Any]]:
        return await self.fetchall(
            """
            SELECT pack_id AS id, 'pack' AS kind, title, total_items AS total,
            pack_type, pack_name, pack_link, created_at, status
            FROM sticker_packs WHERE user_id = ? ORDER BY created_at DESC LIMIT ? OFFSET ?
            """,
            (user_id, limit, offset),
        )

    async def count_sticker_packs(self, user_id: int) -> int:
        row = await self.fetchone("SELECT COUNT(*) AS n FROM sticker_packs WHERE user_id = ?", (user_id,))
        return int(row["n"]) if row else 0

    async def get_sticker_pack(self, user_id: int, pack_id: int) -> Optional[dict[str, Any]]:
        return await self.fetchone(
            """
            SELECT pack_id AS id, 'pack' AS kind, title, total_items AS total,
            pack_type, pack_name, pack_link, files, created_at, status
            FROM sticker_packs WHERE user_id = ? AND pack_id = ?
            """,
            (user_id, pack_id),
        )

    async def delete_sticker_pack(self, user_id: int, pack_id: int) -> None:
        await self.execute("DELETE FROM sticker_packs WHERE user_id = ? AND pack_id = ?", (user_id, pack_id))

    async def count_all_packs(self) -> int:
        row = await self.fetchone(
            "SELECT (SELECT COUNT(*) FROM mosaics) + (SELECT COUNT(*) FROM sticker_packs) AS n"
        )
        return int(row["n"]) if row else 0

    # ---------- конвертации ----------
    async def add_conversion(self, user_id: int, source_type: str, result_type: str,
                             file_path: str | None = None) -> int:
        await self.execute(
            """
            INSERT INTO conversions (user_id, source_type, result_type, file_path, status, created_at)
            VALUES (?, ?, ?, ?, 'done', ?)
            """,
            (user_id, source_type, result_type, file_path, utc_now_iso()),
        )
        row = await self.fetchone("SELECT last_insert_rowid() AS id")
        return int(row["id"]) if row else 0

    async def count_conversions(self, user_id: int) -> int:
        row = await self.fetchone("SELECT COUNT(*) AS n FROM conversions WHERE user_id = ?", (user_id,))
        return int(row["n"]) if row else 0

    # ---------- история ----------
    async def add_history(self, user_id: int, op_type: str, title: str,
                          status: str = "processing", details: str = "") -> int:
        await self.execute(
            """
            INSERT INTO history (user_id, op_type, title, status, details, created_at)
            VALUES (?, ?, ?, ?, ?, ?)
            """,
            (user_id, op_type, title, status, details, utc_now_iso()),
        )
        row = await self.fetchone("SELECT last_insert_rowid() AS id")
        return int(row["id"]) if row else 0

    async def set_history_status(self, history_id: int, status: str, details: str = "") -> None:
        await self.execute(
            "UPDATE history SET status = ?, details = ? WHERE id = ?",
            (status, details, history_id),
        )

    async def list_history(self, user_id: int, limit: int, offset: int) -> list[dict[str, Any]]:
        return await self.fetchall(
            """
            SELECT id, op_type, title, status, details, created_at
            FROM history WHERE user_id = ? ORDER BY created_at DESC LIMIT ? OFFSET ?
            """,
            (user_id, limit, offset),
        )

    async def count_history(self, user_id: int) -> int:
        row = await self.fetchone("SELECT COUNT(*) AS n FROM history WHERE user_id = ?", (user_id,))
        return int(row["n"]) if row else 0

    # ---------- файлы ----------
    async def add_file(self, user_id: int, path: Path, kind: str, ttl_hours: float) -> None:
        try:
            size = path.stat().st_size
        except OSError:
            size = 0
        expires = int(time.time() + ttl_hours * 3600)
        await self.execute(
            """
            INSERT INTO files (user_id, path, kind, size, created_at, expires_at)
            VALUES (?, ?, ?, ?, ?, ?)
            ON CONFLICT(path) DO UPDATE SET size = excluded.size, expires_at = excluded.expires_at
            """,
            (user_id, str(path), kind, size, utc_now_iso(), expires),
        )

    async def delete_file_record(self, path: Path) -> None:
        await self.execute("DELETE FROM files WHERE path = ?", (str(path),))

    async def list_user_files(self, user_id: int) -> list[dict[str, Any]]:
        return await self.fetchall("SELECT path, size, kind FROM files WHERE user_id = ?", (user_id,))

    async def delete_user_files(self, user_id: int) -> list[str]:
        rows = await self.fetchall("SELECT path FROM files WHERE user_id = ?", (user_id,))
        paths = [row["path"] for row in rows]
        await self.execute("DELETE FROM files WHERE user_id = ?", (user_id,))
        return paths

    async def purge_expired(self) -> list[str]:
        now = int(time.time())
        rows = await self.fetchall("SELECT path FROM files WHERE expires_at <= ?", (now,))
        paths = [row["path"] for row in rows]
        if paths:
            await self.execute("DELETE FROM files WHERE expires_at <= ?", (now,))
        return paths

    async def user_storage(self, user_id: int) -> tuple[int, int]:
        row = await self.fetchone(
            "SELECT COALESCE(SUM(size), 0) AS size, COUNT(*) AS n FROM files WHERE user_id = ?",
            (user_id,),
        )
        return (int(row["size"]) if row else 0, int(row["n"]) if row else 0)

    async def total_storage(self) -> int:
        row = await self.fetchone("SELECT COALESCE(SUM(size), 0) AS size FROM files")
        return int(row["size"]) if row else 0

    async def count_files(self) -> int:
        row = await self.fetchone("SELECT COUNT(*) AS n FROM files")
        return int(row["n"]) if row else 0


# =====================================================================
# 8. МЕДИА-ДВИЖОК: ИЗОБРАЖЕНИЯ
# =====================================================================

try:
    DITHER_FS = Image.Dither.FLOYDSTEINBERG
    DITHER_NONE = Image.Dither.NONE
    QUANTIZE_MEDIAN = Image.Quantize.MEDIANCUT
except AttributeError:  # pragma: no cover - старые Pillow
    DITHER_FS = Image.FLOYDSTEINBERG  # type: ignore[attr-defined]
    DITHER_NONE = Image.NONE  # type: ignore[attr-defined]
    QUANTIZE_MEDIAN = 0  # type: ignore[attr-defined]


class ImageInfo:
    __slots__ = ("width", "height", "format", "animated", "frames", "path")

    def __init__(self, path: Path, width: int, height: int, fmt: str,
                 animated: bool = False, frames: int = 1) -> None:
        self.path = path
        self.width = width
        self.height = height
        self.format = fmt
        self.animated = animated
        self.frames = frames

    @property
    def ratio(self) -> str:
        return ratio_text(self.width, self.height)

    @property
    def aspect(self) -> float:
        return self.width / max(1, self.height)


def open_checked(path: Path) -> Image.Image:
    try:
        image = Image.open(path)
    except Exception as exc:
        raise BotError("err_bad_image") from exc
    width, height = image.size
    if width <= 0 or height <= 0:
        raise BotError("err_bad_image")
    if width * height > MAX_IMAGE_PIXELS:
        raise BotError("err_pixel_limit")
    try:
        image.load()
    except Exception as exc:
        raise BotError("err_bad_image") from exc
    return image


def inspect_image(path: Path) -> ImageInfo:
    image = open_checked(path)
    animated = bool(getattr(image, "is_animated", False))
    frames = int(getattr(image, "n_frames", 1)) if animated else 1
    fmt = (image.format or "").upper()
    return ImageInfo(path, image.width, image.height, fmt, animated, frames)


def first_frame(image: Image.Image) -> Image.Image:
    if bool(getattr(image, "is_animated", False)):
        try:
            image.seek(0)
        except Exception:
            pass
    return image.convert("RGBA")


def slice_image_sync(path: Path, out_dir: Path, cols: int, rows: int,
                     size: int = STICKER_SIZE) -> dict[str, Any]:
    """Нарезает изображение на квадратные фрагменты слева направо, сверху вниз.

    Исходник не редактируется: только обрезка по центру (если пропорции сетки
    отличаются) и равномерное распределение остатка пикселей.
    """
    image = open_checked(path).convert("RGBA")
    width, height = image.size
    crop = compute_crop(width, height, cols, rows)
    image = image.crop(crop)
    crop_w, crop_h = image.size

    # Границы ячеек: остаток пикселей распределяется равномерно.
    xs = [round(i * crop_w / cols) for i in range(cols + 1)]
    ys = [round(i * crop_h / rows) for i in range(rows + 1)]

    out_dir.mkdir(parents=True, exist_ok=True)
    paths: list[Path] = []
    index = 0
    for row in range(rows):
        for col in range(cols):
            box = (xs[col], ys[row], xs[col + 1], ys[row + 1])
            cell = image.crop(box)
            if cell.size != (size, size):
                cell = cell.resize((size, size), Image.LANCZOS)
            target = out_dir / f"cell_{index:04d}.webp"
            save_image_capped(cell, target, "WEBP", EMOJI_STICKER_MAX_BYTES, quality=95)
            paths.append(target)
            index += 1
    return {
        "paths": paths,
        "crop": crop,
        "source_size": (width, height),
        "cropped_size": (crop_w, crop_h),
    }


def save_image_capped(image: Image.Image, path: Path, fmt: str, max_bytes: int,
                      quality: int = 95) -> Path:
    """Сохраняет изображение, понижая качество, пока файл не уложится в лимит."""
    quality = max(30, min(100, quality))
    if fmt.upper() == "PNG":
        image.save(path, "PNG", optimize=True)
        if path.stat().st_size <= max_bytes:
            return path
        # PNG не уложился: переходим на WebP с потерей качества.
        fmt = "WEBP"
        path = path.with_suffix(".webp")
    if path.suffix.lower() != ".webp":
        path = path.with_suffix(".webp")
    current = quality
    while True:
        image.save(path, "WEBP", quality=current, method=4)
        if path.stat().st_size <= max_bytes or current <= 35:
            break
        current -= 10
    return path


def build_mosaic_preview_sync(paths: Sequence[Path], cols: int, rows: int,
                              out_path: Path, max_width: int = 1024) -> Path:
    """Собирает точный предпросмотр мозаики из подготовленных фрагментов."""
    cell = max(8, max_width // max(1, cols))
    canvas = Image.new("RGB", (cell * cols, cell * rows), (255, 255, 255))
    for index, fragment in enumerate(paths):
        try:
            image = Image.open(fragment).convert("RGBA")
        except Exception:
            image = Image.new("RGBA", (cell, cell), (200, 200, 200, 255))
        image = image.resize((cell, cell), Image.LANCZOS)
        x = (index % cols) * cell
        y = (index // cols) * cell
        canvas.paste(image, (x, y), image)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    canvas.save(out_path, "PNG", optimize=True)
    return out_path


def build_contact_sheet_sync(paths: Sequence[Path], out_path: Path,
                             cols: int = 5, cell: int = 160) -> Path:
    """Плитка предпросмотра для набора emoji или стикеров."""
    cols = max(1, min(cols, 8))
    rows = max(1, math.ceil(len(paths) / cols))
    canvas = Image.new("RGB", (cell * cols, cell * rows), (246, 247, 249))
    draw = ImageDraw.Draw(canvas)
    for index, path in enumerate(paths[: cols * rows]):
        try:
            image = Image.open(path).convert("RGBA")
        except Exception:
            image = Image.new("RGBA", (cell, cell), (220, 220, 220, 255))
        image.thumbnail((cell - 12, cell - 12), Image.LANCZOS)
        x = (index % cols) * cell + (cell - image.width) // 2
        y = (index // cols) * cell + (cell - image.height) // 2
        canvas.paste(image, (x, y), image)
        draw.rectangle(
            [(index % cols) * cell, (index // cols) * cell,
             (index % cols) * cell + cell - 1, (index // cols) * cell + cell - 1],
            outline=(221, 224, 228), width=1,
        )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    canvas.save(out_path, "PNG", optimize=True)
    return out_path


def prepare_static_sticker_sync(path: Path, out_path: Path,
                                max_bytes: int = STATIC_STICKER_MAX_BYTES) -> Path:
    """Статичный стикер: одна сторона ровно 512, другая не больше 512."""
    image = first_frame(open_checked(path))
    image.thumbnail((STICKER_SIZE, STICKER_SIZE), Image.LANCZOS)
    largest = max(image.size)
    if largest < STICKER_SIZE:
        scale = STICKER_SIZE / largest
        image = image.resize(
            (max(1, round(image.width * scale)), max(1, round(image.height * scale))),
            Image.LANCZOS,
        )
    if out_path.suffix.lower() not in (".webp", ".png"):
        out_path = out_path.with_suffix(".webp")
    return save_image_capped(image, out_path, out_path.suffix.lower()[1:], max_bytes)


def prepare_custom_emoji_sync(path: Path, out_path: Path,
                              max_bytes: int = EMOJI_STICKER_MAX_BYTES) -> Path:
    """Custom Emoji: строго 512 × 512, прозрачные поля, без искажений."""
    image = first_frame(open_checked(path))
    image.thumbnail((EMOJI_SIZE, EMOJI_SIZE), Image.LANCZOS)
    canvas = Image.new("RGBA", (EMOJI_SIZE, EMOJI_SIZE), (0, 0, 0, 0))
    canvas.paste(image, ((EMOJI_SIZE - image.width) // 2, (EMOJI_SIZE - image.height) // 2), image)
    if out_path.suffix.lower() not in (".webp", ".png"):
        out_path = out_path.with_suffix(".webp")
    return save_image_capped(canvas, out_path, out_path.suffix.lower()[1:], max_bytes)


def webp_to_png_sync(path: Path, out_path: Path) -> Path:
    image = first_frame(open_checked(path))
    out_path = out_path.with_suffix(".png")
    image.save(out_path, "PNG", optimize=True)
    return out_path


def draw_text_badge(text: str) -> Image.Image:
    """Заглушка-превью для TGS, когда рендер недоступен."""
    canvas = Image.new("RGBA", (512, 512), (0, 0, 0, 0))
    draw = ImageDraw.Draw(canvas)
    draw.rounded_rectangle([48, 48, 464, 464], radius=64, fill=(238, 241, 245, 255))
    bbox = draw.textbbox((0, 0), text, font=_DEFAULT_FONT)
    draw.text(((512 - (bbox[2] - bbox[0])) / 2, (512 - (bbox[3] - bbox[1])) / 2),
              text, font=_DEFAULT_FONT, fill=(60, 70, 85, 255))
    return canvas


# =====================================================================
# 9. МЕДИА-ДВИЖОК: GIF И TGS
# =====================================================================

def frames_to_gif_sync(frames: Sequence[Image.Image], out_path: Path, fps: int = 30,
                       size: int = 512, colors: int = 255,
                       dither: Any = DITHER_FS) -> Path:
    """Кодирует RGBA-кадры в GIF с глобальной палитрой и прозрачностью."""
    if not frames:
        raise BotError("err_bad_file")
    size = max(64, min(1024, int(size)))
    colors = max(32, min(255, int(colors)))
    prepared: list[Image.Image] = []
    for frame in frames:
        image = frame.convert("RGBA")
        if image.size != (size, size):
            image = image.resize((size, size), Image.LANCZOS)
        prepared.append(image)

    # Глобальная палитра из выборки кадров: без мерцания между кадрами.
    sample_count = min(len(prepared), 10)
    sample = Image.new("RGB", (size * sample_count, size), (255, 255, 255))
    for index in range(sample_count):
        source = prepared[round(index * (len(prepared) - 1) / max(1, sample_count - 1))]
        sample.paste(source, (index * size, 0), source)
    palette = sample.quantize(colors=colors, method=QUANTIZE_MEDIAN)

    transparent_index = colors if colors < 256 else 0
    encoded: list[Image.Image] = []
    for image in prepared:
        background = Image.new("RGB", image.size, (255, 255, 255))
        background.paste(image, (0, 0), image)
        quantized = background.quantize(palette=palette, dither=dither)
        alpha = image.getchannel("A")
        mask = alpha.point(lambda value: 255 if value < 128 else 0)
        quantized.paste(transparent_index, (0, 0), mask)
        encoded.append(quantized)

    out_path = out_path.with_suffix(".gif")
    encoded[0].save(
        out_path, save_all=True, append_images=encoded[1:],
        duration=round(1000 / max(1, fps)), loop=0, disposal=2,
        transparency=transparent_index, optimize=False,
    )
    return out_path


def tgs_to_gif_sync(frames: Sequence[Image.Image], out_path: Path, quality: str = "normal") -> Path:
    presets = {
        "high": dict(fps=30, size=512, colors=255, dither=DITHER_FS),
        "normal": dict(fps=30, size=384, colors=200, dither=DITHER_FS),
        "small": dict(fps=15, size=256, colors=128, dither=DITHER_NONE),
    }
    preset = presets.get(quality, presets["normal"])
    selected = frames
    if preset["fps"] < 30:
        step = max(1, round(30 / preset["fps"]))
        selected = frames[::step]
    return frames_to_gif_sync(selected, out_path, **preset)


def _prepare_pyrlottie() -> Any:
    try:
        import pyrlottie  # type: ignore
    except Exception as exc:  # pragma: no cover
        raise BotError("err_no_tgs") from exc
    package_dir = Path(pyrlottie.__file__).resolve().parent
    for child in package_dir.rglob("*"):
        if child.is_file() and child.name in ("lottie2gif", "gif2webp"):
            try:
                child.chmod(0o755)
            except OSError:
                pass
    return pyrlottie


async def render_tgs_frames(path: Path, frame_skip: int = 0) -> list[Image.Image]:
    """Рендерит TGS (gzip + Lottie) в RGBA-кадры через rlottie."""
    pyrlottie = await run_blocking(_prepare_pyrlottie)
    try:
        lottie_file = pyrlottie.LottieFile(str(path))
    except Exception as exc:
        raise BotError("err_bad_file") from exc
    try:
        result = await pyrlottie.convSingleLottieTransparentFrames(
            lottie_file, frameSkip=max(0, int(frame_skip))
        )
    except BotError:
        raise
    except Exception as exc:
        LOG.warning("Ошибка рендера TGS %s: %s", path.name, exc)
        raise BotError("err_bad_file") from exc
    frames: list[Image.Image] = []
    for value in result.values():
        frames.extend(getattr(value, "frames", []) or [])
    if not frames:
        raise BotError("err_bad_file")
    return frames


def limit_frames(frames: Sequence[Image.Image], limit: int) -> tuple[list[Image.Image], bool]:
    if len(frames) <= limit:
        return list(frames), False
    step = len(frames) / limit
    picked = [frames[min(len(frames) - 1, int(i * step))] for i in range(limit)]
    return picked, True


# =====================================================================
# 10. МЕДИА-ДВИЖОК: FFMPEG
# =====================================================================

def find_ffmpeg() -> Optional[str]:
    for name in ("ffmpeg", "ffmpeg.exe"):
        found = shutil.which(name)
        if found:
            return found
    try:
        import imageio_ffmpeg  # type: ignore
        candidate = imageio_ffmpeg.get_ffmpeg_exe()
        if candidate and Path(candidate).is_file():
            return candidate
    except Exception:
        pass
    return None


def _ffmpeg_required() -> str:
    if not RT.ffmpeg:
        raise BotError("err_no_ffmpeg")
    return RT.ffmpeg


def run_ffmpeg_sync(args: Sequence[str], timeout: int = 300) -> "subprocess.CompletedProcess[bytes]":
    import subprocess
    executable = _ffmpeg_required()
    try:
        completed = subprocess.run(
            [executable, "-hide_banner", "-loglevel", "error", "-y", *args],
            capture_output=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise BotError("err_timeout") from exc
    except OSError as exc:
        raise BotError("err_no_ffmpeg") from exc
    if completed.returncode != 0:
        stderr = completed.stderr.decode("utf-8", "ignore")[:400]
        LOG.warning("FFmpeg ошибка: %s", stderr)
        raise BotError("err_video_convert")
    return completed


def probe_video_sync(path: Path) -> dict[str, Any]:
    import subprocess
    executable = _ffmpeg_required()
    try:
        completed = subprocess.run(
            [executable, "-hide_banner", "-i", str(path)],
            capture_output=True, timeout=60,
        )
    except (subprocess.TimeoutExpired, OSError) as exc:
        raise BotError("err_bad_file") from exc
    text = completed.stderr.decode("utf-8", "ignore")
    duration = 0.0
    match = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", text)
    if match:
        duration = int(match.group(1)) * 3600 + int(match.group(2)) * 60 + float(match.group(3))
    fps = 0.0
    match = re.search(r"([\d.]+)\s*fps", text)
    if match:
        fps = float(match.group(1))
    size = (0, 0)
    match = re.search(r",\s*(\d{2,5})x(\d{2,5})[\s,]", text)
    if match:
        size = (int(match.group(1)), int(match.group(2)))
    codec = ""
    match = re.search(r"Video:\s*([A-Za-z0-9_]+)", text)
    if match:
        codec = match.group(1).lower()
    return {"duration": duration, "fps": fps, "width": size[0],
            "height": size[1], "codec": codec}


def webm_to_gif_sync(path: Path, out_path: Path, quality: str = "normal") -> Path:
    presets = {
        "high": dict(fps=30, scale=512, colors=256, dither="sierra2_4a"),
        "normal": dict(fps=30, scale=384, colors=200, dither="sierra2_4a"),
        "small": dict(fps=15, scale=256, colors=128, dither="none"),
    }
    preset = presets.get(quality, presets["normal"])
    scale = preset["scale"]
    video_filter = (
        f"fps={preset['fps']},"
        f"scale={scale}:{scale}:force_original_aspect_ratio=decrease,"
        f"pad={scale}:{scale}:(ow-iw)/2:(oh-ih)/2:color=black@0.0,"
        f"split[a][b];"
        f"[a]palettegen=max_colors={preset['colors']}:reserve_transparent=1:stats_mode=diff[p];"
        f"[b][p]paletteuse=dither={preset['dither']}:alpha_threshold=128:diff_mode=rectangle"
    )
    out_path = out_path.with_suffix(".gif")
    run_ffmpeg_sync(["-i", str(path), "-vf", video_filter, "-loop", "0", str(out_path)])
    if not out_path.exists() or out_path.stat().st_size == 0:
        raise BotError("err_video_convert")
    return out_path


def webm_first_frame_sync(path: Path, out_path: Path) -> Path:
    out_path = out_path.with_suffix(".png")
    run_ffmpeg_sync(["-i", str(path), "-frames:v", "1", "-pix_fmt", "rgba", str(out_path)])
    if not out_path.exists():
        raise BotError("err_video_convert")
    return out_path


def webm_to_mp4_sync(path: Path, out_path: Path) -> Path:
    out_path = out_path.with_suffix(".mp4")
    run_ffmpeg_sync([
        "-i", str(path), "-c:v", "libx264", "-pix_fmt", "yuv420p",
        "-movflags", "+faststart", "-an", str(out_path),
    ])
    if not out_path.exists():
        raise BotError("err_video_convert")
    return out_path


def video_to_webm_sticker_sync(path: Path, out_path: Path) -> Path:
    """Конвертирует видео в WebM-стикер: 512 × 512, VP9, без звука, до 3 секунд."""
    out_path = out_path.with_suffix(".webm")
    video_filter = (
        "fps=30,scale=512:512:force_original_aspect_ratio=decrease,"
        "pad=512:512:(ow-iw)/2:(oh-ih)/2:color=black@0.0"
    )
    last_error: Optional[Exception] = None
    for crf in (28, 34, 40, 46, 52):
        try:
            run_ffmpeg_sync([
                "-t", f"{WEBM_MAX_SECONDS}",
                "-i", str(path),
                "-vf", video_filter,
                "-c:v", "libvpx-vp9", "-pix_fmt", "yuva420p",
                "-b:v", "0", "-crf", str(crf), "-row-mt", "1",
                "-an", str(out_path),
            ], timeout=300)
        except BotError as exc:
            last_error = exc
            continue
        if out_path.exists() and 0 < out_path.stat().st_size <= WEBM_MAX_BYTES:
            return out_path
    if out_path.exists() and out_path.stat().st_size > WEBM_MAX_BYTES:
        raise BotError("err_video_convert")
    raise BotError("err_video_convert") from last_error


def webm_extract_frames_sync(path: Path, out_dir: Path, limit: int = 90) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    run_ffmpeg_sync([
        "-i", str(path), "-vf", "scale=256:-1", "-pix_fmt", "rgba",
        str(out_dir / "frame_%04d.png"),
    ])
    frames = sorted(out_dir.glob("frame_*.png"))
    if len(frames) > limit:
        for extra in frames[limit:]:
            cleanup_path(extra)
        frames = frames[:limit]
    return frames


def make_zip_sync(files: Sequence[Path], zip_path: Path) -> Path:
    zip_path = zip_path.with_suffix(".zip")
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for index, file_path in enumerate(files):
            if file_path.exists():
                archive.write(file_path, arcname=f"frame_{index:04d}{file_path.suffix}")
    return zip_path


# =====================================================================
# 11. TELEGRAM: ЗАГРУЗКА ФАЙЛОВ, ПОВТОРЫ, СОЗДАНИЕ НАБОРОВ
# =====================================================================

async def api_call(func: Callable[..., Any], *args: Any, retries: int = 4, **kwargs: Any) -> Any:
    """Вызов Bot API с повторами и уважением retry_after."""
    delay = 1.0
    for attempt in range(1, retries + 1):
        try:
            return await func(*args, **kwargs)
        except TelegramRetryAfter as exc:
            wait = float(getattr(exc, "retry_after", 3)) + TELEGRAM_FLOOD_PADDING
            LOG.warning("Telegram flood: ждём %.1f сек", wait)
            await asyncio.sleep(wait)
        except TelegramNetworkError as exc:
            if attempt >= retries:
                raise
            LOG.warning("Сетевая ошибка Telegram (попытка %s): %s", attempt, exc)
            await asyncio.sleep(delay)
            delay = min(delay * 2, 20.0)
        except TelegramAPIError:
            raise
    return await func(*args, **kwargs)


def telegram_error_key(exc: Exception) -> tuple[str, dict[str, Any]]:
    """Преобразует ошибку Telegram в ключ локализации."""
    text = str(exc).lower()
    if "too many requests" in text or "flood" in text:
        return "err_pack_flood", {}
    if "sticker set name is already occupied" in text or "sticker_set_invalid" in text or "name is already" in text:
        return "err_pack_name_taken", {}
    if "sticker_png_dimensions" in text or "stickerset_invalid" in text:
        return "err_pack", {"reason": esc(str(exc)[:300])}
    if "sticker_emoji_invalid" in text:
        return "err_pack", {"reason": esc(str(exc)[:300])}
    if "premium" in text and "emoji" in text:
        return "err_pack", {"reason": esc(str(exc)[:300])}
    if "bot was blocked" in text or "blocked by the user" in text:
        return "err_pack", {"reason": esc(str(exc)[:300])}
    return "err_telegram", {}


class ProgressReporter:
    """Редактирует статус не чаще раза в 2 секунды, чтобы не ловить flood."""

    def __init__(self, message: Message, lang: str, total: int, key: str) -> None:
        self.message = message
        self.lang = lang
        self.total = max(1, int(total))
        self.key = key
        self._last_edit = 0.0
        self._last_value = -1

    async def update(self, done: int, force: bool = False) -> None:
        if done == self._last_value:
            return
        now = time.monotonic()
        if not force and now - self._last_edit < 2.0 and done < self.total:
            return
        text = t(self.lang, self.key, done=done, total=self.total)
        try:
            await self.message.edit_text(text)
            self._last_edit = now
            self._last_value = done
        except TelegramBadRequest:
            pass
        except TelegramAPIError as exc:
            LOG.debug("Не удалось обновить прогресс: %s", exc)

    async def finish(self, text: str) -> None:
        try:
            await self.message.edit_text(text)
        except TelegramAPIError:
            pass


async def download_file(bot: Bot, file_id: str, dest_dir: Path, prefix: str,
                        max_bytes: int = MAX_DOWNLOAD_BYTES,
                        user_id: Optional[int] = None) -> Path:
    if user_id is not None and RT.db is not None:
        used, _count = await RT.db.user_storage(user_id)
        if used >= MAX_USER_STORAGE_MB * 1024 * 1024:
            raise BotError("err_quota")
    try:
        tg_file = await api_call(bot.get_file, file_id)
    except BotError:
        raise
    except Exception as exc:
        LOG.warning("get_file failed: %s", exc)
        raise BotError("err_bad_file") from exc
    if tg_file.file_size and tg_file.file_size > max_bytes:
        raise BotError("err_too_big", max=MAX_DOWNLOAD_MB)
    suffix = Path(tg_file.file_path or "").suffix.lower() or ".bin"
    dest = new_file_path(dest_dir, prefix, suffix)
    try:
        await bot.download_file(tg_file.file_path, destination=str(dest))
    except Exception as exc:
        cleanup_path(dest)
        LOG.warning("download failed: %s", exc)
        raise BotError("err_bad_file") from exc
    try:
        async with aiofiles.open(dest, "rb") as handle:
            head = await handle.read(16)
    except OSError as exc:
        cleanup_path(dest)
        raise BotError("err_bad_file") from exc
    if not head:
        cleanup_path(dest)
        raise BotError("err_bad_file")
    if dest.stat().st_size > max_bytes:
        cleanup_path(dest)
        raise BotError("err_too_big", max=MAX_DOWNLOAD_MB)
    return dest


async def create_pack(bot: Bot, user_id: int, name: str, title: str,
                      stickers: Sequence[InputSticker], sticker_type: str,
                      progress: Optional[ProgressReporter] = None) -> None:
    """Создаёт набор через Bot API: 50 стикеров за вызов, остальные по одному."""
    if not stickers:
        raise BotError("err_no_items")
    first, rest = stickers[:50], stickers[50:]
    await api_call(
        bot.create_new_sticker_set,
        user_id=user_id, name=name, title=title, stickers=list(first),
        sticker_type=sticker_type,
    )
    done = len(first)
    if progress:
        await progress.update(done)
    for sticker in rest:
        await api_call(bot.add_sticker_to_set, user_id=user_id, name=name, sticker=sticker)
        done += 1
        if progress:
            await progress.update(done)
        await asyncio.sleep(0.12)


async def fetch_pack_stickers(bot: Bot, name: str) -> list[Sticker]:
    sticker_set = await api_call(bot.get_sticker_set, name)
    return list(sticker_set.stickers or [])


def build_mosaic_text(emoji_ids: Sequence[str], cols: int, rows: int,
                      fallback: str = "🖼") -> str:
    lines = []
    for row in range(rows):
        chunk = emoji_ids[row * cols:(row + 1) * cols]
        if not chunk:
            continue
        lines.append("".join(
            f'<tg-emoji emoji-id="{emoji_id}">{fallback}</tg-emoji>' for emoji_id in chunk
        ))
    return "\n".join(lines)


def split_mosaic_messages(emoji_ids: Sequence[str], cols: int, rows: int) -> list[str]:
    """Делит мозаику на сообщения, чтобы не превысить лимит 4096 символов."""
    messages: list[str] = []
    current: list[str] = []
    current_length = 0
    for row in range(rows):
        chunk = emoji_ids[row * cols:(row + 1) * cols]
        if not chunk:
            continue
        line = "".join(f'<tg-emoji emoji-id="{eid}">🖼</tg-emoji>' for eid in chunk)
        line_length = cols * 2 + 1
        if current and current_length + line_length > 3500:
            messages.append("\n".join(current))
            current = []
            current_length = 0
        current.append(line)
        current_length += line_length
    if current:
        messages.append("\n".join(current))
    return messages


async def send_mosaic_emoji(bot: Bot, chat_id: int, emoji_ids: Sequence[str],
                            cols: int, rows: int, lang: str) -> bool:
    """Отправляет мозаику из Custom Emoji. Возвращает False, если Telegram запретил."""
    chunks = split_mosaic_messages(emoji_ids, cols, rows)
    if not chunks:
        return False
    try:
        for index, chunk in enumerate(chunks):
            await bot.send_message(
                chat_id, chunk,
                reply_markup=None,
                disable_web_page_preview=True,
            )
            if index == 0:
                await bot.send_message(chat_id, t(lang, "mos_emoji_sent"))
    except TelegramBadRequest as exc:
        LOG.warning("Не удалось отправить мозаику из emoji: %s", exc)
        return False
    except TelegramAPIError as exc:
        LOG.warning("Ошибка отправки мозаики: %s", exc)
        return False
    return True


# =====================================================================
# 12. КЛАВИАТУРЫ
# =====================================================================

def btn(text: str, data: Optional[str] = None, url: Optional[str] = None,
        style: Optional[str] = None) -> InlineKeyboardButton:
    """Кнопка с официальным стилем Bot API 9.4 (primary/success/danger).

    На старых версиях aiogram поле style может быть недоступно: в этом случае
    кнопка создаётся без стиля, интерфейс остаётся рабочим.
    """
    if style:
        try:
            return InlineKeyboardButton(text=text, callback_data=data, url=url, style=style)
        except Exception:
            pass
    return InlineKeyboardButton(text=text, callback_data=data, url=url)


def markup(rows: Sequence[Sequence[InlineKeyboardButton]]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[list(row) for row in rows])


def main_menu_kb(lang: str) -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "btn_mosaic"), "mosaic:start", style="primary"),
         btn(t(lang, "btn_emoji_pack"), "emoji:start")],
        [btn(t(lang, "btn_sticker_pack"), "stickers:start"),
         btn(t(lang, "btn_to_png"), "conv:png")],
        [btn(t(lang, "btn_to_gif"), "conv:gif"),
         btn(t(lang, "btn_my_packs"), "packs:list")],
        [btn(t(lang, "btn_history"), "hist:list"),
         btn(t(lang, "btn_settings"), "settings:main")],
        [btn(t(lang, "btn_help"), "help:main")],
    ])


def language_kb() -> InlineKeyboardMarkup:
    return markup([
        [btn(t("ru", "btn_ru"), "lang:ru", style="primary")],
        [btn(t("en", "btn_en"), "lang:en")],
    ])


def nav_kb(lang: str, back: Optional[str] = None, home: bool = True,
           cancel: Optional[str] = None) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    if back:
        rows.append([btn(t(lang, "btn_back"), back)])
    if cancel:
        rows.append([btn(t(lang, "btn_cancel"), cancel, style="danger")])
    if home:
        rows.append([btn(t(lang, "btn_home"), "home")])
    return markup(rows)


def grid_kb(lang: str, grids: Sequence[tuple[int, int]]) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    current: list[InlineKeyboardButton] = []
    for cols, rows_count in grids:
        current.append(btn(f"{cols} × {rows_count}", f"mosaic:grid:{cols}:{rows_count}", style="primary"))
        if len(current) == 2:
            rows.append(current)
            current = []
    if current:
        rows.append(current)
    rows.append([btn(t(lang, "btn_manual_grid"), "mosaic:manual")])
    rows.append([btn(t(lang, "btn_cancel"), "cancel", style="danger")])
    return markup(rows)


def mosaic_preview_kb(lang: str, cols: int, rows: int) -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "btn_confirm"), f"mosaic:create:{cols}:{rows}", style="success")],
        [btn(t(lang, "btn_change_grid"), "mosaic:change", style="primary")],
        [btn(t(lang, "btn_cancel"), "cancel", style="danger")],
    ])


def items_kb(lang: str, items: Sequence[dict[str, Any]], prefix: str,
             done_label: str) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    for index, item in enumerate(items):
        emoji = str(item.get("emoji") or "😀")
        rows.append([
            btn(f"{index + 1} · {emoji}", f"{prefix}:e:{index}"),
            btn("🗑", f"{prefix}:d:{index}", style="danger"),
            btn("⬆️", f"{prefix}:u:{index}"),
            btn("⬇️", f"{prefix}:m:{index}"),
        ])
    rows.append([btn(done_label, f"{prefix}:done", style="success")])
    rows.append([btn(t(lang, "btn_cancel"), f"{prefix}:cancel", style="danger")])
    return markup(rows)


def pack_type_kb(lang: str) -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "sp_type_static"), "stickers:type:static", style="primary")],
        [btn(t(lang, "sp_type_animated"), "stickers:type:animated")],
        [btn(t(lang, "sp_type_video"), "stickers:type:video")],
        [btn(t(lang, "btn_back"), "home")],
    ])


def confirm_pack_kb(lang: str, prefix: str) -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "btn_create"), f"{prefix}:confirm", style="success")],
        [btn(t(lang, "btn_back"), f"{prefix}:back", style="primary")],
        [btn(t(lang, "btn_cancel"), "cancel", style="danger")],
    ])


def quality_kb(lang: str, prefix: str) -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "cv_q_normal"), f"{prefix}:q:normal", style="primary")],
        [btn(t(lang, "cv_q_high"), f"{prefix}:q:high")],
        [btn(t(lang, "cv_q_small"), f"{prefix}:q:small")],
        [btn(t(lang, "btn_back"), f"{prefix}:options")],
        [btn(t(lang, "btn_cancel"), "cancel", style="danger")],
    ])


def converter_options_kb(lang: str, kind: str) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    if kind == "static":
        rows.append([btn(t(lang, "cv_btn_png"), "conv:do:png", style="success")])
    elif kind == "animated":
        rows.append([btn(t(lang, "cv_btn_gif"), "conv:do:gif", style="primary"),
                     btn(t(lang, "cv_btn_png"), "conv:do:png")])
        rows.append([btn(t(lang, "cv_btn_all_frames"), "conv:do:frames")])
    else:
        rows.append([btn(t(lang, "cv_btn_gif"), "conv:do:gif", style="primary"),
                     btn(t(lang, "cv_btn_png"), "conv:do:png")])
        rows.append([btn(t(lang, "cv_btn_all_frames"), "conv:do:frames"),
                     btn(t(lang, "cv_btn_source_video"), "conv:do:mp4")])
    rows.append([btn(t(lang, "btn_cancel"), "cancel", style="danger")])
    return markup(rows)


def pagination_kb(lang: str, prefix: str, page: int, pages: int,
                  back: Optional[str] = None) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    if pages > 1:
        row: list[InlineKeyboardButton] = []
        if page > 0:
            row.append(btn("⬅️", f"{prefix}:page:{page - 1}"))
        row.append(btn(t(lang, "mp_page", page=page + 1, pages=pages), f"{prefix}:page:{page}"))
        if page < pages - 1:
            row.append(btn("➡️", f"{prefix}:page:{page + 1}"))
        rows.append(row)
    if back:
        rows.append([btn(t(lang, "btn_back"), back)])
    rows.append([btn(t(lang, "btn_home"), "home")])
    return markup(rows)


def settings_kb(lang: str, language_name: str) -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "st_lang", language=language_name), "settings:lang", style="primary")],
        [btn(t(lang, "st_clear_files"), "settings:clear", style="danger")],
        [btn(t(lang, "btn_back"), "home")],
    ])


def settings_lang_kb() -> InlineKeyboardMarkup:
    return markup([
        [btn(t("ru", "btn_ru"), "lang:ru", style="primary")],
        [btn(t("en", "btn_en"), "lang:en")],
        [btn(t("ru", "btn_back"), "settings:main")],
    ])


def confirm_kb(lang: str, prefix: str, yes_style: str = "danger") -> InlineKeyboardMarkup:
    return markup([
        [btn(t(lang, "btn_yes"), f"{prefix}:yes", style=yes_style)],
        [btn(t(lang, "btn_no"), f"{prefix}:no", style="primary")],
    ])


# =====================================================================
# 13. FSM-СОСТОЯНИЯ
# =====================================================================

class MosaicStates(StatesGroup):
    photo = State()
    manual = State()
    preview = State()


class EmojiPackStates(StatesGroup):
    files = State()
    emoji = State()
    title = State()
    short = State()
    preview = State()


class StickerStates(StatesGroup):
    files = State()
    emoji = State()
    title = State()
    short = State()
    preview = State()


class ConvertStates(StatesGroup):
    waiting = State()
    options = State()


# =====================================================================
# 14. ПОМОЩНИКИ ОТПРАВКИ
# =====================================================================

async def get_lang(user_id: int) -> str:
    cached = RT.lang_cache.get(user_id)
    if cached:
        return cached
    assert RT.db is not None
    user = await RT.db.get_user(user_id)
    lang = (user or {}).get("language") or "ru"
    RT.lang_cache[user_id] = lang
    return lang


async def safe_edit_text(message: Message, text: str,
                         reply_markup: Optional[InlineKeyboardMarkup] = None) -> bool:
    try:
        await message.edit_text(text, reply_markup=reply_markup)
        return True
    except TelegramBadRequest as exc:
        if "message is not modified" in str(exc).lower():
            return True
        if "there is no text in the message to edit" in str(exc).lower():
            return False
        LOG.debug("edit_text: %s", exc)
        return False
    except TelegramAPIError as exc:
        LOG.debug("edit_text: %s", exc)
        return False
    except Exception as exc:  # недоступное сообщение (InaccessibleMessage)
        LOG.debug("edit_text: %s", exc)
        return False


async def safe_answer(message: Message, text: str,
                      reply_markup: Optional[InlineKeyboardMarkup] = None) -> Optional[Message]:
    """Отправляет текст в чат сообщения через Bot API."""
    if RT.bot is None:
        return None
    chat_id = getattr(getattr(message, "chat", None), "id", None)
    if chat_id is None:
        return None
    try:
        return await RT.bot.send_message(
            chat_id, text, reply_markup=reply_markup, disable_web_page_preview=True,
        )
    except TelegramAPIError as exc:
        LOG.debug("send_message: %s", exc)
        return None


async def show_text(message: Message, text: str,
                    reply_markup: Optional[InlineKeyboardMarkup] = None) -> Message:
    """Редактирует сообщение, если возможно, иначе отправляет новое."""
    if await safe_edit_text(message, text, reply_markup):
        return message
    try:
        await message.delete()
    except Exception:
        pass
    sent = await safe_answer(message, text, reply_markup)
    return sent or message


async def notify_error(message: Message, lang: str, exc: Exception) -> None:
    if isinstance(exc, BotError):
        text = t(lang, exc.key, **exc.kwargs)
    elif isinstance(exc, TelegramRetryAfter):
        text = t(lang, "err_rate", sec=getattr(exc, "retry_after", 5))
    elif isinstance(exc, TelegramBadRequest):
        LOG.warning("Telegram BadRequest: %s", exc)
        key, kwargs = telegram_error_key(exc)
        text = t(lang, key, **kwargs)
    elif isinstance(exc, TelegramAPIError):
        LOG.error("Telegram API error: %s", exc)
        text = t(lang, "err_telegram")
    else:
        LOG.exception("Необработанная ошибка: %s", exc)
        text = t(lang, "err_generic")
    await safe_answer(message, text)


async def answer_callback(callback: CallbackQuery, text: Optional[str] = None,
                          show_alert: bool = False) -> None:
    try:
        await callback.answer(text=text, show_alert=show_alert)
    except TelegramAPIError:
        pass


def chat_action(chat_id: int, action: str) -> None:
    task = asyncio.create_task(_send_chat_action(chat_id, action))
    RT.tasks.add(task)
    task.add_done_callback(RT.tasks.discard)


async def _send_chat_action(chat_id: int, action: str) -> None:
    if RT.bot is None:
        return
    try:
        await RT.bot.send_chat_action(chat_id, action)
    except TelegramAPIError:
        pass


# =====================================================================
# 15. ОБРАБОТЧИКИ: КОМАНДЫ, ЯЗЫК, НАВИГАЦИЯ
# =====================================================================

router = Router()
router.message.filter(F.from_user.id != 0)  # только личные сообщения пользователей


async def cleanup_state_files(state: FSMContext) -> None:
    data = await state.get_data()
    for raw in data.get("cleanup_paths", []) or []:
        target = Path(str(raw))
        if target.is_dir():
            cleanup_dir(target)
        else:
            cleanup_path(target)


async def register_files(user_id: int, paths: Sequence[Path], kind: str, ttl_hours: float) -> None:
    assert RT.db is not None
    for path in paths:
        if path and path.exists():
            await RT.db.add_file(user_id, path, kind, ttl_hours)


async def update_panel(bot: Bot, state: FSMContext, chat_id: int, text: str,
                       reply_markup: InlineKeyboardMarkup) -> int:
    data = await state.get_data()
    message_id = data.get("panel_id")
    if message_id:
        try:
            await bot.edit_message_text(
                chat_id=chat_id, message_id=int(message_id),
                text=text, reply_markup=reply_markup, disable_web_page_preview=True,
            )
            return int(message_id)
        except TelegramAPIError:
            pass
    sent = await bot.send_message(chat_id, text, reply_markup=reply_markup, disable_web_page_preview=True)
    await state.update_data(panel_id=sent.message_id)
    return sent.message_id


async def show_error(message: Message, lang: str, exc: Exception) -> None:
    if isinstance(exc, BotError):
        text = t(lang, exc.key, **exc.kwargs)
    elif isinstance(exc, TelegramRetryAfter):
        text = t(lang, "err_rate", sec=getattr(exc, "retry_after", 5))
    elif isinstance(exc, TelegramBadRequest):
        key, kwargs = telegram_error_key(exc)
        LOG.warning("Telegram BadRequest: %s", exc)
        text = t(lang, key, **kwargs)
    elif isinstance(exc, TelegramAPIError):
        LOG.error("Telegram API error: %s", exc)
        text = t(lang, "err_telegram")
    else:
        LOG.exception("Необработанная ошибка: %s", exc)
        text = t(lang, "err_generic")
    edited = await safe_edit_text(message, text)
    if not edited:
        await safe_answer(message, text)


@router.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext, bot: Bot) -> None:
    await state.clear()
    user = message.from_user
    if not user:
        return
    assert RT.db is not None
    existing = await RT.db.get_user(user.id)
    if existing:
        lang = existing.get("language") or "ru"
        RT.lang_cache[user.id] = lang
        await message.answer(t(lang, "main_title"), reply_markup=main_menu_kb(lang))
        return
    await RT.db.upsert_user(user.id, user.username, "ru")
    RT.lang_cache[user.id] = "ru"
    await message.answer(t("ru", "welcome_new"), reply_markup=language_kb())


@router.message(Command("menu"))
async def cmd_menu(message: Message, state: FSMContext) -> None:
    await state.clear()
    if not message.from_user:
        return
    lang = await get_lang(message.from_user.id)
    await message.answer(t(lang, "main_title"), reply_markup=main_menu_kb(lang))


@router.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext) -> None:
    await cleanup_state_files(state)
    await state.clear()
    if not message.from_user:
        return
    lang = await get_lang(message.from_user.id)
    await message.answer(t(lang, "cancelled"), reply_markup=main_menu_kb(lang))


@router.message(Command("help"))
async def cmd_help(message: Message) -> None:
    if not message.from_user:
        return
    lang = await get_lang(message.from_user.id)
    await message.answer(
        t(lang, "help_title") + "\n\n" + t(lang, "help_text") + "\n\n" + t(
            lang, "help_limits",
            mosaic=MAX_MOSAIC_ITEMS, emoji=MAX_EMOJI_PACK_ITEMS,
            static=MAX_STATIC_PACK_ITEMS, anim=MAX_ANIMATED_PACK_ITEMS,
            video=MAX_VIDEO_PACK_ITEMS, mb=MAX_DOWNLOAD_MB,
            storage=MAX_USER_STORAGE_MB,
        ),
        reply_markup=main_menu_kb(lang),
        disable_web_page_preview=True,
    )


@router.callback_query(F.data.in_({"lang:ru", "lang:en"}))
async def cb_language(callback: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    from_settings = bool(data.get("from_settings"))
    await state.clear()
    user = callback.from_user
    if not user:
        return
    lang = "ru" if callback.data.endswith(":ru") else "en"
    assert RT.db is not None
    await RT.db.upsert_user(user.id, user.username, lang)
    await RT.db.set_language(user.id, lang)
    RT.lang_cache[user.id] = lang
    await answer_callback(callback, t(lang, "lang_saved" if lang == "ru" else "lang_saved_en"))
    if callback.message:
        if from_settings:
            text = await settings_text(user.id, lang)
            keyboard = settings_kb(lang, "🇷🇺 Русский" if lang == "ru" else "🇬🇧 English")
        else:
            text = t(lang, "main_title")
            keyboard = main_menu_kb(lang)
        await show_text(callback.message, text, keyboard)


@router.callback_query(F.data == "home")
async def cb_home(callback: CallbackQuery, state: FSMContext) -> None:
    await cleanup_state_files(state)
    await state.clear()
    lang = await get_lang(callback.from_user.id)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, t(lang, "main_title"), main_menu_kb(lang))


@router.callback_query(F.data == "cancel")
async def cb_cancel(callback: CallbackQuery, state: FSMContext) -> None:
    await cleanup_state_files(state)
    await state.clear()
    lang = await get_lang(callback.from_user.id)
    await answer_callback(callback, t(lang, "cancelled"))
    if callback.message:
        await show_text(callback.message, t(lang, "cancelled"), main_menu_kb(lang))


# =====================================================================
# 16. МОЗАИКА ИЗ CUSTOM EMOJI
# =====================================================================

async def receive_image(message: Message, bot: Bot, dest_dir: Path,
                        prefix: str, user_id: Optional[int] = None) -> tuple[Path, ImageInfo]:
    if message.photo:
        path = await download_file(bot, message.photo[-1].file_id, dest_dir, prefix, user_id=user_id)
    elif message.document:
        document = message.document
        extension = Path(document.file_name or "").suffix.lower()
        mime = (document.mime_type or "").lower()
        if mime and not mime.startswith("image/") and not (extension in IMAGE_EXT):
            raise BotError("err_bad_format", expected="JPEG, PNG, WebP, GIF, BMP, TIFF")
        if extension and extension not in IMAGE_EXT and not (mime.startswith("image/")):
            raise BotError("err_bad_format", expected="JPEG, PNG, WebP, GIF, BMP, TIFF")
        path = await download_file(bot, document.file_id, dest_dir, prefix, user_id=user_id)
    else:
        raise BotError("err_no_photo")

    real_format = sniff_format(path)
    if real_format not in ("JPEG", "PNG", "WEBP", "GIF", "BMP", "TIFF"):
        cleanup_path(path)
        raise BotError("err_bad_format", expected="JPEG, PNG, WebP, GIF, BMP, TIFF")
    info = inspect_image(path)
    if info.width < 8 or info.height < 8:
        cleanup_path(path)
        raise BotError("err_too_small_image")
    return path, info


@router.callback_query(F.data == "mosaic:start")
async def cb_mosaic_start(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    await state.set_state(MosaicStates.photo)
    await state.update_data(mode="mosaic", cleanup_paths=[])
    await answer_callback(callback)
    if callback.message:
        await show_text(
            callback.message,
            t(lang, "mos_intro", max=MAX_DOWNLOAD_MB),
            nav_kb(lang, back="home", cancel="cancel"),
        )


@router.message(MosaicStates.photo, F.photo)
@router.message(MosaicStates.photo, F.document)
async def mosaic_receive_photo(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    status = await message.answer(t(lang, "mos_downloading"))
    chat_action(message.chat.id, ChatAction.TYPING)
    try:
        target_dir = user_subdir(ORIGINALS_DIR, user.id)
        path, info = await receive_image(message, bot, target_dir, "mosaic", user.id)
        await register_files(user.id, [path], "original", ORIGINAL_TTL_HOURS)
        await state.update_data(src=str(path), width=info.width, height=info.height,
                                fmt=info.format, cleanup_paths=[str(path)])
        grids = suggest_grids(info.width, info.height, MAX_MOSAIC_ITEMS)
        text = t(
            lang, "mos_photo_info",
            w=info.width, h=info.height, ratio=info.ratio, fmt=info.format,
        )
        await state.set_state(MosaicStates.preview)
        try:
            await status.edit_text(text, reply_markup=grid_kb(lang, grids))
        except TelegramAPIError:
            await message.answer(text, reply_markup=grid_kb(lang, grids))
    except Exception as exc:
        await show_error(status, lang, exc)


@router.callback_query(F.data == "mosaic:manual")
async def cb_mosaic_manual(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    await state.set_state(MosaicStates.manual)
    await answer_callback(callback)
    if callback.message:
        try:
            await callback.message.edit_text(
                t(lang, "mos_manual_prompt", max=MAX_MOSAIC_ITEMS),
                reply_markup=nav_kb(lang, back="mosaic:change", cancel="cancel"),
            )
        except TelegramAPIError:
            pass


@router.message(MosaicStates.manual, F.text)
async def mosaic_manual_grid(message: Message, state: FSMContext) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    grid = parse_grid(message.text or "")
    if not grid:
        await message.answer(t(lang, "mos_manual_bad"))
        return
    cols, rows = grid
    if cols * rows > MAX_MOSAIC_ITEMS:
        await message.answer(t(lang, "mos_manual_too_many", total=cols * rows, max=MAX_MOSAIC_ITEMS))
        return
    data = await state.get_data()
    src = data.get("src")
    if not src or not Path(str(src)).exists():
        await message.answer(t(lang, "err_no_photo"))
        return
    await state.update_data(cols=cols, rows=rows)
    await build_mosaic_preview(message, state, lang, Path(str(src)), cols, rows)


@router.callback_query(F.data.startswith("mosaic:grid:"))
async def cb_mosaic_grid(callback: CallbackQuery, state: FSMContext) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4:
        await answer_callback(callback)
        return
    try:
        cols, rows = int(parts[2]), int(parts[3])
    except ValueError:
        await answer_callback(callback)
        return
    lang = await get_lang(callback.from_user.id)
    data = await state.get_data()
    src = data.get("src")
    if not src or not Path(str(src)).exists():
        await answer_callback(callback, t(lang, "err_no_photo"), show_alert=True)
        return
    await answer_callback(callback)
    await state.update_data(cols=cols, rows=rows)
    if callback.message:
        await build_mosaic_preview(callback.message, state, lang, Path(str(src)), cols, rows)


@router.callback_query(F.data == "mosaic:change")
async def cb_mosaic_change(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    data = await state.get_data()
    src = data.get("src")
    if not src or not Path(str(src)).exists():
        await answer_callback(callback, t(lang, "err_no_photo"), show_alert=True)
        return
    info = inspect_image(Path(str(src)))
    grids = suggest_grids(info.width, info.height, MAX_MOSAIC_ITEMS)
    await state.set_state(MosaicStates.preview)
    await answer_callback(callback)
    if callback.message:
        try:
            await callback.message.delete()
        except TelegramAPIError:
            pass
        await callback.message.answer(
            t(lang, "mos_photo_info", w=info.width, h=info.height, ratio=info.ratio, fmt=info.format),
            reply_markup=grid_kb(lang, grids),
        )


async def build_mosaic_preview(message: Message, state: FSMContext, lang: str,
                               src: Path, cols: int, rows: int) -> None:
    user = message.from_user
    if not user:
        return
    chat_action(message.chat.id, ChatAction.UPLOAD_PHOTO)
    status = await message.answer(t(lang, "mos_building_preview"))
    try:
        data = await state.get_data()
        run_id = secrets.token_hex(4)
        fragments_dir = user_subdir(FRAGMENTS_DIR, user.id) / f"mosaic_{run_id}"
        result = await run_blocking(slice_image_sync, src, fragments_dir, cols, rows)
        preview_path = new_file_path(user_subdir(PREVIEWS_DIR, user.id), f"mosaic_{run_id}", ".png")
        await run_blocking(build_mosaic_preview_sync, result["paths"], cols, rows, preview_path)
        await register_files(user.id, result["paths"], "fragment", ORIGINAL_TTL_HOURS)
        await register_files(user.id, [preview_path], "preview", RESULT_TTL_HOURS)

        cleanup_paths = list(data.get("cleanup_paths") or [])
        cleanup_paths.extend([str(fragments_dir), str(preview_path)])
        await state.update_data(
            fragments=[str(p) for p in result["paths"]],
            preview=str(preview_path),
            crop=result["crop"],
            cropped_size=result["cropped_size"],
            cleanup_paths=cleanup_paths,
        )
        await state.set_state(MosaicStates.preview)

        crop_w, crop_h = result["cropped_size"]
        if tuple(result["crop"]) == (0, 0, result["source_size"][0], result["source_size"][1]):
            crop_line = t(lang, "mos_crop_none")
        else:
            crop_line = t(lang, "mos_crop_line", w=crop_w, h=crop_h)
        caption = t(
            lang, "mos_preview_caption",
            cols=cols, rows=rows, total=cols * rows, crop=crop_line,
        )
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        await message.answer_photo(
            FSInputFile(preview_path),
            caption=caption,
            reply_markup=mosaic_preview_kb(lang, cols, rows),
        )
    except Exception as exc:
        await show_error(status, lang, exc)


@router.callback_query(F.data.startswith("mosaic:create:"))
async def cb_mosaic_create(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4:
        await answer_callback(callback)
        return
    try:
        cols, rows = int(parts[2]), int(parts[3])
    except ValueError:
        await answer_callback(callback)
        return
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    fragments = [Path(str(p)) for p in (data.get("fragments") or [])]
    if not fragments:
        await answer_callback(callback, t(lang, "err_no_photo"), show_alert=True)
        return
    await answer_callback(callback)
    if not callback.message:
        return
    await create_mosaic_pack(callback.message, state, bot, user, lang, cols, rows, fragments)


async def create_mosaic_pack(message: Message, state: FSMContext, bot: Bot,
                             user: Any, lang: str, cols: int, rows: int,
                             fragments: Sequence[Path]) -> None:
    total = cols * rows
    status = await message.answer(t(lang, "mos_creating", done=0, total=total))
    progress = ProgressReporter(status, lang, total, "mos_creating")
    history_id = 0
    name = ""
    created = False
    assert RT.db is not None
    try:
        async with heavy_job(user.id):
            history_id = await RT.db.add_history(user.id, "mosaic", f"{cols}×{rows}", "processing")

            stickers: list[InputSticker] = []
            for index, fragment in enumerate(fragments):
                emoji = MOSAIC_EMOJI_PALETTE[index % len(MOSAIC_EMOJI_PALETTE)]
                stickers.append(InputSticker(
                    sticker=FSInputFile(fragment),
                    emoji_list=[emoji],
                    format="static",
                ))

            suffix = f"_by_{RT.bot_username}"
            base_name = f"mosaic_{cols}x{rows}_{secrets.token_hex(3)}"
            name = base_name[:max(1, MAX_PACK_NAME - len(suffix))] + suffix
            title = f"Mosaic {cols}x{rows}"
            await create_pack(bot, user.id, name, title, stickers, "custom_emoji", progress)
            created = True
            await progress.update(total, force=True)

            emoji_ids: list[str] = []
            try:
                pack_stickers = await fetch_pack_stickers(bot, name)
                emoji_ids = [sticker.custom_emoji_id for sticker in pack_stickers if sticker.custom_emoji_id]
            except Exception as exc:
                LOG.warning("Не удалось получить набор после создания: %s", exc)

            link = PACK_LINK_PREFIX + name
            pack_files = [str(path) for path in fragments]
            preview_value = (await state.get_data()).get("preview")
            if preview_value:
                pack_files.append(str(preview_value))
            await RT.db.add_mosaic(user.id, cols, rows, total, name, link, title, pack_files)
            await RT.db.set_history_status(history_id, "done", link)

            try:
                await status.delete()
            except TelegramAPIError:
                pass
            try:
                await message.edit_reply_markup(reply_markup=None)
            except TelegramAPIError:
                pass

            preview = (await state.get_data()).get("preview")
            caption = t(lang, "mos_done", cols=cols, rows=rows, total=total, link=link)
            keyboard = markup([
                [btn(t(lang, "btn_link"), url=link, style="primary")],
                [btn(t(lang, "btn_my_packs"), "packs:list")],
                [btn(t(lang, "btn_home"), "home")],
            ])
            if preview and Path(str(preview)).exists():
                await message.answer_photo(FSInputFile(str(preview)), caption=caption, reply_markup=keyboard)
            else:
                await message.answer(caption, reply_markup=keyboard, disable_web_page_preview=True)

            if emoji_ids:
                sent = await send_mosaic_emoji(bot, message.chat.id, emoji_ids, cols, rows, lang)
                if not sent:
                    await message.answer(t(lang, "mos_emoji_blocked"))
            else:
                await message.answer(t(lang, "mos_emoji_blocked"))

            await state.clear()
    except Exception as exc:
        if history_id:
            await RT.db.set_history_status(history_id, "error", str(exc)[:300])
        if not created and name:
            # Не оставляем недоделанный набор в Telegram.
            try:
                await bot.delete_sticker_set(name)
            except Exception:
                pass
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        await notify_error(message, lang, exc)


# =====================================================================
# 17. СОЗДАНИЕ CUSTOM EMOJI PACK
# =====================================================================

async def open_panel(message: Message, state: FSMContext, text: str,
                     reply_markup: InlineKeyboardMarkup) -> Message:
    try:
        await message.delete()
    except TelegramAPIError:
        pass
    sent = await message.answer(text, reply_markup=reply_markup, disable_web_page_preview=True)
    await state.update_data(panel_id=sent.message_id)
    return sent


@router.callback_query(F.data == "emoji:start")
async def cb_emoji_start(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    await state.set_state(EmojiPackStates.files)
    await state.update_data(items=[], cleanup_paths=[])
    await answer_callback(callback)
    if callback.message:
        await open_panel(
            callback.message, state,
            t(lang, "ep_intro", max=MAX_EMOJI_PACK_ITEMS),
            items_kb(lang, [], "ep", t(lang, "btn_done")),
        )


def emoji_panel_text(lang: str, items: Sequence[dict[str, Any]]) -> str:
    return t(lang, "ep_count", n=len(items)) + "\n" + t(lang, "ep_add_more_hint")


@router.message(EmojiPackStates.files, F.photo)
@router.message(EmojiPackStates.files, F.document)
async def emoji_receive_image(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    if len(items) >= MAX_EMOJI_PACK_ITEMS:
        await message.answer(t(lang, "err_too_many_items", max=MAX_EMOJI_PACK_ITEMS))
        return
    status = await message.answer(t(lang, "status_working"))
    try:
        src, _info = await receive_image(message, bot, user_subdir(ORIGINALS_DIR, user.id), "emoji_src", user.id)
        target = new_file_path(user_subdir(STICKERS_DIR, user.id), f"emoji_{len(items):03d}", ".webp")
        prepared = await run_blocking(prepare_custom_emoji_sync, src, target)
        await register_files(user.id, [src], "original", ORIGINAL_TTL_HOURS)
        await register_files(user.id, [prepared], "sticker", RESULT_TTL_HOURS)
        items.append({"path": str(prepared), "emoji": "😀", "src": str(src), "kind": "static"})
        cleanup_paths = list(data.get("cleanup_paths") or [])
        cleanup_paths.extend([str(src), str(prepared)])
        await state.update_data(items=items, cleanup_paths=cleanup_paths)
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        await update_panel(
            bot, state, message.chat.id,
            emoji_panel_text(lang, items),
            items_kb(lang, items, "ep", t(lang, "btn_done")),
        )
    except Exception as exc:
        await show_error(status, lang, exc)


async def mutate_items(callback: CallbackQuery, state: FSMContext, bot: Bot,
                       prefix: str, action: str, index: int) -> None:
    lang = await get_lang(callback.from_user.id)
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    if index < 0 or index >= len(items):
        await answer_callback(callback, t(lang, "err_not_found"), show_alert=True)
        return

    if action == "delete":
        removed = items.pop(index)
        cleanup_paths = list(data.get("cleanup_paths") or [])
        for key in ("path", "src", "preview"):
            value = removed.get(key)
            if value:
                cleanup_paths.append(str(value))
        await state.update_data(items=items, cleanup_paths=cleanup_paths)
        await answer_callback(callback)
    elif action == "up":
        if index > 0:
            items[index - 1], items[index] = items[index], items[index - 1]
            await state.update_data(items=items)
        await answer_callback(callback)
    elif action == "down":
        if index < len(items) - 1:
            items[index + 1], items[index] = items[index], items[index + 1]
            await state.update_data(items=items)
        await answer_callback(callback)
    elif action == "emoji":
        await state.set_state(EmojiPackStates.emoji if prefix == "ep" else StickerStates.emoji)
        await state.update_data(pending_index=index)
        await answer_callback(callback)
        if callback.message:
            try:
                await callback.message.answer(
                    t(lang, "ep_emoji_prompt" if prefix == "ep" else "sp_emoji_prompt", i=index + 1)
                )
            except TelegramAPIError:
                pass
        return

    done_label = t(lang, "btn_done")
    text = emoji_panel_text(lang, items) if prefix == "ep" else (
        t(lang, "sp_count", n=len(items)) + "\n" + t(lang, "ep_add_more_hint")
    )
    await update_panel(
        bot, state, callback.message.chat.id if callback.message else 0,
        text, items_kb(lang, items, prefix, done_label),
    )


@router.callback_query(F.data.startswith("ep:"))
async def cb_emoji_actions(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    parts = callback.data.split(":")
    if len(parts) < 2:
        await answer_callback(callback)
        return
    action = parts[1]
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    message = callback.message

    if action == "cancel":
        await cleanup_state_files(state)
        await state.clear()
        await answer_callback(callback, t(lang, "cancelled"))
        if message:
            await show_text(message, t(lang, "main_title"), main_menu_kb(lang))
        return

    if action == "done":
        if not items:
            await answer_callback(callback, t(lang, "err_no_items"), show_alert=True)
            return
        await state.set_state(EmojiPackStates.title)
        await answer_callback(callback)
        if message:
            await update_panel(bot, state, message.chat.id, t(lang, "ep_title_prompt"),
                               nav_kb(lang, back="ep:back", cancel="ep:cancel"))
        return

    if action == "back":
        await state.set_state(EmojiPackStates.files)
        await answer_callback(callback)
        if message:
            await update_panel(bot, state, message.chat.id, emoji_panel_text(lang, items),
                               items_kb(lang, items, "ep", t(lang, "btn_done")))
        return

    if action == "title_back":
        await state.set_state(EmojiPackStates.title)
        await answer_callback(callback)
        if message:
            await update_panel(bot, state, message.chat.id, t(lang, "ep_title_prompt"),
                               nav_kb(lang, back="ep:back", cancel="ep:cancel"))
        return

    if action == "confirm":
        await answer_callback(callback)
        if message:
            await create_user_pack(message, state, bot, user, lang, "ep")
        return

    if len(parts) >= 3 and parts[2].isdigit():
        await mutate_items(callback, state, bot, "ep", action, int(parts[2]))
        return
    await answer_callback(callback)


@router.message(EmojiPackStates.emoji, F.text)
async def emoji_set_emoji(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    emojis = parse_emoji_list(message.text or "")
    if not emojis:
        await message.answer(t(lang, "ep_emoji_bad"))
        return
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    index = int(data.get("pending_index", -1))
    if 0 <= index < len(items):
        items[index]["emoji"] = emojis[0]
        await state.update_data(items=items)
        await message.answer(t(lang, "ep_emoji_saved", i=index + 1, emoji=emojis[0]))
    await state.set_state(EmojiPackStates.files)
    try:
        await update_panel(
            bot, state, message.chat.id,
            emoji_panel_text(lang, items),
            items_kb(lang, items, "ep", t(lang, "btn_done")),
        )
    except TelegramAPIError:
        pass


@router.message(EmojiPackStates.title, F.text)
async def emoji_set_title(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    title = normalize_title(message.text or "")
    if not title:
        await message.answer(t(lang, "ep_title_bad"))
        return
    await state.update_data(title=title)
    await state.set_state(EmojiPackStates.short)
    await update_panel(
        bot, state, message.chat.id,
        t(lang, "ep_short_prompt", bot=RT.bot_username),
        nav_kb(lang, back="ep:title_back", cancel="ep:cancel"),
    )


@router.message(EmojiPackStates.short, F.text)
async def emoji_set_short(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    raw = (message.text or "").strip()
    suffix = f"_by_{RT.bot_username.lower()}"
    if raw.lower().endswith(suffix):
        raw = raw[: -len(suffix)]
    name = sanitize_short_name(raw, RT.bot_username)
    if not name:
        await message.answer(t(lang, "ep_short_bad"))
        return
    await state.update_data(name=name)
    await build_pack_preview(message, state, bot, user, lang, "ep")


# =====================================================================
# 18. STICKER MAKER
# =====================================================================

@router.callback_query(F.data == "stickers:start")
async def cb_stickers_start(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    await state.clear()
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, t(lang, "sp_intro"), pack_type_kb(lang))


@router.callback_query(F.data.startswith("stickers:type:"))
async def cb_stickers_type(callback: CallbackQuery, state: FSMContext) -> None:
    mode = callback.data.split(":")[2]
    if mode not in ("static", "animated", "video"):
        await answer_callback(callback)
        return
    lang = await get_lang(callback.from_user.id)
    await state.set_state(StickerStates.files)
    await state.update_data(mode=mode, items=[], cleanup_paths=[])
    await answer_callback(callback)
    text = {
        "static": t(lang, "sp_add_static", max=MAX_STATIC_PACK_ITEMS),
        "animated": t(lang, "sp_add_animated", max=MAX_ANIMATED_PACK_ITEMS),
        "video": t(lang, "sp_add_video", max=MAX_VIDEO_PACK_ITEMS),
    }[mode]
    if callback.message:
        await open_panel(callback.message, state, text, items_kb(lang, [], "sp", t(lang, "btn_done")))


def pack_limit(mode: str) -> int:
    return {
        "static": MAX_STATIC_PACK_ITEMS,
        "animated": MAX_ANIMATED_PACK_ITEMS,
        "video": MAX_VIDEO_PACK_ITEMS,
    }.get(mode, MAX_STATIC_PACK_ITEMS)


def validate_tgs_sync(path: Path) -> dict[str, Any]:
    if path.stat().st_size > TGS_MAX_BYTES:
        raise BotError("err_too_big", max=64)
    try:
        with gzip.open(path, "rb") as handle:
            data = json.load(handle)
    except Exception as exc:
        raise BotError("err_bad_file") from exc
    if not isinstance(data, dict) or "layers" not in data:
        raise BotError("err_bad_file")
    width = int(data.get("w", 0) or 0)
    height = int(data.get("h", 0) or 0)
    if width != STICKER_SIZE or height != STICKER_SIZE:
        raise BotError("err_bad_format", expected="TGS 512 × 512")
    return {"width": width, "height": height, "frames": int(data.get("op", 0) or 0)}


def validate_webm_sync(path: Path) -> dict[str, Any]:
    if path.stat().st_size > WEBM_MAX_BYTES:
        raise BotError("err_too_big", max=256)
    info = probe_video_sync(path)
    if info["duration"] > WEBM_MAX_SECONDS + 0.1:
        raise BotError("err_bad_format", expected="WebM ≤ 3 сек")
    return info


async def add_sticker_item(message: Message, state: FSMContext, bot: Bot,
                           mode: str, items: list[dict[str, Any]], lang: str) -> dict[str, Any]:
    user = message.from_user
    assert user
    target_dir = user_subdir(STICKERS_DIR, user.id)
    index = len(items)

    if mode == "static":
        src, _info = await receive_image(message, bot, user_subdir(ORIGINALS_DIR, user.id), "sticker_src", user.id)
        target = new_file_path(target_dir, f"sticker_{index:03d}", ".webp")
        prepared = await run_blocking(prepare_static_sticker_sync, src, target)
        await register_files(user.id, [src], "original", ORIGINAL_TTL_HOURS)
        await register_files(user.id, [prepared], "sticker", RESULT_TTL_HOURS)
        return {"path": str(prepared), "emoji": "😀", "src": str(src), "kind": "static"}

    if mode == "animated":
        if not message.document:
            raise BotError("sp_not_tgs")
        document = message.document
        extension = Path(document.file_name or "").suffix.lower()
        mime = (document.mime_type or "").lower()
        if extension != ".tgs" and not (mime in ("application/x-tgsticker", "application/gzip", "application/octet-stream")):
            raise BotError("sp_not_tgs")
        path = await download_file(bot, document.file_id, target_dir, "sticker_tgs", user_id=user.id)
        if sniff_format(path) != "TGS":
            cleanup_path(path)
            raise BotError("sp_not_tgs")
        await run_blocking(validate_tgs_sync, path)
        await register_files(user.id, [path], "sticker", RESULT_TTL_HOURS)
        return {"path": str(path), "emoji": "😀", "kind": "animated"}

    # video
    if message.document:
        document = message.document
        extension = Path(document.file_name or "").suffix.lower()
        mime = (document.mime_type or "").lower()
        if extension == ".webm" or mime == "video/webm":
            path = await download_file(bot, document.file_id, target_dir, "sticker_webm", user_id=user.id)
            if sniff_format(path) != "WEBM":
                cleanup_path(path)
                raise BotError("sp_not_video")
            info = await run_blocking(probe_video_sync, path)
            needs_encode = (
                path.stat().st_size > WEBM_MAX_BYTES
                or info.get("duration", 0) > WEBM_MAX_SECONDS + 0.1
                or info.get("codec") not in ("", "vp9", "vp09")
                or info.get("width") not in (0, STICKER_SIZE)
                or info.get("height") not in (0, STICKER_SIZE)
            )
            if needs_encode:
                target = new_file_path(target_dir, f"sticker_{index:03d}", ".webm")
                encoded = await run_blocking(video_to_webm_sticker_sync, path, target)
                cleanup_path(path)
                path = encoded
            await run_blocking(validate_webm_sync, path)
            await register_files(user.id, [path], "sticker", RESULT_TTL_HOURS)
            return {"path": str(path), "emoji": "😀", "kind": "video"}
        if extension in VIDEO_EXT or mime.startswith("video/"):
            src = await download_file(bot, document.file_id, user_subdir(TEMPORARY_DIR, user.id), "video_src", user_id=user.id)
        else:
            raise BotError("sp_not_video")
    elif message.video or message.animation:
        source = message.video or message.animation
        src = await download_file(bot, source.file_id, user_subdir(TEMPORARY_DIR, user.id), "video_src", user_id=user.id)
    else:
        raise BotError("sp_not_video")

    status = await message.answer(t(lang, "sp_converting_video"))
    try:
        target = new_file_path(target_dir, f"sticker_{index:03d}", ".webm")
        prepared = await run_blocking(video_to_webm_sticker_sync, src, target)
        await run_blocking(validate_webm_sync, prepared)
        await register_files(user.id, [prepared], "sticker", RESULT_TTL_HOURS)
        return {"path": str(prepared), "emoji": "😀", "src": str(src), "kind": "video"}
    finally:
        cleanup_path(src)
        try:
            await status.delete()
        except TelegramAPIError:
            pass


@router.message(StickerStates.files, F.photo)
@router.message(StickerStates.files, F.document)
@router.message(StickerStates.files, F.video)
@router.message(StickerStates.files, F.animation)
async def sticker_receive(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    mode = str(data.get("mode") or "static")
    items: list[dict[str, Any]] = list(data.get("items") or [])
    if len(items) >= pack_limit(mode):
        await message.answer(t(lang, "err_too_many_items", max=pack_limit(mode)))
        return
    status = await message.answer(t(lang, "status_working"))
    try:
        item = await add_sticker_item(message, state, bot, mode, items, lang)
        items.append(item)
        cleanup_paths = list(data.get("cleanup_paths") or [])
        for key in ("path", "src"):
            if item.get(key):
                cleanup_paths.append(str(item[key]))
        await state.update_data(items=items, cleanup_paths=cleanup_paths)
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        text = t(lang, "sp_count", n=len(items)) + "\n" + t(lang, "ep_add_more_hint")
        await update_panel(
            bot, state, message.chat.id, text,
            items_kb(lang, items, "sp", t(lang, "btn_done")),
        )
    except Exception as exc:
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        await notify_error(message, lang, exc)


@router.callback_query(F.data.startswith("sp:"))
async def cb_sticker_actions(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    parts = callback.data.split(":")
    if len(parts) < 2:
        await answer_callback(callback)
        return
    action = parts[1]
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    message = callback.message

    if action == "cancel":
        await cleanup_state_files(state)
        await state.clear()
        await answer_callback(callback, t(lang, "cancelled"))
        if message:
            await show_text(message, t(lang, "main_title"), main_menu_kb(lang))
        return

    if action == "done":
        if not items:
            await answer_callback(callback, t(lang, "err_no_items"), show_alert=True)
            return
        await state.set_state(StickerStates.title)
        await answer_callback(callback)
        if message:
            await update_panel(bot, state, message.chat.id, t(lang, "sp_title_prompt"),
                               nav_kb(lang, back="sp:back", cancel="sp:cancel"))
        return

    if action == "back":
        await state.set_state(StickerStates.files)
        await answer_callback(callback)
        if message:
            await update_panel(
                bot, state, message.chat.id,
                t(lang, "sp_count", n=len(items)) + "\n" + t(lang, "ep_add_more_hint"),
                items_kb(lang, items, "sp", t(lang, "btn_done")),
            )
        return

    if action == "title_back":
        await state.set_state(StickerStates.title)
        await answer_callback(callback)
        if message:
            await update_panel(bot, state, message.chat.id, t(lang, "sp_title_prompt"),
                               nav_kb(lang, back="sp:back", cancel="sp:cancel"))
        return

    if action == "confirm":
        await answer_callback(callback)
        if message:
            await create_user_pack(message, state, bot, user, lang, "sp")
        return

    if len(parts) >= 3 and parts[2].isdigit():
        await mutate_items(callback, state, bot, "sp", action, int(parts[2]))
        return
    await answer_callback(callback)


@router.message(StickerStates.emoji, F.text)
async def sticker_set_emoji(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    emojis = parse_emoji_list(message.text or "")
    if not emojis:
        await message.answer(t(lang, "ep_emoji_bad"))
        return
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    index = int(data.get("pending_index", -1))
    if 0 <= index < len(items):
        items[index]["emoji"] = " ".join(emojis)
        await state.update_data(items=items)
        await message.answer(t(lang, "sp_emoji_saved", i=index + 1, emoji=" ".join(emojis)))
    await state.set_state(StickerStates.files)
    try:
        await update_panel(
            bot, state, message.chat.id,
            t(lang, "sp_count", n=len(items)) + "\n" + t(lang, "ep_add_more_hint"),
            items_kb(lang, items, "sp", t(lang, "btn_done")),
        )
    except TelegramAPIError:
        pass


@router.message(StickerStates.title, F.text)
async def sticker_set_title(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    title = normalize_title(message.text or "")
    if not title:
        await message.answer(t(lang, "sp_title_bad"))
        return
    await state.update_data(title=title)
    await state.set_state(StickerStates.short)
    await update_panel(
        bot, state, message.chat.id,
        t(lang, "sp_short_prompt", bot=RT.bot_username),
        nav_kb(lang, back="sp:title_back", cancel="sp:cancel"),
    )


@router.message(StickerStates.short, F.text)
async def sticker_set_short(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    raw = (message.text or "").strip()
    suffix = f"_by_{RT.bot_username.lower()}"
    if raw.lower().endswith(suffix):
        raw = raw[: -len(suffix)]
    name = sanitize_short_name(raw, RT.bot_username)
    if not name:
        await message.answer(t(lang, "sp_short_bad"))
        return
    await state.update_data(name=name)
    await build_pack_preview(message, state, bot, user, lang, "sp")


# =====================================================================
# 19. ПРЕДПРОСМОТР И СОЗДАНИЕ ПОЛЬЗОВАТЕЛЬСКИХ НАБОРОВ
# =====================================================================

async def ensure_item_preview(item: dict[str, Any], user_id: int) -> Optional[Path]:
    """Гарантирует наличие PNG-превью для элемента набора."""
    existing = item.get("preview")
    if existing and Path(str(existing)).exists():
        return Path(str(existing))
    kind = item.get("kind")
    source = Path(str(item.get("path") or ""))
    if not source.exists():
        return None
    preview_dir = user_subdir(PREVIEWS_DIR, user_id)
    try:
        if kind == "animated":
            frames = await asyncio.wait_for(render_tgs_frames(source), timeout=25)
            frames, _ = limit_frames(frames, 1)
            target = new_file_path(preview_dir, "tgs_preview", ".png")
            await run_blocking(frames[0].save, target)
        elif kind == "video":
            target = new_file_path(preview_dir, "webm_preview", ".png")
            await run_blocking(webm_first_frame_sync, source, target)
        else:
            return source
        item["preview"] = str(target)
        if RT.db:
            await RT.db.add_file(user_id, target, "preview", RESULT_TTL_HOURS)
        return target
    except Exception as exc:
        LOG.debug("Не удалось построить превью для %s: %s", source.name, exc)
        badge = new_file_path(preview_dir, "badge", ".png")
        badge_image = draw_text_badge("TGS" if kind == "animated" else "VIDEO")
        await run_blocking(badge_image.save, badge)
        item["preview"] = str(badge)
        return badge


async def build_pack_preview(message: Message, state: FSMContext, bot: Bot,
                             user: Any, lang: str, prefix: str) -> None:
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    mode = str(data.get("mode") or "static")
    title = str(data.get("title") or "")
    name = str(data.get("name") or "")
    is_emoji = prefix == "ep"
    status = await message.answer(t(lang, "status_working"))
    panel_id = data.get("panel_id")
    if panel_id:
        try:
            await bot.delete_message(message.chat.id, int(panel_id))
        except TelegramAPIError:
            pass
    try:
        preview_paths: list[Path] = []
        for item in items[:30]:
            preview = await ensure_item_preview(item, user.id)
            if preview:
                preview_paths.append(preview)
        await state.update_data(items=items)
        sheet = new_file_path(user_subdir(PREVIEWS_DIR, user.id), f"pack_{secrets.token_hex(3)}", ".png")
        await run_blocking(build_contact_sheet_sync, preview_paths, sheet, 5, 150)
        await register_files(user.id, [sheet], "preview", RESULT_TTL_HOURS)

        cleanup_paths = list(data.get("cleanup_paths") or [])
        cleanup_paths.append(str(sheet))
        await state.update_data(cleanup_paths=cleanup_paths, preview=str(sheet))
        await state.set_state(EmojiPackStates.preview if is_emoji else StickerStates.preview)

        if is_emoji:
            type_name = "Custom Emoji"
            caption = t(lang, "ep_preview_caption", title=esc(title), short=esc(name), n=len(items))
        else:
            type_name = {
                "static": t(lang, "sp_type_static_short"),
                "animated": t(lang, "sp_type_animated_short"),
                "video": t(lang, "sp_type_video_short"),
            }[mode]
            caption = t(lang, "sp_preview_caption", title=esc(title), short=esc(name),
                        type=type_name, n=len(items))
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        await message.answer_photo(
            FSInputFile(sheet), caption=caption,
            reply_markup=confirm_pack_kb(lang, prefix),
        )
    except Exception as exc:
        await show_error(status, lang, exc)


async def create_user_pack(message: Message, state: FSMContext, bot: Bot,
                           user: Any, lang: str, prefix: str) -> None:
    data = await state.get_data()
    items: list[dict[str, Any]] = list(data.get("items") or [])
    mode = str(data.get("mode") or "static")
    title = str(data.get("title") or "Pack")
    name = str(data.get("name") or "")
    is_emoji = prefix == "ep"
    if not items or not name:
        await notify_error(message, lang, BotError("err_no_items"))
        return

    total = len(items)
    status = await message.answer(
        t(lang, "ep_creating" if is_emoji else "sp_creating", done=0, total=total)
    )
    progress = ProgressReporter(status, lang, total, "ep_creating" if is_emoji else "sp_creating")
    history_id = 0
    created = False
    assert RT.db is not None
    try:
        async with heavy_job(user.id):
            op_type = "emoji_pack" if is_emoji else "sticker_pack"
            history_id = await RT.db.add_history(user.id, op_type, title, "processing")

            stickers: list[InputSticker] = []
            for item in items:
                kind = str(item.get("kind") or "static")
                sticker_format = "static" if kind == "static" else ("animated" if kind == "animated" else "video")
                emoji_list = parse_emoji_list(str(item.get("emoji") or "😀"), 20) or ["😀"]
                stickers.append(InputSticker(
                    sticker=FSInputFile(Path(str(item["path"]))),
                    emoji_list=emoji_list,
                    format=sticker_format,
                ))

            await create_pack(
                bot, user.id, name, title, stickers,
                "custom_emoji" if is_emoji else "regular", progress,
            )
            created = True
            await progress.update(total, force=True)

            link = PACK_LINK_PREFIX + name
            pack_type = "custom_emoji" if is_emoji else mode
            pack_files = [str(item.get("path")) for item in items if item.get("path")]
            if data.get("preview"):
                pack_files.append(str(data.get("preview")))
            await RT.db.add_sticker_pack(user.id, name, pack_type, link, title, total, pack_files)
            await RT.db.set_history_status(history_id, "done", link)

            try:
                await status.delete()
            except TelegramAPIError:
                pass
            try:
                await message.edit_reply_markup(reply_markup=None)
            except TelegramAPIError:
                pass

            if is_emoji:
                caption = t(lang, "ep_done", title=esc(title), n=total, link=link)
            else:
                caption = t(lang, "sp_done", title=esc(title), n=total, link=link)
            keyboard = markup([
                [btn(t(lang, "btn_link"), url=link, style="primary")],
                [btn(t(lang, "btn_my_packs"), "packs:list")],
                [btn(t(lang, "btn_home"), "home")],
            ])
            preview = str(data.get("preview") or "")
            if preview and Path(preview).exists():
                await message.answer_photo(FSInputFile(preview), caption=caption, reply_markup=keyboard)
            else:
                await message.answer(caption, reply_markup=keyboard, disable_web_page_preview=True)

            await state.clear()
    except Exception as exc:
        if history_id:
            await RT.db.set_history_status(history_id, "error", str(exc)[:300])
        if not created:
            # Не оставляем недоделанный набор в Telegram.
            try:
                await bot.delete_sticker_set(name)
            except Exception:
                pass
        try:
            await status.delete()
        except TelegramAPIError:
            pass
        await notify_error(message, lang, exc)


# =====================================================================
# 20. КОНВЕРТЕР СТИКЕРОВ
# =====================================================================

@router.callback_query(F.data.in_({"conv:png", "conv:gif"}))
async def cb_conv_start(callback: CallbackQuery, state: FSMContext) -> None:
    mode = callback.data.split(":")[1]
    lang = await get_lang(callback.from_user.id)
    await state.set_state(ConvertStates.waiting)
    await state.update_data(mode=mode, cleanup_paths=[])
    await answer_callback(callback)
    if callback.message:
        text = t(lang, "cv_png_intro" if mode == "png" else "cv_gif_intro")
        await show_text(callback.message, text, nav_kb(lang, back="home", cancel="cancel"))


@router.message(ConvertStates.waiting, F.sticker)
async def conv_receive_sticker(message: Message, state: FSMContext, bot: Bot) -> None:
    user = message.from_user
    if not user or not message.sticker:
        return
    lang = await get_lang(user.id)
    sticker = message.sticker
    kind = "animated" if sticker.is_animated else ("video" if sticker.is_video else "static")
    status = await message.answer(t(lang, "cv_processing"))
    try:
        temp_dir = user_subdir(TEMPORARY_DIR, user.id)
        path = await download_file(bot, sticker.file_id, temp_dir, "conv", user_id=user.id)
        real = sniff_format(path)
        if real == "TGS":
            kind = "animated"
        elif real == "WEBM":
            kind = "video"
        elif real in ("WEBP", "PNG", "GIF"):
            kind = "static"
        await register_files(user.id, [path], "temporary", TEMP_TTL_HOURS)
        await state.update_data(src=str(path), kind=kind, cleanup_paths=[str(path)])
        await state.set_state(ConvertStates.options)

        if kind == "static":
            text = t(lang, "cv_static_title")
        elif kind == "animated":
            text = t(lang, "cv_animated_title")
        else:
            text = t(lang, "cv_video_title")
        try:
            await status.edit_text(text, reply_markup=converter_options_kb(lang, kind))
        except TelegramAPIError:
            await message.answer(text, reply_markup=converter_options_kb(lang, kind))
    except Exception as exc:
        await show_error(status, lang, exc)


async def conv_send_document(message: Message, path: Path, caption: str, lang: str,
                             user_id: int,
                             keyboard: Optional[InlineKeyboardMarkup] = None) -> None:
    await message.answer_document(
        FSInputFile(path), caption=caption,
        reply_markup=keyboard or markup([
            [btn(t(lang, "cv_btn_again"), "conv:again", style="primary")],
            [btn(t(lang, "btn_home"), "home")],
        ]),
    )
    assert RT.db is not None
    await RT.db.add_file(user_id, path, "result", RESULT_TTL_HOURS)
    await RT.db.add_conversion(user_id, "sticker", "file", str(path))


@router.callback_query(F.data.startswith("conv:do:"))
async def cb_conv_do(callback: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    action = callback.data.split(":")[2]
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    kind = str(data.get("kind") or "static")
    src_raw = data.get("src")
    if not src_raw or not Path(str(src_raw)).exists():
        await answer_callback(callback, t(lang, "err_no_sticker"), show_alert=True)
        return
    src = Path(str(src_raw))
    await answer_callback(callback)

    if action == "gif" and kind != "static":
        await state.set_state(ConvertStates.options)
        if callback.message:
            try:
                await callback.message.edit_text(
                    t(lang, "cv_quality_title"), reply_markup=quality_kb(lang, "conv"),
                )
            except TelegramAPIError:
                await callback.message.answer(
                    t(lang, "cv_quality_title"), reply_markup=quality_kb(lang, "conv"),
                )
        return

    if action == "options":
        await state.set_state(ConvertStates.options)
        if callback.message:
            text = t(lang, "cv_animated_title" if kind == "animated" else "cv_video_title")
            try:
                await callback.message.edit_text(text, reply_markup=converter_options_kb(lang, kind))
            except TelegramAPIError:
                await callback.message.answer(text, reply_markup=converter_options_kb(lang, kind))
        return

    if action == "again":
        await state.set_state(ConvertStates.waiting)
        if callback.message:
            await callback.message.answer(
                t(lang, "cv_gif_intro" if data.get("mode") == "gif" else "cv_png_intro"),
                reply_markup=nav_kb(lang, back="home", cancel="cancel"),
            )
        return

    if action not in ("png", "gif", "frames", "mp4"):
        await answer_callback(callback)
        return

    if action == "gif" and kind == "static":
        status = await callback.message.answer(t(lang, "status_working")) if callback.message else None
        try:
            async with heavy_job(user.id):
                result = await run_conversion(user.id, src, kind, "png", "normal")
                assert status is not None
                await status.delete()
                caption = t(lang, "cv_no_animation") + "\n\n" + t(
                    lang, "cv_png_caption", size=human_size(result.stat().st_size))
                await conv_send_document(callback.message, result, caption, lang, user.id)
        except Exception as exc:
            if status:
                await show_error(status, lang, exc)
            else:
                await notify_error(callback.message, lang, exc)
        return

    status = await callback.message.answer(t(lang, "status_working")) if callback.message else None
    try:
        async with heavy_job(user.id):
            history_id = await RT.db.add_history(user.id, "frames" if action == "frames" else ("png" if action == "png" else "gif"), "sticker", "processing")
            result = await run_conversion(user.id, src, kind, action, "normal")
            assert status is not None
            await status.delete()
            caption = conversion_caption(lang, kind, action, result, "normal")
            await conv_send_document(callback.message, result, caption, lang, user.id)
            await RT.db.set_history_status(history_id, "done", result.name)
            await state.set_state(ConvertStates.waiting)
    except Exception as exc:
        if status:
            await show_error(status, lang, exc)
        else:
            await notify_error(callback.message, lang, exc)


async def run_conversion(user_id: int, src: Path, kind: str, action: str, quality: str) -> Path:
    out_dir = user_subdir(PREVIEWS_DIR, user_id)
    if action == "png":
        if kind == "static":
            target = new_file_path(out_dir, "sticker_png", ".png")
            return await run_blocking(webp_to_png_sync, src, target)
        if kind == "animated":
            frames = await render_tgs_frames(src)
            frames, _ = limit_frames(frames, 1)
            target = new_file_path(out_dir, "tgs_frame", ".png")
            await run_blocking(frames[0].save, target)
            return target
        target = new_file_path(out_dir, "webm_frame", ".png")
        return await run_blocking(webm_first_frame_sync, src, target)

    if action == "gif":
        if kind == "static":
            target = new_file_path(out_dir, "sticker_png", ".png")
            return await run_blocking(webp_to_png_sync, src, target)
        if kind == "animated":
            frames = await render_tgs_frames(src)
            target = new_file_path(out_dir, "tgs_gif", ".gif")
            return await run_blocking(tgs_to_gif_sync, frames, target, quality)
        target = new_file_path(out_dir, "webm_gif", ".gif")
        return await run_blocking(webm_to_gif_sync, src, target, quality)

    if action == "frames":
        frames_dir = user_subdir(TEMPORARY_DIR, user_id) / f"frames_{secrets.token_hex(3)}"
        if kind == "animated":
            rendered = await render_tgs_frames(src, frame_skip=0)
            rendered, limited = limit_frames(rendered, 90)
            paths: list[Path] = []
            for index, frame in enumerate(rendered):
                target = frames_dir / f"frame_{index:04d}.png"
                frames_dir.mkdir(parents=True, exist_ok=True)
                await run_blocking(frame.resize((256, 256), Image.LANCZOS).save, target)
                paths.append(target)
        else:
            paths = await run_blocking(webm_extract_frames_sync, src, frames_dir, 90)
        zip_path = new_file_path(out_dir, "frames", ".zip")
        archive_path = await run_blocking(make_zip_sync, paths, zip_path)
        cleanup_dir(frames_dir)
        return archive_path

    if action == "mp4":
        target = new_file_path(out_dir, "sticker_video", ".mp4")
        return await run_blocking(webm_to_mp4_sync, src, target)

    raise BotError("err_bad_format", expected="png, gif, frames, mp4")


def conversion_caption(lang: str, kind: str, action: str, result: Path,
                       quality: str) -> str:
    size = human_size(result.stat().st_size if result.exists() else 0)
    if action == "png":
        return t(lang, "cv_png_caption", size=size)
    if action == "gif":
        source_name = "TGS" if kind == "animated" else "WebM"
        quality_name = {
            "normal": t(lang, "cv_q_normal"),
            "high": t(lang, "cv_q_high"),
            "small": t(lang, "cv_q_small"),
        }.get(quality, quality)
        return t(lang, "cv_gif_caption", src=source_name, q=quality_name, size=size)
    if action == "frames":
        try:
            with zipfile.ZipFile(result) as archive:
                count = len([n for n in archive.namelist() if n.endswith(".png")])
        except Exception:
            count = 0
        return t(lang, "cv_frames_caption", n=count, size=size)
    return t(lang, "cv_mp4_caption", size=size)


@router.callback_query(F.data.startswith("conv:q:"))
async def cb_conv_quality(callback: CallbackQuery, state: FSMContext) -> None:
    quality = callback.data.split(":")[2]
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    data = await state.get_data()
    kind = str(data.get("kind") or "static")
    src_raw = data.get("src")
    if not src_raw or not Path(str(src_raw)).exists():
        await answer_callback(callback, t(lang, "err_no_sticker"), show_alert=True)
        return
    src = Path(str(src_raw))
    await answer_callback(callback)
    if not callback.message:
        return
    status = await callback.message.answer(t(lang, "status_working"))
    try:
        async with heavy_job(user.id):
            history_id = await RT.db.add_history(user.id, "gif", "sticker", "processing")
            result = await run_conversion(user.id, src, kind, "gif", quality)
            await status.delete()
            caption = conversion_caption(lang, kind, "gif", result, quality)
            await conv_send_document(callback.message, result, caption, lang, user.id)
            await RT.db.set_history_status(history_id, "done", result.name)
            await state.set_state(ConvertStates.waiting)
    except Exception as exc:
        await show_error(status, lang, exc)


@router.callback_query(F.data == "conv:again")
async def cb_conv_again(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    await state.set_state(ConvertStates.waiting)
    await answer_callback(callback)
    if callback.message:
        await callback.message.answer(
            t(lang, "cv_png_intro"), reply_markup=nav_kb(lang, back="home", cancel="cancel")
        )


# =====================================================================
# 21. МОИ НАБОРЫ
# =====================================================================

async def collect_user_packs(user_id: int) -> list[dict[str, Any]]:
    assert RT.db is not None
    mosaics = await RT.db.list_mosaics(user_id, 500, 0)
    packs = await RT.db.list_sticker_packs(user_id, 500, 0)
    items = list(mosaics) + list(packs)
    items.sort(key=lambda row: str(row.get("created_at") or ""), reverse=True)
    return items


def pack_type_name(lang: str, row: dict[str, Any]) -> str:
    if row.get("kind") == "mosaic":
        return t(lang, "mp_mosaic")
    pack_type = str(row.get("pack_type") or "")
    if pack_type == "custom_emoji":
        return t(lang, "mp_emoji")
    if pack_type == "animated":
        return t(lang, "sp_type_animated_short")
    if pack_type == "video":
        return t(lang, "sp_type_video_short")
    return t(lang, "mp_sticker")


def pack_icon(row: dict[str, Any]) -> str:
    if row.get("kind") == "mosaic":
        return "🧩"
    if str(row.get("pack_type") or "") == "custom_emoji":
        return "⭐"
    return "🎨"


async def render_packs_page(user_id: int, page: int, lang: str) -> tuple[str, InlineKeyboardMarkup]:
    items = await collect_user_packs(user_id)
    per_page = 5
    pages = max(1, math.ceil(len(items) / per_page))
    page = max(0, min(page, pages - 1))
    chunk = items[page * per_page:(page + 1) * per_page]

    if not items:
        return t(lang, "mp_empty"), nav_kb(lang, back="home")

    lines = [t(lang, "mp_title")]
    rows: list[list[InlineKeyboardButton]] = []
    for row in chunk:
        title = str(row.get("title") or row.get("pack_name") or "-")
        icon = pack_icon(row)
        lines.append(t(
            lang, "mp_item_title",
            icon=icon, title=esc(title),
            type=pack_type_name(lang, row),
            n=row.get("total", 0),
            date=format_date(str(row.get("created_at") or "")),
        ))
        rows.append([btn(f"{icon} {title[:36]}", f"packs:view:{row['kind']}:{row['id']}")])

    if pages > 1:
        nav_row: list[InlineKeyboardButton] = []
        if page > 0:
            nav_row.append(btn("⬅️", f"packs:page:{page - 1}"))
        nav_row.append(btn(t(lang, "mp_page", page=page + 1, pages=pages), f"packs:page:{page}"))
        if page < pages - 1:
            nav_row.append(btn("➡️", f"packs:page:{page + 1}"))
        rows.append(nav_row)
    rows.append([btn(t(lang, "btn_home"), "home")])
    return "\n\n".join(lines), markup(rows)


@router.callback_query(F.data.in_({"packs:list", "packs:page:0"}))
async def cb_packs_list(callback: CallbackQuery, state: FSMContext) -> None:
    await cleanup_state_files(state)
    await state.clear()
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    text, keyboard = await render_packs_page(user.id, 0, lang)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, keyboard)


@router.callback_query(F.data.startswith("packs:page:"))
async def cb_packs_page(callback: CallbackQuery) -> None:
    user = callback.from_user
    if not user:
        return
    page_text = callback.data.split(":")[2]
    page = int(page_text) if page_text.isdigit() else 0
    lang = await get_lang(user.id)
    text, keyboard = await render_packs_page(user.id, page, lang)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, keyboard)


async def fetch_pack_record(user_id: int, kind: str, item_id: int) -> Optional[dict[str, Any]]:
    assert RT.db is not None
    if kind == "mosaic":
        return await RT.db.get_mosaic(user_id, item_id)
    if kind == "pack":
        return await RT.db.get_sticker_pack(user_id, item_id)
    return None


@router.callback_query(F.data.startswith("packs:view:"))
async def cb_pack_view(callback: CallbackQuery) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4 or not parts[3].isdigit():
        await answer_callback(callback)
        return
    kind, item_id = parts[2], int(parts[3])
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    row = await fetch_pack_record(user.id, kind, item_id)
    if not row:
        await answer_callback(callback, t(lang, "err_not_found"), show_alert=True)
        return
    title = str(row.get("title") or row.get("pack_name") or "-")
    text = t(
        lang, "mp_detail",
        title=esc(title), type=pack_type_name(lang, row),
        n=row.get("total", 0), date=format_date(str(row.get("created_at") or "")),
        link=str(row.get("pack_link") or ""),
    )
    keyboard = markup([
        [btn(t(lang, "btn_link"), url=str(row.get("pack_link") or PACK_LINK_PREFIX), style="primary")],
        [btn(t(lang, "mp_delete_local"), f"packs:del:{kind}:{item_id}", style="danger")],
        [btn(t(lang, "mp_delete_remote"), f"packs:delremote:{kind}:{item_id}", style="danger")],
        [btn(t(lang, "btn_back"), "packs:list"), btn(t(lang, "btn_home"), "home")],
    ])
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, keyboard)


async def delete_pack_record(user_id: int, kind: str, item_id: int,
                             bot: Optional[Bot], remote: bool) -> tuple[bool, str]:
    assert RT.db is not None
    row = await fetch_pack_record(user_id, kind, item_id)
    if not row:
        return False, "err_not_found"
    if remote and bot:
        try:
            await api_call(bot.delete_sticker_set, name=str(row.get("pack_name") or ""))
        except BotError:
            raise
        except Exception as exc:
            LOG.warning("Не удалось удалить набор %s: %s", row.get("pack_name"), exc)
            return False, "err_telegram"
    try:
        paths = json.loads(row.get("files") or "[]")
    except Exception:
        paths = []
    for raw in paths:
        cleanup_path(str(raw))
        await RT.db.delete_file_record(Path(str(raw)))
    if kind == "mosaic":
        await RT.db.delete_mosaic(user_id, item_id)
    else:
        await RT.db.delete_sticker_pack(user_id, item_id)
    return True, ("mp_deleted_remote" if remote else "mp_deleted")


@router.callback_query(F.data.startswith("packs:del:"))
async def cb_pack_delete(callback: CallbackQuery, state: FSMContext) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4:
        await answer_callback(callback)
        return
    kind, item_id = parts[2], int(parts[3])
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    row = await fetch_pack_record(user.id, kind, item_id)
    if not row:
        await answer_callback(callback, t(lang, "err_not_found"), show_alert=True)
        return
    title = str(row.get("title") or row.get("pack_name") or "-")
    keyboard = markup([
        [btn(t(lang, "btn_yes"), f"packs:delyes:{kind}:{item_id}", style="danger")],
        [btn(t(lang, "btn_no"), f"packs:view:{kind}:{item_id}", style="primary")],
    ])
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, t(lang, "mp_delete_title", title=esc(title)), keyboard)


@router.callback_query(F.data.startswith("packs:delyes:"))
async def cb_pack_delete_yes(callback: CallbackQuery, bot: Bot) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4:
        await answer_callback(callback)
        return
    kind, item_id = parts[2], int(parts[3])
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    try:
        ok, key = await delete_pack_record(user.id, kind, item_id, bot, remote=False)
    except BotError as exc:
        await answer_callback(callback, t(lang, exc.key, **exc.kwargs), show_alert=True)
        return
    await answer_callback(callback, t(lang, key) if ok else t(lang, key), show_alert=not ok)
    text, keyboard = await render_packs_page(user.id, 0, lang)
    if callback.message:
        await show_text(callback.message, t(lang, key) + "\n\n" + text, keyboard)


@router.callback_query(F.data.startswith("packs:delremote:"))
async def cb_pack_delete_remote(callback: CallbackQuery) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4:
        await answer_callback(callback)
        return
    kind, item_id = parts[2], int(parts[3])
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    row = await fetch_pack_record(user.id, kind, item_id)
    if not row:
        await answer_callback(callback, t(lang, "err_not_found"), show_alert=True)
        return
    title = str(row.get("title") or row.get("pack_name") or "-")
    keyboard = markup([
        [btn(t(lang, "btn_yes"), f"packs:remyes:{kind}:{item_id}", style="danger")],
        [btn(t(lang, "btn_no"), f"packs:view:{kind}:{item_id}", style="primary")],
    ])
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, t(lang, "mp_delete_confirm", title=esc(title)), keyboard)


@router.callback_query(F.data.startswith("packs:remyes:"))
async def cb_pack_remote_yes(callback: CallbackQuery, bot: Bot) -> None:
    parts = callback.data.split(":")
    if len(parts) != 4:
        await answer_callback(callback)
        return
    kind, item_id = parts[2], int(parts[3])
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    try:
        ok, key = await delete_pack_record(user.id, kind, item_id, bot, remote=True)
    except BotError as exc:
        await answer_callback(callback, t(lang, exc.key, **exc.kwargs), show_alert=True)
        return
    await answer_callback(callback, t(lang, key), show_alert=not ok)
    text, keyboard = await render_packs_page(user.id, 0, lang)
    if callback.message:
        await show_text(callback.message, t(lang, key) + "\n\n" + text, keyboard)


# =====================================================================
# 22. ИСТОРИЯ ОПЕРАЦИЙ
# =====================================================================

async def render_history_page(user_id: int, page: int, lang: str) -> tuple[str, InlineKeyboardMarkup]:
    assert RT.db is not None
    per_page = 6
    total = await RT.db.count_history(user_id)
    pages = max(1, math.ceil(total / per_page))
    page = max(0, min(page, pages - 1))
    rows = await RT.db.list_history(user_id, per_page, page * per_page)
    if not rows:
        return t(lang, "hist_empty"), nav_kb(lang, back="home")

    status_key = {"processing": "status_processing", "done": "status_done",
                  "error": "status_error", "cancelled": "status_cancelled"}
    lines = [t(lang, "hist_title")]
    for row in rows:
        icon = {"mosaic": "🧩", "emoji_pack": "⭐", "sticker_pack": "🎨",
                "png": "🖼", "gif": "🎞", "frames": "📦"}.get(str(row.get("op_type")), "•")
        status = t(lang, status_key.get(str(row.get("status")), "status_processing"))
        title = esc(str(row.get("title") or "-"))[:40]
        lines.append(f"{icon} <b>{title}</b>\n{status} · {format_date(str(row.get('created_at') or ''))}")

    keyboard_rows: list[list[InlineKeyboardButton]] = []
    if pages > 1:
        nav_row: list[InlineKeyboardButton] = []
        if page > 0:
            nav_row.append(btn("⬅️", f"hist:page:{page - 1}"))
        nav_row.append(btn(t(lang, "mp_page", page=page + 1, pages=pages), f"hist:page:{page}"))
        if page < pages - 1:
            nav_row.append(btn("➡️", f"hist:page:{page + 1}"))
        keyboard_rows.append(nav_row)
    keyboard_rows.append([btn(t(lang, "btn_home"), "home")])
    return "\n\n".join(lines), markup(keyboard_rows)


@router.callback_query(F.data.in_({"hist:list", "hist:page:0"}))
async def cb_history(callback: CallbackQuery, state: FSMContext) -> None:
    await cleanup_state_files(state)
    await state.clear()
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    text, keyboard = await render_history_page(user.id, 0, lang)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, keyboard)


@router.callback_query(F.data.startswith("hist:page:"))
async def cb_history_page(callback: CallbackQuery) -> None:
    user = callback.from_user
    if not user:
        return
    page_text = callback.data.split(":")[2]
    page = int(page_text) if page_text.isdigit() else 0
    lang = await get_lang(user.id)
    text, keyboard = await render_history_page(user.id, page, lang)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, keyboard)


# =====================================================================
# 23. НАСТРОЙКИ
# =====================================================================

async def settings_text(user_id: int, lang: str) -> str:
    assert RT.db is not None
    size, count = await RT.db.user_storage(user_id)
    language_name = "🇷🇺 Русский" if lang == "ru" else "🇬🇧 English"
    return (
        t(lang, "st_title") + "\n\n"
        + t(lang, "st_storage", size=human_size(size), n=count) + "\n\n"
        + t(lang, "st_lang", language=language_name)
    )


@router.callback_query(F.data == "settings:main")
async def cb_settings(callback: CallbackQuery) -> None:
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    language_name = "🇷🇺 Русский" if lang == "ru" else "🇬🇧 English"
    text = await settings_text(user.id, lang)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, settings_kb(lang, language_name))


@router.callback_query(F.data == "settings:lang")
async def cb_settings_lang(callback: CallbackQuery, state: FSMContext) -> None:
    lang = await get_lang(callback.from_user.id)
    await state.update_data(from_settings=True)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, t(lang, "st_choose_lang"), settings_lang_kb())


@router.callback_query(F.data == "settings:clear")
async def cb_settings_clear(callback: CallbackQuery) -> None:
    lang = await get_lang(callback.from_user.id)
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, t(lang, "st_clear_confirm"), confirm_kb(lang, "settings:clear"))


@router.callback_query(F.data == "settings:clear:yes")
async def cb_settings_clear_yes(callback: CallbackQuery) -> None:
    user = callback.from_user
    if not user:
        return
    lang = await get_lang(user.id)
    assert RT.db is not None
    paths = await RT.db.delete_user_files(user.id)
    for raw in paths:
        cleanup_path(raw)
    for base in (ORIGINALS_DIR, FRAGMENTS_DIR, PREVIEWS_DIR, STICKERS_DIR, TEMPORARY_DIR):
        cleanup_dir(base / str(user.id))
    await answer_callback(callback, t(lang, "st_cleared"))
    text = await settings_text(user.id, lang)
    if callback.message:
        await show_text(callback.message, text, settings_kb(lang, "🇷🇺 Русский" if lang == "ru" else "🇬🇧 English"))


@router.callback_query(F.data == "settings:clear:no")
async def cb_settings_clear_no(callback: CallbackQuery) -> None:
    await cb_settings(callback)


# =====================================================================
# 24. ПОМОЩЬ
# =====================================================================

@router.callback_query(F.data == "help:main")
async def cb_help(callback: CallbackQuery) -> None:
    lang = await get_lang(callback.from_user.id)
    text = (
        t(lang, "help_title") + "\n\n" + t(lang, "help_text") + "\n\n"
        + t(lang, "help_limits", mosaic=MAX_MOSAIC_ITEMS, emoji=MAX_EMOJI_PACK_ITEMS,
            static=MAX_STATIC_PACK_ITEMS, anim=MAX_ANIMATED_PACK_ITEMS,
            video=MAX_VIDEO_PACK_ITEMS, mb=MAX_DOWNLOAD_MB, storage=MAX_USER_STORAGE_MB)
    )
    await answer_callback(callback)
    if callback.message:
        await show_text(callback.message, text, nav_kb(lang, back="home"))


# =====================================================================
# 25. FALLBACK И ОШИБКИ
# =====================================================================

@router.message(StateFilter(None), F.text)
async def fallback_text(message: Message) -> None:
    if not message.from_user:
        return
    lang = await get_lang(message.from_user.id)
    await message.answer(t(lang, "main_title"), reply_markup=main_menu_kb(lang))


@router.message()
async def fallback_any(message: Message, state: FSMContext) -> None:
    if not message.from_user:
        return
    lang = await get_lang(message.from_user.id)
    await message.answer(t(lang, "err_wrong_state"), reply_markup=main_menu_kb(lang))


async def on_error(event: Any) -> None:
    exception = getattr(event, "exception", None)
    update = getattr(event, "update", None)
    LOG.error("Ошибка обработки обновления %s: %s", getattr(update, "update_id", "?"), exception,
              exc_info=exception)
    try:
        message = getattr(update, "message", None) or getattr(update, "callback_query", None)
        if message is not None and hasattr(message, "answer"):
            user = getattr(message, "from_user", None)
            lang = await get_lang(user.id) if user else "ru"
            if hasattr(message, "answer"):
                await message.answer(t(lang, "err_generic"))
    except Exception:
        pass


# =====================================================================
# 26. ОЧИСТКА И КВОТЫ
# =====================================================================

async def enforce_quotas() -> None:
    assert RT.db is not None
    limit = MAX_TOTAL_STORAGE_MB * 1024 * 1024
    rows = await RT.db.fetchall("SELECT path, size FROM files ORDER BY expires_at ASC")
    total = sum(int(row["size"] or 0) for row in rows)
    if total <= limit:
        return
    LOG.warning("Превышен общий лимит хранилища: %s", human_size(total))
    for row in rows:
        if total <= limit:
            break
        path = Path(str(row["path"]))
        if path.exists():
            cleanup_path(path)
        await RT.db.delete_file_record(path)
        total -= int(row["size"] or 0)


async def cleanup_once() -> None:
    assert RT.db is not None
    try:
        expired = await RT.db.purge_expired()
        removed = 0
        for raw in expired:
            path = Path(str(raw))
            if path.exists():
                cleanup_path(path)
                removed += 1
        for base in (ORIGINALS_DIR, FRAGMENTS_DIR, PREVIEWS_DIR, STICKERS_DIR, TEMPORARY_DIR):
            if not base.exists():
                continue
            for child in base.iterdir():
                if child.is_dir() and not any(child.iterdir()):
                    try:
                        child.rmdir()
                    except OSError:
                        pass
        await enforce_quotas()
        if removed:
            LOG.info("Очистка: удалено %s файлов", removed)
    except Exception as exc:
        LOG.warning("Ошибка очистки хранилища: %s", exc)


async def cleanup_loop() -> None:
    while True:
        await asyncio.sleep(CLEANUP_INTERVAL_SECONDS)
        await cleanup_once()


# =====================================================================
# 27. ЗАПУСК
# =====================================================================

def get_bot_token() -> str:
    token = os.getenv("BOT_TOKEN", "").strip()
    if not token:
        raise RuntimeError("Не задана системная переменная окружения BOT_TOKEN")
    return token


async def main() -> None:
    token = get_bot_token()
    SECRET_FILTER.add_secret(token)
    ensure_storage()

    RT.db = Database(DB_PATH)
    await RT.db.init()
    RT.ffmpeg = await run_blocking(find_ffmpeg)
    if not RT.ffmpeg:
        LOG.warning("FFmpeg не найден: конвертация видео и WebM будет недоступна")

    bot = Bot(token=token, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    RT.bot = bot
    try:
        me = await bot.get_me()
    except TelegramUnauthorizedError:
        LOG.error("Telegram не принял токен. Проверьте переменную окружения BOT_TOKEN.")
        raise SystemExit(1)
    except TelegramNetworkError as exc:
        LOG.error("Нет связи с Telegram API: %s", exc)
        raise SystemExit(1)
    RT.bot_username = (me.username or "").lower()
    LOG.info("Запущен @%s (id=%s), ffmpeg=%s", RT.bot_username, me.id, bool(RT.ffmpeg))

    from aiogram.types import BotCommand
    await bot.set_my_commands([
        BotCommand(command="start", description="Главное меню · Main menu"),
        BotCommand(command="menu", description="Меню · Menu"),
        BotCommand(command="cancel", description="Отмена · Cancel"),
        BotCommand(command="help", description="Помощь · Help"),
    ])

    dispatcher = Dispatcher(storage=MemoryStorage())
    dispatcher.include_router(router)
    dispatcher.errors.register(on_error)

    cleanup_task = asyncio.create_task(cleanup_loop())
    try:
        await bot.delete_webhook(drop_pending_updates=True)
        await dispatcher.start_polling(bot, allowed_updates=dispatcher.resolve_used_update_types())
    finally:
        cleanup_task.cancel()
        try:
            await cleanup_task
        except (asyncio.CancelledError, Exception):
            pass
        if RT.db:
            await RT.db.close()
        await bot.session.close()
        LOG.info("Бот остановлен")


# =====================================================================
# 28. САМОПРОВЕРКА БЕЗ TELEGRAM (python bot.py --selftest)
# =====================================================================

async def self_test() -> int:
    ensure_storage()
    RT.ffmpeg = await run_blocking(find_ffmpeg)
    work = TEMPORARY_DIR / "_selftest"
    cleanup_dir(work)
    work.mkdir(parents=True, exist_ok=True)
    print("== Sticker & Emoji Studio: self test ==")
    failures = 0

    def check(name: str, condition: bool, extra: str = "") -> None:
        nonlocal failures
        if condition:
            print(f"  OK   {name} {extra}")
        else:
            failures += 1
            print(f"  FAIL {name} {extra}")

    source = work / "source.png"
    image = Image.new("RGB", (960, 640))
    draw = ImageDraw.Draw(image)
    for x in range(960):
        draw.line([(x, 0), (x, 640)], fill=(int(x / 960 * 255), 90, int(255 - x / 960 * 255)))
    image.save(source)

    info = inspect_image(source)
    check("image inspect", info.width == 960 and info.height == 640, f"{info.width}x{info.height}")

    result = slice_image_sync(source, work / "fragments", 4, 3)
    check("slice 4x3", len(result["paths"]) == 12, f"{len(result['paths'])} fragments")
    cell = Image.open(result["paths"][0])
    check("fragment size", cell.size == (512, 512), str(cell.size))
    check("crop aspect", abs((result["cropped_size"][0] / result["cropped_size"][1]) - 4 / 3) < 0.01,
          f"crop={result['cropped_size']}")

    preview = build_mosaic_preview_sync(result["paths"], 4, 3, work / "preview.png", max_width=512)
    check("mosaic preview", preview.exists() and Image.open(preview).size == (512, 384),
          str(Image.open(preview).size))

    emoji = prepare_custom_emoji_sync(source, work / "emoji.webp")
    check("custom emoji 512x512", Image.open(emoji).size == (512, 512) and emoji.stat().st_size <= EMOJI_STICKER_MAX_BYTES,
          f"{Image.open(emoji).size} {emoji.stat().st_size} B")

    sticker = prepare_static_sticker_sync(source, work / "sticker.webp")
    size = Image.open(sticker).size
    check("static sticker", max(size) == 512 and min(size) <= 512, str(size))

    png = webp_to_png_sync(sticker, work / "sticker.png")
    check("webp to png", png.exists() and Image.open(png).mode == "RGBA", str(Image.open(png).mode))

    if RT.ffmpeg:
        frames_dir = work / "frames"
        frames_dir.mkdir(exist_ok=True)
        for index, path in enumerate(result["paths"][:12]):
            Image.open(path).save(frames_dir / f"f{index:03d}.png")
        webm = work / "sticker.webm"
        try:
            import subprocess
            subprocess.run([RT.ffmpeg, "-y", "-loglevel", "error", "-framerate", "30",
                            "-i", str(frames_dir / "f%03d.png"), "-c:v", "libvpx-vp9",
                            "-pix_fmt", "yuva420p", "-b:v", "0", "-crf", "34", str(webm)],
                           check=True, capture_output=True)
            check("ffmpeg webm", webm.exists() and webm.stat().st_size > 0, f"{webm.stat().st_size} B")
            gif = webm_to_gif_sync(webm, work / "out.gif", "normal")
            check("webm to gif", gif.exists() and gif.stat().st_size > 0, f"{gif.stat().st_size} B")
            frame = webm_first_frame_sync(webm, work / "frame.png")
            check("webm first frame", frame.exists(), str(Image.open(frame).size))
        except Exception as exc:
            check("ffmpeg pipeline", False, str(exc))
    else:
        print("  SKIP ffmpeg (не найден)")

    try:
        import pyrlottie  # noqa: F401
        check("pyrlottie available", True)
    except Exception as exc:
        check("pyrlottie available", False, str(exc))

    cleanup_dir(work)
    print(f"== Готово. Ошибок: {failures} ==")
    return 1 if failures else 0


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        raise SystemExit(asyncio.run(self_test()))
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        pass
    except RuntimeError as exc:
        LOG.error("%s", exc)
        raise SystemExit(1)