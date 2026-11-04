"""PigHub 随机猪猪。

群里发送「/随机猪猪」或「/sjzz」时，从 https://pighub.top 随机取一张猪猪图片发送出来。
发送「/随机猪猪 关键词」时，只发标题/文件名里含该关键词的图；查不到就回一句提示。
管理员可以用「/sjzz 关键词 数量」一次要 1~10 张（小数向下取整），普通用户写了数量会被提示只能用管理员。
图库列表来自 https://pighub.top/api/images?sort=2，图片直链为 https://pighub.top + image_url。

群聊里每位用户每天有抽取上限（默认 10 次），私聊不限。
支持群聊黑名单/白名单，以及插件级管理员名单；管理员触发时不受冷却与每日上限限制。
"""

from __future__ import annotations

import asyncio
import hashlib
import json
import random
import re
import time
from collections import deque
from datetime import date
from pathlib import Path
from typing import Any
from urllib.parse import quote

import aiohttp

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.message_components import Image, Plain
from astrbot.api.star import Context, Star, StarTools
from astrbot.core import AstrBotConfig

PLUGIN_NAME = "astrbot_plugin_pighub"
BASE_URL = "https://pighub.top"
IMAGES_API = f"{BASE_URL}/api/images"

TRIGGER_WORD = "随机猪猪"
TRIGGER_ALIAS = "sjzz"
# 只是让消息进入 handler 的粗筛，真正的判定在 _parse_trigger 里做（要求 / 前缀）
TRIGGER_PATTERN = r"(?i)随机猪猪|sjzz"
KEYWORD_MISS_TEXT = "根本没有这样的小猪！！"
COUNT_ADMIN_ONLY_TEXT = "只有管理员才能指定张数哦～ 直接发 /sjzz 可以拿一张 🐷"
DEFAULT_IMAGE_COUNT = 1
MAX_IMAGE_COUNT = 10
IMAGE_COUNT_RE = re.compile(r"\d+(?:\.\d+)?")

SORT_MAP = {"random": 2, "latest": 2, "popular": 3, "oldest": 1, "name": 0}
IMAGE_SUFFIXES = {".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp"}
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AstrBot-PigHub/1.1"
REQUEST_TIMEOUT = aiohttp.ClientTimeout(total=40, sock_read=30, sock_connect=10)

DEFAULT_SORT = "random"
DEFAULT_COOLDOWN = 5
DEFAULT_CACHE_MINUTES = 10
DEFAULT_MAX_MB = 15
DEFAULT_DAILY_LIMIT = 10


def _plain_text(event: AstrMessageEvent) -> str:
    """取消息里的纯文本（保留前缀，AstrBot 只会剥离 event.message_str）。"""
    try:
        segments = event.message_obj.message or []
    except Exception:  # noqa: BLE001
        segments = []
    parts = [seg.text or "" for seg in segments if isinstance(seg, Plain)]
    return "".join(parts)


class PigHubPlugin(Star):
    def __init__(self, context: Context, config: AstrBotConfig | None = None) -> None:
        super().__init__(context, config)
        self.conf: Any = config or {}
        self.data_dir = StarTools.get_data_dir(PLUGIN_NAME)
        self.image_dir = self.data_dir / "images"
        self.image_dir.mkdir(parents=True, exist_ok=True)
        self.cache_file = self.data_dir / "list_cache.json"
        self.usage_file = self.data_dir / "usage.json"

        self._items: list[dict[str, Any]] = []
        self._fetched_at: float = 0.0
        self._fetch_lock = asyncio.Lock()
        self._last_sent: dict[str, float] = {}
        self._recent: deque[int] = deque(maxlen=40)

        self._usage: dict[str, Any] = {"date": "", "counts": {}}
        self._usage_lock = asyncio.Lock()
        self._load_usage()

        self.logger.info("PigHub 随机猪猪已加载，数据目录：%s", self.data_dir)

    # ------------------------------------------------------------------ 配置

    def _conf(self, key: str, default: Any) -> Any:
        try:
            value = self.conf.get(key, default)
        except Exception:  # noqa: BLE001
            return default
        return default if value is None else value

    def _int_conf(self, key: str, default: int, minimum: int = 0) -> int:
        try:
            value = int(self._conf(key, default))
        except (TypeError, ValueError):
            value = default
        return max(minimum, value)

    def _list_conf(self, key: str) -> set[str]:
        """读取名单类配置，兼容列表与「逗号/空格分隔的字符串」两种写法。"""
        raw = self._conf(key, [])
        if isinstance(raw, str):
            raw = re.split(r"[\s,，、]+", raw)
        if not isinstance(raw, (list, tuple, set)):
            return set()
        return {str(item).strip() for item in raw if str(item).strip()}

    @staticmethod
    def _matches_group(entries: set[str], group_id: str) -> bool:
        """群号匹配：支持裸群号，也支持 A1:GroupMessage:924818395 这种 UMO 写法。"""
        for entry in entries:
            if entry == group_id or entry.rsplit(":", 1)[-1] == group_id:
                return True
        return False

    def _group_allowed(self, event: AstrMessageEvent) -> bool:
        """群聊黑名单优先于白名单；白名单为空表示所有群都允许。私聊不受影响。"""
        if event.is_private_chat():
            return True
        group_id = str(event.get_group_id() or "").strip()
        if not group_id:
            return True
        if self._matches_group(self._list_conf("group_blacklist"), group_id):
            return False
        whitelist = self._list_conf("group_whitelist")
        if whitelist and not self._matches_group(whitelist, group_id):
            return False
        return True

    def _is_plugin_admin(self, event: AstrMessageEvent) -> bool:
        """插件级管理员：AstrBot 全局管理员，或 admin_users 名单里的 QQ 号。"""
        try:
            if event.is_admin():
                return True
        except Exception:  # noqa: BLE001
            pass
        uid = str(event.get_sender_id() or "")
        return bool(uid) and uid in self._list_conf("admin_users")

    # ------------------------------------------------------------------ 入口

    # priority 高于其它插件（默认 0），保证先抢到 /随机猪猪 并在结束时 stop_event，
    # 避免群聊增强（group_chat_plus）或 LLM 阶段再回复一遍。
    @filter.regex(TRIGGER_PATTERN, priority=1000)
    async def on_random_pig(self, event: AstrMessageEvent):
        """收到「/随机猪猪 [关键词] [数量]」时回复 pighub.top 的图片。"""
        hit, keyword, count = self._parse_trigger(event)
        if not hit:
            return
        if not self._group_allowed(event):
            # 被群名单排除的群不回复，也不放行给后续 LLM，避免意外发言
            self.logger.debug(
                "群聊 %s 不在允许范围内，忽略 /随机猪猪", event.get_group_id()
            )
            event.stop_event()
            return
        try:
            await self._handle(event, keyword, count)
        except Exception as exc:  # noqa: BLE001 - 兜底，避免插件异常打断管线
            self.logger.exception("随机猪猪处理失败：%s", exc)
            try:
                await event.send(event.plain_result("猪猪跑丢了，稍后再试试吧 🐷"))
            except Exception:  # noqa: BLE001
                pass
        finally:
            # 处理完就结束本条消息，避免再被 LLM 兜底回复一次
            event.stop_event()

    def _parse_trigger(self, event: AstrMessageEvent) -> tuple[bool, str, int | None]:
        """判断是否为本插件指令，返回 (是否命中, 关键词, 指定的张数)。

        必须带 "/"（或全角「／」）前缀；支持「/随机猪猪」与「/sjzz」，
        "/随机猪猪 磁流体" 的「磁流体」作为关键词；末尾的整数/小数是张数
        （小数向下取整，范围 1~10）。没写数字时张数为 None，由 _handle 决定：
        1 张（且指定张数只有管理员能用）。
        """
        # 中文输入法很容易打出全角斜杠，统一成半角再判断
        text = _plain_text(event).strip().replace("／", "/")
        if not text:
            return False, "", None
        if not text.startswith("/"):
            return False, "", None
        body = text[1:].strip()
        # 指令词：/随机猪猪 或 /sjzz（大小写不敏感）
        if body.startswith(TRIGGER_WORD):
            rest = body[len(TRIGGER_WORD) :]
        elif body.lower().startswith(TRIGGER_ALIAS):
            rest = body[len(TRIGGER_ALIAS) :]
        else:
            return False, "", None
        if rest and not rest[0].isspace() and rest[0] not in "!！。.~～?？,，、":
            # 比如「/随机猪猪们」「/随机猪猪2」，不当作指令
            return False, "", None
        # 允许句末标点
        rest = rest.strip().strip("!！。.~～?？,，、")
        tokens = rest.split()
        count: int | None = None
        # 末尾是数字（整数或小数）就当作张数：小数向下取整，并夹到 1~10
        if tokens and IMAGE_COUNT_RE.fullmatch(tokens[-1]):
            try:
                count = int(float(tokens[-1]))
            except ValueError:
                count = None
            if count is not None:
                count = max(1, min(MAX_IMAGE_COUNT, count))
            tokens = tokens[:-1]
        # 关键词里去掉空白，方便和标题/文件名比对
        return True, "".join(tokens), count

    async def _handle(
        self, event: AstrMessageEvent, keyword: str, count: int | None
    ) -> None:
        is_private = event.is_private_chat()
        if is_private and not bool(self._conf("allow_private", True)):
            return

        uid = str(event.get_sender_id() or "")
        is_admin = self._is_plugin_admin(event)
        if count is not None and not is_admin:
            # 指定张数是管理员专属，普通用户只认「/sjzz [关键词]」
            await event.send(event.plain_result(COUNT_ADMIN_ONLY_TEXT))
            return
        count = (
            max(1, min(MAX_IMAGE_COUNT, count))
            if count is not None
            else DEFAULT_IMAGE_COUNT
        )
        limit = self._int_conf("daily_limit", DEFAULT_DAILY_LIMIT)
        # 每日次数限制只作用于群聊；私聊与管理员不受限
        if (
            not is_private
            and not is_admin
            and limit > 0
            and uid
            and self._used_today(uid) >= limit
        ):
            await event.send(event.plain_result(self._limit_text(limit)))
            return

        # 冷却按「会话 + 用户」计算：同一个人刷屏会被拦，但不会把群里其他人一起卡住
        cooldown = self._int_conf("cooldown_seconds", DEFAULT_COOLDOWN)
        session_key = f"{event.unified_msg_origin}:{uid}"
        now = time.time()
        last = self._last_sent.get(session_key, 0.0)
        if cooldown > 0 and not is_admin and now - last < cooldown:
            return

        keyword = (keyword or str(self._conf("keyword", "") or "")).strip().lower()

        items: list[dict[str, Any]] = []
        try:
            items = await self._get_items()
        except Exception as exc:  # noqa: BLE001
            self.logger.warning("拉取 pighub 图库失败：%s", exc)

        if keyword:
            matched = [it for it in items if keyword in self._match_blob(it)]
            if not matched:
                await event.send(event.plain_result(KEYWORD_MISS_TEXT))
                return
            candidates = self._fresh(matched)
        else:
            candidates = self._fresh(items)

        picks: list[tuple[Path, dict[str, Any] | None]] = []
        pool = list(candidates)
        for _ in range(count):
            if not pool:
                break
            picked_path, picked_item = await self._pick_and_download(pool)
            if picked_path is None:
                break
            picks.append((picked_path, picked_item))
            if picked_item and picked_item.get("id") is not None:
                picked_id = picked_item["id"]
                pool = [it for it in pool if it.get("id") != picked_id]

        if not picks:
            # 图库接口挂了也尽量用本地缓存过的图顶上
            cached = self._random_cached_image()
            if cached is None:
                await event.send(
                    event.plain_result("猪猪图床暂时连不上，等会儿再试吧 🐷")
                )
                return
            picks = [(cached, None)]

        if not is_private and not is_admin and limit > 0 and uid:
            await self._consume_daily(uid)

        self._last_sent[session_key] = time.time()
        if len(self._last_sent) > 500:
            self._last_sent = {session_key: self._last_sent[session_key]}
        for _path, _item in picks:
            if _item and _item.get("id") is not None:
                self._recent.append(_item["id"])

        if bool(self._conf("send_title", False)) and picks[0][1] and picks[0][1].get("title"):
            await event.send(event.plain_result(f"🐷 {picks[0][1]['title']}"))

        files = [str(path) for path, _item in picks]
        if len(files) == 1:
            await event.send(event.image_result(files[0]))
        else:
            await event.send(
                event.chain_result([Image.fromFileSystem(f) for f in files])
            )

    # ------------------------------------------------------------------ 每日次数

    def _load_usage(self) -> None:
        try:
            raw = json.loads(self.usage_file.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            return
        if isinstance(raw, dict) and isinstance(raw.get("counts"), dict):
            self._usage = {
                "date": str(raw.get("date") or ""),
                "counts": {
                    str(k): int(v)
                    for k, v in raw["counts"].items()
                    if str(v).isdigit()
                },
            }

    def _save_usage(self) -> None:
        try:
            tmp = self.usage_file.with_suffix(".json.part")
            tmp.write_text(
                json.dumps(self._usage, ensure_ascii=False), encoding="utf-8"
            )
            tmp.replace(self.usage_file)
        except Exception as exc:  # noqa: BLE001
            self.logger.debug("写入次数记录失败：%s", exc)

    def _used_today(self, uid: str) -> int:
        if self._usage.get("date") != date.today().isoformat():
            return 0
        try:
            return int(self._usage["counts"].get(uid, 0))
        except (TypeError, ValueError, KeyError):
            return 0

    async def _consume_daily(self, uid: str) -> None:
        async with self._usage_lock:
            today = date.today().isoformat()
            if self._usage.get("date") != today:
                self._usage = {"date": today, "counts": {}}
            counts = self._usage.setdefault("counts", {})
            counts[uid] = int(counts.get(uid, 0)) + 1
            self._save_usage()

    @staticmethod
    def _limit_text(limit: int) -> str:
        return f"你今天的小猪次数已经用完啦（{limit}/{limit}），明天再来吧～ 私聊不限量哦 🐷"

    # ------------------------------------------------------------------ 图库

    async def _get_items(self) -> list[dict[str, Any]]:
        ttl = self._int_conf("cache_minutes", DEFAULT_CACHE_MINUTES, minimum=1) * 60
        if self._items and time.time() - self._fetched_at < ttl:
            return self._items

        async with self._fetch_lock:
            if self._items and time.time() - self._fetched_at < ttl:
                return self._items
            try:
                items = await self._fetch_items()
            except Exception as exc:  # noqa: BLE001
                if self._items:
                    self.logger.warning("图库刷新失败，沿用内存缓存：%s", exc)
                    return self._items
                cached = self._load_cache()
                if cached:
                    self.logger.warning("图库刷新失败，沿用磁盘缓存：%s", exc)
                    self._items = cached
                    return cached
                raise

            self._items = items
            self._fetched_at = time.time()
            self._save_cache(items)
            self.logger.info("pighub 图库已刷新，共 %d 张", len(items))
            return items

    async def _fetch_items(self) -> list[dict[str, Any]]:
        sort_name = str(self._conf("sort_mode", DEFAULT_SORT)).strip().lower()
        sort = SORT_MAP.get(sort_name, 2)
        headers = {"User-Agent": USER_AGENT, "Accept": "application/json"}
        async with aiohttp.ClientSession(
            timeout=REQUEST_TIMEOUT, headers=headers
        ) as session:
            async with session.get(IMAGES_API, params={"sort": str(sort)}) as resp:
                if resp.status != 200:
                    raise RuntimeError(f"HTTP {resp.status}")
                payload = await resp.json(content_type=None)

        if not isinstance(payload, dict) or payload.get("code") != 0:
            raise RuntimeError(f"接口返回异常：{str(payload)[:200]}")

        data = payload.get("data") or []
        items = [
            d for d in data if isinstance(d, dict) and str(d.get("image_url") or "")
        ]
        if not items:
            raise RuntimeError("图库为空")
        return items

    @staticmethod
    def _match_blob(item: dict[str, Any]) -> str:
        blob = (
            str(item.get("title") or "") + " " + str(item.get("filename") or "")
        ).lower()
        return "".join(blob.split())

    def _fresh(self, items: list[dict[str, Any]]) -> list[dict[str, Any]]:
        if not items:
            return []
        fresh = [it for it in items if it.get("id") not in self._recent]
        return fresh or items

    def _load_cache(self) -> list[dict[str, Any]]:
        try:
            raw = json.loads(self.cache_file.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            return []
        items = raw.get("items") if isinstance(raw, dict) else None
        if not isinstance(items, list):
            return []
        return [it for it in items if isinstance(it, dict) and it.get("image_url")]

    def _save_cache(self, items: list[dict[str, Any]]) -> None:
        try:
            self.cache_file.write_text(
                json.dumps({"items": items}, ensure_ascii=False),
                encoding="utf-8",
            )
        except Exception as exc:  # noqa: BLE001
            self.logger.debug("写入图库缓存失败：%s", exc)

    # ------------------------------------------------------------------ 图片

    async def _pick_and_download(
        self, candidates: list[dict[str, Any]]
    ) -> tuple[Path | None, dict[str, Any] | None]:
        pool = list(candidates)
        random.shuffle(pool)
        for item in pool[:4]:
            try:
                path = await self._download(item)
            except Exception as exc:  # noqa: BLE001
                self.logger.warning(
                    "下载失败（%s）：%s", item.get("filename"), exc
                )
                continue
            if path is not None:
                return path, item
        return None, None

    async def _download(self, item: dict[str, Any]) -> Path | None:
        raw_url = str(item.get("image_url") or "")
        if not raw_url:
            return None
        url = raw_url if raw_url.startswith("http") else BASE_URL + raw_url

        digest = hashlib.sha1(url.encode("utf-8")).hexdigest()[:16]
        suffix = Path(raw_url.split("?")[0]).suffix.lower()
        if suffix not in IMAGE_SUFFIXES:
            suffix = ".img"
        path = self.image_dir / f"{digest}{suffix}"
        if path.is_file() and path.stat().st_size > 0:
            return path

        max_bytes = self._int_conf("max_size_mb", DEFAULT_MAX_MB, minimum=1) * 1024 * 1024
        headers = {"User-Agent": USER_AGENT}

        async with aiohttp.ClientSession(
            timeout=REQUEST_TIMEOUT, headers=headers
        ) as session:
            data = await self._fetch_bytes(session, quote(url, safe=":/?=&[]@!$'()*+,;~"))
            if data is None:
                # 少数文件名可能已经是编码过的，回退成原样再试一次
                data = await self._fetch_bytes(session, url)
        if data is None:
            return None
        if len(data) > max_bytes:
            raise RuntimeError(f"图片过大：{len(data) / 1024 / 1024:.1f} MB")
        if len(data) < 16:
            raise RuntimeError("图片数据为空")

        tmp = path.with_suffix(path.suffix + ".part")
        tmp.write_bytes(data)
        tmp.replace(path)
        return path

    async def _fetch_bytes(
        self, session: aiohttp.ClientSession, url: str
    ) -> bytes | None:
        async with session.get(url) as resp:
            if resp.status != 200:
                self.logger.debug("下载 %s 返回 HTTP %s", url, resp.status)
                return None
            content_type = str(resp.headers.get("Content-Type") or "").lower()
            if content_type and not content_type.startswith("image/"):
                self.logger.debug("下载 %s 内容类型异常：%s", url, content_type)
                return None
            return await resp.read()

    def _random_cached_image(self) -> Path | None:
        files = [
            p
            for p in self.image_dir.glob("*")
            if p.is_file() and p.suffix.lower() in IMAGE_SUFFIXES and p.stat().st_size > 0
        ]
        if not files:
            return None
        return random.choice(files)

    async def terminate(self) -> None:
        self.logger.info("PigHub 随机猪猪已卸载")
