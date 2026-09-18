#!/usr/bin/env python3
"""Spotify companion service for V1: browser-as-playback-device control panel.

V1 never touches Spotify audio or artwork bytes. This service only:
  - manages the OAuth Authorization Code exchange/refresh (client_secret stays
    server-side; only the refresh_token is persisted, in a local sqlite db),
  - proxies read-only Spotify Web API calls (search, artist albums, album
    tracks) so the client_secret and refresh_token never reach the browser,
  - hands the browser a short-lived access_token so the Spotify Web Playback
    SDK can stream audio directly from Spotify into this browser tab,
  - proxies playback-control calls (play/pause/next/previous/volume/transfer)
    to whichever Spotify Connect device (this browser or another one) the
    user picks.

Everything here sits behind Caddy forward_auth against the existing V1
session cookie (see /recorder, /recorder-api in the Caddyfile for the same
pattern); this process itself does not know about that cookie.

Routes:
  GET  /spotify                          -> control panel page
  GET  /spotify-api/status                -> {"linked": bool, ...}
  GET  /spotify-api/login                 -> 302 to Spotify consent
  GET  /spotify-api/callback              -> OAuth redirect target
  POST /spotify-api/logout                -> forget the linked account
  GET  /spotify-api/player-token          -> short-lived access_token for the Web Playback SDK
  GET  /spotify-api/search/artists?q=&offset=  -> {"items", "offset", "total", "has_more"}
  GET  /spotify-api/search/albums?q=&offset=
  GET  /spotify-api/search/tracks?q=&offset=
  GET  /spotify-api/artists/<id>/albums?refresh=1 -- bypass the permanent cache and re-fetch
  GET  /spotify-api/artists/<id>/dedup-tracks
  GET  /spotify-api/albums/<id>?refresh=1          -- bypass the permanent cache and re-fetch
  GET  /spotify-api/albums/<id>/next-in-artist -> {"next": {id, name, image}|null} -- same-artist auto-continue lookup
  GET  /spotify-api/devices
  GET  /spotify-api/recently-played
  GET  /spotify-api/player/queue       -> {"currently_playing": {...}|null, "queue": [...]}
  GET  /spotify-api/player/now-playing
  PUT  /spotify-api/player/transfer   {"device_id": "...", "play": true}
  PUT  /spotify-api/player/play       {"device_id", "uris"|"context_uri", "offset", "position_ms"}
  PUT  /spotify-api/player/pause      {"device_id"}
  PUT  /spotify-api/player/volume?value=0..100&device_id=...
  PUT  /spotify-api/player/seek?position_ms=&device_id=...
  POST /spotify-api/player/next       {"device_id"}
  POST /spotify-api/player/previous   {"device_id"}
  POST /spotify-api/player/queue      {"uri", "device_id"} -- append without interrupting current playback
  GET  /spotify-api/view-state        -> {"view": {...}|null, "updated_at", "updated_by"}
  PUT  /spotify-api/view-state        {"view": {...}, "client_id": "..."} -- cross-device "what's on screen" sync
  GET    /spotify-api/favorites            -> {"items": [{id, name, artists, image, release_date, genres, added_at}]}
  GET    /spotify-api/favorites/<album_id> -> {"favorited": bool}
  PUT    /spotify-api/favorites/<album_id> {"name", "artists", "image", "album_type", "release_date", "tracks"} -- add/update a favorite album
  PUT    /spotify-api/favorites/<album_id>/genres {"genres": [...]} -- hand-tagged genres (Spotify rarely has album-level genre data)
  DELETE /spotify-api/favorites/<album_id> -- remove a favorite album
"""
import base64
import json
import os
import re
import secrets
import sqlite3
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HOST = os.environ.get("SPOTIFY_HOST", "127.0.0.1")
PORT = int(os.environ.get("SPOTIFY_PORT", "8793"))
DB_PATH = os.environ.get("SPOTIFY_DB", "/opt/spotify/tokens.db")
CLIENT_ID = os.environ.get("SPOTIFY_CLIENT_ID", "")
CLIENT_SECRET = os.environ.get("SPOTIFY_CLIENT_SECRET", "")
REDIRECT_URI = os.environ.get("SPOTIFY_REDIRECT_URI", "https://spotify.example.com/spotify-api/callback")
SCOPES = ("streaming user-read-email user-read-private "
          "user-read-playback-state user-modify-playback-state user-read-currently-playing "
          "user-read-recently-played")

ACCOUNTS_TOKEN_URL = "https://accounts.spotify.com/api/token"
AUTHORIZE_URL = "https://accounts.spotify.com/authorize"
API_BASE = "https://api.spotify.com/v1"

# This app/account is capped by Spotify at limit<=10 on every paginated
# endpoint (search, artist albums, album tracks) -- the documented max of 50
# returns {"error":{"status":400,"message":"Invalid limit"}} above 10, verified
# empirically against the live API. Keep every page/limit param at or below this.
SPOTIFY_PAGE_LIMIT = 10
SEARCH_CACHE_TTL = 60
ARTIST_ALBUMS_RE = re.compile(r"^/spotify-api/artists/([A-Za-z0-9]{10,40})/albums$")
ARTIST_DEDUP_RE = re.compile(r"^/spotify-api/artists/([A-Za-z0-9]{10,40})/dedup-tracks$")
ALBUM_RE = re.compile(r"^/spotify-api/albums/([A-Za-z0-9]{10,40})$")
NEXT_IN_ARTIST_RE = re.compile(r"^/spotify-api/albums/([A-Za-z0-9]{10,40})/next-in-artist$")
FAVORITE_RE = re.compile(r"^/spotify-api/favorites/([A-Za-z0-9]{10,40})$")
FAVORITE_GENRES_RE = re.compile(r"^/spotify-api/favorites/([A-Za-z0-9]{10,40})/genres$")
ALBUM_TYPE_RANK = {"album": 3, "single": 2, "compilation": 1, "appears_on": 0}

_search_cache = {}
_search_cache_lock = threading.Lock()
_token_lock = threading.Lock()
_token_cache = {"access_token": None, "expires_at": 0.0}

# In-memory "what is everyone currently looking at" pointer, shared across every
# browser/device using this single-user Spotify link, so e.g. opening an artist
# on the phone also switches the laptop's page to that artist. Not persisted --
# it's just a UI convenience, not data, so it resetting on a service restart is fine.
_view_state_lock = threading.Lock()
_view_state = {"view": None, "updated_at": 0.0, "updated_by": None}


def set_view_state(view, client_id):
    with _view_state_lock:
        _view_state["view"] = view
        _view_state["updated_at"] = time.time()
        _view_state["updated_by"] = client_id


def get_view_state():
    with _view_state_lock:
        return dict(_view_state)


# The Web Playback SDK device IS this browser tab, so a reload always tears
# down and recreates it -- Spotify's live /v1/me/player then briefly (or
# permanently, if nothing resumes it) reports no active device at all. Caching
# the last known now-playing payload here means a reload still shows the same
# track and playhead instead of the bar just going blank; handle_now_playing
# forces playing=False on a cached fallback since we genuinely don't know
# whether it's still advancing.
_last_playback_lock = threading.Lock()
_last_playback = None


def set_last_playback(payload):
    global _last_playback
    with _last_playback_lock:
        _last_playback = payload


def get_last_playback():
    with _last_playback_lock:
        return dict(_last_playback) if _last_playback else None


def clear_last_playback():
    global _last_playback
    with _last_playback_lock:
        _last_playback = None


# ---------------------------------------------------------------- storage --

def db():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.execute("PRAGMA busy_timeout=5000")
    conn.execute("""CREATE TABLE IF NOT EXISTS account (
        id INTEGER PRIMARY KEY CHECK (id = 1),
        refresh_token TEXT NOT NULL,
        display_name TEXT,
        product TEXT,
        linked_at INTEGER NOT NULL
    )""")
    conn.execute("""CREATE TABLE IF NOT EXISTS favorite_albums (
        id TEXT PRIMARY KEY,
        name TEXT NOT NULL,
        artists TEXT NOT NULL,
        image TEXT,
        added_at INTEGER NOT NULL
    )""")
    # Added later than the table itself; ALTER TABLE has no "IF NOT EXISTS"
    # in sqlite, so ignore the "duplicate column" error on every run after
    # the first.
    for stmt in ("ALTER TABLE favorite_albums ADD COLUMN album_type TEXT",
                 "ALTER TABLE favorite_albums ADD COLUMN release_date TEXT",
                 "ALTER TABLE favorite_albums ADD COLUMN tracks TEXT",
                 "ALTER TABLE favorite_albums ADD COLUMN genres TEXT"):
        try:
            conn.execute(stmt)
        except sqlite3.OperationalError:
            pass
    conn.execute("""CREATE TABLE IF NOT EXISTS catalog_cache (
        cache_key TEXT PRIMARY KEY,
        payload TEXT NOT NULL,
        cached_at INTEGER NOT NULL
    )""")
    return conn


# Permanent (no expiration) cache for the artist/album/track catalog data
# this app reads from Spotify's Web API. Artist discographies and album
# tracklists essentially never change, and the alternative is repeatedly
# re-paying this app's tight per-endpoint daily quota (see README) for data
# that was already fetched once. Every catalog read in this file checks here
# before calling Spotify at all.
def cache_get(key):
    with db() as conn:
        row = conn.execute("SELECT payload FROM catalog_cache WHERE cache_key=?", (key,)).fetchone()
    return json.loads(row[0]) if row else None


def cache_set(key, value):
    with db() as conn:
        conn.execute("""INSERT INTO catalog_cache(cache_key, payload, cached_at) VALUES (?, ?, ?)
                         ON CONFLICT(cache_key) DO UPDATE SET payload=excluded.payload, cached_at=excluded.cached_at""",
                     (key, json.dumps(value), int(time.time())))
        conn.commit()


def save_account(refresh_token, display_name, product):
    with db() as conn:
        conn.execute("""INSERT INTO account(id, refresh_token, display_name, product, linked_at)
                         VALUES (1, ?, ?, ?, ?)
                         ON CONFLICT(id) DO UPDATE SET
                             refresh_token=excluded.refresh_token,
                             display_name=excluded.display_name,
                             product=excluded.product""",
                     (refresh_token, display_name, product, int(time.time())))
        conn.commit()


def load_account():
    with db() as conn:
        row = conn.execute(
            "SELECT refresh_token, display_name, product FROM account WHERE id=1").fetchone()
    if not row:
        return None
    return {"refresh_token": row[0], "display_name": row[1], "product": row[2]}


def clear_account():
    with db() as conn:
        conn.execute("DELETE FROM account WHERE id=1")
        conn.commit()
    with _token_lock:
        _token_cache["access_token"] = None
        _token_cache["expires_at"] = 0.0
    clear_last_playback()


def add_favorite(album_id, name, artists, image, album_type=None, release_date=None, tracks=None):
    # tracks (and album_type/release_date) are optional: favoriting from the
    # album page sends the full detail already on screen so no extra Spotify
    # call is needed, but COALESCE keeps any previously-cached tracks intact
    # if a caller ever re-favorites without that data (e.g. an older client).
    with db() as conn:
        conn.execute("""INSERT INTO favorite_albums(id, name, artists, image, album_type, release_date, tracks, added_at)
                         VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                         ON CONFLICT(id) DO UPDATE SET
                             name=excluded.name, artists=excluded.artists, image=excluded.image,
                             album_type=COALESCE(excluded.album_type, favorite_albums.album_type),
                             release_date=COALESCE(excluded.release_date, favorite_albums.release_date),
                             tracks=COALESCE(excluded.tracks, favorite_albums.tracks)""",
                     (album_id, name, json.dumps(artists or []), image, album_type, release_date,
                      json.dumps(tracks) if tracks is not None else None, int(time.time())))
        conn.commit()


def remove_favorite(album_id):
    with db() as conn:
        conn.execute("DELETE FROM favorite_albums WHERE id=?", (album_id,))
        conn.commit()


def list_favorites():
    with db() as conn:
        rows = conn.execute(
            "SELECT id, name, artists, image, release_date, genres, added_at "
            "FROM favorite_albums ORDER BY added_at DESC").fetchall()
    return [{"id": r[0], "name": r[1], "artists": json.loads(r[2]), "image": r[3],
             "release_date": r[4], "genres": json.loads(r[5]) if r[5] else [], "added_at": r[6]} for r in rows]


def set_favorite_genres(album_id, genres):
    with db() as conn:
        conn.execute("UPDATE favorite_albums SET genres=? WHERE id=?", (json.dumps(genres), album_id))
        conn.commit()


def is_favorite(album_id):
    with db() as conn:
        row = conn.execute("SELECT 1 FROM favorite_albums WHERE id=?", (album_id,)).fetchone()
    return row is not None


def get_favorite_album_detail(album_id):
    """Cached full album+tracks for a favorited album, or None if it isn't
    favorited or hasn't been cached yet (favorited before this existed)."""
    with db() as conn:
        row = conn.execute(
            "SELECT id, name, artists, image, album_type, release_date, tracks FROM favorite_albums WHERE id=?",
            (album_id,)).fetchone()
    if not row or not row[6]:
        return None
    return {"id": row[0], "name": row[1], "artists": json.loads(row[2]), "image": row[3],
            "album_type": row[4], "release_date": row[5], "tracks": json.loads(row[6])}


# ------------------------------------------------------------- spotify io --

class SpotifyAuthError(Exception):
    pass


class SpotifyAPIError(Exception):
    def __init__(self, status, payload):
        self.status = status
        self.payload = payload
        super().__init__(f"spotify api error {status}")


def _post_form(url, fields, auth=None):
    body = urllib.parse.urlencode(fields).encode()
    req = urllib.request.Request(url, data=body, method="POST")
    req.add_header("Content-Type", "application/x-www-form-urlencoded")
    if auth:
        basic = base64.b64encode(f"{auth[0]}:{auth[1]}".encode()).decode()
        req.add_header("Authorization", f"Basic {basic}")
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        raise SpotifyAPIError(exc.code, exc.read().decode("utf-8", "replace")) from exc


def exchange_code(code):
    return _post_form(ACCOUNTS_TOKEN_URL, {
        "grant_type": "authorization_code",
        "code": code,
        "redirect_uri": REDIRECT_URI,
    }, auth=(CLIENT_ID, CLIENT_SECRET))


def refresh_access_token(refresh_token):
    return _post_form(ACCOUNTS_TOKEN_URL, {
        "grant_type": "refresh_token",
        "refresh_token": refresh_token,
    }, auth=(CLIENT_ID, CLIENT_SECRET))


def fetch_profile(access_token):
    req = urllib.request.Request(f"{API_BASE}/me", method="GET")
    req.add_header("Authorization", f"Bearer {access_token}")
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode("utf-8"))


def get_access_token():
    with _token_lock:
        if _token_cache["access_token"] and _token_cache["expires_at"] - 60 > time.time():
            return _token_cache["access_token"]
        account = load_account()
        if not account:
            raise SpotifyAuthError("not_linked")
        result = refresh_access_token(account["refresh_token"])
        access_token = result["access_token"]
        expires_in = result.get("expires_in", 3600)
        new_refresh = result.get("refresh_token")
        if new_refresh and new_refresh != account["refresh_token"]:
            save_account(new_refresh, account["display_name"], account["product"])
        _token_cache["access_token"] = access_token
        _token_cache["expires_at"] = time.time() + expires_in
        return access_token


def spotify_api(method, path, params=None, body=None, retry=True):
    token = get_access_token()
    url = f"{API_BASE}{path}"
    if params:
        clean = {k: v for k, v in params.items() if v is not None}
        if clean:
            url += "?" + urllib.parse.urlencode(clean)
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("Authorization", f"Bearer {token}")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            raw = resp.read()
            if not raw.strip():
                return {}
            try:
                return json.loads(raw.decode("utf-8"))
            except ValueError:
                # Undocumented but real: POST .../player/queue returns 200
                # with a bare opaque token ("L_GEVkWQD3v0..."), not JSON, on
                # success. Every caller only reads specific keys via .get(),
                # so treating any non-JSON success body as {} is safe -- the
                # call still succeeded, we just have nothing structured back.
                return {}
    except urllib.error.HTTPError as exc:
        if exc.code == 401 and retry:
            with _token_lock:
                _token_cache["access_token"] = None
            return spotify_api(method, path, params=params, body=body, retry=False)
        raise SpotifyAPIError(exc.code, exc.read().decode("utf-8", "replace")) from exc


def cached_search(kind, query, limit, offset=0):
    key = (kind, query.lower(), limit, offset)
    now = time.time()
    with _search_cache_lock:
        hit = _search_cache.get(key)
        if hit and hit[0] > now:
            return hit[1]
    result = spotify_api("GET", "/search", params={"q": query, "type": kind, "limit": limit, "offset": offset})
    with _search_cache_lock:
        if len(_search_cache) > 200:
            _search_cache.clear()
        _search_cache[key] = (now + SEARCH_CACHE_TTL, result)
    return result


def fetch_artist_albums(artist_id, groups, limit_total=200, force=False):
    cache_key = f"artist_albums:{artist_id}:{groups}"
    cached = None if force else cache_get(cache_key)
    if cached is not None:
        return cached[:limit_total]
    albums = []
    seen = set()
    offset = 0
    while len(albums) < limit_total:
        page = spotify_api("GET", f"/artists/{artist_id}/albums",
                            params={"include_groups": groups, "limit": SPOTIFY_PAGE_LIMIT, "offset": offset})
        items = page.get("items", [])
        if not items:
            break
        for album in items:
            key = (normalize_title(album.get("name", "")), album.get("release_date", ""))
            if key in seen:
                continue
            seen.add(key)
            albums.append(album)
        if not page.get("next"):
            break
        offset += SPOTIFY_PAGE_LIMIT
    result = albums[:limit_total]
    cache_set(cache_key, result)
    return result


def fetch_album_meta(album_id, force=False):
    cache_key = f"album_meta:{album_id}"
    cached = None if force else cache_get(cache_key)
    if cached is not None:
        return cached
    album = spotify_api("GET", f"/albums/{album_id}")
    cache_set(cache_key, album)
    return album


def find_next_album_for_artist(artist_id, album_type, after_album_id):
    """Bounded (a single Spotify request, not fetch_artist_albums's full
    pagination) lookup used only by the lazy same-artist auto-continue
    trigger, so one automatic background event costs at most one request
    against the quota-limited artists/albums endpoint. Cached permanently
    under its own key either way, separate from fetch_artist_albums's cache
    (which covers the "album,single,compilation" combined groups a deliberate
    artist-page visit fetches, not the single group this needs)."""
    cache_key = f"artist_albums_page1:{artist_id}:{album_type}"
    albums = cache_get(cache_key)
    if albums is None:
        page = spotify_api("GET", f"/artists/{artist_id}/albums",
                            params={"include_groups": album_type, "limit": SPOTIFY_PAGE_LIMIT, "offset": 0})
        items = page.get("items", [])
        seen = set()
        albums = []
        for a in items:
            key = (normalize_title(a.get("name", "")), a.get("release_date", ""))
            if key in seen:
                continue
            seen.add(key)
            albums.append(a)
        cache_set(cache_key, albums)
    ordered = sorted(albums, key=lambda a: a.get("release_date") or "", reverse=True)
    ids = [a["id"] for a in ordered]
    if after_album_id not in ids:
        return None
    pos = ids.index(after_album_id)
    if pos + 1 >= len(ids):
        return None
    return ordered[pos + 1]


def track_summary(t):
    """Common {id, uri, name, image, artists, album_id, album_name, duration_ms}
    shape used by search/recently-played/queue -- all render via the same
    frontend trackRow()."""
    if not t:
        return None
    album = t.get("album") or {}
    images = album.get("images") or []
    return {"id": t.get("id"), "uri": t.get("uri"), "name": t.get("name"),
            "image": images[0]["url"] if images else None,
            "artists": [a["name"] for a in t.get("artists", [])],
            "album_id": album.get("id"), "album_name": album.get("name", ""),
            "duration_ms": t.get("duration_ms", 0)}


def fetch_album_tracks(album_id, limit_total=300, force=False):
    cache_key = f"album_tracks:{album_id}"
    cached = None if force else cache_get(cache_key)
    if cached is not None:
        return cached[:limit_total]
    tracks = []
    offset = 0
    while len(tracks) < limit_total:
        page = spotify_api("GET", f"/albums/{album_id}/tracks",
                            params={"limit": SPOTIFY_PAGE_LIMIT, "offset": offset})
        items = page.get("items", [])
        if not items:
            break
        tracks.extend(items)
        if not page.get("next"):
            break
        offset += SPOTIFY_PAGE_LIMIT
    result = tracks[:limit_total]
    cache_set(cache_key, result)
    return result


# ---------------------------------------------------------- dedup helpers --

_STRIP_WORDS = (r"remaster(?:ed)?(?: \d{4})?|\d{4} remaster(?:ed)?|live(?: at [^)\]]+)?|mono|stereo|"
                r"single version|album version|radio edit|explicit|clean|bonus track|"
                r"deluxe(?: edition)?|remix(?:ed)?|edit|anniversary edition|\d{4} version")
_STRIP_PATTERNS = [
    re.compile(r"\s*-\s*(" + _STRIP_WORDS + r")\s*$", re.I),
    re.compile(r"\s*\((" + _STRIP_WORDS + r")\)\s*$", re.I),
    re.compile(r"\s*\[(" + _STRIP_WORDS + r")\]\s*$", re.I),
]


def normalize_title(name):
    text = name or ""
    changed = True
    while changed:
        changed = False
        for pattern in _STRIP_PATTERNS:
            new_text = pattern.sub("", text).strip()
            if new_text != text:
                text, changed = new_text, True
    text = re.sub(r"[^\w\s]", "", text, flags=re.UNICODE).lower().strip()
    return re.sub(r"\s+", " ", text)


def _date_ordinal(date_str):
    parts = (date_str or "").split("-")
    try:
        year = int(parts[0]) if parts[0] else 9999
        month = int(parts[1]) if len(parts) > 1 and parts[1] else 1
        day = int(parts[2]) if len(parts) > 2 and parts[2] else 1
        return year * 10000 + month * 100 + day
    except ValueError:
        return 99990101


def build_dedup_tracks(artist_id, groups):
    # Spotify no longer exposes track `popularity` to Development Mode apps
    # (missing even from the singular /v1/tracks/{id} response, and the batch
    # /v1/tracks?ids=... endpoint is outright 403 for this app), so dedup can
    # only rank by album_type (studio album > single > compilation > appears_on)
    # and, within a type, the earliest release date -- i.e. prefer the original
    # release over a later reissue/remaster/deluxe repackaging.
    albums = fetch_artist_albums(artist_id, groups)
    entries = []
    for album in albums:
        for track in fetch_album_tracks(album["id"]):
            if not any(a.get("id") == artist_id for a in track.get("artists", [])):
                continue
            entries.append({
                "id": track["id"],
                "uri": track["uri"],
                "name": track["name"],
                "duration_ms": track.get("duration_ms", 0),
                "album_name": album["name"],
                "album_type": album.get("album_type", "album"),
                "release_date": album.get("release_date", ""),
                "image": (album.get("images") or [{}])[0].get("url"),
            })

    groups_map = {}
    for e in entries:
        groups_map.setdefault(normalize_title(e["name"]), []).append(e)

    def score(e):
        rank = ALBUM_TYPE_RANK.get(e["album_type"], 0)
        return (rank, -_date_ordinal(e["release_date"]))

    out = []
    for variants in groups_map.values():
        ranked = sorted(variants, key=score, reverse=True)
        best = ranked[0]
        out.append({
            "name": best["name"],
            "uri": best["uri"],
            "id": best["id"],
            "album_name": best["album_name"],
            "album_type": best["album_type"],
            "release_date": best["release_date"],
            "duration_ms": best["duration_ms"],
            "image": best["image"],
            "variant_count": len(ranked),
            "variants": [{"uri": v["uri"], "id": v["id"], "album_name": v["album_name"],
                          "album_type": v["album_type"], "release_date": v["release_date"]}
                         for v in ranked],
        })
    out.sort(key=lambda t: (t["release_date"] or "", t["name"].lower()))
    return out


# -------------------------------------------------------------- frontend --

# Same black-on-white-rounded-square visual language as files-server.py's
# FILES_ICON / MEDIA_ICON (stroke only, no fill besides the background).
SPOTIFY_ICON = b'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64">
<rect width="64" height="64" rx="14" fill="#ffffff"/>
<path d="M20 40 V24 M32 44 V16 M44 40 V28" fill="none" stroke="#000000" stroke-width="5" stroke-linecap="round"/>
</svg>'''

SPOTIFY_APPLE_ICON = base64.b64decode(
    'iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAAIEklEQVR4nO3dX0hT/x/H8bPj5sy5uRrmNCk1Yi2yIIKSrLsiIhhC'
    'iyK8C4oisgtNoou6k6gLJZIuugkvIhTqYjfRRVTSCKSyjSyNuXBSbS6a7a/787vw9/Xbd+69nW2enY87r8dd9XG98zz9nLOZZwpu'
    'laRSqdV6KCieQqFYhQcp/iGQBbOKTKSoD0YWa0LBiRTyYWhiLSogEV6MOYBBBXxJ51cT9owyIHwLyWPnQBnlQfhxFBQRsihLObeQ'
    '3DsHyihXOY9sjjhQhpxl21hQhkxQ5xdy50AZ8kEd68xxoAy5yXjE8SIYkDLEgW1DnlYe9/Q4UIacpR19nFaA9O9zGOwZsGT5mS12'
    'DiAhDki3fA7h034NwP3TA3YOICk4bBtAwM4BJB7bBlCwcwAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQBJKfUADIlE'
    'IvF4vLKysrKyUupZmIA4uGg0arfbx8fHJycnA4GA0WjcuXNne3v7jh07VuWefGtYSt5mZ2d7e3uNRmPap6Wtre3+/fvhcFjqAaUk'
    '6zhmZ2c7Ozt5PvOFl1arvXnzZigUknpMycj3gjQajQ4ODj59+jSZTGZcsLCwMDg4aLPZSjwYO+Qbh91uf/jwIVXGkvn5+YGBgfn5'
    '+ZJNxRT5xjE+Pv79+/ecyz58+DA9PV2CeRgk0zgikcjnz5+FrFxcXPz06ZPY87BJpnHE43G/3y9kZSKRELiy/Mg0DhACcQAJcQAJ'
    'cQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQCJ9f99nkql/H7/9PS0z+fT6XRbt26tr6+vqKiQei5ZYDqOmZmZBw8e2Gw2'
    'n88XDofVarVerz9w4MCFCxd2794t9XTlj904xsbG+vr6xsbGUn/d79Dj8TidzpcvX964cePkyZNy/7kSkTF6zeF0Ont6el6/fp3K'
    'dCfMycnJvr6+58+fl34wWWExjnA4fPfu3Tdv3mRZMzMzc/v27bm5uZJNJUMsxuFyuUZHR3Mue/Hixdu3b0swj2yxGIfT6fz9+3fO'
    'ZbFYbGJiIvsPnkAxWIzD5XIlEgkhK91udywWE3se2WIxDuHHOxaLZbxihVXBYhzACMQBJHZfBCtLgUDA6/Umk8kNGzYYDAapx8kB'
    'cZTI1NTU8PCww+HweDzxeNxoNJpMJqvVum/fPmZf50UcokskEiMjI/39/e/fv//792022+joaHd399mzZ2tqaiSaLhvEIbqRkZHL'
    'ly//+PFj5R+53e7r16+HQqGenh6VSlX62bLDBam4pqam+vv7M5axJBgMDgwMvHr1qpRTCYQ4xDU8PJx2Nlnp58+f9+7dW1xcLMlE'
    'eUAcIgoEAg6HQ8jKL1++MPhNRMQhIq/X6/F4hKz89euX2+0We558IQ4RxWKxSCQiZGU8Hg+Hw2LPky/EwQoGX+1AHEBCHEBCHEBC'
    'HEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBCHEBC'
    'HEBCHEBCHEBCHKxg8CbuLMah1WoF3smkpqaG51n8JyxRq9Xr1q0TslKlUlVXV4s9T75Y/Mxu375dqRR0g1STyaRWq8Wep2B1dXWb'
    'Nm0SsnL9+vVbtmwRe558sRiHyWRqamrKuUyv17e1tZVgnoJptVqB72JpNpsbGxvFnidfLMaxefPm8+fP59wSTp06tX///tKMVLAz'
    'Z87s3bs3+5rGxsaLFy8K3CxLicU4eJ7v6uqyWq1Zrjw6Ojq6u7s1Gk0pBytAa2vrtWvXspxcdDrdlStX2tvbSzmVUClWzc3NXbp0'
    'aeX7TlRXV1ut1omJiWIefGFh4cSJE0I+PyqV6s6dO8X8XYlE4smTJxnfHWHbtm1DQ0OhUKiYxxcPc1vZsoaGhlu3bh05cuTZs2df'
    'v36dn5/XarXNzc0HDx60WCy1tbVSDygUz/MWi2XXrl2PHz/++PHjt2/fEolEQ0OD2Wzu7Ozcs2eP1AOS2I2D47iqqqrjx48fO3bM'
    '5/MFg8GqqiqDwVBZWSn1XIVoaWm5evVqMBj0+/3JZLK2tlav10s9VA5Mx7GE5/mNGzdKPcXq0Gg07F8nLWPxghQYId84UoJfrha+'
    'sszINA6FQiHwpVXhK8uPTONQq9XNzc1CViqVytbWVpHHYZRM41AqlW1tbULeVs1gMJjN5hKMxCCZxsFxXEdHx6FDh3IuO336tJBv'
    '9JQl+cbR1NTU29ub/Xuhhw8fPnfuHIPv21giUr9EK6VkMvno0aOMZ42KioqjR4++e/dO6hmlpEjJ9XnaMofDMTQ0ZLfb/X5/NBrV'
    'aDT19fUWi6Wrq8toNEo9nZQQB8dxXDKZ9Hq9Lpfrz58/dXV1LS0tOp1O6qGkhziAJN8LUsgJcQAJcQAJcQAJcQAJcQAJcQAJcQAJ'
    'cQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQAJcQCJF3iXcZAh7BxA4jmOw+YBKykUCuwcQPp/HNg8'
    '4G9LPWDngHTLOwW/8rcAlvxn50Af8HcDOK3Av9J2h/Q4sHnAsgw7B/qQp5XHHacV4DhiR8gcBzYP4DguRwS412DZy7IR4LQia9lP'
    'ETniwPlFzgQde5xcyo+QL/s8NgYkUjYEnhDyO2ugj7Uur+uEQi4pkMgale8VZOHXm0hkDSnsiUXhT2XxRGatKPhIrcIBxhbCrCK/'
    'gP8H74XWaTHJpfIAAAAASUVORK5CYII='
)

SPOTIFY_PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no">
<title>Spotify</title>
<link rel="icon" href="/spotify-api/icon-v2.svg" type="image/svg+xml" sizes="any">
<link rel="apple-touch-icon" sizes="180x180" href="/spotify-api/apple-touch-icon-v2.png">
<style>
  * { box-sizing:border-box; }
  body { font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;
         touch-action:manipulation; background:#fff; color:#000; min-height:100vh;
         padding:20px 20px 96px; }
  header { display:flex; align-items:center; justify-content:space-between; margin-bottom:14px; gap:12px; }
  .logo { height:32px; width:32px; display:block; }
  .header-right { display:flex; align-items:center; gap:10px; }
  .panel { border:1px solid #000; padding:14px 16px; margin-bottom:20px; }
  .row { display:flex; align-items:center; gap:10px; flex-wrap:wrap; }
  .button { padding:8px 16px; border:1px solid #000; background:#fff; color:#000;
            font:inherit; font-size:14px; cursor:pointer; -webkit-appearance:none; appearance:none; }
  .button:hover { background:#f0f0f0; }
  .button.primary { background:#000; color:#fff; }
  .button.primary:hover { background:#222; }
  .button.danger { border-color:#c00; color:#c00; }
  .button.danger:hover { background:#c00; color:#fff; }
  .button.small { padding:4px 10px; font-size:12px; }
  .muted { color:#666; font-size:13px; }
  .icon-btn { display:inline-flex; align-items:center; justify-content:center; width:38px; height:38px;
              border:1px solid #000; background:#fff; color:#000; cursor:pointer; padding:0; flex:none;
              -webkit-appearance:none; appearance:none; }
  .icon-btn:hover { background:#f0f0f0; }
  .icon-btn.active { background:#000; color:#fff; }
  .icon-btn.active:hover { background:#222; }
  input[type=text] { flex:1; min-width:160px; padding:9px 10px; border:1px solid #999; font:inherit; font-size:15px; }
  h2 { font-size:15px; margin:22px 0 10px; }
  ul.list { list-style:none; margin:0; padding:0; }
  ul.list li { display:flex; align-items:center; gap:10px; padding:8px 0; border-bottom:1px solid #eee; }
  ul.list li:last-child { border-bottom:none; }
  ul.list li.fav-item { flex-wrap:wrap; }
  select { padding:6px 8px; border:1px solid #999; background:#fff; color:#000; font:inherit; font-size:13px; -webkit-appearance:none; appearance:none; }
  .genre-tags { display:flex; flex-wrap:wrap; gap:4px; width:100%; margin:2px 0 0 50px; }
  .chip { padding:2px 8px; border:1px solid #999; background:#fff; color:#666; font:inherit; font-size:11px;
          cursor:pointer; -webkit-appearance:none; appearance:none; }
  .chip:hover { border-color:#000; color:#000; }
  .chip.active { background:#000; border-color:#000; color:#fff; }
  .cover { width:40px; height:40px; object-fit:cover; background:#eee; flex:none; }
  .cover.lg { width:64px; height:64px; }
  .meta { flex:1; min-width:0; cursor:pointer; }
  .meta .title { font-size:14px; }
  .meta .sub { color:#666; font-size:12px; margin-top:2px; }
  .badge { color:#999; font-size:11px; border:1px solid #ccc; padding:1px 6px; margin-left:6px; }
  .variants { margin:6px 0 0; padding-left:50px; font-size:12px; color:#666; }
  .variants div { padding:2px 0; cursor:pointer; }
  .variants div:hover { color:#000; }
  .empty { color:#999; padding:14px 0; text-align:center; font-size:13px; }
  .error { color:#b00020; font-size:13px; margin-top:8px; }
  .toast { position:fixed; bottom:90px; left:50%; transform:translateX(-50%); background:#000; color:#fff;
           padding:8px 16px; font-size:13px; z-index:1000; max-width:90vw; text-align:center; }
  .crumbs { font-size:13px; color:#666; margin-bottom:6px; }
  .crumbs a { color:#000; text-decoration:none; cursor:pointer; }
  #nowplaying { position:fixed; left:0; right:0; bottom:0; background:#fff; border-top:1px solid #000;
                padding:8px 16px 10px; display:none; flex-direction:column; gap:6px; }
  #nowplaying .main-row { display:flex; align-items:center; gap:12px; }
  #nowplaying .track { flex:1; min-width:0; }
  #nowplaying .track .title { font-size:13px; }
  #nowplaying .track .title:hover { text-decoration:underline; }
  #nowplaying .track .sub { font-size:11px; color:#666; }
  #nowplaying .controls { display:flex; align-items:center; gap:6px; flex:none; }
  #nowplaying .controls button { border:1px solid #000; background:#fff; color:#000; padding:6px 10px;
                                  font:inherit; font-size:12px; cursor:pointer; -webkit-appearance:none; appearance:none; }
  #nowplaying .controls button:hover { background:#f0f0f0; }
  #nowplaying .controls button#npPlay { min-width:52px; }
  #nowplaying .volume { display:flex; align-items:center; flex:none; }
  #nowplaying .volume input[type=range] { width:70px; accent-color:#000; }
  #nowplaying .progress-row { display:flex; align-items:center; gap:8px; order:-1; }
  #nowplaying .progress-row input[type=range] { flex:1; min-width:0; accent-color:#000; touch-action:none; cursor:pointer; }
  #nowplaying .progress-row .time { font-size:11px; color:#666; font-variant-numeric:tabular-nums; flex:none; min-width:34px; }
  #nowplaying .progress-row .time.start { text-align:left; }
  #nowplaying .progress-row .time.end { text-align:right; }
  @media (max-width: 520px) {
    #nowplaying .track .sub { display:none; }
    #nowplaying .controls button { padding:6px 8px; font-size:11px; }
    #searchPanel input[type=text] { flex-basis:100%; }
  }
</style>
</head>
<body>
<header>
  <img src="/spotify-api/icon-v2.svg" alt="Spotify" class="logo">
  <div class="header-right">
    <button class="icon-btn" id="recentlyPlayedButton" title="Recently played"><svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="10" r="7.5" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M10 6v4l3 2" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg></button>
    <button class="icon-btn" id="queueViewButton" title="Play queue"><svg width="18" height="18" viewBox="0 0 20 20"><line x1="4" y1="6" x2="16" y2="6" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><line x1="4" y1="10" x2="16" y2="10" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><line x1="4" y1="14" x2="12" y2="14" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button>
    <button class="icon-btn" id="favoritesButton" title="Favorite albums"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 2.5l2.35 4.76 5.25.76-3.8 3.7.9 5.23L10 14.5l-4.7 2.45.9-5.23-3.8-3.7 5.25-.76z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round"/></svg></button>
    <button class="icon-btn" id="connectionButton" title="Connect Spotify"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 3v6" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" fill="none"/><path d="M5.5 6.5a6 6 0 1 0 9 0" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" fill="none"/></svg></button>
  </div>
</header>

<div id="connectPanel" class="panel" style="display:none"></div>

<div id="searchPanel" class="panel" style="display:none">
  <div class="row">
    <input type="text" id="searchInput">
    <button class="icon-btn" id="searchArtistButton" title="Search artists"><svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="6.8" r="3.1" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M3.5 17c0-3.6 2.9-6 6.5-6s6.5 2.4 6.5 6" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button>
    <button class="icon-btn" id="searchAlbumButton" title="Search albums"><svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="10" r="7.2" fill="none" stroke="currentColor" stroke-width="1.6"/><circle cx="10" cy="10" r="2" fill="none" stroke="currentColor" stroke-width="1.6"/></svg></button>
    <button class="icon-btn" id="searchTrackButton" title="Search tracks"><svg width="18" height="18" viewBox="0 0 20 20"><circle cx="6.5" cy="15" r="2.3" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M8.8 15V4.5L15 3v3" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linejoin="round" stroke-linecap="round"/></svg></button>
    <button class="icon-btn" id="coversButton" title="Show covers"><svg width="18" height="18" viewBox="0 0 20 20"><rect x="2" y="4" width="16" height="12" rx="1" fill="none" stroke="currentColor" stroke-width="1.6"/><circle cx="7" cy="9" r="1.5" fill="currentColor"/><path d="M3 15l4.5-4.5 3 3 3-4 3.5 5.5" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linejoin="round" stroke-linecap="round"/></svg></button>
  </div>
  <div id="searchError" class="error"></div>
</div>

<div id="view"></div>

<div id="nowplaying">
  <div class="main-row">
    <img id="npCover" class="cover" style="display:none">
    <div class="track">
      <div class="title" id="npTitle">-</div>
      <div class="sub" id="npSub"></div>
    </div>
    <div class="controls">
      <button id="npPrev">Prev</button>
      <button id="npPlay">Play</button>
      <button id="npNext">Next</button>
    </div>
    <div class="volume">
      <input type="range" id="npVolume" min="0" max="100" value="70">
    </div>
  </div>
  <div class="progress-row">
    <span class="time start" id="npElapsed">0:00</span>
    <input type="range" id="npProgress" min="0" max="1000" value="0">
    <span class="time end" id="npDuration">0:00</span>
  </div>
</div>

<script src="https://sdk.scdn.co/spotify-player.js"></script>
<script>
function getClientId() {
  let id = localStorage.getItem('spotify_client_id');
  if (!id) { id = (crypto.randomUUID ? crypto.randomUUID() : String(Math.random()).slice(2)); localStorage.setItem('spotify_client_id', id); }
  return id;
}

const state = {
  linked: false,
  showCovers: localStorage.getItem('spotify_show_covers') !== '0',
  deviceId: null,
  devices: [],
  player: null,
  clientId: getClientId(),
  albumQueue: null, // {ids: [albumId, ...], pos: index} -- drives auto-advance to the next album
};

function api(path, opts) {
  return fetch(path, Object.assign({credentials: 'same-origin'}, opts || {})).then(async r => {
    let body = null;
    try { body = await r.json(); } catch (e) {}
    if (!r.ok) throw Object.assign(new Error((body && body.error) || r.statusText), {status: r.status, body});
    return body;
  });
}

function el(tag, cls, text) {
  const n = document.createElement(tag);
  if (cls) n.className = cls;
  if (text !== undefined) n.textContent = text;
  return n;
}

function iconButton(svg, title, cls) {
  const btn = el('button', cls || 'icon-btn');
  btn.title = title;
  btn.innerHTML = svg;
  return btn;
}

function fmtDuration(ms) {
  const s = Math.round(ms / 1000);
  return Math.floor(s / 60) + ':' + String(s % 60).padStart(2, '0');
}

function coverImg(url, cls) {
  const img = el('img', cls || 'cover');
  img.dataset.src = url || '';
  if (state.showCovers && url) { img.src = url; } else { img.style.display = 'none'; }
  return img;
}

function applyCoversVisibility() {
  document.querySelectorAll('img.cover, #npCover').forEach(img => {
    const src = img.dataset.src || '';
    if (state.showCovers && src) { img.src = src; img.style.display = ''; }
    else { img.style.display = 'none'; }
  });
}

// ---- link status / SDK bootstrap ----

// One icon button toggles between "Connect" and "Disconnect" instead of a
// separate connect panel + a plain text link, so it lines up with the other
// header icon buttons (recently played / queue / favorites) instead of
// taking its own row.
function renderAuthArea(status) {
  document.getElementById('connectPanel').style.display = 'none';
  const btn = document.getElementById('connectionButton');
  btn.classList.toggle('active', status.linked);
  btn.title = status.linked ? 'Disconnect Spotify' : 'Connect Spotify';
  btn.onclick = status.linked ? async () => {
    if (!confirm('Disconnect Spotify?')) return;
    await api('/spotify-api/logout', {method: 'POST'});
    location.reload();
  } : () => { window.location.href = '/spotify-api/login'; };
}

let sdkConnectTriggered = false;
let sdkPlayerReady = false;
let sdkPlayerWaiters = [];
let deviceReadyWaiters = [];

function initSDK() {
  window.onSpotifyWebPlaybackSDKReady = () => {
    const player = new Spotify.Player({
      name: 'V1 Spotify Player',
      getOAuthToken: cb => api('/spotify-api/player-token').then(d => cb(d.access_token)).catch(() => {}),
      volume: 0.7,
    });
    state.player = player;
    sdkPlayerReady = true;
    sdkPlayerWaiters.forEach(fn => fn());
    sdkPlayerWaiters = [];
    player.addListener('ready', ({device_id}) => {
      state.deviceId = device_id;
      deviceReadyWaiters.forEach(fn => fn(device_id));
      deviceReadyWaiters = [];
    });
    player.addListener('not_ready', () => { state.deviceId = null; });
    player.addListener('initialization_error', ({message}) => console.error('spotify init error', message));
    player.addListener('authentication_error', ({message}) => console.error('spotify auth error', message));
    player.addListener('account_error', ({message}) => console.error('spotify account error (Premium required)', message));
  };
}

function waitForPlayerObject(timeoutMs) {
  if (sdkPlayerReady) return Promise.resolve(true);
  return new Promise(resolve => {
    const timer = setTimeout(() => resolve(false), timeoutMs);
    sdkPlayerWaiters.push(() => { clearTimeout(timer); resolve(true); });
  });
}

// iOS/Safari requires connect() (and, where supported, activateElement()) to
// happen inside a real synchronous click handler or there is no audio at all --
// calling this is not a separate "Enable Playback" step for the user, it just
// has to be the very first statement of whichever click actually starts
// playback, so the browser still counts it as the same user gesture. If the
// sdk.scdn.co script itself hasn't finished loading yet (very first click,
// slow network), wait briefly for the Player object to exist -- best effort,
// since that wait technically happens outside the original gesture.
async function ensureAudioUnlocked() {
  if (sdkConnectTriggered) return;
  if (!sdkPlayerReady) await waitForPlayerObject(5000);
  if (!state.player || sdkConnectTriggered) return;
  sdkConnectTriggered = true;
  if (typeof state.player.activateElement === 'function') {
    try { state.player.activateElement(); } catch (e) {}
  }
  state.player.connect();
}

function waitForDeviceReady(timeoutMs) {
  if (state.deviceId) return Promise.resolve(state.deviceId);
  return new Promise(resolve => {
    const timer = setTimeout(() => resolve(null), timeoutMs);
    deviceReadyWaiters.push(id => { clearTimeout(timer); resolve(id); });
  });
}

async function refreshDevices() {
  try {
    const {items} = await api('/spotify-api/devices');
    state.devices = items;
  } catch (e) {}
}

// This browser's own SDK device is always the preferred playback target --
// that's the whole point of "whichever device you clicked Play on is the one
// that should make sound" -- so if we just triggered connect(), wait for this
// device to actually come online before falling back to whatever other
// Spotify Connect device happens to be active. The very first connect() on a
// device involves a fresh WebSocket handshake, auth, and (on some browsers) an
// EME session negotiation, which can legitimately take several seconds -- this
// is a one-time cold-start cost, not a retry loop, so it's worth a long wait.
async function ensureDevice() {
  if (state.deviceId) return state.deviceId;
  if (sdkConnectTriggered) {
    const id = await waitForDeviceReady(12000);
    if (id) return id;
  }
  await refreshDevices();
  const active = state.devices.find(d => d.is_active) || state.devices[0];
  if (!active) { alert('No available Spotify device. Please try again, or open Spotify on your phone/computer.'); return null; }
  return active.id;
}

async function playUris(uris, contextUri, offset) {
  // A raw uris-based queue (dedup list, "Play all") isn't part of any
  // album-to-album auto-advance context, so starting one clears it.
  if (uris) state.albumQueue = null;
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  const body = {device_id};
  if (contextUri) body.context_uri = contextUri; else body.uris = uris;
  if (offset !== undefined) body.offset = offset;
  await api('/spotify-api/player/play', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)});
  pollNowPlaying();
}

// ---- navigation ----
// A small back-stack of view descriptors ({type, ...ids}) drives both the
// in-app Back button and cross-device sync: whichever device navigates writes
// its descriptor to the server, every other device polling it re-fetches and
// renders the same thing through this same renderDescriptor() function.

let navStack = [];
let currentDescriptor = {type: 'home'};

async function renderDescriptor(d) {
  if (!d || d.type === 'home') { await loadRecentlyPlayed(); return; }
  if (d.type === 'search') { document.getElementById('searchInput').value = d.query || ''; await runSearch(d.query, d.kind || 'artist'); return; }
  if (d.type === 'artist') { await loadArtist(d.id, d.name); return; }
  if (d.type === 'album') { await loadAlbum(d.id, d.queueCtx); return; }
  if (d.type === 'dedup') { await loadDedup(d.id, d.name); return; }
  if (d.type === 'favorites') { await loadFavorites(); return; }
  if (d.type === 'queue') { await loadQueueView(); return; }
}

function pushViewState(view) {
  api('/spotify-api/view-state', {method: 'PUT', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({view, client_id: state.clientId})}).catch(() => {});
}

// Forward navigation: remember where we came from, switch, tell other devices.
async function goTo(descriptor) {
  navStack.push(currentDescriptor);
  currentDescriptor = descriptor;
  await renderDescriptor(descriptor);
  pushViewState(descriptor);
}

// Back: pop one level (defaults to home if the stack is empty).
async function goBack() {
  const prev = navStack.pop() || {type: 'home'};
  currentDescriptor = prev;
  await renderDescriptor(prev);
  pushViewState(prev);
}

// Replace the current view without pushing a new back-stack level (used by
// album-to-album auto-advance, which shouldn't pile up Back history).
async function replaceCurrent(descriptor) {
  currentDescriptor = descriptor;
  await renderDescriptor(descriptor);
  pushViewState(descriptor);
}

let lastAppliedViewAt = 0;

// Someone else navigated; mirror it locally. Our own Back history doesn't
// carry over since we don't know their navigation path, which is an
// acceptable tradeoff -- Back from here just goes Home.
async function applyRemoteView(view) {
  navStack = [];
  currentDescriptor = view || {type: 'home'};
  await renderDescriptor(currentDescriptor);
}

async function pollViewState() {
  try {
    const remote = await api('/spotify-api/view-state');
    if (remote.updated_by === state.clientId) { lastAppliedViewAt = remote.updated_at || lastAppliedViewAt; return; }
    if (!remote.updated_at || remote.updated_at <= lastAppliedViewAt) return;
    // Don't yank the search box away while this device is mid-typing.
    if (document.activeElement === document.getElementById('searchInput')) return;
    lastAppliedViewAt = remote.updated_at;
    await applyRemoteView(remote.view);
  } catch (e) {}
}
setInterval(pollViewState, 3000);

// ---- favorites ----

document.getElementById('favoritesButton').onclick = () => goTo({type: 'favorites'});
document.getElementById('recentlyPlayedButton').onclick = () => goTo({type: 'home'});
document.getElementById('queueViewButton').onclick = () => goTo({type: 'queue'});

async function loadQueueView() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const {currently_playing, queue} = await api('/spotify-api/player/queue');
    renderQueueView(currently_playing, queue);
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderQueueView(currentlyPlaying, queue) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  if (currentlyPlaying) {
    view.appendChild(el('h2', null, 'Now Playing'));
    const nowList = el('ul', 'list');
    nowList.appendChild(trackRow(currentlyPlaying));
    view.appendChild(nowList);
  }
  view.appendChild(el('h2', null, 'Up Next'));
  const list = el('ul', 'list');
  if (!queue.length) list.appendChild(el('li', 'empty', 'Nothing queued'));
  for (const t of queue) list.appendChild(trackRow(t));
  view.appendChild(list);
}

// Spotify rarely populates album-level genres, so favorites are tagged by
// hand from this fixed list instead of anything derived from the API --
// kept small on purpose, this is a personal library filter, not a taxonomy.
const COMMON_GENRES = ['Jazz', 'Rock', 'Pop', 'Classical', 'Electronic', 'Hip-Hop', 'Folk', 'Blues', 'Metal', 'Soul'];
const UNTAGGED = '__untagged__';
const UNKNOWN_ERA = '__unknown__';

function eraOf(releaseDate) {
  const year = releaseDate ? parseInt(releaseDate.slice(0, 4), 10) : NaN;
  return year ? (Math.floor(year / 10) * 10) + 's' : '';
}

let favoritesState = null;
let favoritesFilter = {artist: '', genre: '', era: ''};

async function loadFavorites() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const {items} = await api('/spotify-api/favorites');
    favoritesState = items;
    favoritesFilter = {artist: '', genre: '', era: ''};
    renderFavoritesView();
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function buildFilterSelect(options, selected, onChange) {
  const select = el('select');
  for (const [value, label] of options) {
    const opt = el('option', null, label);
    opt.value = value;
    if (value === selected) opt.selected = true;
    select.appendChild(opt);
  }
  select.onchange = () => onChange(select.value);
  return select;
}

function renderFavoritesView() {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Back'); back.onclick = () => goBack();
  crumbs.appendChild(back);
  view.appendChild(crumbs);
  view.appendChild(el('h2', null, 'Favorite Albums'));

  const artists = [...new Set(favoritesState.flatMap(a => a.artists || []))].sort();
  const eras = [...new Set(favoritesState.map(a => eraOf(a.release_date)).filter(Boolean))].sort();
  const hasUnknownEra = favoritesState.some(a => !eraOf(a.release_date));

  const filterRow = el('div', 'row');
  filterRow.style.marginBottom = '14px';
  filterRow.appendChild(buildFilterSelect(
    [['', 'All artists'], ...artists.map(a => [a, a])], favoritesFilter.artist,
    v => { favoritesFilter.artist = v; renderFavoritesView(); }));
  filterRow.appendChild(buildFilterSelect(
    [['', 'All genres'], ...COMMON_GENRES.map(g => [g, g]), [UNTAGGED, 'Untagged']], favoritesFilter.genre,
    v => { favoritesFilter.genre = v; renderFavoritesView(); }));
  const eraOptions = [['', 'All eras'], ...eras.map(e => [e, e])];
  if (hasUnknownEra) eraOptions.push([UNKNOWN_ERA, 'Unknown era']);
  filterRow.appendChild(buildFilterSelect(eraOptions, favoritesFilter.era,
    v => { favoritesFilter.era = v; renderFavoritesView(); }));
  view.appendChild(filterRow);

  const filtered = favoritesState.filter(a => {
    if (favoritesFilter.artist && !(a.artists || []).includes(favoritesFilter.artist)) return false;
    const genres = a.genres || [];
    if (favoritesFilter.genre === UNTAGGED && genres.length) return false;
    if (favoritesFilter.genre && favoritesFilter.genre !== UNTAGGED && !genres.includes(favoritesFilter.genre)) return false;
    const era = eraOf(a.release_date);
    if (favoritesFilter.era === UNKNOWN_ERA && era) return false;
    if (favoritesFilter.era && favoritesFilter.era !== UNKNOWN_ERA && era !== favoritesFilter.era) return false;
    return true;
  });

  const list = el('ul', 'list');
  if (!filtered.length) {
    list.appendChild(el('li', 'empty', favoritesState.length ? 'No favorites match these filters' : 'No favorites yet'));
  }
  for (const a of filtered) {
    const li = el('li', 'fav-item');
    li.appendChild(coverImg(a.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', a.name));
    meta.appendChild(el('div', 'sub', (a.artists || []).join(', ')));
    meta.onclick = () => goTo({type: 'album', id: a.id});
    li.appendChild(meta);
    const tags = el('div', 'genre-tags');
    for (const g of COMMON_GENRES) {
      const active = (a.genres || []).includes(g);
      const chip = el('button', active ? 'chip active' : 'chip', g);
      chip.onclick = async () => {
        const genres = a.genres || [];
        a.genres = active ? genres.filter(x => x !== g) : [...genres, g];
        await api('/spotify-api/favorites/' + a.id + '/genres', {method: 'PUT', headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({genres: a.genres})});
        renderFavoritesView();
      };
      tags.appendChild(chip);
    }
    li.appendChild(tags);
    list.appendChild(li);
  }
  view.appendChild(list);
}

// ---- search / browse ----

document.getElementById('coversButton').classList.toggle('active', state.showCovers);
document.getElementById('coversButton').onclick = () => {
  state.showCovers = !state.showCovers;
  localStorage.setItem('spotify_show_covers', state.showCovers ? '1' : '0');
  document.getElementById('coversButton').classList.toggle('active', state.showCovers);
  applyCoversVisibility();
};

// Search is split into three buttons (one Spotify API call each) instead of
// always querying all three types together, since most searches only care
// about one of them. Enter repeats whichever type was last used.
let lastSearchKind = 'artist';

function triggerSearch(kind) {
  const q = document.getElementById('searchInput').value.trim();
  if (q) goTo({type: 'search', query: q, kind});
}
document.getElementById('searchArtistButton').onclick = () => triggerSearch('artist');
document.getElementById('searchAlbumButton').onclick = () => triggerSearch('album');
document.getElementById('searchTrackButton').onclick = () => triggerSearch('track');
document.getElementById('searchInput').addEventListener('keydown', e => {
  if (e.key === 'Enter') triggerSearch(lastSearchKind);
});

// searchState holds the current single-type result set plus Spotify's
// has_more, so "More" can fetch and append the next page in place.
let searchState = null;

const SEARCH_KIND_LABEL = {artist: 'Artists', album: 'Albums', track: 'Tracks'};
const SEARCH_KIND_EMPTY = {artist: 'No artists', album: 'No albums', track: 'No tracks'};
const SEARCH_KIND_ROW = {artist: artistRow, album: albumRow, track: trackRow};

async function runSearch(query, kind) {
  const err = document.getElementById('searchError');
  err.textContent = '';
  if (!query) return;
  lastSearchKind = kind;
  try {
    const result = await api('/spotify-api/search/' + kind + 's?q=' + encodeURIComponent(query));
    searchState = {query, kind, items: result.items, has_more: result.has_more};
    renderSearchResults();
  } catch (e) { err.textContent = 'Search failed: ' + e.message; }
}

async function loadMoreSearch(btn) {
  btn.disabled = true;
  btn.textContent = 'Loading…';
  try {
    const page = await api('/spotify-api/search/' + searchState.kind + 's?q=' + encodeURIComponent(searchState.query) +
                            '&offset=' + searchState.items.length);
    searchState.items = searchState.items.concat(page.items);
    searchState.has_more = page.has_more;
    renderSearchResults();
  } catch (e) {
    btn.disabled = false;
    btn.textContent = 'More';
  }
}

function artistRow(a) {
  const li = el('li');
  li.appendChild(coverImg(a.image));
  const meta = el('div', 'meta');
  meta.appendChild(el('div', 'title', a.name));
  meta.appendChild(el('div', 'sub', (a.genres || []).slice(0, 3).join(', ') || 'Artist'));
  meta.onclick = () => goTo({type: 'artist', id: a.id, name: a.name});
  li.appendChild(meta);
  return li;
}

function albumRow(a) {
  const li = el('li');
  li.appendChild(coverImg(a.image));
  const meta = el('div', 'meta');
  meta.appendChild(el('div', 'title', a.name));
  meta.appendChild(el('div', 'sub', (a.artists || []).join(', ') + ' · ' + (a.release_date || '').slice(0, 4)));
  meta.onclick = () => goTo({type: 'album', id: a.id});
  li.appendChild(meta);
  return li;
}

// Appends to whatever's already playing instead of replacing it -- for
// queueing something up without interrupting the current track.
function showToast(message) {
  const toast = el('div', 'toast', message);
  document.body.appendChild(toast);
  setTimeout(() => toast.remove(), 2200);
}

function queueButton(uri) {
  const btn = el('button', 'button small', '+');
  btn.title = 'Add to queue';
  btn.onclick = async e => {
    e.stopPropagation();
    await ensureAudioUnlocked();
    const device_id = await ensureDevice();
    if (!device_id) return;
    btn.disabled = true;
    try {
      await api('/spotify-api/player/queue', {method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({uri, device_id})});
      showToast('Added to queue');
    } catch (err) {
      showToast('Could not add to queue: ' + err.message);
    } finally { btn.disabled = false; }
  };
  return btn;
}

function trackRow(t) {
  // Start the track's own album context at this track, same continuation
  // behavior as every other play entry point in the app.
  const playFromHere = () => playUris(null, 'spotify:album:' + t.album_id, {uri: t.uri});
  const li = el('li');
  li.appendChild(coverImg(t.image));
  const meta = el('div', 'meta');
  meta.appendChild(el('div', 'title', t.name));
  meta.appendChild(el('div', 'sub', t.artists.join(', ') + ' · ' + t.album_name + ' · ' + fmtDuration(t.duration_ms)));
  meta.onclick = playFromHere;
  li.appendChild(meta);
  const playBtn = el('button', 'button small', '▶'); playBtn.onclick = playFromHere;
  li.appendChild(playBtn);
  li.appendChild(queueButton(t.uri));
  return li;
}

async function loadRecentlyPlayed() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const {items} = await api('/spotify-api/recently-played');
    renderRecentlyPlayedView(items);
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderRecentlyPlayedView(items) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  view.appendChild(el('h2', null, 'Recently Played'));
  const list = el('ul', 'list');
  if (!items.length) list.appendChild(el('li', 'empty', 'Nothing played yet'));
  for (const t of items) list.appendChild(trackRow(t));
  view.appendChild(list);
}

function renderSearchResults() {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const {kind, items, has_more} = searchState;
  view.appendChild(el('h2', null, SEARCH_KIND_LABEL[kind]));
  const list = el('ul', 'list');
  if (!items.length) list.appendChild(el('li', 'empty', SEARCH_KIND_EMPTY[kind]));
  for (const item of items) list.appendChild(SEARCH_KIND_ROW[kind](item));
  view.appendChild(list);
  if (has_more) {
    const moreBtn = el('button', 'button small', 'More');
    moreBtn.style.marginTop = '8px';
    moreBtn.onclick = () => loadMoreSearch(moreBtn);
    view.appendChild(moreBtn);
  }
}

async function loadArtist(id, name, refresh) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const albums = await api('/spotify-api/artists/' + id + '/albums' + (refresh ? '?refresh=1' : ''));
    renderArtistView({id, name, albums: albums.items});
    if (refresh) showToast('Refreshed');
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderArtistView(artist) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Back'); back.onclick = () => goBack();
  crumbs.appendChild(back);
  view.appendChild(crumbs);
  const heading = el('div', 'row');
  heading.style.margin = '22px 0 10px';
  const artistTitle = el('h2', null, artist.name);
  artistTitle.style.margin = '0';
  heading.appendChild(artistTitle);
  const refreshBtn = iconButton('<svg width="14" height="14" viewBox="0 0 20 20"><path d="M15.5 5.5A7 7 0 1 0 17 10" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><path d="M15.5 2v4h-4" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg>',
    'Update cache', 'icon-btn small');
  refreshBtn.style.width = '26px'; refreshBtn.style.height = '26px';
  refreshBtn.onclick = () => loadArtist(artist.id, artist.name, true);
  heading.appendChild(refreshBtn);
  view.appendChild(heading);

  // Hidden for now: building a dedup list calls fetch_artist_albums *and*
  // fetch_album_tracks for every single album, which is by far the heaviest
  // consumer of this app's daily per-endpoint Spotify quota. The backend
  // route and loadDedup/renderDedupView are untouched -- this is just the
  // entry point, easy to re-add once Extended Quota Mode lifts that limit.
  //
  // const dedupBtn = el('button', 'button small', 'Build deduplicated track list');
  // dedupBtn.onclick = () => goTo({type: 'dedup', id: artist.id, name: artist.name});
  // view.appendChild(dedupBtn);

  const groups = {album: [], single: [], compilation: [], appears_on: []};
  for (const a of artist.albums) (groups[a.album_type] || groups.appears_on).push(a);

  for (const [label, items] of [['Albums', groups.album], ['Singles', groups.single], ['Compilations', groups.compilation]]) {
    if (!items.length) continue;
    view.appendChild(el('h2', null, label));
    const list = el('ul', 'list');
    // Playing any album in this group sets up auto-advance to the next one in
    // the same group (Albums -> next studio album, etc; groups don't mix).
    const ids = items.map(a => a.id);
    items.forEach((a, i) => {
      const li = el('li');
      li.appendChild(coverImg(a.image));
      const meta = el('div', 'meta');
      meta.appendChild(el('div', 'title', a.name));
      meta.appendChild(el('div', 'sub', (a.release_date || '').slice(0, 4) + ' · ' + a.total_tracks + ' tracks'));
      meta.onclick = () => goTo({type: 'album', id: a.id, queueCtx: {ids, pos: i}});
      li.appendChild(meta);
      list.appendChild(li);
    });
    view.appendChild(list);
  }
}

async function loadDedup(id, name) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Building deduplicated list…</div>';
  try {
    const {items} = await api('/spotify-api/artists/' + id + '/dedup-tracks');
    renderDedupView({id, name}, items);
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderDedupView(artist, items) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Back'); back.onclick = () => goBack();
  crumbs.appendChild(back);
  view.appendChild(crumbs);
  view.appendChild(el('h2', null, artist.name + ' · Deduplicated (' + items.length + ' songs)'));
  const playAll = el('button', 'button primary small', 'Play all');
  playAll.onclick = () => playUris(items.slice(0, 50).map(t => t.uri));
  view.appendChild(playAll);
  const list = el('ul', 'list');
  items.forEach((t, i) => {
    // Clicking a track queues it plus the rest of this (already-capped)
    // deduplicated list, so playback continues track-to-track instead of
    // stopping after the one song -- same continuation behavior as "Play all".
    const queueFrom = idx => items.slice(idx, idx + 50).map(x => x.uri);
    const li = el('li');
    li.appendChild(coverImg(t.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', t.name));
    const sub = el('div', 'sub', t.album_name + ' · ' + (t.release_date || '').slice(0, 4) + ' · ' + fmtDuration(t.duration_ms));
    if (t.variant_count > 1) sub.appendChild(el('span', 'badge', t.variant_count + ' versions'));
    meta.appendChild(sub);
    meta.onclick = () => playUris(queueFrom(i));
    li.appendChild(meta);
    const playBtn = el('button', 'button small', '▶'); playBtn.onclick = () => playUris(queueFrom(i));
    li.appendChild(playBtn);
    list.appendChild(li);
    if (t.variant_count > 1) {
      const variants = el('div', 'variants');
      for (const v of t.variants) {
        const row = el('div', null, v.album_name + ' (' + v.album_type + ', ' + (v.release_date || '').slice(0, 4) + ')');
        row.onclick = () => playUris([v.uri, ...queueFrom(i + 1)]);
        variants.appendChild(row);
      }
      list.appendChild(variants);
    }
  });
  view.appendChild(list);
}

async function loadAlbum(id, queueCtx, refresh) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const album = await api('/spotify-api/albums/' + id + (refresh ? '?refresh=1' : ''));
    state.albumQueue = queueCtx || null;
    await renderAlbumView(album);
    if (refresh) showToast('Refreshed');
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

async function renderAlbumView(album) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Back'); back.onclick = () => goBack();
  crumbs.appendChild(back);
  view.appendChild(crumbs);

  const header = el('div', 'row');
  header.appendChild(coverImg(album.image, 'cover lg'));
  const meta = el('div');
  meta.appendChild(el('div', 'title', album.name));
  meta.appendChild(el('div', 'sub', (album.artists || []).join(', ') + ' · ' + (album.release_date || '')));
  header.appendChild(meta);
  view.appendChild(header);

  const actions = el('div', 'row');
  actions.style.marginTop = '10px';
  const playAlbumBtn = el('button', 'button primary small', 'Play album');
  playAlbumBtn.onclick = () => playUris(null, 'spotify:album:' + album.id);
  actions.appendChild(playAlbumBtn);

  const favBtn = iconButton('<svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 2.5l2.35 4.76 5.25.76-3.8 3.7.9 5.23L10 14.5l-4.7 2.45.9-5.23-3.8-3.7 5.25-.76z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round"/></svg>', 'Add to favorites', 'icon-btn small');
  favBtn.style.width = '32px'; favBtn.style.height = '32px';
  let favorited = false;
  try { const st = await api('/spotify-api/favorites/' + album.id); favorited = !!st.favorited; } catch (e) {}
  const syncFavBtn = () => {
    favBtn.classList.toggle('active', favorited);
    favBtn.title = favorited ? 'Remove from favorites' : 'Add to favorites';
  };
  syncFavBtn();
  favBtn.onclick = async () => {
    favorited = !favorited;
    syncFavBtn();
    if (favorited) {
      // Send the full album + tracks already on screen so the backend can
      // cache it and never has to call Spotify again for this album.
      await api('/spotify-api/favorites/' + album.id, {method: 'PUT', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({name: album.name, artists: album.artists, image: album.image,
                               album_type: album.album_type, release_date: album.release_date, tracks: album.tracks})});
    } else {
      await api('/spotify-api/favorites/' + album.id, {method: 'DELETE'});
    }
  };
  actions.appendChild(favBtn);

  const refreshBtn = iconButton('<svg width="14" height="14" viewBox="0 0 20 20"><path d="M15.5 5.5A7 7 0 1 0 17 10" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><path d="M15.5 2v4h-4" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg>',
    'Update cache', 'icon-btn small');
  refreshBtn.style.width = '32px'; refreshBtn.style.height = '32px';
  refreshBtn.onclick = () => loadAlbum(album.id, state.albumQueue, true);
  actions.appendChild(refreshBtn);
  view.appendChild(actions);

  const list = el('ul', 'list');
  for (const t of album.tracks) {
    // Start the real album context at this track (not just a single-track
    // queue), so playback continues through the rest of the album afterward --
    // same continuation behavior as "Play album".
    const playFromHere = () => playUris(null, 'spotify:album:' + album.id, {uri: t.uri});
    const li = el('li');
    const meta2 = el('div', 'meta');
    meta2.appendChild(el('div', 'title', t.track_number + '. ' + t.name));
    meta2.appendChild(el('div', 'sub', (t.artists || []).join(', ') + ' · ' + fmtDuration(t.duration_ms)));
    meta2.onclick = playFromHere;
    li.appendChild(meta2);
    const playBtn = el('button', 'button small', '▶'); playBtn.onclick = playFromHere;
    li.appendChild(playBtn);
    li.appendChild(queueButton(t.uri));
    list.appendChild(li);
  }
  view.appendChild(list);
}

// Album finished with nothing next queued by Spotify itself -- if it was
// played from an artist's album list, auto-advance to the next album in that
// same list, replacing the current view without adding Back history.
async function advanceAlbumQueue(finishedAlbumId) {
  const queue = state.albumQueue;
  if (queue) {
    const nextPos = queue.pos + 1;
    if (nextPos < queue.ids.length) {
      const nextId = queue.ids[nextPos];
      await replaceCurrent({type: 'album', id: nextId, queueCtx: {ids: queue.ids, pos: nextPos}});
      await playUris(null, 'spotify:album:' + nextId);
      return;
    }
    state.albumQueue = null;
    // Curated group exhausted -- fall through to the same-artist lookup below
    // instead of just stopping.
  }
  // No known queue context at all (album reached via search/recently-played/
  // queue rather than browsing the artist), or the curated group just ran
  // out: look up "the next album by this artist" on demand, once, right now
  // that it's actually needed -- server-side this is cached permanently and
  // bounded to a single Spotify request on a cold cache.
  if (!finishedAlbumId) return;
  try {
    const result = await api('/spotify-api/albums/' + finishedAlbumId + '/next-in-artist');
    if (result.next) {
      await replaceCurrent({type: 'album', id: result.next.id});
      await playUris(null, 'spotify:album:' + result.next.id);
    }
  } catch (e) {}
}

// ---- now playing / transport ----

document.getElementById('npPrev').onclick = async () => {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/player/previous', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
};
document.getElementById('npNext').onclick = async () => {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/player/next', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
};
async function togglePlayPause() {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  const np = await api('/spotify-api/player/now-playing');
  if (np.playing) {
    await api('/spotify-api/player/pause', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  } else if (np.live === false && np.track) {
    // np.live===false means this is the cached snapshot from before a reload
    // -- this device_id is brand new and was never given a context to resume,
    // so a bare "play" has nothing to continue. Explicitly restart the same
    // track at its saved position instead of silently doing nothing.
    const body = {device_id, position_ms: np.progress_ms || 0};
    if (np.track.album_id) { body.context_uri = 'spotify:album:' + np.track.album_id; body.offset = {uri: np.track.uri}; }
    else { body.uris = [np.track.uri]; }
    await api('/spotify-api/player/play', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)});
  } else {
    await api('/spotify-api/player/play', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  }
  pollNowPlaying();
}
document.getElementById('npPlay').onclick = togglePlayPause;

// Spacebar play/pause, except while actually typing (a text input/textarea
// focused, or a button mid-activation via a real space keypress on it).
document.addEventListener('keydown', e => {
  if (e.code !== 'Space' && e.key !== ' ') return;
  const tag = (document.activeElement && document.activeElement.tagName) || '';
  if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'BUTTON') return;
  e.preventDefault();
  togglePlayPause();
});
document.getElementById('npVolume').onchange = async e => {
  const device_id = await ensureDevice();
  if (!device_id) return;
  api('/spotify-api/player/volume?value=' + e.target.value + '&device_id=' + encodeURIComponent(device_id), {method: 'PUT'});
};

// npState holds the last poll's snapshot; a fast local timer interpolates the
// visible position between 5s polls so the progress bar moves smoothly
// instead of jumping once every 5 seconds. wasPlayingTick tracks the previous
// tick's is_playing so we can edge-detect "playback just stopped" once, to
// drive album-to-album auto-advance without re-triggering every poll.
let npState = null;
let wasPlayingTick = false;

async function pollNowPlaying() {
  try {
    const np = await api('/spotify-api/player/now-playing');
    const bar = document.getElementById('nowplaying');
    if (!np.track) {
      // Only true when nothing has ever played this session (no server-side
      // cache to fall back to yet) -- once something has played, the backend
      // always returns that last snapshot instead of an empty track.
      bar.style.display = 'none';
      wasPlayingTick = false;
      npState = null;
      return;
    }
    bar.style.display = 'flex';
    const cover = document.getElementById('npCover');
    cover.dataset.src = np.track.image || '';
    if (state.showCovers && np.track.image) { cover.src = np.track.image; cover.style.display = ''; } else { cover.style.display = 'none'; }
    const npTitle = document.getElementById('npTitle');
    npTitle.textContent = np.track.name;
    npTitle.onclick = np.track.album_id ? (() => goTo({type: 'album', id: np.track.album_id})) : null;
    npTitle.style.cursor = np.track.album_id ? 'pointer' : '';
    document.getElementById('npSub').textContent = np.track.artists.join(', ') + ' · ' + (np.device || '');
    document.getElementById('npPlay').textContent = np.playing ? 'Pause' : 'Play';
    const nearEnd = np.track.duration_ms && (np.progress_ms >= np.track.duration_ms - 2000);
    const justStopped = wasPlayingTick && !np.playing;
    wasPlayingTick = np.playing;
    npState = {progressMs: np.progress_ms || 0, durationMs: np.track.duration_ms || 0, playing: np.playing, at: Date.now()};
    if (justStopped && nearEnd) await advanceAlbumQueue(np.track.album_id);
  } catch (e) {}
}
setInterval(pollNowPlaying, 5000);

// While the user is actively dragging the thumb, the 250ms auto-render must
// not fight the drag by snapping the value back to the last poll's position.
let draggingProgress = false;
const progressInput = document.getElementById('npProgress');

progressInput.addEventListener('input', () => {
  draggingProgress = true;
  document.getElementById('npElapsed').textContent = fmtDuration(Number(progressInput.value));
});
progressInput.addEventListener('change', async () => {
  const position_ms = Math.round(Number(progressInput.value));
  const device_id = await ensureDevice();
  draggingProgress = false;
  if (!device_id) return;
  await api('/spotify-api/player/seek?position_ms=' + position_ms + '&device_id=' + encodeURIComponent(device_id), {method: 'PUT'});
  if (npState) { npState.progressMs = position_ms; npState.at = Date.now(); }
});

function renderProgress() {
  const elapsedEl = document.getElementById('npElapsed');
  const durationEl = document.getElementById('npDuration');
  if (!npState || !npState.durationMs) {
    if (!draggingProgress) { progressInput.value = 0; elapsedEl.textContent = '0:00'; }
    durationEl.textContent = '0:00';
    return;
  }
  progressInput.max = npState.durationMs;
  durationEl.textContent = fmtDuration(npState.durationMs);
  if (draggingProgress) return;
  let pos = npState.progressMs;
  if (npState.playing) pos += Date.now() - npState.at;
  pos = Math.max(0, Math.min(pos, npState.durationMs));
  progressInput.value = pos;
  elapsedEl.textContent = fmtDuration(pos);
}
setInterval(renderProgress, 250);

// ---- boot ----

(async function boot() {
  initSDK();
  try {
    const status = await api('/spotify-api/status');
    state.linked = status.linked;
    renderAuthArea(status);
    if (status.linked) {
      document.getElementById('searchPanel').style.display = '';
      pollNowPlaying();
      const remote = await api('/spotify-api/view-state');
      if (remote.view) { lastAppliedViewAt = remote.updated_at || 0; await applyRemoteView(remote.view); }
    }
  } catch (e) {
    document.getElementById('connectPanel').style.display = '';
    document.getElementById('connectPanel').textContent = 'Failed to load status: ' + e.message;
  }
})();
</script>
</body>
</html>
"""


# ------------------------------------------------------------------ http --

class Handler(BaseHTTPRequestHandler):
    server_version = "V1Spotify/1.0"

    def log_message(self, fmt, *args):
        print(f"{self.address_string()} - {fmt % args}", flush=True)

    def send_json(self, status, value):
        body = json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def send_html(self, content):
        body = content.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def send_icon(self, body):
        self.send_response(200)
        self.send_header("Content-Type", "image/svg+xml; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "public, max-age=86400")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(body)

    def send_apple_icon(self, body):
        self.send_response(200)
        self.send_header("Content-Type", "image/png")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "public, max-age=86400")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(body)

    def get_cookie(self, name):
        raw = self.headers.get("Cookie", "")
        for part in raw.split(";"):
            part = part.strip()
            if part.startswith(name + "="):
                return part[len(name) + 1:]
        return None

    def read_json_body(self):
        try:
            length = int(self.headers.get("Content-Length", "0") or "0")
        except ValueError:
            length = 0
        if length <= 0 or length > 64 * 1024:
            return {}
        raw = self.rfile.read(length)
        if not raw:
            return {}
        try:
            return json.loads(raw.decode("utf-8"))
        except ValueError:
            return {}

    def safe(self, fn):
        try:
            fn()
        except SpotifyAuthError:
            self.send_json(409, {"error": "not_linked"})
        except SpotifyAPIError as exc:
            status = exc.status if 400 <= exc.status < 600 else 502
            self.send_json(status, {"error": "spotify_api_error", "detail": exc.payload[:500]})
        except Exception as exc:
            self.send_json(500, {"error": "internal_error", "detail": str(exc)[:300]})

    # -- GET --

    def do_GET(self):
        self.safe(self._do_GET)

    def _do_GET(self):
        parsed = urlparse(self.path)
        path, query = parsed.path, parse_qs(parsed.query)

        if path == "/health":
            self.send_json(200, {"ok": True}); return
        if path in ("/spotify", "/spotify/"):
            self.send_html(SPOTIFY_PAGE); return
        if path == "/spotify-api/icon-v2.svg":
            self.send_icon(SPOTIFY_ICON); return
        if path == "/spotify-api/apple-touch-icon-v2.png":
            self.send_apple_icon(SPOTIFY_APPLE_ICON); return
        if path == "/spotify-api/status":
            self.handle_status(); return
        if path == "/spotify-api/login":
            self.handle_login(); return
        if path == "/spotify-api/callback":
            self.handle_callback(query); return
        if path == "/spotify-api/player-token":
            self.handle_player_token(); return
        if path == "/spotify-api/search/artists":
            self.handle_search("artist", query); return
        if path == "/spotify-api/search/albums":
            self.handle_search("album", query); return
        if path == "/spotify-api/search/tracks":
            self.handle_search("track", query); return
        if path == "/spotify-api/devices":
            self.handle_devices(); return
        if path == "/spotify-api/recently-played":
            self.handle_recently_played(); return
        if path == "/spotify-api/player/queue":
            self.handle_queue(); return
        if path == "/spotify-api/player/now-playing":
            self.handle_now_playing(); return
        if path == "/spotify-api/view-state":
            self.send_json(200, get_view_state()); return
        if path == "/spotify-api/favorites":
            self.send_json(200, {"items": list_favorites()}); return
        match = ARTIST_ALBUMS_RE.match(path)
        if match:
            self.handle_artist_albums(match.group(1), query); return
        match = ARTIST_DEDUP_RE.match(path)
        if match:
            self.handle_dedup(match.group(1), query); return
        match = NEXT_IN_ARTIST_RE.match(path)
        if match:
            self.handle_next_in_artist(match.group(1)); return
        match = ALBUM_RE.match(path)
        if match:
            self.handle_album(match.group(1), query); return
        match = FAVORITE_RE.match(path)
        if match:
            self.send_json(200, {"favorited": is_favorite(match.group(1))}); return
        self.send_json(404, {"error": "not_found"})

    def handle_status(self):
        account = load_account()
        if not account:
            self.send_json(200, {"linked": False}); return
        self.send_json(200, {
            "linked": True,
            "display_name": account["display_name"],
            "product": account["product"],
            "premium": account["product"] == "premium",
        })

    def handle_login(self):
        state = secrets.token_urlsafe(24)
        params = {
            "client_id": CLIENT_ID, "response_type": "code", "redirect_uri": REDIRECT_URI,
            "scope": SCOPES, "state": state, "show_dialog": "false",
        }
        self.send_response(302)
        self.send_header("Location", AUTHORIZE_URL + "?" + urllib.parse.urlencode(params))
        self.send_header("Set-Cookie", f"spotify_oauth_state={state}; Path=/spotify-api; Max-Age=600; "
                                        f"HttpOnly; Secure; SameSite=Lax")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def handle_callback(self, query):
        error = query.get("error", [None])[0]
        code = query.get("code", [None])[0]
        state = query.get("state", [None])[0]
        expected = self.get_cookie("spotify_oauth_state")
        if error or not code or not state or not expected or state != expected:
            self._redirect("/spotify?spotify_error=" + urllib.parse.quote(error or "state_mismatch"))
            return
        token_result = exchange_code(code)
        access_token = token_result["access_token"]
        refresh_token = token_result.get("refresh_token")
        if not refresh_token:
            self._redirect("/spotify?spotify_error=no_refresh_token"); return
        profile = fetch_profile(access_token)
        save_account(refresh_token, profile.get("display_name"), profile.get("product"))
        with _token_lock:
            _token_cache["access_token"] = access_token
            _token_cache["expires_at"] = time.time() + token_result.get("expires_in", 3600)
        self.send_response(302)
        self.send_header("Location", "/spotify")
        self.send_header("Set-Cookie", "spotify_oauth_state=; Path=/spotify-api; Max-Age=0")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def _redirect(self, location):
        self.send_response(302)
        self.send_header("Location", location)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def handle_player_token(self):
        token = get_access_token()
        with _token_lock:
            expires_in = max(0, int(_token_cache["expires_at"] - time.time()))
        self.send_json(200, {"access_token": token, "expires_in": expires_in})

    def handle_search(self, kind, query):
        q = (query.get("q", [""])[0] or "").strip()
        if not q:
            self.send_json(400, {"error": "missing_query"}); return
        try:
            limit = min(max(int(query.get("limit", [str(SPOTIFY_PAGE_LIMIT)])[0]), 1), SPOTIFY_PAGE_LIMIT)
        except ValueError:
            limit = SPOTIFY_PAGE_LIMIT
        try:
            offset = max(0, int(query.get("offset", ["0"])[0]))
        except ValueError:
            offset = 0
        result = cached_search(kind, q, limit, offset)
        block = result.get(kind + "s") or {}
        items = block.get("items", [])
        total = block.get("total", len(items))
        out = []
        for item in items:
            if not item:
                continue
            if kind == "track":
                album = item.get("album") or {}
                images = album.get("images") or []
                out.append({
                    "id": item["id"], "name": item["name"], "uri": item["uri"],
                    "image": images[0]["url"] if images else None,
                    "artists": [a["name"] for a in item.get("artists", [])],
                    "album_id": album.get("id"), "album_name": album.get("name", ""),
                    "duration_ms": item.get("duration_ms", 0),
                })
                continue
            images = item.get("images") or []
            entry = {"id": item["id"], "name": item["name"],
                     "image": images[0]["url"] if images else None, "uri": item["uri"]}
            if kind == "artist":
                entry["genres"] = item.get("genres", [])
            else:
                entry["artists"] = [a["name"] for a in item.get("artists", [])]
                entry["release_date"] = item.get("release_date", "")
                entry["album_type"] = item.get("album_type", "")
            out.append(entry)
        self.send_json(200, {"items": out, "offset": offset, "total": total, "has_more": offset + len(items) < total})

    def handle_artist_albums(self, artist_id, query):
        groups = query.get("groups", ["album,single,compilation"])[0]
        force = query.get("refresh", ["0"])[0] in ("1", "true")
        albums = fetch_artist_albums(artist_id, groups, force=force)
        out = []
        for album in albums:
            images = album.get("images") or []
            out.append({"id": album["id"], "name": album["name"], "album_type": album.get("album_type", ""),
                        "release_date": album.get("release_date", ""), "total_tracks": album.get("total_tracks", 0),
                        "image": images[0]["url"] if images else None, "uri": album["uri"]})
        out.sort(key=lambda a: a["release_date"] or "", reverse=True)
        self.send_json(200, {"items": out})

    def handle_dedup(self, artist_id, query):
        groups = query.get("groups", ["album,single,compilation"])[0]
        self.send_json(200, {"items": build_dedup_tracks(artist_id, groups)})

    def handle_album(self, album_id, query=None):
        force = bool(query) and query.get("refresh", ["0"])[0] in ("1", "true")
        # Favorited albums are a small, stable set -- serve them straight from
        # sqlite with zero Spotify calls once cached, instead of re-fetching
        # metadata + tracks (paginated at this app's limit=10) every visit.
        cached = None if force else get_favorite_album_detail(album_id)
        if cached:
            self.send_json(200, cached)
            return
        album = fetch_album_meta(album_id, force=force)
        tracks = fetch_album_tracks(album_id, force=force)
        images = album.get("images") or []
        result = {
            "id": album["id"], "name": album["name"], "album_type": album.get("album_type", ""),
            "release_date": album.get("release_date", ""), "image": images[0]["url"] if images else None,
            "artists": [a["name"] for a in album.get("artists", [])],
            "tracks": [{"id": t["id"], "uri": t["uri"], "name": t["name"],
                        "track_number": t.get("track_number", 0), "disc_number": t.get("disc_number", 1),
                        "duration_ms": t.get("duration_ms", 0),
                        "artists": [a["name"] for a in t.get("artists", [])]} for t in tracks],
        }
        # Backfill the cache if this was already favorited before caching
        # existed (or before this album's page had ever been opened), so the
        # next view is free.
        if is_favorite(album_id):
            add_favorite(album_id, result["name"], result["artists"], result["image"],
                         result["album_type"], result["release_date"], result["tracks"])
        self.send_json(200, result)

    def handle_next_in_artist(self, album_id):
        album = fetch_album_meta(album_id)
        artists = album.get("artists") or []
        if not artists:
            self.send_json(200, {"next": None}); return
        nxt = find_next_album_for_artist(artists[0]["id"], album.get("album_type", "album"), album_id)
        if not nxt:
            self.send_json(200, {"next": None}); return
        images = nxt.get("images") or []
        self.send_json(200, {"next": {"id": nxt["id"], "name": nxt["name"],
                                       "image": images[0]["url"] if images else None}})

    def handle_devices(self):
        result = spotify_api("GET", "/me/player/devices")
        self.send_json(200, {"items": result.get("devices", [])})

    def handle_recently_played(self):
        result = spotify_api("GET", "/me/player/recently-played", params={"limit": SPOTIFY_PAGE_LIMIT})
        out = [track_summary(entry.get("track")) for entry in result.get("items", [])]
        self.send_json(200, {"items": [t for t in out if t]})

    def handle_queue(self):
        result = spotify_api("GET", "/me/player/queue")
        self.send_json(200, {
            "currently_playing": track_summary(result.get("currently_playing")),
            "queue": [t for t in (track_summary(x) for x in result.get("queue", [])) if t],
        })

    def handle_now_playing(self):
        result = spotify_api("GET", "/me/player")
        item = (result or {}).get("item")
        if item:
            images = (item.get("album", {}).get("images")) or []
            device = (result or {}).get("device") or {}
            payload = {
                "playing": bool((result or {}).get("is_playing")),
                "progress_ms": (result or {}).get("progress_ms", 0),
                "device": device.get("name"),
                "device_id": device.get("id"),
                "track": {
                    "name": item.get("name"), "artists": [a["name"] for a in item.get("artists", [])],
                    "album": item.get("album", {}).get("name"), "album_id": item.get("album", {}).get("id"),
                    "duration_ms": item.get("duration_ms", 0),
                    "image": images[0]["url"] if images else None, "uri": item.get("uri"),
                },
                "live": True,
            }
            set_last_playback(payload)
            self.send_json(200, payload)
            return
        # The Web Playback SDK device is this browser tab; Spotify reports no
        # active device between "tab just reloaded" and "a device reconnects",
        # which can be indistinguishable from "genuinely stopped". Fall back to
        # the last known snapshot (frozen, not live) so the bar and playhead
        # stay put across a refresh instead of going blank.
        cached = get_last_playback()
        if cached:
            cached["playing"] = False
            cached["live"] = False
            self.send_json(200, cached)
            return
        self.send_json(200, {"playing": False, "progress_ms": 0, "device": None, "device_id": None,
                              "track": None, "live": True})

    # -- PUT --

    def do_PUT(self):
        self.safe(self._do_PUT)

    def _do_PUT(self):
        parsed = urlparse(self.path)
        path, query = parsed.path, parse_qs(parsed.query)
        if path == "/spotify-api/player/transfer":
            body = self.read_json_body()
            device_id = body.get("device_id")
            if not device_id:
                self.send_json(400, {"error": "missing_device_id"}); return
            spotify_api("PUT", "/me/player", body={"device_ids": [device_id], "play": bool(body.get("play", True))})
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/play":
            body = self.read_json_body()
            device_id = body.get("device_id")
            payload = {}
            if body.get("uris"):
                payload["uris"] = body["uris"]
            if body.get("context_uri"):
                payload["context_uri"] = body["context_uri"]
            if body.get("offset") is not None:
                payload["offset"] = body["offset"]
            if body.get("position_ms") is not None:
                payload["position_ms"] = body["position_ms"]
            spotify_api("PUT", "/me/player/play", params={"device_id": device_id}, body=payload or None)
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/pause":
            body = self.read_json_body()
            spotify_api("PUT", "/me/player/pause", params={"device_id": body.get("device_id")})
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/volume":
            value = query.get("value", [None])[0]
            device_id = query.get("device_id", [None])[0]
            if value is None:
                self.send_json(400, {"error": "missing_value"}); return
            try:
                volume = max(0, min(100, int(value)))
            except ValueError:
                self.send_json(400, {"error": "invalid_value"}); return
            spotify_api("PUT", "/me/player/volume", params={"volume_percent": volume, "device_id": device_id})
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/seek":
            value = query.get("position_ms", [None])[0]
            device_id = query.get("device_id", [None])[0]
            if value is None:
                self.send_json(400, {"error": "missing_position_ms"}); return
            try:
                position_ms = max(0, int(value))
            except ValueError:
                self.send_json(400, {"error": "invalid_position_ms"}); return
            spotify_api("PUT", "/me/player/seek", params={"position_ms": position_ms, "device_id": device_id})
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/view-state":
            body = self.read_json_body()
            set_view_state(body.get("view"), body.get("client_id"))
            self.send_json(200, {"ok": True}); return
        match = FAVORITE_GENRES_RE.match(path)
        if match:
            body = self.read_json_body()
            genres = body.get("genres")
            if not isinstance(genres, list):
                self.send_json(400, {"error": "genres_must_be_array"}); return
            set_favorite_genres(match.group(1), [str(g) for g in genres][:10])
            self.send_json(200, {"ok": True}); return
        match = FAVORITE_RE.match(path)
        if match:
            body = self.read_json_body()
            add_favorite(match.group(1), body.get("name", ""), body.get("artists"), body.get("image"),
                         body.get("album_type"), body.get("release_date"), body.get("tracks"))
            self.send_json(200, {"ok": True}); return
        self.send_json(404, {"error": "not_found"})

    # -- DELETE --

    def do_DELETE(self):
        self.safe(self._do_DELETE)

    def _do_DELETE(self):
        path = urlparse(self.path).path
        match = FAVORITE_RE.match(path)
        if match:
            remove_favorite(match.group(1))
            self.send_json(200, {"ok": True}); return
        self.send_json(404, {"error": "not_found"})

    # -- POST --

    def do_POST(self):
        self.safe(self._do_POST)

    def _do_POST(self):
        path = urlparse(self.path).path
        if path == "/spotify-api/logout":
            clear_account()
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/next":
            body = self.read_json_body()
            spotify_api("POST", "/me/player/next", params={"device_id": body.get("device_id")})
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/previous":
            body = self.read_json_body()
            spotify_api("POST", "/me/player/previous", params={"device_id": body.get("device_id")})
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/queue":
            body = self.read_json_body()
            uri = body.get("uri")
            if not uri:
                self.send_json(400, {"error": "missing_uri"}); return
            spotify_api("POST", "/me/player/queue", params={"uri": uri, "device_id": body.get("device_id")})
            self.send_json(200, {"ok": True}); return
        self.send_json(404, {"error": "not_found"})


def main():
    os.makedirs(os.path.dirname(DB_PATH) or ".", exist_ok=True)
    with db():
        pass
    if not CLIENT_ID or not CLIENT_SECRET:
        print("WARNING: SPOTIFY_CLIENT_ID/SPOTIFY_CLIENT_SECRET not set", flush=True)
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"Spotify service listening on http://{HOST}:{PORT}; db={DB_PATH}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
