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
  GET  /spotify-api/search/artists?q=
  GET  /spotify-api/search/albums?q=
  GET  /spotify-api/artists/<id>/albums
  GET  /spotify-api/artists/<id>/dedup-tracks
  GET  /spotify-api/albums/<id>
  GET  /spotify-api/devices
  GET  /spotify-api/player/now-playing
  PUT  /spotify-api/player/transfer   {"device_id": "...", "play": true}
  PUT  /spotify-api/player/play       {"device_id", "uris"|"context_uri", "offset", "position_ms"}
  PUT  /spotify-api/player/pause      {"device_id"}
  PUT  /spotify-api/player/volume?value=0..100&device_id=...
  PUT  /spotify-api/player/seek?position_ms=&device_id=...
  POST /spotify-api/player/next       {"device_id"}
  POST /spotify-api/player/previous   {"device_id"}
  GET  /spotify-api/view-state        -> {"view": {...}|null, "updated_at", "updated_by"}
  PUT  /spotify-api/view-state        {"view": {...}, "client_id": "..."} -- cross-device "what's on screen" sync
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
          "user-read-playback-state user-modify-playback-state user-read-currently-playing")

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
    return conn


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
            return json.loads(raw.decode("utf-8")) if raw else {}
    except urllib.error.HTTPError as exc:
        if exc.code == 401 and retry:
            with _token_lock:
                _token_cache["access_token"] = None
            return spotify_api(method, path, params=params, body=body, retry=False)
        raise SpotifyAPIError(exc.code, exc.read().decode("utf-8", "replace")) from exc


def cached_search(kind, query, limit):
    key = (kind, query.lower(), limit)
    now = time.time()
    with _search_cache_lock:
        hit = _search_cache.get(key)
        if hit and hit[0] > now:
            return hit[1]
    result = spotify_api("GET", "/search", params={"q": query, "type": kind, "limit": limit})
    with _search_cache_lock:
        if len(_search_cache) > 200:
            _search_cache.clear()
        _search_cache[key] = (now + SEARCH_CACHE_TTL, result)
    return result


def fetch_artist_albums(artist_id, groups, limit_total=200):
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
    return albums[:limit_total]


def fetch_album_tracks(album_id, limit_total=300):
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
    return tracks[:limit_total]


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
    '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'
    'gP8H74XWaTHJpfIAAAAASUVORK5CYII='
)

SPOTIFY_PAGE = r"""<!doctype html>
<html lang="zh">
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
         padding:32px 20px 96px; }
  header { display:flex; align-items:baseline; justify-content:space-between; margin-bottom:6px; }
  h1 { font-size:20px; margin:0; }
  .nav { font-size:13px; }
  .nav a { color:#666; text-decoration:underline; margin-left:12px; }
  .hint { color:#666; font-size:13px; line-height:1.5; margin:0 0 20px; }
  .panel { border:1px solid #000; padding:14px 16px; margin-bottom:20px; }
  .row { display:flex; align-items:center; gap:10px; flex-wrap:wrap; }
  .button { padding:8px 16px; border:1px solid #000; background:#fff; color:#000;
            font:inherit; font-size:14px; cursor:pointer; }
  .button:hover { background:#f0f0f0; }
  .button.primary { background:#000; color:#fff; }
  .button.primary:hover { background:#222; }
  .button.danger { border-color:#c00; color:#c00; }
  .button.danger:hover { background:#c00; color:#fff; }
  .button.small { padding:4px 10px; font-size:12px; }
  .muted { color:#666; font-size:13px; }
  select { padding:6px 8px; border:1px solid #999; background:#fff; color:#000; font:inherit; font-size:13px; }
  input[type=text] { flex:1; min-width:160px; padding:9px 10px; border:1px solid #999; font:inherit; font-size:15px; }
  label.toggle { display:inline-flex; align-items:center; gap:6px; font-size:13px; color:#333; cursor:pointer; }
  h2 { font-size:15px; margin:22px 0 10px; }
  ul.list { list-style:none; margin:0; padding:0; }
  ul.list li { display:flex; align-items:center; gap:10px; padding:8px 0; border-bottom:1px solid #eee; }
  ul.list li:last-child { border-bottom:none; }
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
  .crumbs { font-size:13px; color:#666; margin-bottom:6px; }
  .crumbs a { color:#000; text-decoration:none; cursor:pointer; }
  #nowplaying { position:fixed; left:0; right:0; bottom:0; background:#fff; border-top:1px solid #000;
                padding:8px 16px 10px; display:none; flex-direction:column; gap:6px; }
  #nowplaying .main-row { display:flex; align-items:center; gap:12px; }
  #nowplaying .track { flex:1; min-width:0; }
  #nowplaying .track .title { font-size:13px; }
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
  }
  #columns { display:flex; gap:24px; flex-wrap:wrap; }
  #columns > div { flex:1; min-width:260px; }
</style>
</head>
<body>
<header>
  <h1>Spotify</h1>
  <div class="nav"><a href="https://spotify.example.com/">Media</a><a href="https://example.com/">Home</a></div>
</header>
<p class="hint">按艺人/专辑搜索。音乐和封面直接从 Spotify 流到这个浏览器，V1 只负责搜索、鉴权和播放控制。</p>

<div id="linkPanel" class="panel"></div>

<div id="searchPanel" class="panel" style="display:none">
  <div class="row">
    <input type="text" id="searchInput" placeholder="搜索艺人或专辑">
    <button class="button primary" id="searchButton">搜索</button>
    <label class="toggle"><input type="checkbox" id="coversToggle"> 显示封面</label>
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

function fmtDuration(ms) {
  const s = Math.round(ms / 1000);
  return Math.floor(s / 60) + ':' + String(s % 60).padStart(2, '0');
}

// ---- link status / SDK bootstrap ----

function renderLinkPanel(status) {
  const panel = document.getElementById('linkPanel');
  panel.innerHTML = '';
  if (!status.linked) {
    panel.appendChild(el('div', 'muted', '还没有连接 Spotify 账号。'));
    const btn = el('button', 'button primary', 'Connect Spotify');
    btn.style.marginTop = '10px';
    btn.onclick = () => { window.location.href = '/spotify-api/login'; };
    panel.appendChild(btn);
    return;
  }
  const row = el('div', 'row');
  row.appendChild(el('div', 'muted', 'Connected as ' + (status.display_name || 'Spotify user') +
    (status.premium ? '' : '（非 Premium 账号，播放控制会失败）')));
  const disconnect = el('button', 'button danger small', 'Disconnect');
  disconnect.onclick = async () => {
    if (!confirm('断开 Spotify 连接？')) return;
    await api('/spotify-api/logout', {method: 'POST'});
    location.reload();
  };
  row.appendChild(disconnect);
  panel.appendChild(row);
}

let sdkConnectTriggered = false;
let deviceReadyWaiters = [];

function initSDK() {
  window.onSpotifyWebPlaybackSDKReady = () => {
    const player = new Spotify.Player({
      name: 'V1 Spotify Player',
      getOAuthToken: cb => api('/spotify-api/player-token').then(d => cb(d.access_token)).catch(() => {}),
      volume: 0.7,
    });
    state.player = player;
    player.addListener('ready', ({device_id}) => {
      state.deviceId = device_id;
      deviceReadyWaiters.forEach(fn => fn(device_id));
      deviceReadyWaiters = [];
    });
    player.addListener('not_ready', () => { state.deviceId = null; });
    player.addListener('initialization_error', ({message}) => console.error('spotify init error', message));
    player.addListener('authentication_error', ({message}) => console.error('spotify auth error', message));
    player.addListener('account_error', ({message}) => console.error('spotify account error (需要 Premium)', message));
  };
}

// iOS/Safari requires connect() (and, where supported, activateElement()) to
// happen inside a real synchronous click handler or there is no audio at all --
// calling this is not a separate "Enable Playback" step for the user, it just
// has to be the very first statement of whichever click actually starts
// playback, so the browser still counts it as the same user gesture.
function ensureAudioUnlocked() {
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
// that should make sound" -- so if we just triggered connect(), wait a few
// seconds for this device to actually come online before falling back to
// whatever other Spotify Connect device happens to be active.
async function ensureDevice() {
  if (state.deviceId) return state.deviceId;
  if (sdkConnectTriggered) {
    const id = await waitForDeviceReady(4000);
    if (id) return id;
  }
  await refreshDevices();
  const active = state.devices.find(d => d.is_active) || state.devices[0];
  if (!active) { alert('没有可用的 Spotify 设备，请重试一次，或在手机/电脑上打开 Spotify。'); return null; }
  return active.id;
}

async function playUris(uris, contextUri, offset) {
  ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  const body = {device_id};
  if (contextUri) body.context_uri = contextUri; else body.uris = uris;
  if (offset !== undefined) body.offset = offset;
  await api('/spotify-api/player/play', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)});
  pollNowPlaying();
}

// ---- search / browse ----

document.getElementById('coversToggle').checked = state.showCovers;
document.getElementById('coversToggle').onchange = e => {
  state.showCovers = e.target.checked;
  localStorage.setItem('spotify_show_covers', state.showCovers ? '1' : '0');
  rerenderCurrentView();
};

let lastView = {type: 'search'};

function rerenderCurrentView() {
  if (lastView.type === 'artist') renderArtistView(lastView.artist);
  else if (lastView.type === 'album') renderAlbumView(lastView.album);
  else if (lastView.type === 'searchResults') renderSearchResults(lastView.artists, lastView.albums);
}

function coverImg(url, cls) {
  const img = el('img', cls || 'cover');
  img.style.display = state.showCovers && url ? '' : 'none';
  if (url) img.src = url;
  return img;
}

// ---- cross-device view sync ----
// Every device sharing this Spotify link polls a tiny server-side pointer for
// "what is currently on screen"; whichever device navigates writes it, the
// others pick it up on their next poll and re-fetch+render the same view
// themselves (only a {type, id/query} pointer is shared, never rendered HTML
// or search result payloads, so it stays cheap and always up to date).

let lastAppliedViewAt = 0;

function pushViewState(view) {
  api('/spotify-api/view-state', {method: 'PUT', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({view, client_id: state.clientId})}).catch(() => {});
}

async function applyRemoteView(view) {
  if (!view) { lastView = {type: 'search'}; document.getElementById('view').innerHTML = ''; return; }
  if (view.type === 'home') { lastView = {type: 'search'}; document.getElementById('view').innerHTML = ''; }
  else if (view.type === 'search') { document.getElementById('searchInput').value = view.query || ''; await doSearch(false); }
  else if (view.type === 'artist') await openArtist(view.id, view.name, false);
  else if (view.type === 'album') await openAlbum(view.id, false);
  else if (view.type === 'dedup') await openDedup({id: view.id, name: view.name}, false);
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

document.getElementById('searchButton').onclick = () => doSearch();
document.getElementById('searchInput').addEventListener('keydown', e => { if (e.key === 'Enter') doSearch(); });

async function doSearch(push) {
  const q = document.getElementById('searchInput').value.trim();
  const err = document.getElementById('searchError');
  err.textContent = '';
  if (!q) return;
  try {
    const [artists, albums] = await Promise.all([
      api('/spotify-api/search/artists?q=' + encodeURIComponent(q)),
      api('/spotify-api/search/albums?q=' + encodeURIComponent(q)),
    ]);
    lastView = {type: 'searchResults', artists: artists.items, albums: albums.items};
    renderSearchResults(artists.items, albums.items);
    if (push !== false) pushViewState({type: 'search', query: q});
  } catch (e) { err.textContent = '搜索失败：' + e.message; }
}

function renderSearchResults(artists, albums) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const cols = el('div', ''); cols.id = 'columns';
  const artistCol = el('div');
  artistCol.appendChild(el('h2', null, 'Artists'));
  const artistList = el('ul', 'list');
  if (!artists.length) artistList.appendChild(el('li', 'empty', 'No artists'));
  for (const a of artists) {
    const li = el('li');
    li.appendChild(coverImg(a.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', a.name));
    meta.appendChild(el('div', 'sub', (a.genres || []).slice(0, 3).join(', ') || 'Artist'));
    meta.onclick = () => openArtist(a.id, a.name);
    li.appendChild(meta);
    artistList.appendChild(li);
  }
  artistCol.appendChild(artistList);

  const albumCol = el('div');
  albumCol.appendChild(el('h2', null, 'Albums'));
  const albumList = el('ul', 'list');
  if (!albums.length) albumList.appendChild(el('li', 'empty', 'No albums'));
  for (const a of albums) {
    const li = el('li');
    li.appendChild(coverImg(a.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', a.name));
    meta.appendChild(el('div', 'sub', (a.artists || []).join(', ') + ' · ' + (a.release_date || '').slice(0, 4)));
    meta.onclick = () => openAlbum(a.id);
    li.appendChild(meta);
    albumList.appendChild(li);
  }
  albumCol.appendChild(albumList);

  cols.appendChild(artistCol);
  cols.appendChild(albumCol);
  view.appendChild(cols);
}

async function openArtist(id, name, push) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const albums = await api('/spotify-api/artists/' + id + '/albums');
    lastView = {type: 'artist', artist: {id, name, albums: albums.items}};
    renderArtistView(lastView.artist);
    if (push !== false) pushViewState({type: 'artist', id, name});
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderArtistView(artist) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Search'); back.onclick = () => { lastView = {type: 'search'}; view.innerHTML = ''; pushViewState({type: 'home'}); };
  crumbs.appendChild(back);
  view.appendChild(crumbs);
  view.appendChild(el('h2', null, artist.name));

  const dedupBtn = el('button', 'button small', 'Build deduplicated track list');
  dedupBtn.onclick = () => openDedup(artist);
  view.appendChild(dedupBtn);

  const groups = {album: [], single: [], compilation: [], appears_on: []};
  for (const a of artist.albums) (groups[a.album_type] || groups.appears_on).push(a);

  for (const [label, items] of [['Albums', groups.album], ['Singles', groups.single], ['Compilations', groups.compilation]]) {
    if (!items.length) continue;
    view.appendChild(el('h2', null, label));
    const list = el('ul', 'list');
    for (const a of items) {
      const li = el('li');
      li.appendChild(coverImg(a.image));
      const meta = el('div', 'meta');
      meta.appendChild(el('div', 'title', a.name));
      meta.appendChild(el('div', 'sub', (a.release_date || '').slice(0, 4) + ' · ' + a.total_tracks + ' tracks'));
      meta.onclick = () => openAlbum(a.id);
      li.appendChild(meta);
      list.appendChild(li);
    }
    view.appendChild(list);
  }
}

async function openDedup(artist, push) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Building deduplicated list…</div>';
  try {
    const {items} = await api('/spotify-api/artists/' + artist.id + '/dedup-tracks');
    view.innerHTML = '';
    const crumbs = el('div', 'crumbs');
    const back = el('a', null, '← ' + artist.name);
    back.onclick = () => { renderArtistView(artist); pushViewState({type: 'artist', id: artist.id, name: artist.name}); };
    crumbs.appendChild(back);
    view.appendChild(crumbs);
    view.appendChild(el('h2', null, artist.name + ' · Deduplicated (' + items.length + ' songs)'));
    if (push !== false) pushViewState({type: 'dedup', id: artist.id, name: artist.name});
    const playAll = el('button', 'button primary small', 'Play all');
    playAll.onclick = () => playUris(items.slice(0, 50).map(t => t.uri));
    view.appendChild(playAll);
    const list = el('ul', 'list');
    for (const t of items) {
      const li = el('li');
      li.appendChild(coverImg(t.image));
      const meta = el('div', 'meta');
      meta.appendChild(el('div', 'title', t.name));
      const sub = el('div', 'sub', t.album_name + ' · ' + (t.release_date || '').slice(0, 4) + ' · ' + fmtDuration(t.duration_ms));
      if (t.variant_count > 1) sub.appendChild(el('span', 'badge', t.variant_count + ' versions'));
      meta.appendChild(sub);
      meta.onclick = () => playUris([t.uri]);
      li.appendChild(meta);
      const playBtn = el('button', 'button small', '▶'); playBtn.onclick = () => playUris([t.uri]);
      li.appendChild(playBtn);
      list.appendChild(li);
      if (t.variant_count > 1) {
        const variants = el('div', 'variants');
        for (const v of t.variants) {
          const row = el('div', null, v.album_name + ' (' + v.album_type + ', ' + (v.release_date || '').slice(0, 4) + ')');
          row.onclick = () => playUris([v.uri]);
          variants.appendChild(row);
        }
        list.appendChild(variants);
      }
    }
    view.appendChild(list);
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

async function openAlbum(id, push) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const album = await api('/spotify-api/albums/' + id);
    lastView = {type: 'album', album};
    renderAlbumView(album);
    if (push !== false) pushViewState({type: 'album', id});
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderAlbumView(album) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Search'); back.onclick = () => { lastView = {type: 'search'}; view.innerHTML = ''; pushViewState({type: 'home'}); };
  crumbs.appendChild(back);
  view.appendChild(crumbs);

  const header = el('div', 'row');
  header.appendChild(coverImg(album.image, 'cover lg'));
  const meta = el('div');
  meta.appendChild(el('div', 'title', album.name));
  meta.appendChild(el('div', 'sub', (album.artists || []).join(', ') + ' · ' + (album.release_date || '')));
  header.appendChild(meta);
  view.appendChild(header);

  const playAlbumBtn = el('button', 'button primary small', 'Play album');
  playAlbumBtn.style.marginTop = '10px';
  playAlbumBtn.onclick = () => playUris(null, 'spotify:album:' + album.id);
  view.appendChild(playAlbumBtn);

  const list = el('ul', 'list');
  for (const t of album.tracks) {
    const li = el('li');
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', t.track_number + '. ' + t.name));
    meta.appendChild(el('div', 'sub', (t.artists || []).join(', ') + ' · ' + fmtDuration(t.duration_ms)));
    meta.onclick = () => playUris([t.uri]);
    li.appendChild(meta);
    const playBtn = el('button', 'button small', '▶'); playBtn.onclick = () => playUris([t.uri]);
    li.appendChild(playBtn);
    list.appendChild(li);
  }
  view.appendChild(list);
}

// ---- now playing / transport ----

document.getElementById('npPrev').onclick = async () => {
  ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/player/previous', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
};
document.getElementById('npNext').onclick = async () => {
  ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/player/next', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
};
document.getElementById('npPlay').onclick = async () => {
  ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  const np = await api('/spotify-api/player/now-playing');
  const path = np.playing ? '/spotify-api/player/pause' : '/spotify-api/player/play';
  await api(path, {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
};
document.getElementById('npVolume').onchange = async e => {
  const device_id = await ensureDevice();
  if (!device_id) return;
  api('/spotify-api/player/volume?value=' + e.target.value + '&device_id=' + encodeURIComponent(device_id), {method: 'PUT'});
};

// npState holds the last poll's snapshot; a fast local timer interpolates the
// visible position between 5s polls so the progress bar moves smoothly
// instead of jumping once every 5 seconds.
let npState = null;

async function pollNowPlaying() {
  try {
    const np = await api('/spotify-api/player/now-playing');
    const bar = document.getElementById('nowplaying');
    if (!np.track) { bar.style.display = 'none'; npState = null; return; }
    bar.style.display = 'flex';
    const cover = document.getElementById('npCover');
    cover.style.display = state.showCovers && np.track.image ? '' : 'none';
    if (np.track.image) cover.src = np.track.image;
    document.getElementById('npTitle').textContent = np.track.name;
    document.getElementById('npSub').textContent = np.track.artists.join(', ') + ' · ' + (np.device || '');
    document.getElementById('npPlay').textContent = np.playing ? 'Pause' : 'Play';
    npState = {progressMs: np.progress_ms || 0, durationMs: np.track.duration_ms || 0, playing: np.playing, at: Date.now()};
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
    renderLinkPanel(status);
    if (status.linked) {
      document.getElementById('searchPanel').style.display = '';
      pollNowPlaying();
      const remote = await api('/spotify-api/view-state');
      if (remote.view) { lastAppliedViewAt = remote.updated_at || 0; await applyRemoteView(remote.view); }
    }
  } catch (e) {
    document.getElementById('linkPanel').textContent = '状态加载失败：' + e.message;
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
        if path == "/spotify-api/devices":
            self.handle_devices(); return
        if path == "/spotify-api/player/now-playing":
            self.handle_now_playing(); return
        if path == "/spotify-api/view-state":
            self.send_json(200, get_view_state()); return
        match = ARTIST_ALBUMS_RE.match(path)
        if match:
            self.handle_artist_albums(match.group(1), query); return
        match = ARTIST_DEDUP_RE.match(path)
        if match:
            self.handle_dedup(match.group(1), query); return
        match = ALBUM_RE.match(path)
        if match:
            self.handle_album(match.group(1)); return
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
        result = cached_search(kind, q, limit)
        items = (result.get(kind + "s") or {}).get("items", [])
        out = []
        for item in items:
            if not item:
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
        self.send_json(200, {"items": out})

    def handle_artist_albums(self, artist_id, query):
        groups = query.get("groups", ["album,single,compilation"])[0]
        albums = fetch_artist_albums(artist_id, groups)
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

    def handle_album(self, album_id):
        album = spotify_api("GET", f"/albums/{album_id}")
        tracks = fetch_album_tracks(album_id)
        images = album.get("images") or []
        self.send_json(200, {
            "id": album["id"], "name": album["name"], "album_type": album.get("album_type", ""),
            "release_date": album.get("release_date", ""), "image": images[0]["url"] if images else None,
            "artists": [a["name"] for a in album.get("artists", [])],
            "tracks": [{"id": t["id"], "uri": t["uri"], "name": t["name"],
                        "track_number": t.get("track_number", 0), "disc_number": t.get("disc_number", 1),
                        "duration_ms": t.get("duration_ms", 0),
                        "artists": [a["name"] for a in t.get("artists", [])]} for t in tracks],
        })

    def handle_devices(self):
        result = spotify_api("GET", "/me/player/devices")
        self.send_json(200, {"items": result.get("devices", [])})

    def handle_now_playing(self):
        result = spotify_api("GET", "/me/player")
        item = (result or {}).get("item")
        images = (item.get("album", {}).get("images") if item else []) or []
        device = (result or {}).get("device") or {}
        self.send_json(200, {
            "playing": bool((result or {}).get("is_playing")),
            "progress_ms": (result or {}).get("progress_ms", 0),
            "device": device.get("name"),
            "device_id": device.get("id"),
            "track": None if not item else {
                "name": item.get("name"), "artists": [a["name"] for a in item.get("artists", [])],
                "album": item.get("album", {}).get("name"), "duration_ms": item.get("duration_ms", 0),
                "image": images[0]["url"] if images else None, "uri": item.get("uri"),
            },
        })

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
