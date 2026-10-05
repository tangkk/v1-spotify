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
  GET  /spotify-api/search/best?q=  -> {"kind", "items", "offset", "total", "has_more"} -- one combined
    Spotify call across all three types; "kind" is whichever type has an exact
    (case-insensitive) name match at the top, else artist by default.
  GET  /spotify-api/artists/<id>/albums?refresh=1 -- bypass the permanent cache and re-fetch
  GET  /spotify-api/artists/<id>/dedup-tracks
  GET  /spotify-api/albums/<id>?refresh=1          -- bypass the permanent cache and re-fetch
  GET  /spotify-api/devices
  GET  /spotify-api/recently-played
  GET  /spotify-api/queue              -> {"current", "next", "manual", "auto", "autoplay"} (V1-owned queue, no Spotify call)
  GET  /spotify-api/player/now-playing
  PUT  /spotify-api/player/transfer   {"device_id": "...", "play": true}
  PUT  /spotify-api/player/play       {"device_id", "uris"|"context_uri", "offset", "position_ms"}
  PUT  /spotify-api/player/pause      {"device_id"}
  PUT  /spotify-api/player/volume?value=0..100&device_id=...
  PUT  /spotify-api/player/seek?position_ms=&device_id=...
  POST /spotify-api/player/previous   {"device_id"}
  POST /spotify-api/queue/add         {"track"} -- manual add (promotes it if it was in the auto section)
  POST /spotify-api/queue/remove      {"list": "manual"|"auto", "index", "uri"}
  POST /spotify-api/queue/play-track  {"track", "device_id"} -- play now; album remainder becomes auto (when on)
  POST /spotify-api/queue/play-album  {"album_id", "device_id"} -- play now; the rest of the album becomes the whole (manual) queue, replacing the old one
  POST /spotify-api/queue/play-albums {"album_ids": [...], "device_id", "shuffle_tracks"?} -- same for a list of albums in that order (one long queue, capped at PLAY_ALBUMS_MAX_TRACKS); shuffle_tracks: true shuffles all their tracks together instead (a single album: shuffle that album)
  POST /spotify-api/queue/play-tracks  {"tracks": [...], "device_id"} -- same, but for already-known track objects (favorite tracks list) instead of looking albums up
  POST /spotify-api/queue/clear       -- empty the manual and auto sections (the track already handed to Spotify stays: Spotify can't take it back)
  POST /spotify-api/queue/next        {"device_id"} -- play the queue head (else Spotify's own next)
  PUT  /spotify-api/queue-settings    {"autoplay": bool} -- off drops the auto section, on recomputes it
  GET  /spotify-api/view-state        -> {"view": {...}|null, "updated_at", "updated_by"}
  PUT  /spotify-api/view-state        {"view": {...}, "client_id": "..."} -- cross-device "what's on screen" sync
  GET    /spotify-api/favorites            -> {"items": [{id, name, artists, image, release_date, genres, added_at}]}
  GET    /spotify-api/favorites/<album_id> -> {"favorited": bool}
  PUT    /spotify-api/favorites/<album_id> {"name", "artists", "image", "album_type", "release_date", "tracks"} -- add/update a favorite album
  PUT    /spotify-api/favorites/<album_id>/genres {"genres": [...]} -- hand-tagged genres (Spotify rarely has album-level genre data)
  DELETE /spotify-api/favorites/<album_id> -- remove a favorite album
  GET    /spotify-api/favorite-tracks            -> {"items": [{id, uri, name, artists, image, album_id, album_name, release_date, duration_ms, genres, added_at}]}
  GET    /spotify-api/favorite-tracks/<track_id> -> {"favorited": bool}
  PUT    /spotify-api/favorite-tracks/<track_id> {"uri", "name", "artists", "image", "album_id", "album_name", "release_date", "duration_ms"} -- add/update a favorite track, independent of the album's own favorite status
  PUT    /spotify-api/favorite-tracks/<track_id>/genres {"genres": [...]}
  DELETE /spotify-api/favorite-tracks/<track_id>
  GET    /spotify-api/favorite-artists            -> {"items": [{id, name, image, genres, added_at, release_date, track_count}]} (release_date = the artist's earliest album; track_count = favorite tracks + favorite albums' tracks by that artist name, all local)
  GET    /spotify-api/favorite-artists/<artist_id> -> {"favorited": bool, "release_date"}
  PUT    /spotify-api/favorite-artists/<artist_id> {"name", "image", "release_date"}
  PUT    /spotify-api/favorite-artists/<artist_id>/genres {"genres": [...]}
  DELETE /spotify-api/favorite-artists/<artist_id>
  POST   /spotify-api/queue/play-artists {"artist_ids": [...], "shuffle": bool, "device_id"} -- play those artists' favorited music as one queue (see build_artist_queue)
"""
import base64
import json
import os
import random
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
FAVORITE_RE = re.compile(r"^/spotify-api/favorites/([A-Za-z0-9]{10,40})$")
FAVORITE_GENRES_RE = re.compile(r"^/spotify-api/favorites/([A-Za-z0-9]{10,40})/genres$")
FAVORITE_ARTIST_RE = re.compile(r"^/spotify-api/favorite-artists/([A-Za-z0-9]{10,40})$")
FAVORITE_ARTIST_GENRES_RE = re.compile(r"^/spotify-api/favorite-artists/([A-Za-z0-9]{10,40})/genres$")
FAVORITE_TRACK_RE = re.compile(r"^/spotify-api/favorite-tracks/([A-Za-z0-9]{10,40})$")
FAVORITE_TRACK_GENRES_RE = re.compile(r"^/spotify-api/favorite-tracks/([A-Za-z0-9]{10,40})/genres$")
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


_view_state_loaded = False


def set_view_state(view, client_id):
    global _view_state_loaded
    with _view_state_lock:
        _view_state["view"] = view
        _view_state["updated_at"] = time.time()
        _view_state["updated_by"] = client_id
        _view_state_loaded = True
        saved = json.dumps(_view_state)
    try:                      # kept across restarts: "reopen where you left off" shouldn't depend on uptime
        with db() as conn:
            conn.execute("""INSERT INTO app_settings(key, value) VALUES ('view_state', ?)
                             ON CONFLICT(key) DO UPDATE SET value=excluded.value""", (saved,))
            conn.commit()
    except Exception as exc:
        print(f"view state not saved: {exc}", flush=True)


def get_view_state():
    global _view_state_loaded
    with _view_state_lock:
        if not _view_state_loaded:
            _view_state_loaded = True
            try:
                with db() as conn:
                    row = conn.execute("SELECT value FROM app_settings WHERE key='view_state'").fetchone()
                if row:
                    _view_state.update(json.loads(row[0]))
            except Exception as exc:
                print(f"view state not loaded: {exc}", flush=True)
        return dict(_view_state)


# The Web Playback SDK device IS this browser tab, so a reload always tears
# down and recreates it -- Spotify's live /v1/me/player then briefly (or
# permanently, if nothing resumes it) reports no active device at all. Caching
# the last known now-playing payload here means a reload still shows the same
# track and playhead instead of the bar just going blank; handle_now_playing
# forces playing=False on a cached fallback since we genuinely don't know
# whether it's still advancing.
# Persisted in app_settings['last_playback'] so a restart/deploy doesn't lose
# it (it's what the bar shows while the Spotify app is the active device, and
# what Play resumes). Polls arrive every few seconds, so the row is only
# rewritten when the track or play/pause state changes, or every
# LAST_PLAYBACK_SAVE_EVERY seconds for the playhead -- a pause is a state
# change, so the resume position after pausing is exact.
LAST_PLAYBACK_SAVE_EVERY = 15
_last_playback_lock = threading.Lock()
_last_playback = None
_last_playback_loaded = False
_last_playback_saved = (None, 0.0)   # (track uri + playing, time.time()) of the last write


def _load_last_playback():
    global _last_playback, _last_playback_loaded
    if _last_playback_loaded:
        return
    _last_playback_loaded = True
    try:
        with db() as conn:
            row = conn.execute("SELECT value FROM app_settings WHERE key='last_playback'").fetchone()
        if row and _last_playback is None:
            _last_playback = json.loads(row[0])
    except Exception as exc:
        print(f"last playback not loaded: {exc}", flush=True)


def set_last_playback(payload):
    global _last_playback, _last_playback_loaded, _last_playback_saved
    with _last_playback_lock:
        _last_playback = payload
        _last_playback_loaded = True
        key = ((payload.get("track") or {}).get("uri"), bool(payload.get("playing")))
        now = time.time()
        if key == _last_playback_saved[0] and now - _last_playback_saved[1] < LAST_PLAYBACK_SAVE_EVERY:
            return
        try:
            with db() as conn:
                conn.execute("""INSERT INTO app_settings(key, value) VALUES ('last_playback', ?)
                                 ON CONFLICT(key) DO UPDATE SET value=excluded.value""", (json.dumps(payload),))
                conn.commit()
            _last_playback_saved = (key, now)
        except Exception as exc:
            print(f"last playback not saved: {exc}", flush=True)


def get_last_playback():
    with _last_playback_lock:
        _load_last_playback()
        return dict(_last_playback) if _last_playback else None


def clear_last_playback():
    global _last_playback, _last_playback_loaded, _last_playback_saved
    with _last_playback_lock:
        _last_playback = None
        _last_playback_loaded = True
        _last_playback_saved = (None, 0.0)
        with db() as conn:
            conn.execute("DELETE FROM app_settings WHERE key='last_playback'")
            conn.commit()


# Isolation from the user's other Spotify clients (the phone/desktop app):
# /me/player is account-wide, so without this every queue decision and the
# history followed whatever the *app* was playing -- the driver even pushed
# V1's next track into the app's queue and restarted V1's queue on the app's
# device. Everything V1-owned (queue driver, top-up, "current", history) now
# only reacts when the active device is this page's own Web Playback SDK
# device, recognised by the name the page gives it (must match the frontend's
# `new Spotify.Player({name: ...})`). Every V1 tab/device uses that name.
V1_DEVICE_NAME = "V1 Spotify Player"
PLAY_HISTORY_KEEP = 200
_history_lock = threading.Lock()


def is_v1_device(player):
    return ((player or {}).get("device") or {}).get("name") == V1_DEVICE_NAME


def note_v1_play(item):
    """Record a track as played on V1 (V1's own Recently Played -- the account's
    /me/player/recently-played also has everything the app played). Called on
    every poll that sees V1's device playing; a track is logged once when it
    first shows up, not again while it keeps playing."""
    summary = track_summary(item)
    if not summary or not summary.get("uri"):
        return
    with _history_lock, db() as conn:
        row = conn.execute("SELECT uri FROM play_history ORDER BY id DESC LIMIT 1").fetchone()
        if row and row[0] == summary["uri"]:
            return
        conn.execute("INSERT INTO play_history(uri, track, played_at) VALUES (?, ?, ?)",
                     (summary["uri"], json.dumps(summary), int(time.time())))
        conn.execute("DELETE FROM play_history WHERE id NOT IN "
                     "(SELECT id FROM play_history ORDER BY id DESC LIMIT ?)", (PLAY_HISTORY_KEEP,))
        conn.commit()


def list_play_history(limit=50):
    with db() as conn:
        rows = conn.execute("SELECT track FROM play_history ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
    return [json.loads(r[0]) for r in rows]


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
    conn.execute("""CREATE TABLE IF NOT EXISTS favorite_tracks (
        id TEXT PRIMARY KEY,
        uri TEXT NOT NULL,
        name TEXT NOT NULL,
        artists TEXT NOT NULL,
        image TEXT,
        album_id TEXT,
        album_name TEXT,
        release_date TEXT,
        duration_ms INTEGER,
        genres TEXT,
        added_at INTEGER NOT NULL
    )""")
    conn.execute("""CREATE TABLE IF NOT EXISTS play_history (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        uri TEXT NOT NULL,
        track TEXT NOT NULL,
        played_at INTEGER NOT NULL
    )""")
    conn.execute("""CREATE TABLE IF NOT EXISTS favorite_artists (
        id TEXT PRIMARY KEY,
        name TEXT NOT NULL,
        image TEXT,
        genres TEXT,
        added_at INTEGER NOT NULL
    )""")
    try:    # added after the table first shipped: the date of the artist's earliest album, for Year/Era
        conn.execute("ALTER TABLE favorite_artists ADD COLUMN first_release_date TEXT")
    except sqlite3.OperationalError:
        pass
    conn.execute("""CREATE TABLE IF NOT EXISTS catalog_cache (
        cache_key TEXT PRIMARY KEY,
        payload TEXT NOT NULL,
        cached_at INTEGER NOT NULL
    )""")
    conn.execute("""CREATE TABLE IF NOT EXISTS app_settings (
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL
    )""")
    conn.execute("DROP TABLE IF EXISTS manual_queue")  # superseded by the JSON queue below
    return conn


def get_autoplay():
    with db() as conn:
        row = conn.execute("SELECT value FROM app_settings WHERE key='autoplay'").fetchone()
    return row is not None and row[0] == "1"   # default OFF


def set_autoplay(enabled):
    with db() as conn:
        conn.execute("""INSERT INTO app_settings(key, value) VALUES ('autoplay', ?)
                         ON CONFLICT(key) DO UPDATE SET value=excluded.value""", ("1" if enabled else "0",))
        conn.commit()


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


# The user's own listening skews Jazz heavily enough that it's the sane
# default tag on anything newly favorited (album or track) -- one less tap for
# the common case, and it's still just a starting point: the genre chips are
# editable immediately, and re-favoriting something already in the table never
# touches its existing tags (the ON CONFLICT clauses below don't set genres at
# all), so this only ever applies once, on first favorite.
DEFAULT_FAVORITE_GENRES = ["Jazz"]


def add_favorite(album_id, name, artists, image, album_type=None, release_date=None, tracks=None):
    # tracks (and album_type/release_date) are optional: favoriting from the
    # album page sends the full detail already on screen so no extra Spotify
    # call is needed, but COALESCE keeps any previously-cached tracks intact
    # if a caller ever re-favorites without that data (e.g. an older client).
    with db() as conn:
        conn.execute("""INSERT INTO favorite_albums(id, name, artists, image, album_type, release_date, tracks, genres, added_at)
                         VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                         ON CONFLICT(id) DO UPDATE SET
                             name=excluded.name, artists=excluded.artists, image=excluded.image,
                             album_type=COALESCE(excluded.album_type, favorite_albums.album_type),
                             release_date=COALESCE(excluded.release_date, favorite_albums.release_date),
                             tracks=COALESCE(excluded.tracks, favorite_albums.tracks)""",
                     (album_id, name, json.dumps(artists or []), image, album_type, release_date,
                      json.dumps(tracks) if tracks is not None else None,
                      json.dumps(DEFAULT_FAVORITE_GENRES), int(time.time())))
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


def favorite_track_summaries(album_id):
    """Queue-item track summaries for a favorited album whose tracks are cached
    in the favorites table -- no Spotify calls -- or None."""
    with db() as conn:
        row = conn.execute("SELECT name, image, tracks FROM favorite_albums WHERE id=?", (album_id,)).fetchone()
    if not row or not row[2]:
        return None
    return [{"id": t.get("id"), "uri": t["uri"], "name": t.get("name", ""), "image": row[1],
             "artists": [str(a) for a in (t.get("artists") or [])],
             "album_id": album_id, "album_name": row[0], "duration_ms": int(t.get("duration_ms") or 0)}
            for t in json.loads(row[2]) if t.get("uri")]


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


# Independent from favorite_albums -- a track being favorited has nothing to
# do with whether its album is. Same shape/conventions throughout (artists as
# a JSON array of names, genres hand-tagged from the same fixed list, added_at
# for "recently added" sort) so the frontend can reuse sortFavorites/filtering
# as-is for both.
def add_favorite_track(track_id, uri, name, artists, image, album_id, album_name, release_date, duration_ms):
    with db() as conn:
        conn.execute("""INSERT INTO favorite_tracks(id, uri, name, artists, image, album_id, album_name, release_date, duration_ms, genres, added_at)
                         VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                         ON CONFLICT(id) DO UPDATE SET
                             uri=excluded.uri, name=excluded.name, artists=excluded.artists, image=excluded.image,
                             album_id=excluded.album_id, album_name=excluded.album_name,
                             release_date=COALESCE(excluded.release_date, favorite_tracks.release_date),
                             duration_ms=excluded.duration_ms""",
                     (track_id, uri, name, json.dumps(artists or []), image, album_id, album_name, release_date,
                      int(duration_ms or 0), json.dumps(DEFAULT_FAVORITE_GENRES), int(time.time())))
        conn.commit()


def remove_favorite_track(track_id):
    with db() as conn:
        conn.execute("DELETE FROM favorite_tracks WHERE id=?", (track_id,))
        conn.commit()


def list_favorite_tracks():
    with db() as conn:
        rows = conn.execute(
            "SELECT id, uri, name, artists, image, album_id, album_name, release_date, duration_ms, genres, added_at "
            "FROM favorite_tracks ORDER BY added_at DESC").fetchall()
    return [{"id": r[0], "uri": r[1], "name": r[2], "artists": json.loads(r[3]), "image": r[4],
             "album_id": r[5], "album_name": r[6], "release_date": r[7], "duration_ms": r[8],
             "genres": json.loads(r[9]) if r[9] else [], "added_at": r[10]} for r in rows]


def set_favorite_track_genres(track_id, genres):
    with db() as conn:
        conn.execute("UPDATE favorite_tracks SET genres=? WHERE id=?", (json.dumps(genres), track_id))
        conn.commit()


def is_favorite_track(track_id):
    with db() as conn:
        row = conn.execute("SELECT 1 FROM favorite_tracks WHERE id=?", (track_id,)).fetchone()
    return row is not None


# Favorite artists: independent of albums and tracks. There is no artist-level
# date, so no Year/Era on this list. What "playing an artist" means is decided
# purely from local data: the favorite tracks and the favorite albums' cached
# tracks whose artist *name* matches (those tables store names, not ids) --
# no Spotify call at all.
def add_favorite_artist(artist_id, name, image, first_release_date=None):
    # first_release_date: the release date of the artist's earliest album (the
    # client computes it from the album list it already has on the artist
    # page). It is what gives an artist a Year/Era at all.
    with db() as conn:
        conn.execute("""INSERT INTO favorite_artists(id, name, image, genres, first_release_date, added_at)
                         VALUES (?, ?, ?, ?, ?, ?)
                         ON CONFLICT(id) DO UPDATE SET name=excluded.name,
                             image=COALESCE(excluded.image, favorite_artists.image),
                             first_release_date=COALESCE(excluded.first_release_date, favorite_artists.first_release_date)""",
                     (artist_id, name, image, json.dumps(DEFAULT_FAVORITE_GENRES), first_release_date, int(time.time())))
        conn.commit()


def remove_favorite_artist(artist_id):
    with db() as conn:
        conn.execute("DELETE FROM favorite_artists WHERE id=?", (artist_id,))
        conn.commit()


def favorite_artist_state(artist_id):
    """{"favorited": bool, "release_date": earliest-album date or None}."""
    with db() as conn:
        row = conn.execute("SELECT first_release_date FROM favorite_artists WHERE id=?", (artist_id,)).fetchone()
    return {"favorited": row is not None, "release_date": row[0] if row else None}


def set_favorite_artist_genres(artist_id, genres):
    with db() as conn:
        conn.execute("UPDATE favorite_artists SET genres=? WHERE id=?", (json.dumps(genres), artist_id))
        conn.commit()


def fetch_artist_meta(artist_id):
    """{id, name, images} for an artist, cached permanently (an artist's picture
    doesn't change in any way this app cares about). Spotify's Dev Mode returns
    no genres/popularity here, but the images are there."""
    key = f"artist_meta:{artist_id}"
    cached = cache_get(key)
    if cached is not None:
        return cached
    a = spotify_api("GET", f"/artists/{artist_id}")
    meta = {"id": a.get("id"), "name": a.get("name"), "images": a.get("images") or []}
    cache_set(key, meta)
    return meta


def pick_artist_image(images):
    """The smallest picture that is still at least 160px wide (shown at ~40px,
    so the 1000px original would only be wasted bytes), else the largest."""
    sized = sorted((i for i in (images or []) if i.get("url")), key=lambda i: i.get("width") or 0)
    good = [i for i in sized if (i.get("width") or 0) >= 160]
    pick = good[0] if good else (sized[-1] if sized else None)
    return pick["url"] if pick else None


def refresh_artist_image(artist_id):
    """Replace a favorite artist's stored picture (originally a stand-in album
    cover) with the artist's own. Best effort: on any Spotify error it stays as is."""
    try:
        image = pick_artist_image(fetch_artist_meta(artist_id)["images"])
    except Exception:
        return None
    if image:
        with db() as conn:
            conn.execute("UPDATE favorite_artists SET image=? WHERE id=?", (image, artist_id))
            conn.commit()
    return image


_artist_image_tried = set()   # ids already attempted this process, so a failing lookup isn't retried on every list


def favorite_track_pools():
    """{artist name (lowercase): [queue-item tracks]}, oldest release first.
    Built from the favorite albums' cached tracks (in album order) plus the
    favorite tracks that aren't already part of one of those albums."""
    entries, seen = [], set()
    with db() as conn:
        albums = conn.execute("SELECT id, name, image, artists, release_date, tracks FROM favorite_albums "
                              "WHERE tracks IS NOT NULL").fetchall()
        tracks = conn.execute("SELECT id, uri, name, artists, image, album_id, album_name, release_date, duration_ms "
                              "FROM favorite_tracks").fetchall()
    for aid, aname, image, artists, rd, raw in albums:
        album_artists = json.loads(artists or "[]")
        for pos, t in enumerate(json.loads(raw)):
            if not t.get("uri") or t["uri"] in seen:
                continue
            seen.add(t["uri"])
            names = [str(a) for a in (t.get("artists") or album_artists)]
            item = {"id": t.get("id"), "uri": t["uri"], "name": t.get("name", ""), "image": image, "artists": names,
                    "album_id": aid, "album_name": aname, "duration_ms": int(t.get("duration_ms") or 0)}
            entries.append(((rd or "9999", aname or "", pos), item))
    for tid, uri, name, artists, image, album_id, album_name, rd, dur in tracks:
        if uri in seen:
            continue
        seen.add(uri)
        item = {"id": tid, "uri": uri, "name": name, "image": image, "artists": json.loads(artists or "[]"),
                "album_id": album_id, "album_name": album_name or "", "duration_ms": int(dur or 0)}
        entries.append(((rd or "9999", album_name or "", 10 ** 6), item))
    entries.sort(key=lambda e: e[0])
    pools = {}
    for _, item in entries:
        for n in item["artists"]:
            pools.setdefault(n.lower(), []).append(item)
    return pools


def backfill_artist_images(ids, timeout=4.0):
    """Look up the missing artist pictures concurrently and wait for them (up to
    `timeout` seconds in total) so the list that asked shows them straight away.
    Each artist is looked up once per process and then cached for good, so this
    only ever costs anything the first time; slow ones finish in the background."""
    threads = []
    for aid in ids:
        if aid not in _artist_image_tried and cache_get(f"artist_meta:{aid}") is None:
            _artist_image_tried.add(aid)
            t = threading.Thread(target=refresh_artist_image, args=(aid,), daemon=True)
            t.start()
            threads.append(t)
    deadline = time.time() + timeout
    for t in threads:
        t.join(max(0.0, deadline - time.time()))


def list_favorite_artists():
    pools = favorite_track_pools()
    with db() as conn:
        backfill_artist_images([r[0] for r in conn.execute("SELECT id FROM favorite_artists").fetchall()])
    with db() as conn:
        rows = conn.execute("SELECT id, name, image, genres, added_at, first_release_date FROM favorite_artists "
                            "ORDER BY added_at DESC").fetchall()
    # "release_date" here is the artist's earliest album, named the same as on
    # albums/tracks so sortFavorites/eraOf work on all three lists unchanged.
    return [{"id": r[0], "name": r[1], "image": r[2], "genres": json.loads(r[3]) if r[3] else [],
             "added_at": r[4], "release_date": r[5],
             "track_count": len(pools.get(r[1].lower(), []))} for r in rows]


def build_artist_queue(names, shuffle):
    """The tracks to queue for these artists (names in the order given).
    Ordered: one artist after another, each chronologically. Shuffled: every
    artist's tracks are shuffled, then rounds of one track per artist (artist
    order re-shuffled every round), so an artist with 300 favorites doesn't
    drown one with 3. A track by two of the artists is queued once, under the
    first one that has it. Returns (tracks, artists_with_tracks, artists_without)."""
    pools, seen, lists, empty = favorite_track_pools(), set(), [], 0
    for n in names:
        mine = [t for t in pools.get(n.lower(), []) if t["uri"] not in seen]
        seen.update(t["uri"] for t in mine)
        if mine:
            lists.append(mine)
        else:
            empty += 1
    if not shuffle:
        tracks = [t for lst in lists for t in lst]
    else:
        for lst in lists:
            random.shuffle(lst)
        tracks, live = [], list(lists)
        while live:
            random.shuffle(live)
            for lst in live:
                tracks.append(lst.pop())
            live = [lst for lst in live if lst]
    return tracks[:PLAY_ALBUMS_MAX_TRACKS], len(lists), empty


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


def shape_search_items(kind, items):
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
    return out


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


PLAY_ALBUMS_MAX_ALBUMS = 300   # albums per "play these" request
PLAY_ALBUMS_MAX_TRACKS = 1000  # the whole list is stored in the queue row; this keeps it (and every poll that reads it) small
ARTIST_ALBUM_PAGES_MAX = 12  # cold-cache cost cap per artist+group (120 albums; a big catalogue's old albums sit deep), then permanently cached


def artist_album_page(artist_id, album_type, offset):
    """One page (SPOTIFY_PAGE_LIMIT) of an artist's albums for a single group,
    cached permanently per page so the lazy walk below never repeats a request."""
    cache_key = f"artist_albums_pg:{artist_id}:{album_type}:{offset}"
    page = cache_get(cache_key)
    if page is None:
        raw = spotify_api("GET", f"/artists/{artist_id}/albums",
                          params={"include_groups": album_type, "limit": SPOTIFY_PAGE_LIMIT, "offset": offset})
        page = {"items": [{k: a.get(k) for k in ("id", "name", "album_type", "release_date")}
                          for a in raw.get("items", [])],
                "has_more": bool(raw.get("next"))}
        cache_set(cache_key, page)
    return page


def find_next_album_for_artist(artist_id, album_type, after_album_id, after_release_date=None):
    """The album that follows after_album_id when the artist's albums of this
    group are read newest to oldest. Pages are pulled lazily (newest first, at
    most ARTIST_ALBUM_PAGES_MAX) and cached permanently, so one automatic
    background lookup costs a bounded number of quota-limited requests. If the
    album isn't in the pages walked (e.g. an old album deep in a long
    discography) falls back to the first album released before it."""
    seen, ordered = set(), []
    offset = 0
    for _ in range(ARTIST_ALBUM_PAGES_MAX):
        page = artist_album_page(artist_id, album_type, offset)
        for a in page["items"]:
            key = (normalize_title(a.get("name", "")), a.get("release_date", ""))
            if key in seen:
                continue
            seen.add(key)
            ordered.append(a)
        ordered.sort(key=lambda a: a.get("release_date") or "", reverse=True)
        ids = [a["id"] for a in ordered]
        if after_album_id in ids:
            pos = ids.index(after_album_id)
            if pos + 1 < len(ordered):
                return ordered[pos + 1]
        elif after_release_date:
            older = [a for a in ordered if (a.get("release_date") or "") < after_release_date]
            if older:
                return older[0]
        if not page["has_more"]:
            return None
        offset += SPOTIFY_PAGE_LIMIT
    return None


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
            "release_date": album.get("release_date", ""),
            "duration_ms": t.get("duration_ms", 0)}


# ------------------------------------------------------------- play queue --
# V1 owns the play queue: {next, manual, auto} in app_settings['queue'].
#   manual  tracks the user added, in order; they always play before auto
#   auto    computed continuation (rest of the last queued track's album, then
#           the artist's next albums), only while auto-continue is on. The
#           manual/auto split *is* the boundary shown in the UI.
#   next    the single track already handed to Spotify's own queue, so it
#           plays gaplessly (and with the page in the background); locked.
# Spotify's queue is never read or edited. queue_driver hands Spotify the next
# track only during the last QUEUE_PUSH_WINDOW_MS of the current one, so
# adding / removing / toggling are plain V1 edits with no effect on playback.
_queue_lock = threading.RLock()
_driver_wake = threading.Event()
QUEUE_PUSH_WINDOW_MS = 15000
DRIVER_MAX_NAP = 5.0
AUTO_CAP = 30            # tracks in the auto section
AUTO_LOW = 15            # topped up back to AUTO_CAP when it shrinks below this while playing
AUTO_SEEDS = 4           # last manual albums the mix draws from
AUTO_CHUNK = 6           # tracks taken from a seed per round-robin turn (visible block size per album when several seeds interleave)
AUTO_ALBUMS_PER_SEED = 3      # following albums a seed always spills into, regardless of how many tracks that finds
AUTO_ALBUMS_PER_SEED_MAX = 10 # ...and keeps going up to this many if it still hasn't, e.g. an artist who releases singles (1 track/album) -- a fixed album count alone starves those; capped so a very long run of singles can't turn one seed into an unbounded artist-albums walk
AUTO_SEED_TRACK_TARGET = 12   # "still hasn't": fewer than this many tracks collected from albums after the seed


def load_queue():
    with db() as conn:
        row = conn.execute("SELECT value FROM app_settings WHERE key='queue'").fetchone()
    q = json.loads(row[0]) if row else {}
    return {"next": q.get("next"), "manual": q.get("manual", []), "auto": q.get("auto", []),
            "auto_tried": q.get("auto_tried"), "auto_removed": q.get("auto_removed", [])}


def save_queue(q):
    with db() as conn:
        conn.execute("""INSERT INTO app_settings(key, value) VALUES ('queue', ?)
                         ON CONFLICT(key) DO UPDATE SET value=excluded.value""", (json.dumps(q),))
        conn.commit()


def clean_track(t):
    if not isinstance(t, dict) or not str(t.get("uri", "")).startswith("spotify:track:"):
        return None
    return {"id": t.get("id"), "uri": t["uri"], "name": str(t.get("name", "")), "image": t.get("image"),
            "artists": [str(a) for a in (t.get("artists") or [])], "album_id": t.get("album_id"),
            "album_name": str(t.get("album_name", "")), "duration_ms": int(t.get("duration_ms") or 0)}


def album_track_summaries(album, raw_tracks):
    images = album.get("images") or []
    return [{"id": t.get("id"), "uri": t["uri"], "name": t.get("name", ""),
             "image": images[0]["url"] if images else None,
             "artists": [a["name"] for a in t.get("artists", [])],
             "album_id": album["id"], "album_name": album.get("name", ""),
             "duration_ms": t.get("duration_ms", 0)} for t in raw_tracks if t.get("uri")]


def auto_stream(seed):
    """Lazily yields what would follow a seed (album_id, uri): the rest of its
    album, then the same artist's next albums (same group, newest to oldest)."""
    album_id, uri = seed
    try:
        album = fetch_album_meta(album_id)
        tracks = fetch_album_tracks(album_id)
        uris = [t.get("uri") for t in tracks]
        start = uris.index(uri) + 1 if uri in uris else len(tracks)
        yield from album_track_summaries(album, tracks[start:])
        artists = album.get("artists") or []
        if not artists:
            return
        current, current_date = album_id, album.get("release_date")
        collected, walked = 0, 0
        while walked < AUTO_ALBUMS_PER_SEED_MAX and (walked < AUTO_ALBUMS_PER_SEED or collected < AUTO_SEED_TRACK_TARGET):
            nxt = find_next_album_for_artist(artists[0]["id"], album.get("album_type", "album"),
                                              current, current_date)
            if not nxt:
                return
            walked += 1
            nxt_tracks = album_track_summaries(fetch_album_meta(nxt["id"]), fetch_album_tracks(nxt["id"]))
            collected += len(nxt_tracks)
            yield from nxt_tracks
            current, current_date = nxt["id"], nxt.get("release_date")
    except SpotifyAPIError:
        return  # e.g. the artists/albums quota: keep what was found, don't fail the caller


def compute_auto(seeds, exclude):
    """A mix of what follows each seed: round-robin, AUTO_CHUNK tracks at a
    time, newest seed first, until AUTO_CAP tracks or every stream runs dry."""
    streams = [auto_stream(seed) for seed in seeds]
    seen, out = set(exclude), []
    while streams and len(out) < AUTO_CAP:
        for stream in list(streams):
            taken = 0
            for t in stream:
                if t["uri"] in seen:
                    continue
                seen.add(t["uri"])
                out.append(t)
                taken += 1
                if taken >= AUTO_CHUNK or len(out) >= AUTO_CAP:
                    break
            else:
                streams.remove(stream)      # ran dry
            if len(out) >= AUTO_CAP:
                break
    return out


def queue_seeds(q, fallback=None):
    """(album_id, uri) seeds for the auto section: the albums of the last few
    manual tracks (newest first, one seed per album), then the locked next
    track; with nothing queued, whatever is playing."""
    seeds, albums = [], set()
    for t in reversed(q["manual"]):
        if t.get("album_id") and t["album_id"] not in albums and len(seeds) < AUTO_SEEDS:
            albums.add(t["album_id"])
            seeds.append((t["album_id"], t["uri"]))
    n = q["next"]
    if n and n.get("album_id") and n["album_id"] not in albums and len(seeds) < AUTO_SEEDS:
        seeds.append((n["album_id"], n["uri"]))
    if seeds:
        return seeds
    if fallback and fallback[0]:
        return [fallback]
    item = None
    try:
        player = spotify_api("GET", "/me/player") or {}
        if is_v1_device(player):        # what the app is playing is none of V1's business
            item = player.get("item")
    except SpotifyAPIError:
        pass
    if item and (item.get("album") or {}).get("id"):
        return [(item["album"]["id"], item["uri"])]
    last = (get_last_playback() or {}).get("track") or {}   # no active device: use the last known track
    return [(last["album_id"], last["uri"])] if last.get("album_id") else []


def refresh_auto(fallback_anchor=None, current_uri=None):
    """Rebuild the auto section: emptied while auto-continue is off, a mix
    seeded from the queue's last manual tracks when it's on. Tracks the user
    removed from it (×) and the one playing now stay out. Returns its length."""
    auto = []
    if get_autoplay():
        with _queue_lock:
            q = load_queue()
        exclude = ({t["uri"] for t in q["manual"]} | ({q["next"]["uri"]} if q["next"] else set())
                   | set(q["auto_removed"]) | ({current_uri} if current_uri else set()))
        auto = compute_auto(queue_seeds(q, fallback_anchor), exclude)
    with _queue_lock:
        q = load_queue()
        taken = ({t["uri"] for t in q["manual"]} | ({q["next"]["uri"]} if q["next"] else set())
                 | set(q["auto_removed"]) | ({current_uri} if current_uri else set()))
        q["auto"] = [t for t in auto if t["uri"] not in taken]   # the driver may have committed one meanwhile
        save_queue(q)
        return len(q["auto"])


def refresh_auto_async():
    """Recompute the auto section off the request thread (may touch Spotify)."""
    if not get_autoplay():
        return None
    def run():
        try:
            refresh_auto()
        except Exception as exc:
            print(f"queue: refresh_auto failed: {exc}", flush=True)
    t = threading.Thread(target=run, daemon=True)
    t.start()
    return t


_topup_key = None


def topup_auto(item):
    """Auto-continue keeps ~AUTO_CAP tracks ahead: the section is consumed as
    tracks play, so once per playing track, if it has shrunk below AUTO_LOW,
    recompute it from the queue (or, with nothing queued, from what's playing)."""
    global _topup_key
    if not get_autoplay() or len(load_queue()["auto"]) >= AUTO_LOW:
        return
    if item:
        uri, album_id = item["uri"], (item.get("album") or {}).get("id")
    else:
        last = (get_last_playback() or {}).get("track") or {}
        uri, album_id = last.get("uri"), last.get("album_id")
    if not uri or uri == _topup_key:
        return
    _topup_key = uri      # once per track: an exhausted discography isn't retried every tick
    def run():
        try:
            refresh_auto((album_id, uri), uri)
        except Exception as exc:
            print(f"queue: top-up failed: {exc}", flush=True)
    threading.Thread(target=run, daemon=True).start()


def queue_add(track):
    with _queue_lock:
        q = load_queue()
        for i, t in enumerate(q["auto"]):
            if t["uri"] == track["uri"]:
                del q["auto"][i]   # already queued automatically: promote it to manual
                break
        q["manual"].append(track)
        save_queue(q)
    refresh_auto_async()   # the mix is seeded from the last manual tracks, which just changed
    _driver_wake.set()


def queue_remove(which, index, uri):
    with _queue_lock:
        q = load_queue()
        lst = q.get(which) if which in ("manual", "auto") else None
        if lst is None or not isinstance(index, int) or not 0 <= index < len(lst) or lst[index]["uri"] != uri:
            return False
        removed = lst.pop(index)
        if which == "auto":
            q["auto_removed"] = (q["auto_removed"] + [removed["uri"]])[-200:]   # don't top it back up
        save_queue(q)
    if which == "manual":
        refresh_auto_async()
    return True


def queue_take(q, uri):
    """Drop the first queued (manual, then auto) occurrence of uri."""
    for name in ("manual", "auto"):
        for i, t in enumerate(q[name]):
            if t["uri"] == uri:
                del q[name][i]
                return


def reconcile_queue(current_uri, progress_ms):
    """Once the track handed to Spotify is the one playing, it leaves the queue."""
    with _queue_lock:
        q = load_queue()
        n = q["next"]
        if n and n["uri"] == current_uri and (current_uri != n.get("after") or progress_ms < 10000):
            q["next"] = None
            save_queue(q)


def queue_commit_head(current_uri):
    with _queue_lock:
        q = load_queue()
        if q["next"]:
            return None
        kind = "manual" if q["manual"] else "auto" if q["auto"] else None
        if not kind:
            return None
        head = q[kind].pop(0)
        q["next"] = dict(head, kind=kind, after=current_uri)
        save_queue(q)
    return head, kind


def queue_uncommit(head, kind):
    with _queue_lock:
        q = load_queue()
        q["next"] = None
        q[kind].insert(0, head)
        save_queue(q)


def start_track(track, device_id):
    spotify_api("PUT", "/me/player/play", params={"device_id": device_id}, body={"uris": [track["uri"]]})
    # This replaces whatever Spotify was about to auto-advance to on its own
    # (the single track V1 had handed to Spotify's queue in the final 15s of
    # the previous track) -- that hand-off is now stale. Left alone, it stuck
    # around in "next" forever (reconcile_queue only clears it once its own
    # uri starts playing, which never happens once something else is playing
    # instead), showing at the top of Up Next with no way to remove it (that
    # row has no delete button, unlike manual/auto items).
    with _queue_lock:
        q = load_queue()
        if q["next"]:
            q["next"] = None
            save_queue(q)


_driver_seen = None   # last observation of a playing track: {"uri", "at", "remaining_s"}


def recover_ended_track(player, item, progress):
    """The driver normally hands Spotify the next track during the last 15s, but
    a seek, a short track or a slow tick can skip that window; a single-track
    play then just stops. If the track we last saw playing has run its course
    and playback has stopped at its start/end, start the next queued track here."""
    global _driver_seen
    seen = _driver_seen
    if not seen or seen["uri"] != item["uri"]:
        return False
    ended = time.time() >= seen["at"] + seen["remaining_s"] - 2
    at_edge = progress < 2000 or item.get("duration_ms", 0) - progress < 2000
    if not (ended and at_edge):
        return False
    with _queue_lock:
        q = load_queue()
        idle = not (q["next"] or q["manual"] or q["auto"])
    if idle and get_autoplay():
        refresh_auto()
    with _queue_lock:
        q = load_queue()
        kind = "next" if q["next"] else "manual" if q["manual"] else "auto" if q["auto"] else None
        if not kind:
            _driver_seen = None   # nothing to continue with: stop re-checking this stopped track
            return False
        head = q["next"] if kind == "next" else q[kind].pop(0)
        if kind == "next":
            q["next"] = None      # Spotify's queue lost it (or never got it): play it directly
        save_queue(q)
    try:
        start_track(head, (player.get("device") or {}).get("id"))
    except Exception:
        with _queue_lock:
            q = load_queue()
            if kind == "next":
                q["next"] = head
            else:
                q[kind].insert(0, head)
            save_queue(q)
        raise
    _driver_seen = None
    return True


def queue_driver_tick():
    """One pass of the background driver; returns seconds until the next."""
    global _driver_seen
    if load_account() is None:
        return 30
    q = load_queue()
    if not (q["next"] or q["manual"] or q["auto"] or get_autoplay()):
        _driver_seen = None
        return 30
    player = spotify_api("GET", "/me/player") or {}
    item = player.get("item")
    if item and not is_v1_device(player):
        # Another client (the Spotify app) is the active device: leave its
        # playback and V1's queue alone -- no top-up from its track, no
        # hand-off into its queue, no "recovering" V1's queue onto it.
        _driver_seen = None
        return 15
    topup_auto(item)
    if not item:
        return 15
    if player.get("is_playing"):
        note_v1_play(item)
    progress = player.get("progress_ms", 0)
    reconcile_queue(item["uri"], progress)
    if not player.get("is_playing"):
        if recover_ended_track(player, item, progress):
            return 2
        return 15
    remaining = item.get("duration_ms", 0) - progress
    _driver_seen = {"uri": item["uri"], "at": time.time(), "remaining_s": remaining / 1000}
    if remaining > QUEUE_PUSH_WINDOW_MS:
        # short naps: a seek towards the end can bring the window forward at any moment
        return min(DRIVER_MAX_NAP, max(1.0, (remaining - QUEUE_PUSH_WINDOW_MS) / 1000 - 1))
    q = load_queue()
    if not q["next"]:
        if get_autoplay() and not q["manual"] and not q["auto"] and q["auto_tried"] != item["uri"]:
            with _queue_lock:      # once per track, so an exhausted discography isn't retried every tick
                q2 = load_queue()
                q2["auto_tried"] = item["uri"]
                save_queue(q2)
            refresh_auto((item.get("album", {}).get("id"), item["uri"]), item["uri"])
        committed = queue_commit_head(item["uri"])
        if committed:
            head, kind = committed
            try:
                spotify_api("POST", "/me/player/queue", params={"uri": head["uri"]})
            except Exception:
                queue_uncommit(head, kind)
                raise
    return max(1.0, min(DRIVER_MAX_NAP, remaining / 1000 + 1.5))


def queue_driver_loop():
    while True:
        try:
            delay = queue_driver_tick()
        except SpotifyAuthError:
            delay = 30
        except Exception as exc:
            print(f"queue driver: {exc}", flush=True)
            delay = 20
        _driver_wake.wait(delay)
        _driver_wake.clear()


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
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no, viewport-fit=cover">
<!-- Tints the iOS/Android browser's own status bar and toolbar (not part of
     the page DOM, so the dark-mode filter below can't reach it); kept in sync
     with the theme by the same scripts that toggle "dark". -->
<meta name="theme-color" content="#ffffff" id="themeColorMeta">
<!-- Only takes effect when added to the home screen (standalone mode has no
     Safari chrome for theme-color to tint); harmless no-op in a normal tab. -->
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="default" id="appleStatusBarMeta">
<script>
// Applied before the stylesheet paints anything, so there's no flash of the
// wrong theme on load. Toggled by clicking the logo (header.js, near the end
// of the page); this is just the "remember and apply early" half.
try {
  if (localStorage.getItem('spotify_dark') === '1') {
    document.documentElement.classList.add('dark');
    document.getElementById('themeColorMeta').setAttribute('content', '#000000');
    document.getElementById('appleStatusBarMeta').setAttribute('content', 'black-translucent');
  }
} catch (e) {}
</script>
<title>Spotify</title>
<link rel="icon" href="/spotify-api/icon-v2.svg" type="image/svg+xml" sizes="any">
<link rel="apple-touch-icon" sizes="180x180" href="/spotify-api/apple-touch-icon-v2.png">
<style>
  * { box-sizing:border-box; }
  html, body { background:#fff; margin:0; }
  body { font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;
         touch-action:manipulation; color:#000; min-height:100vh;
         padding:max(20px, env(safe-area-inset-top)) max(20px, env(safe-area-inset-right))
                 96px max(20px, env(safe-area-inset-left)); }
  /* Dark mode: a literal black/white inversion of the whole (deliberately
     monochrome) page, toggled by clicking the logo -- not a separate dark
     palette. invert(1) flips lightness *and* hue; hue-rotate(180deg) undoes
     just the hue part, so the one non-grayscale color (.error's red) stays
     red instead of turning cyan. Album/artist photos (".cover") get the same
     filter a second time, cancelling it, so they show true colors instead of
     a photo negative -- everything else (backgrounds, borders, icons, the
     logo itself) inverts along with the page, which is the point.
     The filter is on #app/#nowplaying, not html/body: filter on an ancestor
     would also make #nowplaying's position:fixed relative to *that* box
     instead of the real viewport (a CSS containing-block rule), breaking the
     pinned player bar; and it would re-invert any literal background we put
     on html/body back to the wrong color (tried, broke it, see git history)
     -- html/body keep a real, un-filtered #fff/#000 so the notch/status-bar
     strip (viewport-fit=cover, safe-area-inset-* above) and an iOS
     pull-to-refresh overscroll bounce -- both outside any element's painted
     box, filled by the browser directly from this property -- show the
     correct color too, not just the filtered content inside #app. */
  html.dark, html.dark body { background:#000; }
  html.dark header, html.dark #app { filter: invert(1) hue-rotate(180deg); }
  html.dark img.cover { filter: invert(1) hue-rotate(180deg); }
  /* #nowplaying itself is NOT filtered: its background is a real #000, and
     only its contents are inverted. iOS 26 Safari ignores theme-color and
     tints the status bar / bottom toolbar from the CSS background-color of a
     position:fixed element touching that edge -- the property value, not
     the filtered pixels. A filtered #nowplaying has a literal #fff
     background, so in fullscreen (where it covers the top edge) the notch
     strip came out white, and in normal mode the bottom toolbar could too.
     (.main-row is display:contents in fullscreen, so its children are
     filtered rather than it; the cover is left alone -- it was only
     inverted before to cancel the parent's filter, which is gone.) */
  html.dark #nowplaying { background:#000; border-top-color:#fff; }
  html.dark #nowplaying .progress-row, html.dark #nowplaying .main-row > * { filter: invert(1) hue-rotate(180deg); }
  html.dark #nowplaying #npCover { filter:none; }
  header { display:flex; align-items:center; justify-content:space-between; margin-bottom:14px; gap:12px; }
  .logo { height:32px; width:32px; display:block; cursor:pointer; }
  .header-right { display:flex; align-items:center; gap:10px; flex-wrap:wrap; justify-content:flex-end; }
  @media (max-width: 420px) { .header-right { gap:6px; } }
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
  .icon-btn:disabled { opacity:.35; cursor:default; }
  .icon-btn:disabled:hover { background:#fff; }
  input[type=text] { flex:1; min-width:160px; padding:9px 10px; border:1px solid #999; font:inherit; font-size:15px; }
  h2 { font-size:15px; margin:22px 0 10px; }
  ul.list { list-style:none; margin:0; padding:0; }
  ul.list li { display:flex; align-items:center; gap:10px; padding:8px 0; border-bottom:1px solid #eee; }
  ul.list li:last-child { border-bottom:none; }
  ul.list li.fav-item { flex-wrap:wrap; }
  ul.list li.boundary { font-size:11px; color:#666; border-top:1px solid #000; padding:8px 0 2px; }
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
  .link { color:inherit; cursor:pointer; text-decoration:underline; text-decoration-color:#bbb; text-underline-offset:2px; }
  .link:hover { color:#000; text-decoration-color:#000; }
  .crumbs { font-size:13px; color:#666; margin-bottom:6px; }
  .crumbs a { color:#000; text-decoration:none; cursor:pointer; }
  /* Direct child of <body>, not of #app (see the dark-mode comment above):
     stays pinned to the real viewport bottom regardless of #app's filter,
     and its own filter independently inverts it in dark mode. */
  #nowplaying { position:fixed; left:0; right:0; bottom:0; background:#fff; border-top:1px solid #000;
                padding:8px max(16px, env(safe-area-inset-right)) max(10px, env(safe-area-inset-bottom))
                        max(16px, env(safe-area-inset-left));
                display:none; flex-direction:column; gap:6px; }
  #nowplaying .main-row { display:flex; align-items:center; gap:12px; }
  #nowplaying .track { flex:1; min-width:0; }
  #nowplaying .track .title { font-size:13px; }
  #nowplaying .track .title:hover { text-decoration:underline; }
  #nowplaying .track .sub { font-size:11px; color:#666; }
  #nowplaying .controls { display:flex; align-items:center; gap:6px; flex:none; }
  /* Not shown in the compact bar (kept deliberately plain there); fullscreen has room. */
  #nowplaying .controls #npFavorite { display:none; }
  #nowplaying .volume { display:flex; align-items:center; flex:none; }
  #nowplaying .volume input[type=range] { width:70px; accent-color:#000; }
  #nowplaying .progress-row { display:flex; align-items:center; gap:8px; order:-1; }
  #nowplaying .progress-row input[type=range] { flex:1; min-width:0; accent-color:#000; touch-action:none; cursor:pointer; }
  #nowplaying .progress-row .time { font-size:11px; color:#666; font-variant-numeric:tabular-nums; flex:none; min-width:34px; }
  #nowplaying .progress-row .time.start { text-align:left; }
  #nowplaying .progress-row .time.end { text-align:right; }
  #npLogo { display:none; }
  /* Full-screen mode: only the current track, centred and enlarged. The bar's
     own rows are flattened (display:contents) so its parts can be re-ordered
     into one column: cover/logo, title, progress, controls, volume. */
  body.fs { overflow:hidden; padding:0; }
  body.fs header { position:fixed; top:max(12px, env(safe-area-inset-top)); right:max(12px, env(safe-area-inset-right)); z-index:20; margin:0; }
  body.fs header .logo, body.fs .header-right > :not(#fullscreenButton),
  body.fs #connectPanel, body.fs #searchPanel, body.fs #view { display:none !important; }
  /* top is the safe-area inset itself, not 0 -- #nowplaying's own background is
     filtered (invert) for dark mode, and whether a filtered position:fixed
     element's paint reliably extends into the actual notch cutout is exactly
     the kind of WebKit edge case this environment can't test (headless
     Chrome's env(safe-area-inset-*) is always 0, so that interaction has
     never actually been exercised). Leaving that strip uncovered by
     #nowplaying falls back to html/body's own real, unfiltered background for
     it instead -- the one mechanism already confirmed working on a real
     device for the non-fullscreen case. */
  body.fs #nowplaying { top:env(safe-area-inset-top); border-top:none;
                        padding:56px max(20px, env(safe-area-inset-right))
                                max(32px, env(safe-area-inset-bottom)) max(20px, env(safe-area-inset-left));
                        gap:clamp(12px, 3vh, 28px);
                        align-items:center; justify-content:center; z-index:10; overflow:hidden; }
  body.fs #nowplaying .main-row { display:contents; }
  body.fs #npCover, body.fs #npLogo { order:1; width:min(72vw, 44vh); height:min(72vw, 44vh); object-fit:cover; }
  body.fs #npLogo { object-fit:contain; }
  body.fs #nowplaying .track { order:2; flex:none; width:min(92vw, 720px); text-align:center; }
  body.fs #nowplaying .track .title { font-size:clamp(22px, 5.5vw, 44px); line-height:1.2; pointer-events:none; }
  body.fs #nowplaying .track .sub { display:block; font-size:clamp(14px, 3.2vw, 22px); margin-top:8px; }
  body.fs #nowplaying .progress-row { order:3; width:min(92vw, 720px); gap:12px; }
  body.fs #nowplaying .progress-row .time { font-size:clamp(13px, 2.6vw, 18px); min-width:46px; }
  body.fs #nowplaying .controls { order:4; gap:12px; }
  body.fs #nowplaying .controls #npFavorite { display:inline-flex; }
  body.fs #nowplaying .controls .icon-btn { width:clamp(48px, 11vw, 64px); height:clamp(48px, 11vw, 64px); }
  body.fs #nowplaying .controls .icon-btn svg { width:52%; height:52%; }
  body.fs #nowplaying .volume { order:5; }
  body.fs #nowplaying .volume input[type=range] { width:min(60vw, 260px); }
  @media (max-width: 520px) {
    #nowplaying .track .sub { display:none; }
    #searchPanel input[type=text] { flex-basis:100%; }
  }
</style>
</head>
<body>
<header>
  <img src="/spotify-api/icon-v2.svg" alt="Spotify" class="logo" id="logoButton" title="Toggle dark mode">
  <div class="header-right">
    <button class="icon-btn" id="recentlyPlayedButton" title="Recently played"><svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="10" r="7.5" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M10 6v4l3 2" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg></button>
    <button class="icon-btn" id="queueViewButton" title="Play queue"><svg width="18" height="18" viewBox="0 0 20 20"><line x1="4" y1="6" x2="16" y2="6" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><line x1="4" y1="10" x2="16" y2="10" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><line x1="4" y1="14" x2="12" y2="14" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button>
    <button class="icon-btn" id="favoriteArtistsButton" title="Favorite artists"><svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="6.8" r="3.1" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M3.5 17c0-3.6 2.9-6 6.5-6s6.5 2.4 6.5 6" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button>
    <button class="icon-btn" id="favoritesButton" title="Favorite albums"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 2.5l2.35 4.76 5.25.76-3.8 3.7.9 5.23L10 14.5l-4.7 2.45.9-5.23-3.8-3.7 5.25-.76z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round"/></svg></button>
    <button class="icon-btn" id="favoriteTracksButton" title="Favorite tracks"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 16.3s-6-4.2-6-8.4C4 5.3 5.8 3.5 8 3.5c.9 0 1.7.4 2 1 .3-.6 1.1-1 2-1 2.2 0 4 1.8 4 4.4 0 4.2-6 8.4-6 8.4z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round" stroke-linecap="round"/></svg></button>
    <button class="icon-btn" id="fullscreenButton" title="Full screen"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M3 7.5V3h4.5M12.5 3H17v4.5M17 12.5V17h-4.5M7.5 17H3v-4.5" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="square"/></svg></button>
    <button class="icon-btn" id="connectionButton" title="Connect Spotify"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 3v6" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" fill="none"/><path d="M5.5 6.5a6 6 0 1 0 9 0" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" fill="none"/></svg></button>
  </div>
</header>

<div id="app">
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
</div>

<div id="nowplaying">
  <div class="main-row">
    <img id="npCover" class="cover" style="display:none">
    <img id="npLogo" src="/spotify-api/icon-v2.svg" alt="Spotify">
    <div class="track">
      <div class="title" id="npTitle">-</div>
      <div class="sub" id="npSub"></div>
    </div>
    <div class="controls">
      <button class="icon-btn" id="npPrev" title="Previous" aria-label="Previous"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M5 4v12" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><path d="M15.5 4.5v11L8 10z" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linejoin="round"/></svg></button>
      <button class="icon-btn" id="npPlay" title="Play" aria-label="Play"></button>
      <button class="icon-btn" id="npNext" title="Next" aria-label="Next"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M15 4v12" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><path d="M4.5 4.5v11L12 10z" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linejoin="round"/></svg></button>
      <button class="icon-btn" id="npFavorite" title="Add to favorites" aria-label="Add to favorites"><svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 16.3s-6-4.2-6-8.4C4 5.3 5.8 3.5 8 3.5c.9 0 1.7.4 2 1 .3-.6 1.1-1 2-1 2.2 0 4 1.8 4 4.4 0 4.2-6 8.4-6 8.4z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round" stroke-linecap="round"/></svg></button>
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
  autoplay: false,  // queue-page toggle; mirrored from the server on every now-playing poll
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

const ICON_PLUS = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 4v12M4 10h12" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg>';
// Arrow pointing up = ascending (smallest first), down = descending.
// One fixed icon for both directions (a straight shaft, arrowhead at each end
// pointing its own way) instead of swapping between two separate glyphs --
// the current direction is conveyed by the title tooltip, not the icon.
const ICON_SORT_UPDOWN = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 3v14M6.5 7l3.5-4 3.5 4M6.5 13l3.5 4 3.5-4" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg>';
const ICON_TRASH = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M4 5.5h12M8 5.5V3.5h4v2M5.5 5.5l.8 11h7.4l.8-11M8.5 9v4.5M11.5 9v4.5" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>';
const ICON_MORE = '<svg width="18" height="18" viewBox="0 0 20 20"><circle cx="4.5" cy="10" r="1.5" fill="currentColor"/><circle cx="10" cy="10" r="1.5" fill="currentColor"/><circle cx="15.5" cy="10" r="1.5" fill="currentColor"/></svg>';
const ICON_CROSS = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M5 5l10 10M15 5L5 15" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg>';
const ICON_PERSON = '<svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="6.8" r="3.1" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M3.5 17c0-3.6 2.9-6 6.5-6s6.5 2.4 6.5 6" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg>';
const ICON_STAR = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 2.5l2.35 4.76 5.25.76-3.8 3.7.9 5.23L10 14.5l-4.7 2.45.9-5.23-3.8-3.7 5.25-.76z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round"/></svg>';
// Track favorites use a heart, distinct from the star used for album favorites.
const ICON_HEART = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M10 16.3s-6-4.2-6-8.4C4 5.3 5.8 3.5 8 3.5c.9 0 1.7.4 2 1 .3-.6 1.1-1 2-1 2.2 0 4 1.8 4 4.4 0 4.2-6 8.4-6 8.4z" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linejoin="round" stroke-linecap="round"/></svg>';
// Distinct from the normal play button -- for the separate "shuffle" action.
const ICON_SHUFFLE = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M2.5 6h3l8 8h3.5" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/><path d="M2.5 14h3l8-8h3.5" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/><path d="M14.5 4l2.5 2-2.5 2M14.5 12l2.5 2-2.5 2" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>';

// Row action buttons (play / add to queue / remove) are the same 38px icon
// buttons as the header and the transport bar.
function playRowButton(onclick) {
  const btn = iconButton(ICON_PLAY, 'Play');
  btn.onclick = onclick;
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
  syncNpLogo();
}

// Full-screen mode shows the Spotify logo in the cover's place whenever the
// cover is off (covers switch) or the track has none.
function syncNpLogo() {
  const cover = document.getElementById('npCover');
  document.getElementById('npLogo').style.display =
    document.body.classList.contains('fs') && cover.style.display === 'none' ? 'block' : '';
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
let playerStateTimer = null;
let sdkTrackUri = null;   // last track this device's SDK reported, to spot a track change
let sdkPos = null;   // this device's own last player state: {uri, position, duration, paused, at}

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
    // Fires on every track change/pause/seek, including with the page in the
    // background where the 5s setInterval is throttled: keep the lock screen current.
    player.addListener('player_state_changed', st => {
      const cur = st && st.track_window && st.track_window.current_track;
      sdkPos = cur ? {uri: cur.uri, position: st.position, duration: st.duration, paused: st.paused, at: Date.now()} : null;
      if (cur) mediaTrackUri = cur.uri;
      sdkTrackUri = cur ? cur.uri : null;
      updateMediaPosition();
      clearTimeout(playerStateTimer);
      playerStateTimer = setTimeout(pollNowPlaying, 300);
    });
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
  unlockLockAudio();   // synchronously, while this is still the click's gesture
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
//
// Two things used to make the "no device" alert fire even though a device was
// about to come online a moment later:
// - if the sdk.scdn.co script itself was still loading (slow network, cold
//   cache), ensureAudioUnlocked()'s own 5s wait for it could time out without
//   ever calling connect() -- sdkConnectTriggered stayed false, so this went
//   straight to a single devices lookup with no wait at all;
// - once connect() *was* called and the local 'ready' event hadn't fired
//   within the wait, this fell through to exactly one /spotify-api/devices
//   call; Spotify's own device registry can lag a beat behind this device
//   actually finishing its handshake, so that single snapshot could still
//   miss it.
// Both are given a further chance below before concluding there's truly
// nothing to play through.
async function ensureDevice() {
  if (state.deviceId) return state.deviceId;
  if (!sdkConnectTriggered) await ensureAudioUnlocked();   // the script may have only just finished loading
  if (sdkConnectTriggered) {
    const id = await waitForDeviceReady(15000);
    if (id) return id;
  }
  showToast('Connecting to Spotify…');
  for (let attempt = 0; attempt < 4; attempt++) {
    await refreshDevices();
    const active = state.devices.find(d => d.is_active) || state.devices[0];
    if (active) return active.id;
    if (attempt < 3) await new Promise(r => setTimeout(r, 1500));
  }
  alert('No available Spotify device. Please try again, or open Spotify on your phone/computer.');
  return null;
}

async function playUris(uris, contextUri, offset) {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  const body = {device_id};
  if (contextUri) body.context_uri = contextUri; else body.uris = uris;
  if (offset !== undefined) body.offset = offset;
  await api('/spotify-api/player/play', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)});
  pollNowPlaying();
}

// Track / album plays go through V1's own queue (which decides what follows,
// see the queue page); playUris above is only the raw Spotify play call.
async function playTrackNow(track) {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/queue/play-track', {method: 'POST', headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({track, device_id})});
  pollNowPlaying();
}

async function playAlbumNow(albumId) {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/queue/play-album', {method: 'POST', headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({album_id: albumId, device_id})});
  pollNowPlaying();
}

// Plays a list of albums in the order given as one long queue: the first track
// now, everything after it (the rest of that album, then the following albums)
// as the manual queue.
async function playAlbumsNow(albumIds, shuffleTracks) {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  try {
    const r = await api('/spotify-api/queue/play-albums', {method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({album_ids: albumIds, device_id, shuffle_tracks: !!shuffleTracks})});
    showToast(r.tracks + ' tracks from ' + r.albums + ' albums queued' + (r.truncated ? ' (first ' + r.tracks + ' only)' : ''));
  } catch (err) { showToast('Could not play: ' + err.message); }
  pollNowPlaying();
}

// Same idea as playAlbumsNow, but for a list of already-known track objects
// (the favorite tracks list) instead of album ids to look up.
async function playTracksNow(tracks) {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  try {
    const r = await api('/spotify-api/queue/play-tracks', {method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({tracks, device_id})});
    showToast(r.tracks + ' tracks queued' + (r.truncated ? ' (first ' + r.tracks + ' only)' : ''));
  } catch (err) { showToast('Could not play: ' + err.message); }
  pollNowPlaying();
}

// Plays these favorite artists' favorited music as one queue (the server builds
// it from local data: see build_artist_queue). shuffle=false: one artist after
// another; true: rounds of one track per artist.
async function playArtistsNow(artistIds, shuffle) {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  try {
    const r = await api('/spotify-api/queue/play-artists', {method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({artist_ids: artistIds, shuffle: !!shuffle, device_id})});
    showToast(r.tracks + ' tracks from ' + r.artists + ' artists queued' + (r.empty ? ' (' + r.empty + ' without favorites skipped)' : ''));
  } catch (err) { showToast(err.status === 404 ? 'No favorite tracks by these artists yet' : 'Could not play: ' + err.message); }
  pollNowPlaying();
}

// Fisher-Yates; never mutates the input (callers pass an already-filtered/
// sorted array they still render from afterward).
function shuffled(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// ---- navigation ----
// A small back-stack of view descriptors ({type, ...ids}) drives both the
// in-app Back button and cross-device sync: whichever device navigates writes
// its descriptor to the server, every other device polling it re-fetches and
// renders the same thing through this same renderDescriptor() function.

let navStack = [];
let currentDescriptor = {type: 'home'};

// The header button of the page being shown is highlighted (the same black
// "active" look as the other toggles). Every navigation -- goTo, goBack,
// another device's navigation, boot -- goes through renderDescriptor, so this
// is the one place that keeps it right. Pages with no header button (search,
// artist, album...) leave none selected.
const HEADER_BUTTON_FOR_VIEW = {home: 'recentlyPlayedButton', queue: 'queueViewButton', favorites: 'favoritesButton',
                                'favorite-tracks': 'favoriteTracksButton', 'favorite-artists': 'favoriteArtistsButton'};
function syncHeaderSelection(d) {
  const current = HEADER_BUTTON_FOR_VIEW[(d && d.type) || 'home'];
  for (const id of Object.values(HEADER_BUTTON_FOR_VIEW)) document.getElementById(id).classList.toggle('active', id === current);
}

async function renderDescriptor(d) {
  syncHeaderSelection(d);
  if (!d || d.type === 'home') { await loadRecentlyPlayed(); return; }
  if (d.type === 'search') { document.getElementById('searchInput').value = d.query || ''; await runSearch(d.query, d.kind || 'artist'); return; }
  if (d.type === 'artist') { await loadArtist(d.id, d.name); return; }
  if (d.type === 'album') { await loadAlbum(d.id); return; }
  if (d.type === 'dedup') { await loadDedup(d.id, d.name); return; }
  if (d.type === 'favorites') { await loadFavorites(); return; }
  if (d.type === 'favorite-tracks') { await loadFavoriteTracks(); return; }
  if (d.type === 'favorite-artists') { await loadFavoriteArtists(); return; }
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
document.getElementById('favoriteTracksButton').onclick = () => goTo({type: 'favorite-tracks'});
document.getElementById('favoriteArtistsButton').onclick = () => goTo({type: 'favorite-artists'});
document.getElementById('recentlyPlayedButton').onclick = () => goTo({type: 'home'});
document.getElementById('queueViewButton').onclick = () => goTo({type: 'queue'});

async function loadQueueView() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const q = await api('/spotify-api/queue');
    state.autoplay = q.autoplay;
    let currentFavorited = false;
    if (q.current && q.current.id) {
      try { currentFavorited = !!(await api('/spotify-api/favorite-tracks/' + q.current.id)).favorited; } catch (e) {}
    }
    renderQueueView(q, currentFavorited);
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function removeButton(list, index, uri) {
  const btn = iconButton(ICON_CROSS, 'Remove from queue');
  btn.onclick = async e => {
    e.stopPropagation();
    btn.disabled = true;
    try {
      await api('/spotify-api/queue/remove', {method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({list, index, uri})});
    } catch (err) {
      showToast(err.message === 'queue_changed' ? 'Queue changed, refreshed' : 'Could not remove: ' + err.message);
    }
    loadQueueView();
  };
  return btn;
}

function queueRow(track, tag, buttons) {
  const li = trackRow(track, buttons);
  li.querySelector('.sub').appendChild(el('span', 'badge', tag));
  return li;
}

// Manual items come first, then a boundary, then the automatic ones. A track
// that Spotify has already been handed (the last ~15s of the current song)
// is locked as "next" and can't be removed any more.
function renderQueueView(q, currentFavorited) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  if (q.current) {
    view.appendChild(el('h2', null, 'Now Playing'));
    const nowList = el('ul', 'list');
    nowList.appendChild(trackRow(q.current, [trackFavoriteButton(q.current, currentFavorited)]));
    view.appendChild(nowList);
  }
  const heading = el('div', 'row');
  heading.style.margin = '22px 0 10px';
  const upNext = el('h2', null, 'Up Next');
  upNext.style.margin = '0';
  heading.appendChild(upNext);
  const autoBtn = iconButton('<svg width="18" height="18" viewBox="0 0 20 20"><circle cx="10" cy="10" r="7.5" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M8.3 6.8L13.2 10l-4.9 3.2z" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round"/></svg>',
    'Auto up next', 'icon-btn');
  autoBtn.classList.toggle('active', state.autoplay);
  autoBtn.title = state.autoplay ? 'Auto up next: on' : 'Auto up next: off';
  autoBtn.onclick = async () => {
    autoBtn.disabled = true;
    try {
      const r = await api('/spotify-api/queue-settings', {method: 'PUT', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({autoplay: !state.autoplay})});
      state.autoplay = r.autoplay;
      state.autoplayLockUntil = Date.now() + 10000;   // a poll already in flight carries the old value
      showToast(!r.autoplay ? 'Auto up next off'
        : r.auto_count ? 'Auto up next on · ' + r.auto_count + ' tracks queued' : 'Auto up next on · nothing to add yet');
    } catch (err) { showToast('Could not change: ' + err.message); }
    loadQueueView();
  };
  heading.appendChild(autoBtn);
  const clearBtn = iconButton(ICON_TRASH, 'Clear queue');
  clearBtn.onclick = async () => {
    if (!confirm('Clear the whole queue (manual and auto)?')) return;
    clearBtn.disabled = true;
    try {
      await api('/spotify-api/queue/clear', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: '{}'});
      showToast('Queue cleared');
    } catch (err) { showToast('Could not clear: ' + err.message); }
    loadQueueView();
  };
  heading.appendChild(clearBtn);
  view.appendChild(heading);

  const list = el('ul', 'list');
  if (q.next) list.appendChild(queueRow(q.next, 'next · ' + q.next.kind, []));
  q.manual.forEach((t, i) => list.appendChild(queueRow(t, 'manual', [removeButton('manual', i, t.uri)])));
  if (q.auto.length) list.appendChild(el('li', 'boundary', 'Auto up next'));
  q.auto.forEach((t, i) => list.appendChild(
    queueRow(t, 'auto', [queueButton(t, loadQueueView), removeButton('auto', i, t.uri)])));
  if (!list.children.length) list.appendChild(el('li', 'empty', 'Nothing queued'));
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

// Sort order and its direction are preferences, not filters: they survive
// reloading the list and are remembered per browser. Each order keeps its own
// direction; the defaults are newest first for Year / Recently added and A to Z.
const FAV_ORDERS = [['year', 'Order: Year'], ['added', 'Order: Recently added'], ['alpha', 'Order: A–Z']];
const FAV_DEFAULT_DIRS = {year: 'desc', added: 'desc', alpha: 'asc'};
let favoritesOrder = 'year';
let favoritesDirs = Object.assign({}, FAV_DEFAULT_DIRS);
try {
  const o = localStorage.getItem('spotify_fav_order'); if (FAV_ORDERS.some(x => x[0] === o)) favoritesOrder = o;
  const d = JSON.parse(localStorage.getItem('spotify_fav_dirs') || '{}');
  for (const k of Object.keys(FAV_DEFAULT_DIRS)) if (d[k] === 'asc' || d[k] === 'desc') favoritesDirs[k] = d[k];
} catch (e) {}

// asc = smallest first: oldest year / oldest added / A to Z. Ties fall back to
// the name (always A to Z); albums with no release date always go last.
function sortFavorites(items, order, dir) {
  const sign = dir === 'asc' ? 1 : -1;
  const byName = (a, b) => (a.name || '').localeCompare(b.name || '', undefined, {sensitivity: 'base'});
  const cmp = {
    alpha: (a, b) => sign * byName(a, b),
    added: (a, b) => sign * ((a.added_at || 0) - (b.added_at || 0)) || byName(a, b),
    year: (a, b) => (!a.release_date - !b.release_date)
      || sign * (a.release_date || '').localeCompare(b.release_date || '') || byName(a, b),
  }[order];
  return items.slice().sort(cmp);
}

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
  filterRow.appendChild(buildFilterSelect(FAV_ORDERS, favoritesOrder, v => {
    favoritesOrder = v;
    try { localStorage.setItem('spotify_fav_order', v); } catch (e) {}
    renderFavoritesView();
  }));
  const dir = favoritesDirs[favoritesOrder];
  const dirBtn = iconButton(ICON_SORT_UPDOWN,
    dir === 'asc' ? 'Ascending (click for descending)' : 'Descending (click for ascending)');
  dirBtn.onclick = () => {
    favoritesDirs[favoritesOrder] = dir === 'asc' ? 'desc' : 'asc';
    try { localStorage.setItem('spotify_fav_dirs', JSON.stringify(favoritesDirs)); } catch (e) {}
    renderFavoritesView();
  };
  filterRow.appendChild(dirBtn);
  view.appendChild(filterRow);

  const filtered = sortFavorites(favoritesState, favoritesOrder, favoritesDirs[favoritesOrder]).filter(a => {
    if (favoritesFilter.artist && !(a.artists || []).includes(favoritesFilter.artist)) return false;
    const genres = a.genres || [];
    if (favoritesFilter.genre === UNTAGGED && genres.length) return false;
    if (favoritesFilter.genre && favoritesFilter.genre !== UNTAGGED && !genres.includes(favoritesFilter.genre)) return false;
    const era = eraOf(a.release_date);
    if (favoritesFilter.era === UNKNOWN_ERA && era) return false;
    if (favoritesFilter.era && favoritesFilter.era !== UNKNOWN_ERA && era !== favoritesFilter.era) return false;
    return true;
  });

  if (filtered.length) {
    // Plays what is listed below, in the order it is listed (current filters and sort).
    const playBtn = iconButton(ICON_PLAY, 'Play these ' + filtered.length + ' albums in this order', 'icon-btn active');
    playBtn.onclick = () => playAlbumsNow(filtered.map(a => a.id));
    filterRow.appendChild(playBtn);
    const shuffleBtn = iconButton(ICON_SHUFFLE, 'Shuffle-play these ' + filtered.length + ' albums');
    shuffleBtn.onclick = () => playAlbumsNow(shuffled(filtered).map(a => a.id));
    filterRow.appendChild(shuffleBtn);
  }

  const list = el('ul', 'list');
  if (!filtered.length) {
    list.appendChild(el('li', 'empty', favoritesState.length ? 'No favorites match these filters' : 'No favorites yet'));
  }
  for (const a of filtered) {
    const li = el('li', 'fav-item');
    li.appendChild(coverImg(a.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', a.name));
    const year = (a.release_date || '').slice(0, 4);
    meta.appendChild(el('div', 'sub', (a.artists || []).join(', ') + (year ? ' · ' + year : '')));
    meta.onclick = () => goTo({type: 'album', id: a.id});
    li.appendChild(meta);
    // Same three buttons as a favorite artist's row: play this album, shuffle
    // its tracks, un-favorite it.
    const playOne = iconButton(ICON_PLAY, 'Play ' + a.name, 'icon-btn active');
    playOne.onclick = () => playAlbumsNow([a.id], false);
    const shuffleOne = iconButton(ICON_SHUFFLE, 'Shuffle-play ' + a.name);
    shuffleOne.onclick = () => playAlbumsNow([a.id], true);
    const unfavBtn = iconButton(ICON_STAR, 'Remove from favorites', 'icon-btn active');
    unfavBtn.onclick = async () => {
      await api('/spotify-api/favorites/' + a.id, {method: 'DELETE'});
      favoritesState = favoritesState.filter(x => x.id !== a.id);
      renderFavoritesView();
    };
    for (const b of [playOne, shuffleOne, unfavBtn]) li.appendChild(b);
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

// ---- favorite tracks ----
// Independent from favorite albums (a track can be favorited without its
// album being, and vice versa) -- its own store, its own page, but the exact
// same filter/sort building blocks (COMMON_GENRES/eraOf/FAV_ORDERS/
// sortFavorites/buildFilterSelect) as the albums page above.

let trackFavoritesState = null;
let trackFavoritesFilter = {artist: '', genre: '', era: ''};
let trackFavoritesOrder = 'year';
let trackFavoritesDirs = Object.assign({}, FAV_DEFAULT_DIRS);
try {
  const o = localStorage.getItem('spotify_trackfav_order'); if (FAV_ORDERS.some(x => x[0] === o)) trackFavoritesOrder = o;
  const d = JSON.parse(localStorage.getItem('spotify_trackfav_dirs') || '{}');
  for (const k of Object.keys(FAV_DEFAULT_DIRS)) if (d[k] === 'asc' || d[k] === 'desc') trackFavoritesDirs[k] = d[k];
} catch (e) {}

async function loadFavoriteTracks() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const {items} = await api('/spotify-api/favorite-tracks');
    trackFavoritesState = items;
    trackFavoritesFilter = {artist: '', genre: '', era: ''};
    renderTrackFavoritesView();
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderTrackFavoritesView() {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Back'); back.onclick = () => goBack();
  crumbs.appendChild(back);
  view.appendChild(crumbs);
  view.appendChild(el('h2', null, 'Favorite Tracks'));

  const artists = [...new Set(trackFavoritesState.flatMap(t => t.artists || []))].sort();
  const eras = [...new Set(trackFavoritesState.map(t => eraOf(t.release_date)).filter(Boolean))].sort();
  const hasUnknownEra = trackFavoritesState.some(t => !eraOf(t.release_date));

  const filterRow = el('div', 'row');
  filterRow.style.marginBottom = '14px';
  filterRow.appendChild(buildFilterSelect(
    [['', 'All artists'], ...artists.map(a => [a, a])], trackFavoritesFilter.artist,
    v => { trackFavoritesFilter.artist = v; renderTrackFavoritesView(); }));
  filterRow.appendChild(buildFilterSelect(
    [['', 'All genres'], ...COMMON_GENRES.map(g => [g, g]), [UNTAGGED, 'Untagged']], trackFavoritesFilter.genre,
    v => { trackFavoritesFilter.genre = v; renderTrackFavoritesView(); }));
  const eraOptions = [['', 'All eras'], ...eras.map(e => [e, e])];
  if (hasUnknownEra) eraOptions.push([UNKNOWN_ERA, 'Unknown era']);
  filterRow.appendChild(buildFilterSelect(eraOptions, trackFavoritesFilter.era,
    v => { trackFavoritesFilter.era = v; renderTrackFavoritesView(); }));
  filterRow.appendChild(buildFilterSelect(FAV_ORDERS, trackFavoritesOrder, v => {
    trackFavoritesOrder = v;
    try { localStorage.setItem('spotify_trackfav_order', v); } catch (e) {}
    renderTrackFavoritesView();
  }));
  const dir = trackFavoritesDirs[trackFavoritesOrder];
  const dirBtn = iconButton(ICON_SORT_UPDOWN,
    dir === 'asc' ? 'Ascending (click for descending)' : 'Descending (click for ascending)');
  dirBtn.onclick = () => {
    trackFavoritesDirs[trackFavoritesOrder] = dir === 'asc' ? 'desc' : 'asc';
    try { localStorage.setItem('spotify_trackfav_dirs', JSON.stringify(trackFavoritesDirs)); } catch (e) {}
    renderTrackFavoritesView();
  };
  filterRow.appendChild(dirBtn);
  view.appendChild(filterRow);

  const filtered = sortFavorites(trackFavoritesState, trackFavoritesOrder, trackFavoritesDirs[trackFavoritesOrder]).filter(t => {
    if (trackFavoritesFilter.artist && !(t.artists || []).includes(trackFavoritesFilter.artist)) return false;
    const genres = t.genres || [];
    if (trackFavoritesFilter.genre === UNTAGGED && genres.length) return false;
    if (trackFavoritesFilter.genre && trackFavoritesFilter.genre !== UNTAGGED && !genres.includes(trackFavoritesFilter.genre)) return false;
    const era = eraOf(t.release_date);
    if (trackFavoritesFilter.era === UNKNOWN_ERA && era) return false;
    if (trackFavoritesFilter.era && trackFavoritesFilter.era !== UNKNOWN_ERA && era !== trackFavoritesFilter.era) return false;
    return true;
  });

  if (filtered.length) {
    // Plays what is listed below, in the order it is listed (current filters and sort).
    const playBtn = iconButton(ICON_PLAY, 'Play these ' + filtered.length + ' tracks in this order', 'icon-btn active');
    playBtn.onclick = () => playTracksNow(filtered);
    filterRow.appendChild(playBtn);
    const shuffleBtn = iconButton(ICON_SHUFFLE, 'Shuffle-play these ' + filtered.length + ' tracks');
    shuffleBtn.onclick = () => playTracksNow(shuffled(filtered));
    filterRow.appendChild(shuffleBtn);
  }

  const list = el('ul', 'list');
  if (!filtered.length) {
    list.appendChild(el('li', 'empty', trackFavoritesState.length ? 'No favorite tracks match these filters' : 'No favorite tracks yet'));
  }
  for (const t of filtered) {
    const li = el('li', 'fav-item');
    li.appendChild(coverImg(t.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', t.name));
    const year = (t.release_date || '').slice(0, 4);
    meta.appendChild(el('div', 'sub', (t.artists || []).join(', ') + ' · ' + t.album_name + (year ? ' · ' + year : '')));
    const playFromHere = () => playTrackNow(t);
    meta.onclick = playFromHere;
    li.appendChild(meta);
    li.appendChild(playRowButton(playFromHere));
    li.appendChild(queueButton(t));
    const unfavBtn = iconButton(ICON_HEART, 'Remove from favorites', 'icon-btn active');
    unfavBtn.onclick = async () => {
      await api('/spotify-api/favorite-tracks/' + t.id, {method: 'DELETE'});
      trackFavoritesState = trackFavoritesState.filter(x => x.id !== t.id);
      renderTrackFavoritesView();
    };
    li.appendChild(unfavBtn);
    const tags = el('div', 'genre-tags');
    for (const g of COMMON_GENRES) {
      const active = (t.genres || []).includes(g);
      const chip = el('button', active ? 'chip active' : 'chip', g);
      chip.onclick = async () => {
        const genres = t.genres || [];
        t.genres = active ? genres.filter(x => x !== g) : [...genres, g];
        await api('/spotify-api/favorite-tracks/' + t.id + '/genres', {method: 'PUT', headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({genres: t.genres})});
        renderTrackFavoritesView();
      };
      tags.appendChild(chip);
    }
    li.appendChild(tags);
    list.appendChild(li);
  }
  view.appendChild(list);
}

// ---- favorite artists ----
// Same building blocks as the album/track favorites pages, minus the Artist
// filter (the row *is* the artist). An artist's Year/Era is the date of their
// earliest album, stored when they're favorited (see earliestRelease), so
// "Year" here means when they started, not a release.
const ARTIST_FAV_ORDERS = FAV_ORDERS;
let artistFavoritesState = null;
let artistFavoritesGenre = '';
let artistFavoritesEra = '';
let artistFavoritesOrder = 'year';
let artistFavoritesDirs = Object.assign({}, FAV_DEFAULT_DIRS);
try {
  const o = localStorage.getItem('spotify_artistfav_order'); if (ARTIST_FAV_ORDERS.some(x => x[0] === o)) artistFavoritesOrder = o;
  const d = JSON.parse(localStorage.getItem('spotify_artistfav_dirs') || '{}');
  for (const k of Object.keys(FAV_DEFAULT_DIRS)) if (d[k] === 'asc' || d[k] === 'desc') artistFavoritesDirs[k] = d[k];
} catch (e) {}

async function loadFavoriteArtists() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const {items} = await api('/spotify-api/favorite-artists');
    artistFavoritesState = items;
    artistFavoritesGenre = '';
    artistFavoritesEra = '';
    renderArtistFavoritesView();
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderArtistFavoritesView() {
  const view = document.getElementById('view');
  view.innerHTML = '';
  const crumbs = el('div', 'crumbs');
  const back = el('a', null, '← Back'); back.onclick = () => goBack();
  crumbs.appendChild(back);
  view.appendChild(crumbs);
  view.appendChild(el('h2', null, 'Favorite Artists'));

  const filterRow = el('div', 'row');
  filterRow.style.marginBottom = '14px';
  filterRow.appendChild(buildFilterSelect(
    [['', 'All genres'], ...COMMON_GENRES.map(g => [g, g]), [UNTAGGED, 'Untagged']], artistFavoritesGenre,
    v => { artistFavoritesGenre = v; renderArtistFavoritesView(); }));
  const artistEras = [...new Set(artistFavoritesState.map(a => eraOf(a.release_date)).filter(Boolean))].sort();
  const artistEraOptions = [['', 'All eras'], ...artistEras.map(e => [e, e])];
  if (artistFavoritesState.some(a => !eraOf(a.release_date))) artistEraOptions.push([UNKNOWN_ERA, 'Unknown era']);
  filterRow.appendChild(buildFilterSelect(artistEraOptions, artistFavoritesEra,
    v => { artistFavoritesEra = v; renderArtistFavoritesView(); }));
  filterRow.appendChild(buildFilterSelect(ARTIST_FAV_ORDERS, artistFavoritesOrder, v => {
    artistFavoritesOrder = v;
    try { localStorage.setItem('spotify_artistfav_order', v); } catch (e) {}
    renderArtistFavoritesView();
  }));
  const dir = artistFavoritesDirs[artistFavoritesOrder];
  const dirBtn = iconButton(ICON_SORT_UPDOWN,
    dir === 'asc' ? 'Ascending (click for descending)' : 'Descending (click for ascending)');
  dirBtn.onclick = () => {
    artistFavoritesDirs[artistFavoritesOrder] = dir === 'asc' ? 'desc' : 'asc';
    try { localStorage.setItem('spotify_artistfav_dirs', JSON.stringify(artistFavoritesDirs)); } catch (e) {}
    renderArtistFavoritesView();
  };
  filterRow.appendChild(dirBtn);
  view.appendChild(filterRow);

  const filtered = sortFavorites(artistFavoritesState, artistFavoritesOrder, artistFavoritesDirs[artistFavoritesOrder]).filter(a => {
    const genres = a.genres || [];
    if (artistFavoritesGenre === UNTAGGED && genres.length) return false;
    if (artistFavoritesGenre && artistFavoritesGenre !== UNTAGGED && !genres.includes(artistFavoritesGenre)) return false;
    const era = eraOf(a.release_date);
    if (artistFavoritesEra === UNKNOWN_ERA && era) return false;
    if (artistFavoritesEra && artistFavoritesEra !== UNKNOWN_ERA && era !== artistFavoritesEra) return false;
    return true;
  });

  if (filtered.length) {
    // In the order listed below / rounds of one track per artist. Artists with no favorited tracks are skipped.
    const ids = filtered.map(a => a.id);
    const playBtn = iconButton(ICON_PLAY, 'Play these ' + filtered.length + ' artists in this order', 'icon-btn active');
    playBtn.onclick = () => playArtistsNow(ids, false);
    filterRow.appendChild(playBtn);
    const shuffleBtn = iconButton(ICON_SHUFFLE, 'Shuffle-play these ' + filtered.length + ' artists');
    shuffleBtn.onclick = () => playArtistsNow(ids, true);
    filterRow.appendChild(shuffleBtn);
  }

  const list = el('ul', 'list');
  if (!filtered.length) {
    list.appendChild(el('li', 'empty', artistFavoritesState.length ? 'No favorite artists match this filter' : 'No favorite artists yet'));
  }
  for (const a of filtered) {
    const li = el('li', 'fav-item');
    li.appendChild(coverImg(a.image));
    const meta = el('div', 'meta');
    meta.appendChild(el('div', 'title', a.name));
    const since = (a.release_date || '').slice(0, 4);
    meta.appendChild(el('div', 'sub', (since ? 'since ' + since + ' · ' : '') +
      (a.track_count ? a.track_count + ' favorite track' + (a.track_count === 1 ? '' : 's') : 'no favorite tracks yet')));
    meta.onclick = () => goTo({type: 'artist', id: a.id, name: a.name});
    li.appendChild(meta);
    // Just this artist: their favorited music in order / shuffled. Nothing to
    // play when none of it is favorited yet, so the buttons are disabled then.
    const playOne = iconButton(ICON_PLAY, 'Play ' + a.name, 'icon-btn active');
    playOne.onclick = () => playArtistsNow([a.id], false);
    const shuffleOne = iconButton(ICON_SHUFFLE, 'Shuffle-play ' + a.name);
    shuffleOne.onclick = () => playArtistsNow([a.id], true);
    if (!a.track_count) {
      for (const b of [playOne, shuffleOne]) { b.disabled = true; b.title = a.name + ' has no favorite tracks yet'; }
    }
    li.appendChild(playOne);
    li.appendChild(shuffleOne);
    const unfavBtn = iconButton(ICON_PERSON, 'Remove from favorite artists', 'icon-btn active');
    unfavBtn.onclick = async () => {
      await api('/spotify-api/favorite-artists/' + a.id, {method: 'DELETE'});
      artistFavoritesState = artistFavoritesState.filter(x => x.id !== a.id);
      renderArtistFavoritesView();
    };
    li.appendChild(unfavBtn);
    const tags = el('div', 'genre-tags');
    for (const g of COMMON_GENRES) {
      const active = (a.genres || []).includes(g);
      const chip = el('button', active ? 'chip active' : 'chip', g);
      chip.onclick = async () => {
        const genres = a.genres || [];
        a.genres = active ? genres.filter(x => x !== g) : [...genres, g];
        await api('/spotify-api/favorite-artists/' + a.id + '/genres', {method: 'PUT', headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({genres: a.genres})});
        renderArtistFavoritesView();
      };
      tags.appendChild(chip);
    }
    li.appendChild(tags);
    list.appendChild(li);
  }
  view.appendChild(list);
}

// ---- theme ----
// The class is already applied by the tiny blocking script in <head> (before
// paint); this just wires up the click and keeps localStorage in sync.
document.getElementById('logoButton').onclick = () => {
  const dark = document.documentElement.classList.toggle('dark');
  document.getElementById('themeColorMeta').setAttribute('content', dark ? '#000000' : '#ffffff');
  document.getElementById('appleStatusBarMeta').setAttribute('content', dark ? 'black-translucent' : 'default');
  try { localStorage.setItem('spotify_dark', dark ? '1' : '0'); } catch (e) {}
};

// ---- search / browse ----

document.getElementById('coversButton').classList.toggle('active', state.showCovers);
document.getElementById('coversButton').onclick = () => {
  state.showCovers = !state.showCovers;
  localStorage.setItem('spotify_show_covers', state.showCovers ? '1' : '0');
  document.getElementById('coversButton').classList.toggle('active', state.showCovers);
  applyCoversVisibility();
};

// Full-screen mode: CSS-only layout (works on iPhone, where the Fullscreen API
// is unavailable for pages) plus the browser's real full screen where offered.
function setFullscreenMode(on) {
  if (on && document.getElementById('nowplaying').style.display === 'none') { showToast('Nothing playing'); return; }
  document.body.classList.toggle('fs', on);
  document.getElementById('fullscreenButton').classList.toggle('active', on);
  syncNpLogo();
  try {
    const de = document.documentElement;
    if (on && !document.fullscreenElement && de.requestFullscreen) de.requestFullscreen().catch(() => {});
    else if (!on && document.fullscreenElement && document.exitFullscreen) document.exitFullscreen().catch(() => {});
  } catch (e) {}
}
document.getElementById('fullscreenButton').onclick = () => setFullscreenMode(!document.body.classList.contains('fs'));
document.addEventListener('fullscreenchange', () => {
  if (!document.fullscreenElement && document.body.classList.contains('fs')) setFullscreenMode(false);
});

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
// Enter doesn't repeat whichever type button was last pressed -- it asks the
// server for whichever type's top result is an exact name match (falling back
// to artist), so typing a track or album title and hitting Enter doesn't land
// on an unrelated artist search.
document.getElementById('searchInput').addEventListener('keydown', e => {
  if (e.key === 'Enter') triggerSearch('best');
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
  try {
    const url = kind === 'best' ? '/spotify-api/search/best?q=' + encodeURIComponent(query)
                                 : '/spotify-api/search/' + kind + 's?q=' + encodeURIComponent(query);
    const result = await api(url);
    const resolvedKind = result.kind || kind;   // 'best' resolves to whichever type actually matched
    lastSearchKind = resolvedKind;
    searchState = {query, kind: resolvedKind, items: result.items, has_more: result.has_more};
    renderSearchResults();
  } catch (e) { err.textContent = 'Search failed: ' + e.message; }
}

async function loadMoreSearch(btn) {
  btn.disabled = true;
  btn.title = 'Loading…';
  try {
    const page = await api('/spotify-api/search/' + searchState.kind + 's?q=' + encodeURIComponent(searchState.query) +
                            '&offset=' + searchState.items.length);
    searchState.items = searchState.items.concat(page.items);
    searchState.has_more = page.has_more;
    renderSearchResults();
  } catch (e) {
    btn.disabled = false;
    btn.title = 'More results';
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

// A track's own favorite heart, independent of whether its album is
// favorited (separate store, see the backend endpoint docs). `favorited` is
// the caller's already-known initial state -- checking is a local sqlite
// lookup with no Spotify cost, so callers rendering a whole list of rows
// fetch all of them up front in parallel rather than each button checking
// for itself and flashing in a moment later. `t` must carry everything
// favorite-tracks needs to store (uri/name/artists/image/album_id/
// album_name/release_date/duration_ms) -- exactly the shape trackRow()
// already expects its rows to have.
function trackFavoriteButton(t, favorited) {
  const btn = iconButton(ICON_HEART, favorited ? 'Remove from favorites' : 'Add to favorites');
  let isFav = !!favorited;
  const sync = () => {
    btn.classList.toggle('active', isFav);
    btn.title = isFav ? 'Remove from favorites' : 'Add to favorites';
  };
  sync();
  btn.onclick = async e => {
    e.stopPropagation();
    isFav = !isFav;
    sync();
    if (isFav) {
      await api('/spotify-api/favorite-tracks/' + t.id, {method: 'PUT', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({uri: t.uri, name: t.name, artists: t.artists, image: t.image,
                               album_id: t.album_id, album_name: t.album_name,
                               release_date: t.release_date, duration_ms: t.duration_ms})});
    } else {
      await api('/spotify-api/favorite-tracks/' + t.id, {method: 'DELETE'});
    }
  };
  return btn;
}

function queueButton(track, onDone) {
  const btn = iconButton(ICON_PLUS, 'Add to queue');
  btn.onclick = async e => {
    e.stopPropagation();
    btn.disabled = true;
    try {
      await api('/spotify-api/queue/add', {method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({track})});
      showToast('Added to queue');
      if (onDone) onDone();
    } catch (err) {
      showToast('Could not add to queue: ' + err.message);
    } finally { btn.disabled = false; }
  };
  return btn;
}

function trackRow(t, actionBtn, opts) {
  // Start the track's own album context at this track, same continuation
  // behavior as every other play entry point in the app.
  const playFromHere = () => playTrackNow(t);
  const li = el('li');
  li.appendChild(coverImg(t.image));
  const meta = el('div', 'meta');
  const title = el('div', 'title', t.name);
  // Opt-in per call site (Recently Played) rather than the trackRow default,
  // so the queue page's rows (also built from trackRow) are unaffected.
  if (opts && opts.titleLinksToAlbum && t.album_id) {
    title.classList.add('link');
    title.onclick = e => { e.stopPropagation(); goTo({type: 'album', id: t.album_id}); };
  }
  meta.appendChild(title);
  meta.appendChild(el('div', 'sub', t.artists.join(', ') + ' · ' + t.album_name + ' · ' + fmtDuration(t.duration_ms)));
  meta.onclick = playFromHere;
  li.appendChild(meta);
  li.appendChild(playRowButton(playFromHere));
  for (const b of (actionBtn ? [].concat(actionBtn) : [queueButton(t)])) li.appendChild(b);
  return li;
}

async function loadRecentlyPlayed() {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const {items} = await api('/spotify-api/recently-played');
    // Local sqlite lookups (no Spotify cost), so fetching every row's
    // favorite state up front and in parallel is cheap -- same pattern as
    // the album page's per-track stars.
    const favStates = await Promise.all(items.map(t =>
      api('/spotify-api/favorite-tracks/' + t.id).catch(() => ({favorited: false}))));
    renderRecentlyPlayedView(items, favStates);
  } catch (e) { view.innerHTML = '<div class="error">' + e.message + '</div>'; }
}

function renderRecentlyPlayedView(items, favStates) {
  const view = document.getElementById('view');
  view.innerHTML = '';
  view.appendChild(el('h2', null, 'Recently Played'));
  const list = el('ul', 'list');
  if (!items.length) list.appendChild(el('li', 'empty', 'Nothing played yet'));
  items.forEach((t, i) => list.appendChild(trackRow(t, [queueButton(t), trackFavoriteButton(t, favStates[i] && favStates[i].favorited)],
                                                     {titleLinksToAlbum: true})));
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
    const moreBtn = iconButton(ICON_MORE, 'More results');
    moreBtn.style.marginTop = '8px';
    moreBtn.onclick = () => loadMoreSearch(moreBtn);
    view.appendChild(moreBtn);
  }
}

// An artist's Year/Era is the date of their earliest album (any release_date
// that isn't a plausible year, e.g. a bogus 0000/1800s placeholder, is ignored).
function earliestRelease(albums) {
  const dates = (albums || []).map(a => a.release_date || '').filter(d => /^\d{4}/.test(d) && parseInt(d.slice(0, 4), 10) >= 1900);
  return dates.length ? dates.sort()[0] : null;
}

async function loadArtist(id, name, refresh) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const albums = await api('/spotify-api/artists/' + id + '/albums' + (refresh ? '?refresh=1' : ''));
    let favState = {favorited: false};
    try { favState = await api('/spotify-api/favorite-artists/' + id); } catch (e) {}
    const firstRelease = earliestRelease(albums.items);
    const artistImage = albums.artist_image || (albums.items[0] || {}).image || null;   // own picture, else the newest album's cover
    // Artists favorited before Year/Era existed have no date yet: fill it in
    // from the album list that's already on screen, no extra request to Spotify.
    if (favState.favorited && !favState.release_date && firstRelease) {
      api('/spotify-api/favorite-artists/' + id, {method: 'PUT', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({name, image: artistImage, release_date: firstRelease})}).catch(() => {});
    }
    renderArtistView({id, name, albums: albums.items, favorited: favState.favorited, firstRelease,
                      image: albums.artist_image || null});
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
  // Follows the covers switch like every other cover (coverImg hides it when off).
  heading.appendChild(coverImg(artist.image, 'cover lg'));
  const artistTitle = el('h2', null, artist.name);
  artistTitle.style.margin = '0';
  heading.appendChild(artistTitle);
  // Favorite this artist (independent of albums/tracks). The cover is the
  // newest album's -- the artist page doesn't carry a picture of its own.
  const favArtistBtn = iconButton(ICON_PERSON, 'Add to favorite artists');
  let artistFavorited = !!artist.favorited;
  const syncFavArtist = () => {
    favArtistBtn.classList.toggle('active', artistFavorited);
    favArtistBtn.title = artistFavorited ? 'Remove from favorite artists' : 'Add to favorite artists';
  };
  syncFavArtist();
  favArtistBtn.onclick = async () => {
    artistFavorited = !artistFavorited;
    syncFavArtist();
    if (artistFavorited) {
      await api('/spotify-api/favorite-artists/' + artist.id, {method: 'PUT', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({name: artist.name, image: artist.image || ((artist.albums || [])[0] || {}).image || null,
                               release_date: artist.firstRelease || null})});
    } else {
      await api('/spotify-api/favorite-artists/' + artist.id, {method: 'DELETE'});
    }
  };
  heading.appendChild(favArtistBtn);
  const refreshBtn = iconButton('<svg width="18" height="18" viewBox="0 0 20 20"><path d="M15.5 5.5A7 7 0 1 0 17 10" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><path d="M15.5 2v4h-4" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg>',
    'Update cache');
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
    items.forEach(a => {
      const li = el('li');
      li.appendChild(coverImg(a.image));
      const meta = el('div', 'meta');
      meta.appendChild(el('div', 'title', a.name));
      meta.appendChild(el('div', 'sub', (a.release_date || '').slice(0, 4) + ' · ' + a.total_tracks + ' tracks'));
      meta.onclick = () => goTo({type: 'album', id: a.id});
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
  const playAll = iconButton(ICON_PLAY, 'Play all', 'icon-btn active');
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
    li.appendChild(playRowButton(() => playUris(queueFrom(i))));
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

async function loadAlbum(id, refresh) {
  const view = document.getElementById('view');
  view.innerHTML = '<div class="empty">Loading…</div>';
  try {
    const album = await api('/spotify-api/albums/' + id + (refresh ? '?refresh=1' : ''));
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
  // Each artist is a link to that artist's albums (when their ids are known).
  const sub = el('div', 'sub');
  (album.artists || []).forEach((name, i) => {
    if (i) sub.appendChild(document.createTextNode(', '));
    const id = (album.artist_ids || [])[i];
    if (!id) { sub.appendChild(document.createTextNode(name)); return; }
    const link = el('a', 'link', name);
    link.onclick = () => goTo({type: 'artist', id, name});
    sub.appendChild(link);
  });
  sub.appendChild(document.createTextNode(' · ' + (album.release_date || '')));
  meta.appendChild(sub);
  header.appendChild(meta);
  view.appendChild(header);

  const actions = el('div', 'row');
  actions.style.marginTop = '10px';
  // Solid black (the "active" look) marks it as the primary action next to the outlined buttons.
  const playAlbumBtn = iconButton(ICON_PLAY, 'Play album', 'icon-btn active');
  playAlbumBtn.onclick = () => playAlbumNow(album.id);
  actions.appendChild(playAlbumBtn);

  const favBtn = iconButton(ICON_STAR, 'Add to favorites');
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

  const refreshBtn = iconButton('<svg width="18" height="18" viewBox="0 0 20 20"><path d="M15.5 5.5A7 7 0 1 0 17 10" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/><path d="M15.5 2v4h-4" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg>',
    'Update cache');
  refreshBtn.onclick = () => loadAlbum(album.id, true);
  actions.appendChild(refreshBtn);
  view.appendChild(actions);

  // Fetched up front (all local sqlite lookups, no Spotify calls, so cheap
  // and safe in parallel) so every row's star shows the right state on first
  // paint instead of flipping a moment after the album renders.
  const trackFavStates = await Promise.all(album.tracks.map(t =>
    api('/spotify-api/favorite-tracks/' + t.id).catch(() => ({favorited: false}))));

  const list = el('ul', 'list');
  album.tracks.forEach((t, i) => {
    // Start the real album context at this track (not just a single-track
    // queue), so playback continues through the rest of the album afterward --
    // same continuation behavior as "Play album".
    const summary = {id: t.id, uri: t.uri, name: t.name, image: album.image, artists: t.artists,
                     album_id: album.id, album_name: album.name, release_date: album.release_date,
                     duration_ms: t.duration_ms};
    const playFromHere = () => playTrackNow(summary);
    const li = el('li');
    const meta2 = el('div', 'meta');
    meta2.appendChild(el('div', 'title', t.track_number + '. ' + t.name));
    meta2.appendChild(el('div', 'sub', (t.artists || []).join(', ') + ' · ' + fmtDuration(t.duration_ms)));
    meta2.onclick = playFromHere;
    li.appendChild(meta2);
    li.appendChild(playRowButton(playFromHere));
    li.appendChild(queueButton(summary));
    li.appendChild(trackFavoriteButton(summary, trackFavStates[i].favorited));
    list.appendChild(li);
  });
  view.appendChild(list);
}

// ---- now playing / transport ----

async function skipPrevious() {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/player/previous', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
}
async function skipNext() {
  await ensureAudioUnlocked();
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/queue/next', {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
  pollNowPlaying();
}
document.getElementById('npPrev').onclick = skipPrevious;
document.getElementById('npNext').onclick = skipNext;
// want: true = make sure it plays, false = make sure it pauses, omitted =
// toggle (lock-screen play/pause pass it so a stale button can't flip the
// wrong way). Exactly one action in flight at a time: a click while one is
// still pending is ignored outright, the button is disabled meanwhile, and
// the icon is only ever set once -- to whatever actually landed -- never
// flipped optimistically and never corrected later by an independent timer.
// That's what "click Play, it's not clickable again until Play has actually
// settled, only then can you click Pause" means: one clear action per click,
// nothing running in the background afterward that could race a later one.
let playPauseBusy = false;
async function togglePlayPause(want) {
  if (playPauseBusy) return;
  playPauseBusy = true;
  const btn = document.getElementById('npPlay');
  btn.disabled = true;
  try {
    await ensureAudioUnlocked();
    let handled = false;
    // Fast path: this tab *is* the Spotify device, so the SDK already knows
    // whether it is playing and can pause/resume it directly -- no V1 or
    // Spotify Web API round trips (each ~0.3s) before anything happens.
    if (fastPlayEnabled && state.player && state.deviceId) {
      let st = null;
      try { st = await state.player.getCurrentState(); } catch (e) {}
      if (st) {
        const playing = !st.paused;
        const wantPlay = typeof want === 'boolean' ? want : !playing;
        if (wantPlay === playing) {
          setPlayButton(playing);
          handled = true;
        } else {
          try {
            if (wantPlay) await lockAudioStartFirst();
            if (wantPlay) await state.player.resume(); else await state.player.pause();
            setPlayButton(wantPlay);
            if (npState) npState = Object.assign({}, npState, {progressMs: st.position, at: Date.now(), playing: wantPlay});
            handled = true;
          } catch (e) { /* fall through to the Web API path below */ }
        }
      }
    }
    if (!handled) {
      const device_id = await ensureDevice();
      if (!device_id) return;
      const np = await api('/spotify-api/player/now-playing');
      const wantPlay = typeof want === 'boolean' ? want : !np.playing;
      if (wantPlay !== np.playing) {
        if (wantPlay && np.live === false && np.track) {
          // np.live===false means this is the cached snapshot from before a
          // reload -- this device_id is brand new and was never given a
          // context to resume, so a bare "play" has nothing to continue.
          // Explicitly restart the same track at its saved position instead
          // of silently doing nothing.
          const body = {device_id, uris: [np.track.uri], position_ms: np.progress_ms || 0};
          await api('/spotify-api/player/play', {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)});
        } else {
          await api('/spotify-api/player/' + (wantPlay ? 'play' : 'pause'), {method: 'PUT', headers: {'Content-Type': 'application/json'}, body: JSON.stringify({device_id})});
        }
      }
      await pollNowPlaying();   // reflects whatever actually happened, settled
    }
  } finally {
    playPauseBusy = false;
    btn.disabled = false;
  }
}
// Play/pause share one button; the glyph shows the action a click will take.
const ICON_PLAY = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M6 3.5v13L16.5 10z" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linejoin="round"/></svg>';
const ICON_PAUSE = '<svg width="18" height="18" viewBox="0 0 20 20"><path d="M6.5 4v12M13.5 4v12" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/></svg>';
function setPlayButton(playing) {
  const b = document.getElementById('npPlay');
  b.innerHTML = playing ? ICON_PAUSE : ICON_PLAY;
  b.title = playing ? 'Pause' : 'Play';
  b.setAttribute('aria-label', b.title);
}
setPlayButton(false);
document.getElementById('npPlay').onclick = () => togglePlayPause();

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
// instead of jumping once every 5 seconds.
let npState = null;

// Fullscreen-only heart for whatever's currently playing (see the CSS above --
// hidden in the compact bar). Only re-checked when the track actually
// changes, not on every 5s poll, so it doesn't flash or spam sqlite lookups.
let npFavTrackUri = null;
async function syncNpFavoriteButton(track) {
  const btn = document.getElementById('npFavorite');
  if (!track || !track.uri) { npFavTrackUri = null; return; }
  if (track.uri === npFavTrackUri) return;
  npFavTrackUri = track.uri;
  const id = track.uri.split(':').pop();
  let favorited = false;
  try { const st = await api('/spotify-api/favorite-tracks/' + id); favorited = !!st.favorited; } catch (e) {}
  if (track.uri !== npFavTrackUri) return;   // a newer track took over while this was in flight
  const sync = fav => {
    btn.classList.toggle('active', fav);
    btn.title = fav ? 'Remove from favorites' : 'Add to favorites';
  };
  sync(favorited);
  btn.onclick = async () => {
    favorited = !favorited;
    sync(favorited);
    if (favorited) {
      await api('/spotify-api/favorite-tracks/' + id, {method: 'PUT', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({uri: track.uri, name: track.name, artists: track.artists, image: track.image,
                               album_id: track.album_id, album_name: track.album,
                               release_date: track.release_date, duration_ms: track.duration_ms})});
    } else {
      await api('/spotify-api/favorite-tracks/' + id, {method: 'DELETE'});
    }
  };
}

async function pollNowPlaying() {
  try {
    const np = await api('/spotify-api/player/now-playing');
    const bar = document.getElementById('nowplaying');
    if (!np.track) {
      // Only true when nothing has ever played this session (no server-side
      // cache to fall back to yet) -- once something has played, the backend
      // always returns that last snapshot instead of an empty track.
      bar.style.display = 'none';
      npState = null;
      updateMediaSession(null);
      return;
    }
    bar.style.display = 'flex';
    const cover = document.getElementById('npCover');
    cover.dataset.src = np.track.image || '';
    if (state.showCovers && np.track.image) { cover.src = np.track.image; cover.style.display = ''; } else { cover.style.display = 'none'; }
    syncNpLogo();
    const npTitle = document.getElementById('npTitle');
    npTitle.textContent = np.track.name;
    npTitle.onclick = np.track.album_id ? (() => goTo({type: 'album', id: np.track.album_id})) : null;
    npTitle.style.cursor = np.track.album_id ? 'pointer' : '';
    document.getElementById('npSub').textContent = [np.track.artists.join(', '), np.track.album, (np.track.release_date || '').slice(0, 4)].filter(Boolean).join(' · ');
    setPlayButton(np.playing);
    syncNpFavoriteButton(np.track);
    npState = {progressMs: np.progress_ms || 0, durationMs: np.track.duration_ms || 0, playing: np.playing, at: Date.now()};
    if (Date.now() > (state.autoplayLockUntil || 0)) state.autoplay = !!np.autoplay;
    updateMediaSession(np);
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
async function seekToMs(position_ms) {
  const device_id = await ensureDevice();
  if (!device_id) return;
  await api('/spotify-api/player/seek?position_ms=' + position_ms + '&device_id=' + encodeURIComponent(device_id), {method: 'PUT'});
  if (npState) { npState.progressMs = position_ms; npState.at = Date.now(); }
  if (sdkPos && sdkPos.uri === mediaTrackUri) { sdkPos.position = position_ms; sdkPos.at = Date.now(); }
  updateMediaPosition();
}
progressInput.addEventListener('change', async () => {
  try { await seekToMs(Math.round(Number(progressInput.value))); } finally { draggingProgress = false; }
});

// ?fastplay=0 (remembered, ?fastplay=1 undoes it): play/pause through V1 and the
// Web API instead of straight through the SDK -- for comparing the two.
const fastPlayEnabled = (() => {
  try {
    const q = new URLSearchParams(location.search).get('fastplay');
    if (q !== null) localStorage.setItem('fastPlay', q);
    return localStorage.getItem('fastPlay') !== '0';
  } catch (e) { return true; }
})();

// ---- page-owned silent audio ----
// The Web Playback SDK plays inside its own cross-origin iframe ("Spotify
// Embedded Player"). A silent, looping element owned by *this* page makes the
// page a media player as far as the OS is concerned: it keeps iOS from
// suspending the page in the gap between two tracks and routes the lock-screen
// buttons to the Media Session handlers below (i.e. through V1's queue).
// It shows no artwork or title of its own -- nothing here tries to control what
// the lock screen displays. Opt out with ?lockscreen=0 (remembered), back in
// with ?lockscreen=1, in case a device pauses Spotify when a second audio
// element starts.
const lockAudioEnabled = (() => {
  try {
    const q = new URLSearchParams(location.search).get('lockscreen');
    if (q !== null) localStorage.setItem('lockscreenAudio', q);
    return localStorage.getItem('lockscreenAudio') !== '0';
  } catch (e) { return true; }
})();
let lockAudio = null;
let lockAudioIdleTimer = null;

function silentWavUrl() {
  // 5 minutes of 8 kHz 8-bit mono (2.4 MB): the element's own timeline is what
  // iOS shows when it ignores setPositionState, so it must rarely wrap to 0.
  const rate = 8000, samples = rate * 300, buf = new ArrayBuffer(44 + samples), v = new DataView(buf);
  const str = (o, t) => { for (let i = 0; i < t.length; i++) v.setUint8(o + i, t.charCodeAt(i)); };
  str(0, 'RIFF'); v.setUint32(4, 36 + samples, true); str(8, 'WAVE'); str(12, 'fmt ');
  v.setUint32(16, 16, true); v.setUint16(20, 1, true); v.setUint16(22, 1, true);
  v.setUint32(24, rate, true); v.setUint32(28, rate, true); v.setUint16(32, 1, true); v.setUint16(34, 8, true);
  str(36, 'data'); v.setUint32(40, samples, true);
  new Uint8Array(buf, 44).fill(0x80);   // unsigned 8-bit: 0x80 is silence
  return URL.createObjectURL(new Blob([buf], {type: 'audio/wav'}));
}

function getLockAudio() {
  if (!lockAudioEnabled) return null;
  if (!lockAudio) {
    lockAudio = new Audio(silentWavUrl());
    lockAudio.loop = true;
    lockAudio.setAttribute('playsinline', '');
    let lastAssert = 0;
    // The element's timeline restarting (its loop, a seek, play after pause)
    // makes iOS show *its* position; put ours back straight away.
    for (const ev of ['seeked', 'playing', 'play']) lockAudio.addEventListener(ev, () => updateMediaPosition());
    lockAudio.addEventListener('timeupdate', () => {
      if (Date.now() - lastAssert < 1000) return;
      lastAssert = Date.now();
      updateMediaPosition();
    });
  }
  return lockAudio;
}

// Called at the top of every transport click until the element has played once:
// a play()/pause() inside a user gesture is what lets the element be started
// later without one. After that it is skipped -- this play()+pause() flick used
// to run on every click while the element was idle, which is right when a
// resume now starts (no network wait in between any more), and audible as a
// hiccup at the start of playback.
let lockAudioUnlocked = false;
function unlockLockAudio() {
  const a = getLockAudio();
  if (!a || lockAudioUnlocked || !a.paused) return;
  a.play().catch(() => {});
  a.pause();
}

function lockAudioPlay() {
  clearTimeout(lockAudioIdleTimer); lockAudioIdleTimer = null;
  const a = getLockAudio();
  if (a && a.paused) a.play().then(() => { lockAudioUnlocked = true; }, () => {});
}

// Before an instant SDK resume: get the silent element going first and give it
// a moment. Starting it *after* the music (the poll that follows a resume used
// to) put a second audio start into the first few hundred ms of playback -- a
// hiccup, but only when the element had gone idle (paused >15s), so only the
// first pause/play of a pair showed it.
async function lockAudioStartFirst() {
  clearTimeout(lockAudioIdleTimer); lockAudioIdleTimer = null;
  const a = getLockAudio();
  if (!a || !a.paused) return;
  try {
    await Promise.race([a.play().then(() => { lockAudioUnlocked = true; }), new Promise(r => setTimeout(r, 300))]);
  } catch (e) {}
}

// Paused Spotify keeps the silent audio going for a moment: the gap between two
// tracks briefly reports "not playing", and pausing here would defeat the point.
function lockAudioIdleSoon(immediately) {
  if (!lockAudio) return;
  if (immediately) { clearTimeout(lockAudioIdleTimer); lockAudioIdleTimer = null; lockAudio.pause(); return; }
  if (lockAudioIdleTimer) return;
  lockAudioIdleTimer = setTimeout(() => { lockAudioIdleTimer = null; if (lockAudio) lockAudio.pause(); }, 15000);
}

// ---- Media Session (lock screen / control centre / headset buttons) ----
// Routes the OS transport buttons through the same functions as the on-page
// buttons, so they honour V1's queue, and reports the playback position so the
// lock-screen progress bar tracks the real one. Best effort: each piece is
// optional per browser.
const hasMediaSession = 'mediaSession' in navigator && typeof MediaMetadata === 'function';
let mediaTrackUri = null;

// A fixed, set-once identity (no artwork, no per-track updates -- the whole
// "reclaim the lock screen from the SDK iframe" approach was tried and
// dropped, see the git history around 2026-09-19). Brought back 2026-09-22:
// with mediaSession.metadata left unset entirely, iOS seemed to stop treating
// the page as a real background media session at all -- not just showing the
// wrong transport buttons (a separate, still-unsolved problem), but actually
// suspending playback on lock. This alone, not the button layout, is why it's
// here again.
const LOCKSCREEN_META = {title: 'Spotify', artist: 'V1', album: '', artwork: []};

function updateMediaPosition() {
  if (!hasMediaSession || !navigator.mediaSession.setPositionState) return;
  // Prefer this browser's own player state (exact, event-driven) over the
  // server poll, whose progress lags and can read 0 just after a track change.
  let src = null;
  if (sdkPos && sdkPos.duration && (!mediaTrackUri || sdkPos.uri === mediaTrackUri)) {
    src = {progressMs: sdkPos.position, durationMs: sdkPos.duration, playing: !sdkPos.paused, at: sdkPos.at};
  } else if (npState && npState.durationMs) {
    src = npState;
  }
  if (!src) return;
  try {
    const duration = src.durationMs / 1000;
    const position = (src.progressMs + (src.playing ? Date.now() - src.at : 0)) / 1000;
    navigator.mediaSession.setPositionState({duration, playbackRate: 1, position: Math.max(0, Math.min(position, duration))});
  } catch (e) {}
}

function updateMediaSession(np) {
  if (!hasMediaSession) return;
  try {
    if (!np || !np.track) {
      navigator.mediaSession.playbackState = 'none';
      mediaTrackUri = null;
      lockAudioIdleSoon(true);
      return;
    }
    mediaTrackUri = np.track.uri;
    navigator.mediaSession.playbackState = np.playing ? 'playing' : 'paused';
    if (np.playing) lockAudioPlay(); else lockAudioIdleSoon(false);
    updateMediaPosition();
  } catch (e) {}
}

if (hasMediaSession) {
  try { navigator.mediaSession.metadata = new MediaMetadata(LOCKSCREEN_META); } catch (e) {}
  const mediaActions = {
    play: async () => { await lockAudioStartFirst(); return togglePlayPause(true); },
    pause: () => { lockAudioIdleSoon(true); return togglePlayPause(false); },
    previoustrack: skipPrevious,
    nexttrack: skipNext,
    seekto: details => seekToMs(Math.round((details.seekTime || 0) * 1000)),
  };
  for (const [action, handler] of Object.entries(mediaActions)) {
    try { navigator.mediaSession.setActionHandler(action, details => Promise.resolve(handler(details)).catch(() => {})); } catch (e) {}
  }
}

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
      lastAppliedViewAt = remote.updated_at || 0;
      await applyRemoteView(remote.view);   // no saved view (fresh server, first visit): applyRemoteView shows home
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

def replace_queue_and_play(tracks, device_id):
    """First track plays now; the rest replace the manual queue (and the auto section)."""
    start_track(tracks[0], device_id)
    with _queue_lock:
        q = load_queue()
        q["manual"] = tracks[1:]   # a new queue: replaces the old manual and auto sections
        q["auto"] = []
        q["auto_tried"] = None
        save_queue(q)
    refresh_auto((tracks[-1].get("album_id"), tracks[-1]["uri"]))
    _driver_wake.set()


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
        if path == "/spotify-api/search/best":
            self.handle_search_best(query); return
        if path == "/spotify-api/devices":
            self.handle_devices(); return
        if path == "/spotify-api/recently-played":
            self.handle_recently_played(); return
        if path == "/spotify-api/queue":
            self.handle_queue(); return
        if path == "/spotify-api/player/now-playing":
            self.handle_now_playing(); return
        if path == "/spotify-api/view-state":
            self.send_json(200, get_view_state()); return
        if path == "/spotify-api/favorites":
            self.send_json(200, {"items": list_favorites()}); return
        if path == "/spotify-api/favorite-tracks":
            self.send_json(200, {"items": list_favorite_tracks()}); return
        if path == "/spotify-api/favorite-artists":
            self.send_json(200, {"items": list_favorite_artists()}); return
        match = ARTIST_ALBUMS_RE.match(path)
        if match:
            self.handle_artist_albums(match.group(1), query); return
        match = ARTIST_DEDUP_RE.match(path)
        if match:
            self.handle_dedup(match.group(1), query); return
        match = ALBUM_RE.match(path)
        if match:
            self.handle_album(match.group(1), query); return
        match = FAVORITE_RE.match(path)
        if match:
            self.send_json(200, {"favorited": is_favorite(match.group(1))}); return
        match = FAVORITE_TRACK_RE.match(path)
        if match:
            self.send_json(200, {"favorited": is_favorite_track(match.group(1))}); return
        match = FAVORITE_ARTIST_RE.match(path)
        if match:
            self.send_json(200, favorite_artist_state(match.group(1))); return
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
        out = shape_search_items(kind, items)
        self.send_json(200, {"items": out, "offset": offset, "total": total, "has_more": offset + len(items) < total})

    def handle_search_best(self, query):
        q = (query.get("q", [""])[0] or "").strip()
        if not q:
            self.send_json(400, {"error": "missing_query"}); return
        # One request across all three types (Spotify's /search takes a
        # comma-separated "type") instead of three -- same cost as a single
        # regular search. "Most relevant" isn't something Spotify ranks across
        # types, so this picks whichever type's top result is an exact name
        # match; with none, it falls back to artist (today's plain-Enter behavior).
        result = cached_search("artist,album,track", q, SPOTIFY_PAGE_LIMIT)
        norm = lambda s: re.sub(r"\s+", " ", (s or "").strip()).casefold()
        qn = norm(q)
        kind = next((k for k in ("artist", "track", "album")
                     if norm(((result.get(k + "s") or {}).get("items") or [{}])[0].get("name")) == qn), "artist")
        block = result.get(kind + "s") or {}
        items = block.get("items", [])
        total = block.get("total", len(items))
        out = shape_search_items(kind, items)
        self.send_json(200, {"kind": kind, "items": out, "offset": 0, "total": total, "has_more": len(items) < total})

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
        try:      # the artist's own picture for the page heading; the page works without it
            artist_image = pick_artist_image(fetch_artist_meta(artist_id)["images"])
        except Exception:
            artist_image = None
        self.send_json(200, {"items": out, "artist_image": artist_image})

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
            # The favorites table keeps artist names only; the ids (for the
            # clickable artists) come from the permanently cached album metadata.
            try:
                cached["artist_ids"] = [a["id"] for a in fetch_album_meta(album_id).get("artists", [])]
            except Exception:
                pass
            self.send_json(200, cached)
            return
        album = fetch_album_meta(album_id, force=force)
        tracks = fetch_album_tracks(album_id, force=force)
        images = album.get("images") or []
        result = {
            "id": album["id"], "name": album["name"], "album_type": album.get("album_type", ""),
            "release_date": album.get("release_date", ""), "image": images[0]["url"] if images else None,
            "artists": [a["name"] for a in album.get("artists", [])],
            "artist_ids": [a["id"] for a in album.get("artists", [])],
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

    def handle_devices(self):
        result = spotify_api("GET", "/me/player/devices")
        self.send_json(200, {"items": result.get("devices", [])})

    def handle_recently_played(self):
        # V1's own history (see note_v1_play), not the account-wide
        # /me/player/recently-played, which also lists everything the app played.
        self.send_json(200, {"items": list_play_history()})

    def handle_queue(self):
        q = load_queue()
        last = get_last_playback()
        current = None
        if last and last.get("track"):
            t = last["track"]
            uri = t.get("uri") or ""
            current = {"id": uri.split(":")[-1] if uri else None, "uri": uri, "name": t.get("name"), "image": t.get("image"),
                       "artists": t.get("artists", []), "album_id": t.get("album_id"),
                       "album_name": t.get("album") or "", "release_date": t.get("release_date", ""),
                       "duration_ms": t.get("duration_ms", 0)}
        self.send_json(200, {"current": current, "next": q["next"], "manual": q["manual"], "auto": q["auto"],
                              "autoplay": get_autoplay()})

    def handle_queue_add(self, body):
        track = clean_track(body.get("track"))
        if not track:
            self.send_json(400, {"error": "invalid_track"}); return
        queue_add(track)
        self.send_json(200, {"ok": True})

    def handle_queue_remove(self, body):
        if not queue_remove(body.get("list"), body.get("index"), body.get("uri")):
            self.send_json(409, {"error": "queue_changed"}); return
        self.send_json(200, {"ok": True})

    def handle_set_autoplay(self, body):
        set_autoplay(bool(body.get("autoplay")))
        try:
            auto_count = refresh_auto()
        except Exception as exc:     # the flag is already saved; the driver retries when it needs the auto section
            print(f"queue-settings: refresh_auto failed: {exc}", flush=True)
            auto_count = len(load_queue()["auto"])
        _driver_wake.set()
        self.send_json(200, {"ok": True, "autoplay": get_autoplay(), "auto_count": auto_count})

    def handle_queue_play_track(self, body):
        track = clean_track(body.get("track"))
        if not track:
            self.send_json(400, {"error": "invalid_track"}); return
        start_track(track, body.get("device_id"))
        with _queue_lock:
            q = load_queue()
            queue_take(q, track["uri"])   # it's playing now, so it leaves the queue
            q["auto_tried"] = None
            save_queue(q)
        refresh_auto((track.get("album_id"), track["uri"]))
        _driver_wake.set()
        self.send_json(200, {"ok": True})

    def handle_queue_play_album(self, body):
        album_id = body.get("album_id")
        if not isinstance(album_id, str) or not re.fullmatch(r"[A-Za-z0-9]{10,40}", album_id):
            self.send_json(400, {"error": "invalid_album"}); return
        tracks = album_track_summaries(fetch_album_meta(album_id), fetch_album_tracks(album_id))
        if not tracks:
            self.send_json(404, {"error": "empty_album"}); return
        start_track(tracks[0], body.get("device_id"))
        with _queue_lock:
            q = load_queue()
            q["manual"] = tracks[1:]   # a new queue: replaces the old manual and auto sections
            q["auto"] = []
            q["auto_tried"] = None
            save_queue(q)
        refresh_auto((album_id, tracks[-1]["uri"]))
        _driver_wake.set()
        self.send_json(200, {"ok": True})

    def handle_queue_play_albums(self, body):
        ids = body.get("album_ids")
        if (not isinstance(ids, list) or not ids or len(ids) > PLAY_ALBUMS_MAX_ALBUMS
                or not all(isinstance(i, str) and re.fullmatch(r"[A-Za-z0-9]{10,40}", i) for i in ids)):
            self.send_json(400, {"error": "invalid_albums"}); return
        tracks, albums, truncated = [], 0, False
        for album_id in dict.fromkeys(ids):          # in the order given, each album once
            if len(tracks) >= PLAY_ALBUMS_MAX_TRACKS:
                truncated = True                     # albums remain that don't fit
                break
            album_tracks = favorite_track_summaries(album_id)
            if album_tracks is None:                 # favorited before tracks were cached: ask Spotify (cached from then on)
                try:
                    album_tracks = album_track_summaries(fetch_album_meta(album_id), fetch_album_tracks(album_id))
                except Exception:
                    album_tracks = []
            if album_tracks:
                tracks.extend(album_tracks)
                albums += 1
        truncated = truncated or len(tracks) > PLAY_ALBUMS_MAX_TRACKS
        tracks = tracks[:PLAY_ALBUMS_MAX_TRACKS]
        if body.get("shuffle_tracks"):
            random.shuffle(tracks)     # every track of the given albums in random order (one album = shuffle that album)
        if not tracks:
            self.send_json(404, {"error": "empty_albums"}); return
        start_track(tracks[0], body.get("device_id"))
        with _queue_lock:
            q = load_queue()
            q["manual"] = tracks[1:]   # like play-album: a new queue, replacing the old manual and auto sections
            q["auto"] = []
            q["auto_tried"] = None
            save_queue(q)
        refresh_auto((tracks[-1]["album_id"], tracks[-1]["uri"]))
        _driver_wake.set()
        self.send_json(200, {"ok": True, "tracks": len(tracks), "albums": albums, "truncated": truncated})

    def handle_queue_play_tracks(self, body):
        raw = body.get("tracks")
        if not isinstance(raw, list) or not raw:
            self.send_json(400, {"error": "invalid_tracks"}); return
        tracks = [t for t in (clean_track(t) for t in raw) if t][:PLAY_ALBUMS_MAX_TRACKS]
        if not tracks:
            self.send_json(400, {"error": "invalid_tracks"}); return
        replace_queue_and_play(tracks, body.get("device_id"))
        self.send_json(200, {"ok": True, "tracks": len(tracks), "truncated": len(raw) > len(tracks)})

    def handle_queue_play_artists(self, body):
        ids = body.get("artist_ids")
        if (not isinstance(ids, list) or not ids or len(ids) > PLAY_ALBUMS_MAX_ALBUMS
                or not all(isinstance(i, str) and re.fullmatch(r"[A-Za-z0-9]{10,40}", i) for i in ids)):
            self.send_json(400, {"error": "invalid_artists"}); return
        with db() as conn:
            known = dict(conn.execute("SELECT id, name FROM favorite_artists").fetchall())
        names = [known[i] for i in dict.fromkeys(ids) if i in known]     # in the order given, each once
        tracks, artists, empty = build_artist_queue(names, bool(body.get("shuffle")))
        if not tracks:
            self.send_json(404, {"error": "no_tracks", "empty": empty}); return
        tracks = [t for t in (clean_track(t) for t in tracks) if t]
        if not tracks:
            self.send_json(404, {"error": "no_tracks", "empty": empty}); return
        replace_queue_and_play(tracks, body.get("device_id"))
        self.send_json(200, {"ok": True, "tracks": len(tracks), "artists": artists, "empty": empty})

    def handle_queue_clear(self, body):
        with _queue_lock:
            q = load_queue()
            q["manual"] = []
            q["auto"] = []
            # Don't refill straight away: mark what's playing as already handled
            # for both the top-up and the "queue ran dry" refresh.
            current = ((get_last_playback() or {}).get("track") or {}).get("uri")
            q["auto_tried"] = current
            save_queue(q)
        global _topup_key
        _topup_key = current
        self.send_json(200, {"ok": True})

    def handle_queue_next(self, body):
        device_id = body.get("device_id")
        head = None
        with _queue_lock:
            q = load_queue()
            if not q["next"]:      # otherwise it's already in Spotify's queue and Spotify's own next plays it
                head = q["manual"].pop(0) if q["manual"] else q["auto"].pop(0) if q["auto"] else None
                save_queue(q)
        if head:
            start_track(head, device_id)
        else:
            spotify_api("POST", "/me/player/next", params={"device_id": device_id})
        _driver_wake.set()
        self.send_json(200, {"ok": True})

    def handle_now_playing(self):
        result = spotify_api("GET", "/me/player")
        item = (result or {}).get("item")
        # Only V1's own device counts as "now playing" here: when the Spotify
        # app (or any other client) is the active device, the bar falls back to
        # V1's last snapshot below -- paused, not live -- exactly as if nothing
        # were playing, so it never shows or controls the app's playback.
        # Pressing Play then resumes that V1 track on this page (the slow path
        # in togglePlayPause restarts it at the saved position on this device),
        # which takes playback over from the app.
        if item and is_v1_device(result):
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
                    "release_date": item.get("album", {}).get("release_date", ""),
                    "duration_ms": item.get("duration_ms", 0),
                    "image": images[0]["url"] if images else None, "uri": item.get("uri"),
                },
                "live": True,
            }
            set_last_playback(payload)
            reconcile_queue(item["uri"], payload["progress_ms"])
            if payload["playing"]:
                note_v1_play(item)
            payload = dict(payload, autoplay=get_autoplay())
            self.send_json(200, payload)
            return
        # Either another client is the active device (see above), or none is:
        # the Web Playback SDK device is this browser tab, and Spotify reports
        # no active device between "tab just reloaded" and "a device
        # reconnects", which can be indistinguishable from "genuinely stopped".
        # Fall back to V1's last known snapshot (frozen, not live) so the bar
        # and playhead stay put instead of going blank.
        cached = get_last_playback()
        if cached:
            cached["playing"] = False
            cached["live"] = False
            cached["autoplay"] = get_autoplay()
            self.send_json(200, cached)
            return
        self.send_json(200, {"playing": False, "progress_ms": 0, "device": None, "device_id": None,
                              "track": None, "live": True, "autoplay": get_autoplay()})

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
            # A play with no position_ms is always a genuinely new starting
            # point (Recently Played / Dedup rows -- the only frontend caller
            # of this raw endpoint that skips V1's queue system entirely), so
            # whatever V1 had handed to Spotify's own queue for the *previous*
            # track is stale now; clear it the same way start_track() does.
            # position_ms is only ever sent to resume the very same track
            # after a reload, where the old hand-off (if any) is still valid.
            if body.get("position_ms") is None:
                with _queue_lock:
                    q = load_queue()
                    if q["next"]:
                        q["next"] = None
                        save_queue(q)
            _driver_wake.set()
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/player/pause":
            body = self.read_json_body()
            spotify_api("PUT", "/me/player/pause", params={"device_id": body.get("device_id")})
            _driver_wake.set()
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
            _driver_wake.set()
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/view-state":
            body = self.read_json_body()
            set_view_state(body.get("view"), body.get("client_id"))
            self.send_json(200, {"ok": True}); return
        if path == "/spotify-api/queue-settings":
            self.handle_set_autoplay(self.read_json_body()); return
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
        match = FAVORITE_TRACK_GENRES_RE.match(path)
        if match:
            body = self.read_json_body()
            genres = body.get("genres")
            if not isinstance(genres, list):
                self.send_json(400, {"error": "genres_must_be_array"}); return
            set_favorite_track_genres(match.group(1), [str(g) for g in genres][:10])
            self.send_json(200, {"ok": True}); return
        match = FAVORITE_ARTIST_GENRES_RE.match(path)
        if match:
            body = self.read_json_body()
            genres = body.get("genres")
            if not isinstance(genres, list):
                self.send_json(400, {"error": "genres_must_be_array"}); return
            set_favorite_artist_genres(match.group(1), [str(g) for g in genres][:10])
            self.send_json(200, {"ok": True}); return
        match = FAVORITE_ARTIST_RE.match(path)
        if match:
            body = self.read_json_body()
            frd = body.get("release_date")
            add_favorite_artist(match.group(1), str(body.get("name", "")), body.get("image"),
                                frd if isinstance(frd, str) and re.match(r"^\d{4}", frd) else None)
            refresh_artist_image(match.group(1))   # the client only has an album cover to offer
            self.send_json(200, {"ok": True}); return
        match = FAVORITE_TRACK_RE.match(path)
        if match:
            body = self.read_json_body()
            uri = body.get("uri")
            if not isinstance(uri, str) or not uri.startswith("spotify:track:"):
                self.send_json(400, {"error": "invalid_uri"}); return
            add_favorite_track(match.group(1), uri, body.get("name", ""), body.get("artists"), body.get("image"),
                               body.get("album_id"), body.get("album_name"), body.get("release_date"), body.get("duration_ms"))
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
        match = FAVORITE_TRACK_RE.match(path)
        if match:
            remove_favorite_track(match.group(1))
            self.send_json(200, {"ok": True}); return
        match = FAVORITE_ARTIST_RE.match(path)
        if match:
            remove_favorite_artist(match.group(1))
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
        if path == "/spotify-api/player/previous":
            body = self.read_json_body()
            spotify_api("POST", "/me/player/previous", params={"device_id": body.get("device_id")})
            self.send_json(200, {"ok": True}); return
        routes = {"/spotify-api/queue/add": self.handle_queue_add,
                  "/spotify-api/queue/remove": self.handle_queue_remove,
                  "/spotify-api/queue/play-track": self.handle_queue_play_track,
                  "/spotify-api/queue/play-album": self.handle_queue_play_album,
                  "/spotify-api/queue/play-albums": self.handle_queue_play_albums,
                  "/spotify-api/queue/play-tracks": self.handle_queue_play_tracks,
                  "/spotify-api/queue/play-artists": self.handle_queue_play_artists,
                  "/spotify-api/queue/clear": self.handle_queue_clear,
                  "/spotify-api/queue/next": self.handle_queue_next}
        if path in routes:
            routes[path](self.read_json_body()); return
        self.send_json(404, {"error": "not_found"})


def main():
    os.makedirs(os.path.dirname(DB_PATH) or ".", exist_ok=True)
    with db():
        pass
    if not CLIENT_ID or not CLIENT_SECRET:
        print("WARNING: SPOTIFY_CLIENT_ID/SPOTIFY_CLIENT_SECRET not set", flush=True)
    threading.Thread(target=queue_driver_loop, daemon=True).start()
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"Spotify service listening on http://{HOST}:{PORT}; db={DB_PATH}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
