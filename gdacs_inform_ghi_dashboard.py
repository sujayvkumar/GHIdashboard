#!/usr/bin/env python3
"""
GDACS Disaster Dashboard v2
===========================

A single-file local dashboard that pulls live events from GDACS (Global Disaster
Alert and Coordination System) and plots them on a world map, with optional
satellite ground tracks (SWOT, Sentinel, MODIS, etc.).

NEW IN v2:
  - Intuitive SVG icons per disaster type (no emoji)
  - Date range selector (last 24h, 3/7/30/90 days, custom)
  - Satellite ground track overlay (toggle on/off, choose which satellites)

USAGE:
    pip install sgp4                 # only needed if you want satellite tracks
    python3 gdacs_dashboard.py
    # then open http://localhost:8765

Without sgp4 installed, the dashboard works fine — the satellite panel just
shows an error if you try to enable a satellite.

Requirements: Python 3.7+. Standard library, plus optional 'sgp4'.
"""

import json
import os
import sys
import time
import datetime as dt
import urllib.request
import urllib.error
import urllib.parse
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse, parse_qs


def _utcnow_naive():
    """UTC 'now' as a naive datetime — replacement for the deprecated
    datetime.utcnow(). Returns the same naive value as before so existing
    arithmetic with timedeltas keeps working unchanged."""
    return dt.datetime.now(dt.timezone.utc).replace(tzinfo=None)


PORT = 8765

# Resolve every on-disk path relative to the script's own directory so the
# dashboard works regardless of the user's current working directory.
# (Previously, all caches/credentials files used bare relative paths, so
# launching the script from a different directory silently broke
# authentication and caching.)
_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def _here(name):
    """Resolve a filename relative to the script's directory."""
    return os.path.join(_SCRIPT_DIR, name)


GDACS_CACHE_PREFIX = _here("gdacs_cache")
GDACS_CACHE_VERSION = "v3"  # bump this whenever fetch_gdacs's logic changes, so
                            # old on-disk cache files (written by the previous
                            # version's logic) are never mistaken for fresh
                            # data — otherwise a code fix can silently appear
                            # to do nothing for up to CACHE_TTL_SECONDS because
                            # the stale file on disk gets served instead of
                            # ever reaching the network.
TLE_CACHE = _here("tle_cache.txt")
CACHE_TTL_SECONDS = 60 * 10        # GDACS itself updates every ~6 min
TLE_TTL_SECONDS = 60 * 60 * 12     # TLEs are good for a few days; refresh twice daily

# Map of friendly id -> dict with display name, NORAD catalog number, color,
# swath width in km, and primary instrument label.
# Swath widths are sourced from official mission/instrument documentation:
#   - SWOT KaRIn:        120 km total (two 50 km swaths + 20 km nadir gap)
#   - Sentinel-1 IW:     250 km
#   - Sentinel-2 MSI:    290 km
#   - Sentinel-3 OLCI:   1270 km (tilted 12.6 deg west of nadir)
#   - Sentinel-6 MF:     ~5 km (nadir altimeter footprint, not a true swath)
#   - Terra/Aqua MODIS:  2330 km
#   - Landsat-8/9 OLI:   185 km
#   - ICESat-2 ATLAS:    ~6 km (3 beam-pair span; each pair is only 90 m)
SATELLITES = {
    "SWOT":         {"name": "SWOT",          "norad": 54754, "color": "#534AB7", "swath_km": 120,  "instr": "KaRIn", "tilt_deg": 0},
    "NISAR":        {"name": "NISAR",         "norad": 65053, "color": "#993556", "swath_km": 242,  "instr": "L/S-SAR", "tilt_deg": 0},
    "SENTINEL-1A":  {"name": "Sentinel-1A",   "norad": 39634, "color": "#185FA5", "swath_km": 250,  "instr": "IW SAR", "tilt_deg": 0},
    "SENTINEL-2A":  {"name": "Sentinel-2A",   "norad": 40697, "color": "#0F6E56", "swath_km": 290,  "instr": "MSI", "tilt_deg": 0},
    "SENTINEL-2B":  {"name": "Sentinel-2B",   "norad": 42063, "color": "#1D9E75", "swath_km": 290,  "instr": "MSI", "tilt_deg": 0},
    "SENTINEL-3A":  {"name": "Sentinel-3A",   "norad": 41335, "color": "#5DCAA5", "swath_km": 1270, "instr": "OLCI", "tilt_deg": 12.6},
    "SENTINEL-6":   {"name": "Sentinel-6 MF", "norad": 46984, "color": "#7F77DD", "swath_km": 5,    "instr": "Poseidon-4", "tilt_deg": 0},
    "TERRA":        {"name": "Terra (MODIS)", "norad": 25994, "color": "#BA7517", "swath_km": 2330, "instr": "MODIS", "tilt_deg": 0},
    "AQUA":         {"name": "Aqua (MODIS)",  "norad": 27424, "color": "#D85A30", "swath_km": 2330, "instr": "MODIS", "tilt_deg": 0},
    "LANDSAT-8":    {"name": "Landsat-8",     "norad": 39084, "color": "#444441", "swath_km": 185,  "instr": "OLI/TIRS", "tilt_deg": 0},
    "LANDSAT-9":    {"name": "Landsat-9",     "norad": 49260, "color": "#5F5E5A", "swath_km": 185,  "instr": "OLI/TIRS", "tilt_deg": 0},
    "ICESAT-2":     {"name": "ICESat-2",      "norad": 43613, "color": "#D4537E", "swath_km": 6,    "instr": "ATLAS", "tilt_deg": 0},
}

CELESTRAK_GROUPS = ["active"]  # 'active' covers all the satellites above


# ---------------------------------------------------------------------------
# Data fetchers (server-side; bypasses CORS)
# ---------------------------------------------------------------------------

def _read_cache(path, ttl):
    if os.path.exists(path):
        age = time.time() - os.path.getmtime(path)
        if age < ttl:
            with open(path, "r", encoding="utf-8") as f:
                return f.read()
    return None


def _write_cache(path, body):
    with open(path, "w", encoding="utf-8") as f:
        f.write(body)


def fetch_gdacs(fromdate=None, todate=None):
    """Fetch GDACS events for the given date window.

    GDACS's SEARCH endpoint does not reliably honor its own filter
    parameters. Testing showed that requests with very different
    eventlist/alertlevel/pagesize values came back byte-identical —
    strong evidence that GDACS (or a CDN in front of it) serves this
    endpoint from a cache keyed on the path alone, ignoring the query
    string. Depending on server-side filtering here means the dashboard's
    results silently depend on unpredictable upstream cache state rather
    than on what was actually requested — which is what made events
    look randomly missing between refreshes.

    So instead of trusting the server to filter, we make ONE request
    (with a cache-busting nonce so we're not just replaying a stale
    cached blob), take whatever GDACS is willing to hand back, and
    apply the event-type and date-window filtering ourselves against
    that response.
    """
    cache_key = f"{GDACS_CACHE_PREFIX}.{GDACS_CACHE_VERSION}.{fromdate or 'all'}.{todate or 'all'}.json"
    cached = _read_cache(cache_key, CACHE_TTL_SECONDS)
    if cached:
        return cached

    # All GDACS-tracked hazard types, including tsunami (TS), which the
    # dashboard's UI previously omitted entirely.
    event_types = "EQ;TC;FL;VO;WF;DR;TS"
    nonce = str(time.time())  # cache-buster against upstream path-only caching

    params = f"eventlist={event_types}&alertlevel=green;orange;red&_={nonce}"
    url = f"https://www.gdacs.org/gdacsapi/api/events/geteventlist/SEARCH?{params}"
    req = urllib.request.Request(url, headers={
        "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    })
    with urllib.request.urlopen(req, timeout=30) as resp:
        body = resp.read().decode("utf-8")

    try:
        data = json.loads(body)
    except json.JSONDecodeError:
        # Malformed response — cache and return as-is; the caller's own
        # JSON parsing will surface the problem rather than us masking it.
        _write_cache(cache_key, body)
        return body

    all_features = data.get("features") or []

    # Our own date-window filter, since fromdate/todate aren't reliably
    # honored server-side. An event counts as "in range" if its
    # [fromdate, todate] interval overlaps the requested window at all,
    # so ongoing floods/droughts/wildfires that started earlier but are
    # still active still show up — matching gdacs.org's own behavior of
    # surfacing anything still current.
    def _parse_dt(s):
        if not s:
            return None
        try:
            return dt.datetime.fromisoformat(s)
        except ValueError:
            return None

    from_dt = _parse_dt(fromdate)
    to_dt = _parse_dt(todate)
    if to_dt:
        to_dt = to_dt + dt.timedelta(days=1)  # todate is a day, not a timestamp

    deduped = {}  # (eventtype, eventid) -> feature
    for feat in all_features:
        props = feat.get("properties", {}) or {}
        key = (props.get("eventtype"), props.get("eventid"))
        if key in deduped:
            continue

        if from_dt or to_dt:
            ev_from = _parse_dt(props.get("fromdate"))
            ev_to = _parse_dt(props.get("todate")) or ev_from
            if ev_from is None:
                continue  # can't place it in time — drop rather than guess
            if to_dt and ev_from > to_dt:
                continue
            if from_dt and ev_to and ev_to < from_dt:
                continue

        deduped[key] = feat

    merged = {"type": "FeatureCollection", "features": list(deduped.values())}
    body_out = json.dumps(merged)
    _write_cache(cache_key, body_out)
    return body_out


def fetch_tle():
    """Fetch the 'active satellites' TLE catalog from Celestrak."""
    cached = _read_cache(TLE_CACHE, TLE_TTL_SECONDS)
    if cached:
        return cached

    text_blocks = []
    for group in CELESTRAK_GROUPS:
        url = f"https://celestrak.org/NORAD/elements/gp.php?GROUP={group}&FORMAT=tle"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (gdacs-dashboard)"})
        with urllib.request.urlopen(req, timeout=30) as resp:
            text_blocks.append(resp.read().decode("utf-8"))

    body = "\n".join(text_blocks)
    _write_cache(TLE_CACHE, body)
    return body


# ---------------------------------------------------------------------------
# NISAR Beta Soil Moisture (L3 SME2) fetcher
# ---------------------------------------------------------------------------
# Workflow:
#   1) Search NASA CMR for the most recent granule covering (lat, lon)
#   2) Download the HDF5 file from ASF (requires Earthdata Login bearer token,
#      read from ./nisar_token.txt — user creates this file once)
#   3) Open the file, extract the soil-moisture grid, subset a small window
#      around the target, reproject to WGS84, and render to a PNG
#   4) Return JSON with the PNG path and lat/lon bounds for Leaflet imageOverlay
#
# The NISAR L3 SME2 collection: short_name=NISAR_L3_SME2_BETA_V1
# CMR concept id: C2850265000-ASF
# Data is on the EASE-Grid 2.0 cylindrical projection (EPSG:6933), 200 m posting.
# IMPORTANT CAVEAT (May 2026): NISAR SME2 is in BETA, "not intended for use in
# scientific research". Latency is ~72 hours after the overpass.

NISAR_COLLECTION_ID = "C2850265000-ASF"
NISAR_TOKEN_FILE = _here("nisar_token.txt")
NISAR_CACHE_DIR = _here("nisar_cache")
NISAR_TILE_URLPATH = "nisar_tiles"            # served at /nisar_tiles/...
NISAR_TILE_DIR = _here(NISAR_TILE_URLPATH)    # filesystem path

CMR_URL = "https://cmr.earthdata.nasa.gov/search/granules.json"


def _read_edl_token():
    """Read Earthdata Login bearer token from ./nisar_token.txt (one line).

    Strips whitespace (including internal newlines/spaces from copy-paste), an
    optional 'Bearer ' prefix, and surrounding quotes. EDL User Tokens are
    usually 100-200 character opaque strings with no whitespace inside.
    """
    if not os.path.exists(NISAR_TOKEN_FILE):
        return None
    with open(NISAR_TOKEN_FILE, "r") as f:
        raw = f.read()

    # Strip ALL whitespace (handles multi-line paste from web UI)
    token = "".join(raw.split())

    # Tolerate common copy-paste mistakes
    if token.lower().startswith("bearer"):
        token = token[6:].lstrip()
    if (token.startswith('"') and token.endswith('"')) or \
       (token.startswith("'") and token.endswith("'")):
        token = token[1:-1].strip()
    return token if token else None


def _diagnose_token():
    """Inspect the token file and return a list of likely issues."""
    issues = []
    if not os.path.exists(NISAR_TOKEN_FILE):
        issues.append(f"File ./{NISAR_TOKEN_FILE} does not exist.")
        return issues, None

    with open(NISAR_TOKEN_FILE, "r") as f:
        raw = f.read()

    if not raw.strip():
        issues.append("File is empty.")
        return issues, None

    if "\n" in raw.strip() or "\r" in raw.strip():
        issues.append("File contains internal line breaks — token should be a single line.")

    token = _read_edl_token()
    if not token:
        issues.append("After cleaning, token is empty.")
        return issues, None

    # EDL User Tokens are opaque strings, typically 100-300 chars, base64-ish.
    # If it looks like an OAuth client ID/secret pair (contains a colon, very
    # short, or has '=' padding only at end and is < 60 chars), it's wrong type.
    if len(token) < 50:
        issues.append(f"Token is only {len(token)} chars — User Tokens are usually 100+ chars. "
                      f"Did you paste an App Key (OAuth client ID) by mistake? "
                      f"You need a User Token from the 'Generate Token' tab, not 'App Keys'.")
    if ":" in token and len(token) < 100:
        issues.append("Token contains ':' and is short — looks like 'client_id:secret', "
                      "which is an OAuth credential, not a bearer token.")
    if " " in token:
        issues.append("Token contains whitespace internally after cleaning — unusual.")

    return issues, token


def download_nisar_granule(url, token):
    """Download a NISAR HDF5 file to the cache directory. Returns local path.

    ASF bounces auth through Earthdata Login: the original URL redirects to
    urs.earthdata.nasa.gov for token validation, then to a TEA-backed download
    URL. The Authorization: Bearer header MUST be present on every hop. Python's
    urllib drops headers on cross-host redirects by default, so we follow
    redirects manually and re-attach the header each time.
    """
    os.makedirs(NISAR_CACHE_DIR, exist_ok=True)
    filename = url.rsplit("/", 1)[-1].split("?")[0]
    local_path = os.path.join(NISAR_CACHE_DIR, filename)
    if os.path.exists(local_path) and os.path.getsize(local_path) > 1024:
        return local_path  # cached

    headers = {
        "Authorization": f"Bearer {token}",
        "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
        "Accept": "*/*",
    }

    # Manual redirect loop. We cap at 10 hops to avoid infinite loops, and
    # re-send the Authorization header on every hop. This is the only
    # reliable way I've found to get cross-host EDL/TEA auth working in stdlib.
    current_url = url
    cookies = {}  # accumulate Set-Cookie across hops; some TEA endpoints need them
    visited = []

    for hop in range(10):
        visited.append(current_url)

        req_headers = dict(headers)
        if cookies:
            req_headers["Cookie"] = "; ".join(f"{k}={v}" for k, v in cookies.items())

        # Build a request that does NOT auto-redirect, so we can see each hop
        # and re-attach headers.
        class NoRedirect(urllib.request.HTTPRedirectHandler):
            def http_error_301(self, *args, **kw): return None
            def http_error_302(self, *args, **kw): return None
            def http_error_303(self, *args, **kw): return None
            def http_error_307(self, *args, **kw): return None
            def http_error_308(self, *args, **kw): return None

        opener = urllib.request.build_opener(NoRedirect)
        req = urllib.request.Request(current_url, headers=req_headers)

        try:
            resp = opener.open(req, timeout=300)
            status = resp.getcode()
        except urllib.error.HTTPError as e:
            status = e.code
            resp = e

        # Capture any Set-Cookie headers from this response
        for k, v in resp.getheaders():
            if k.lower() == "set-cookie":
                # Crude cookie parse: name=value (ignore attributes after ';')
                cookie_pair = v.split(";", 1)[0].strip()
                if "=" in cookie_pair:
                    name, val = cookie_pair.split("=", 1)
                    cookies[name.strip()] = val.strip()

        if status in (301, 302, 303, 307, 308):
            location = resp.getheader("Location")
            if not location:
                raise RuntimeError(f"Redirect with no Location header at {current_url}")
            # Resolve relative redirects
            current_url = urllib.request.urljoin(current_url, location)
            resp.close()
            continue

        if status == 200:
            # Success — stream the body to disk
            tmp_path = local_path + ".part"
            with open(tmp_path, "wb") as out:
                while True:
                    chunk = resp.read(1024 * 256)
                    if not chunk:
                        break
                    out.write(chunk)
            resp.close()
            os.rename(tmp_path, local_path)
            return local_path

        # Anything else: collect diagnostic info and raise
        body_preview = ""
        try:
            body_preview = resp.read(500).decode("utf-8", errors="replace")
        except Exception:
            pass
        resp.close()

        hop_chain = "\n  -> ".join(visited)
        raise urllib.error.HTTPError(
            current_url, status,
            (f"HTTP {status} from ASF after {hop} redirect hops.\n"
             f"Hop chain:\n  -> {hop_chain}\n"
             f"Response preview: {body_preview[:200]}\n"
             f"This usually means: (a) your Earthdata Login token is invalid or expired, "
             f"(b) you haven't accepted the NISAR data EULA at "
             f"https://urs.earthdata.nasa.gov/profile (Applications tab), or "
             f"(c) the token in nisar_token.txt is malformed (should be the raw token "
             f"string from the User Tokens tab, no 'Bearer ' prefix)."),
            resp.headers if hasattr(resp, 'headers') else None, None
        )

    raise RuntimeError(f"Too many redirects following {url}; visited:\n" +
                       "\n".join(visited))


def cmr_search_nisar(lat, lon, start_iso=None, end_iso=None, page_size=10):
    """Search CMR for NISAR soil moisture granules covering (lat, lon).

    Strategy:
      1) Try a spatial bbox search around the target
      2) If that returns zero, do a non-spatial search over the time range
         and filter client-side using the granule polygons in CMR metadata
      3) If THAT returns zero, do a "is there any data at all?" diagnostic
         search so the error message is informative

    Returns a dict {granules: [...], total_in_window: int, total_globally: int,
        spatial_match_count: int}.
    """
    base = {
        "short_name": "NISAR_L3_SME2_BETA_V1",
        "page_size": str(page_size),
        "sort_key": "-start_date",
    }
    if start_iso and end_iso:
        base["temporal"] = f"{start_iso},{end_iso}"

    def _query(extra=None):
        params = dict(base)
        if extra:
            params.update(extra)
        qs = "&".join(f"{k}={urllib.request.quote(str(v), safe=',-:')}" for k, v in params.items())
        url = f"{CMR_URL}?{qs}"
        req = urllib.request.Request(url, headers={
            "Accept": "application/json",
            "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
        })
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def _entries_to_granules(entries):
        out = []
        for entry in entries:
            download_url = None
            for link in entry.get("links", []):
                rel = link.get("rel", "")
                href = link.get("href", "")
                if ("data#" in rel or rel.endswith("/data#")) and href.endswith(".h5"):
                    download_url = href
                    break
            out.append({
                "id": entry.get("id"),
                "title": entry.get("title"),
                "time_start": entry.get("time_start"),
                "time_end": entry.get("time_end"),
                "download_url": download_url,
                "polygons": entry.get("polygons", []),  # for client-side spatial filter
                "boxes": entry.get("boxes", []),
            })
        return out

    # Step 1: spatial bbox search (~50 km box around the target — generous)
    pad = 0.5  # ~55 km in degrees, way bigger than before
    bbox = f"{lon-pad:.4f},{lat-pad:.4f},{lon+pad:.4f},{lat+pad:.4f}"
    try:
        spatial = _query({"bounding_box": bbox})
        spatial_entries = spatial.get("feed", {}).get("entry", [])
    except Exception as e:
        spatial_entries = []
        print(f"[NISAR] spatial CMR query failed: {e}", file=sys.stderr)

    if spatial_entries:
        granules = _entries_to_granules(spatial_entries)
        return {"granules": granules, "method": "spatial", "spatial_match_count": len(granules)}

    # Step 2: non-spatial fallback. Get all granules in the time window.
    try:
        any_window = _query()  # no bbox
        window_entries = any_window.get("feed", {}).get("entry", [])
    except Exception as e:
        window_entries = []
        print(f"[NISAR] non-spatial CMR query failed: {e}", file=sys.stderr)

    # Filter client-side: check whether each granule's polygon contains the point.
    # CMR polygons are space-separated lat/lon pairs (lat first), one polygon per string.
    def point_in_polygon(plat, plon, poly_str):
        coords = [float(x) for x in poly_str.split()]
        pts = [(coords[i], coords[i+1]) for i in range(0, len(coords), 2)]
        # Ray-casting
        inside = False
        n = len(pts)
        for i in range(n):
            lat1, lon1 = pts[i]
            lat2, lon2 = pts[(i + 1) % n]
            if (lon1 > plon) != (lon2 > plon):
                lat_at = lat1 + (plon - lon1) * (lat2 - lat1) / (lon2 - lon1) if lon2 != lon1 else lat1
                if plat < lat_at:
                    inside = not inside
        return inside

    matched = []
    for entry in window_entries:
        for poly in entry.get("polygons", [[]])[0] if entry.get("polygons") else []:
            try:
                if point_in_polygon(lat, lon, poly):
                    matched.append(entry)
                    break
            except (ValueError, ZeroDivisionError):
                continue
        else:
            # Also check boxes (S, W, N, E)
            for box in entry.get("boxes", []):
                try:
                    s, w, n, e = [float(x) for x in box.split()]
                    if s <= lat <= n and w <= lon <= e:
                        matched.append(entry)
                        break
                except ValueError:
                    continue

    if matched:
        granules = _entries_to_granules(matched)
        return {"granules": granules, "method": "spatial-fallback",
                "spatial_match_count": len(granules), "total_in_window": len(window_entries)}

    # Step 3: pure diagnostic — does this collection have ANY granules globally?
    try:
        diag = _query({"page_size": "1"})
        diag_entries = diag.get("feed", {}).get("entry", [])
        first_global_time = diag_entries[0].get("time_start") if diag_entries else None
    except Exception:
        first_global_time = None

    return {
        "granules": [],
        "method": "no-match",
        "spatial_match_count": 0,
        "total_in_window": len(window_entries),
        "first_global_time": first_global_time,
    }





def render_nisar_subset(h5_path, target_lat, target_lon, half_size_km=10):
    """Open the NISAR HDF5 file, subset a window around the target, render PNG.

    Returns dict with: png_path, bounds [[south, west], [north, east]],
    stats {min, max, mean, valid_count, total_count}, value_at_target.
    """
    import h5py
    import numpy as np
    from PIL import Image
    import pyproj

    with h5py.File(h5_path, "r") as h5:
        # The NISAR L3 SME2 internal layout is documented in the product spec
        # but may change between Beta versions. Walk the tree to find a likely
        # Soil_Moisture dataset.
        sm_dataset_name = None
        sm_data = None
        x_coords = None
        y_coords = None

        def walk(name, obj):
            nonlocal sm_dataset_name
            if isinstance(obj, h5py.Dataset):
                low = name.lower()
                if "soil_moisture" in low or low.endswith("/sme") or "/sm" == low[-3:]:
                    if sm_dataset_name is None or len(obj.shape) == 2:
                        sm_dataset_name = name

        h5.visititems(walk)

        if sm_dataset_name is None:
            raise RuntimeError(
                "Couldn't find a soil-moisture dataset in this HDF5. "
                "Top-level keys: " + ", ".join(list(h5.keys())[:10])
            )

        sm_data = h5[sm_dataset_name][:]

        # Try to find x/y coordinate arrays — usually stored as separate datasets
        # named 'xCoordinates'/'yCoordinates' or 'x'/'y' near the data.
        parent_path = sm_dataset_name.rsplit("/", 1)[0]
        for cand in ["xCoordinates", "x", "easting"]:
            p = f"{parent_path}/{cand}"
            if p in h5:
                x_coords = h5[p][:]
                break
        for cand in ["yCoordinates", "y", "northing"]:
            p = f"{parent_path}/{cand}"
            if p in h5:
                y_coords = h5[p][:]
                break

        if x_coords is None or y_coords is None:
            raise RuntimeError(
                f"Couldn't find x/y coordinate arrays for {sm_dataset_name}. "
                f"Datasets in {parent_path}: {list(h5[parent_path].keys()) if parent_path else 'root'}"
            )

    # NISAR uses EASE-Grid 2.0 Global = EPSG:6933.
    # Project the target lat/lon into easting/northing.
    transformer_to_grid = pyproj.Transformer.from_crs(
        "EPSG:4326", "EPSG:6933", always_xy=True
    )
    target_x, target_y = transformer_to_grid.transform(target_lon, target_lat)

    # Find the nearest cell
    col = int(np.argmin(np.abs(x_coords - target_x)))
    row = int(np.argmin(np.abs(y_coords - target_y)))

    # Determine the cell size
    dx = abs(x_coords[1] - x_coords[0]) if len(x_coords) > 1 else 200.0
    half_pixels = int(round(half_size_km * 1000.0 / dx))
    half_pixels = max(half_pixels, 8)  # minimum window size

    # Subset
    r0 = max(0, row - half_pixels)
    r1 = min(sm_data.shape[0], row + half_pixels + 1)
    c0 = max(0, col - half_pixels)
    c1 = min(sm_data.shape[1], col + half_pixels + 1)
    subset = sm_data[r0:r1, c0:c1].astype(np.float32)

    x_subset = x_coords[c0:c1]
    y_subset = y_coords[r0:r1]

    # NISAR fill value is typically -9999 or NaN — mask invalid
    valid = np.isfinite(subset) & (subset >= 0) & (subset <= 1.0)
    valid_count = int(valid.sum())
    total_count = int(subset.size)

    # Compute corner extents in EASE-Grid (cell-centered → expand by half pixel)
    dy = abs(y_subset[1] - y_subset[0]) if len(y_subset) > 1 else 200.0
    grid_west  = x_subset.min() - dx / 2
    grid_east  = x_subset.max() + dx / 2
    grid_south = y_subset.min() - dy / 2
    grid_north = y_subset.max() + dy / 2

    # Convert corners back to lat/lon for Leaflet
    transformer_to_geo = pyproj.Transformer.from_crs(
        "EPSG:6933", "EPSG:4326", always_xy=True
    )
    sw_lon, sw_lat = transformer_to_geo.transform(grid_west, grid_south)
    ne_lon, ne_lat = transformer_to_geo.transform(grid_east, grid_north)

    # NB: EASE-Grid 2.0 cells are not exactly aligned with WGS84 lat/lon, so
    # this bounding box is a small approximation — fine at the 10 km scale.

    # Stats (only valid pixels)
    valid_data = subset[valid]
    if valid_count > 0:
        stats = {
            "min": float(valid_data.min()),
            "max": float(valid_data.max()),
            "mean": float(valid_data.mean()),
            "valid_count": valid_count,
            "total_count": total_count,
        }
    else:
        stats = {"min": None, "max": None, "mean": None,
                 "valid_count": 0, "total_count": total_count}

    # Render PNG with a viridis-like colormap. y_coords are in descending order
    # for EASE-Grid 2.0 (north-to-south), but check just in case.
    if y_subset[0] < y_subset[-1]:
        # ascending y → flip vertically so north is at top of image
        subset = subset[::-1, :]
        valid = valid[::-1, :]

    rgba = np.zeros((subset.shape[0], subset.shape[1], 4), dtype=np.uint8)
    if valid_count > 0:
        # Map [0, 0.6] → colormap (most soils sit in this range; >0.6 saturated)
        norm = np.clip(subset / 0.6, 0, 1)
        # Approximate viridis: blue-purple → green → yellow
        r = np.clip(255 * (0.267 + 0.105 * norm + 0.628 * norm * norm), 0, 255)
        g = np.clip(255 * (0.005 + 1.404 * norm - 0.409 * norm * norm), 0, 255)
        b = np.clip(255 * (0.329 + 0.398 * norm - 0.727 * norm * norm + 0 * norm), 0, 255)
        rgba[..., 0] = np.where(valid, r.astype(np.uint8), 0)
        rgba[..., 1] = np.where(valid, g.astype(np.uint8), 0)
        rgba[..., 2] = np.where(valid, b.astype(np.uint8), 0)
        rgba[..., 3] = np.where(valid, 200, 0)  # ~80% opaque, transparent fills

    # Upscale a bit for better visibility on the map
    img = Image.fromarray(rgba, mode="RGBA")
    img = img.resize((img.width * 4, img.height * 4), Image.NEAREST)

    os.makedirs(NISAR_TILE_DIR, exist_ok=True)
    png_filename = f"sm_{abs(hash((h5_path, target_lat, target_lon, half_size_km)))}.png"
    png_path = os.path.join(NISAR_TILE_DIR, png_filename)
    img.save(png_path, "PNG", optimize=True)

    # Value at the target pixel itself
    target_val = None
    if 0 <= row - r0 < subset.shape[0] and 0 <= col - c0 < subset.shape[1]:
        # NB: the displayed subset may be flipped vertically; use the original
        v = sm_data[row, col]
        if np.isfinite(v) and 0 <= v <= 1:
            target_val = float(v)

    return {
        "png_url": f"/{NISAR_TILE_URLPATH}/{png_filename}",
        "bounds": [[float(sw_lat), float(sw_lon)], [float(ne_lat), float(ne_lon)]],
        "stats": stats,
        "value_at_target": target_val,
        "dataset_name": sm_dataset_name,
        "subset_shape": list(subset.shape),
    }


# ---------------------------------------------------------------------------
# ACLED conflict-event fetcher
# ---------------------------------------------------------------------------
# Auth flow (per https://acleddata.com/api-documentation/getting-started):
#   1) POST email+password+grant_type=password+client_id=acled+scope=authenticated
#      to https://acleddata.com/oauth/token  → returns access_token (24h) +
#      refresh_token (14 days)
#   2) Subsequent data calls send Authorization: Bearer <access_token>
#   3) When access_token expires (24h), use refresh_token to get a new pair
#
# We support two credential modes (user choice via ./acled_credentials.json):
#   (a) {"email": "...", "password": "..."}      → auto-refresh forever
#   (b) {"access_token": "...", "refresh_token": "..."}  → use until expired
# Tokens are cached in ./acled_tokens.json with their expiry times.

ACLED_CRED_FILE = _here("acled_credentials.json")  # user provides one or the other
ACLED_TOKEN_CACHE = _here("acled_tokens.json")     # we manage this
ACLED_OAUTH_URL = "https://acleddata.com/oauth/token"
ACLED_API_URL = "https://acleddata.com/api/acled/read"
ACLED_RESPONSE_CACHE_TTL = 60 * 60 * 6  # 6 hours


def _acled_load_creds():
    """Load ACLED credentials. Returns dict or None.

    Format A: {"email": "...", "password": "..."}
    Format B: {"access_token": "...", "refresh_token": "..."}
    """
    if not os.path.exists(ACLED_CRED_FILE):
        return None
    try:
        with open(ACLED_CRED_FILE, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return None


def _acled_load_tokens():
    """Load cached tokens (access + refresh) and their expiry timestamps."""
    if not os.path.exists(ACLED_TOKEN_CACHE):
        return None
    try:
        with open(ACLED_TOKEN_CACHE, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return None


def _acled_save_tokens(tokens):
    """Persist token cache. `tokens` is the dict from _acled_fetch_token_response."""
    with open(ACLED_TOKEN_CACHE, "w") as f:
        json.dump(tokens, f)


def _acled_fetch_token_response(form_data):
    """POST to ACLED's OAuth endpoint with form data. Returns parsed JSON."""
    data = urllib.parse.urlencode(form_data).encode("utf-8")
    req = urllib.request.Request(
        ACLED_OAUTH_URL,
        data=data,
        headers={
            "Content-Type": "application/x-www-form-urlencoded",
            "Accept": "application/json",
            "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _acled_get_access_token():
    """Return a valid access token, refreshing or re-authing as needed.

    Strategy:
      1) If cached access_token is still valid (>5 min remaining), use it
      2) Else if cached refresh_token is still valid, use refresh_token grant
      3) Else if credentials file has email+password, do a fresh password grant
      4) Else raise — user needs to set up credentials

    Returns: (access_token, source) where source is for diagnostic display
    """
    now = time.time()
    tokens = _acled_load_tokens()

    # Step 1: still-valid cached access token
    if tokens and tokens.get("access_expires_at", 0) > now + 300:
        return tokens["access_token"], "cached"

    creds = _acled_load_creds()

    # Step 2: try refresh_token grant
    have_refresh = tokens and tokens.get("refresh_expires_at", 0) > now + 60
    if have_refresh:
        try:
            resp = _acled_fetch_token_response({
                "grant_type": "refresh_token",
                "refresh_token": tokens["refresh_token"],
                "client_id": "acled",
            })
            new_tokens = {
                "access_token": resp["access_token"],
                "refresh_token": resp.get("refresh_token", tokens["refresh_token"]),
                "access_expires_at": now + resp.get("expires_in", 86400) - 60,
                # refresh tokens typically last 14 days; if not returned, keep old expiry
                "refresh_expires_at": tokens.get("refresh_expires_at",
                                                 now + 14 * 86400 - 60),
            }
            _acled_save_tokens(new_tokens)
            return new_tokens["access_token"], "refreshed"
        except urllib.error.HTTPError as e:
            # Refresh failed; fall through to password grant if we have one
            print(f"[ACLED] refresh_token grant failed: HTTP {e.code}", file=sys.stderr)

    # Step 3: password grant
    if creds and "email" in creds and "password" in creds:
        try:
            resp = _acled_fetch_token_response({
                "grant_type": "password",
                "username": creds["email"],
                "password": creds["password"],
                "client_id": "acled",
                "scope": "authenticated",
            })
            new_tokens = {
                "access_token": resp["access_token"],
                "refresh_token": resp.get("refresh_token", ""),
                "access_expires_at": now + resp.get("expires_in", 86400) - 60,
                "refresh_expires_at": now + 14 * 86400 - 60,
            }
            _acled_save_tokens(new_tokens)
            return new_tokens["access_token"], "password-grant"
        except urllib.error.HTTPError as e:
            body = ""
            try:
                body = e.read().decode("utf-8", errors="replace")[:200]
            except Exception:
                pass
            raise RuntimeError(
                f"ACLED password grant failed (HTTP {e.code}): {body}\n"
                f"Check your email/password in ./{ACLED_CRED_FILE}."
            )

    # Step 4: manual token provided directly in credentials file
    if creds and "access_token" in creds:
        # Trust it; if it's expired the API call will tell us
        return creds["access_token"], "manual"

    raise RuntimeError(
        f"No ACLED credentials available. Create ./{ACLED_CRED_FILE} with "
        f'either {{"email": "...", "password": "..."}} (auto-refresh) or '
        f'{{"access_token": "...", "refresh_token": "..."}} (manual from browser). '
        f"Register at https://acleddata.com/register to get an account."
    )


def fetch_acled_nearby(lat, lon, radius_km=100, days_back=30, limit=200):
    """Fetch ACLED conflict events within `radius_km` of (lat, lon) in the last
    `days_back` days. Returns list of event dicts.

    ACLED's API doesn't support radius queries directly, so we fetch by
    bounding box and then filter client-side using haversine distance.
    """
    import math

    # Bounding box: pad in degrees. 1 deg lat ≈ 111 km; lon shrinks by cos(lat).
    lat_pad = radius_km / 111.0
    lon_pad = radius_km / max(10.0, 111.0 * math.cos(math.radians(lat)))
    south, north = lat - lat_pad, lat + lat_pad
    west, east = lon - lon_pad, lon + lon_pad

    end = _utcnow_naive().date()
    start = end - dt.timedelta(days=days_back)

    cache_key = f"acled_cache.{round(lat,2)}.{round(lon,2)}.{radius_km}.{days_back}.json"
    cached = _read_cache(cache_key, ACLED_RESPONSE_CACHE_TTL)
    if cached:
        return json.loads(cached)

    access_token, _source = _acled_get_access_token()

    # Build URL — ACLED filter syntax: latitude_where=BETWEEN, longitude_where=BETWEEN,
    # event_date_where=BETWEEN, with values as "min|max"
    params = {
        "latitude": f"{south}|{north}",
        "latitude_where": "BETWEEN",
        "longitude": f"{west}|{east}",
        "longitude_where": "BETWEEN",
        "event_date": f"{start.isoformat()}|{end.isoformat()}",
        "event_date_where": "BETWEEN",
        "limit": str(limit),
        "fields": "event_date|event_type|sub_event_type|country|iso3|"
                  "actor1|actor2|location|fatalities|latitude|longitude|notes",
    }
    qs = "&".join(f"{k}={urllib.parse.quote(str(v), safe='|')}" for k, v in params.items())
    url = f"{ACLED_API_URL}?{qs}"

    req = urllib.request.Request(url, headers={
        "Authorization": f"Bearer {access_token}",
        "Accept": "application/json",
        "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
    })

    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = ""
        try:
            body = e.read().decode("utf-8", errors="replace")[:500]
        except Exception:
            pass
        if e.code == 401:
            if os.path.exists(ACLED_TOKEN_CACHE):
                os.remove(ACLED_TOKEN_CACHE)
            raise RuntimeError(f"ACLED token rejected. Body: {body}")
        if e.code == 403:
            raise RuntimeError(
                f"ACLED denied the request (HTTP 403). Server said: {body}. "
                f"Check that your ACLED account has API access approved at "
                f"https://acleddata.com/dashboard."
            )
        raise RuntimeError(f"ACLED HTTP {e.code}: {body}")

    if not data.get("success", True) and data.get("error"):
        raise RuntimeError(f"ACLED API error: {data['error']}")

    raw_events = data.get("data", []) or []

    # Filter to circle, not just bbox; add distance to each
    def haversine_km(la1, lo1, la2, lo2):
        R = 6371.0
        la1, la2 = math.radians(la1), math.radians(la2)
        dlat = la2 - la1
        dlon = math.radians(lo2 - lo1)
        a = math.sin(dlat/2)**2 + math.cos(la1)*math.cos(la2)*math.sin(dlon/2)**2
        return 2 * R * math.asin(min(1.0, math.sqrt(a)))

    out = []
    for e in raw_events:
        try:
            elat = float(e.get("latitude"))
            elon = float(e.get("longitude"))
            d = haversine_km(lat, lon, elat, elon)
            if d <= radius_km:
                out.append({
                    "event_date": e.get("event_date"),
                    "event_type": e.get("event_type"),
                    "sub_event_type": e.get("sub_event_type"),
                    "country": e.get("country"),
                    "iso3": e.get("iso3"),
                    "actor1": e.get("actor1"),
                    "actor2": e.get("actor2"),
                    "location": e.get("location"),
                    "fatalities": int(e.get("fatalities") or 0),
                    "latitude": elat,
                    "longitude": elon,
                    "distance_km": round(d, 1),
                    "notes": e.get("notes", "")[:300],
                })
        except (TypeError, ValueError):
            continue

    out.sort(key=lambda e: e["event_date"], reverse=True)
    _write_cache(cache_key, json.dumps(out))
    return out


def fetch_acled_global(days_back=7, page_size=500, max_pages=200):
    """Fetch ALL ACLED events globally in the last `days_back` days.

    Pages through ACLED's API until we have everything. Returns a lean payload
    optimized for browser rendering — only fields needed to plot a point.

    Cached server-side for 30 min per date range.
    """
    cache_key = f"acled_global.{days_back}.json"
    cached = _read_cache(cache_key, 60 * 30)  # 30 minutes
    if cached:
        return json.loads(cached)

    end = _utcnow_naive().date()
    start = end - dt.timedelta(days=days_back)
    access_token, _src = _acled_get_access_token()

    all_events = []
    for page in range(1, max_pages + 1):
        params = {
            "event_date": f"{start.isoformat()}|{end.isoformat()}",
            "event_date_where": "BETWEEN",
            "limit": str(page_size),
            "page": str(page),
            # Lean field set: just what we need to plot a point
            "fields": "event_date|event_type|sub_event_type|"
                      "fatalities|latitude|longitude|country|iso3|location",
        }
        qs = "&".join(f"{k}={urllib.parse.quote(str(v), safe='|')}"
                      for k, v in params.items())
        url = f"{ACLED_API_URL}?{qs}"
        req = urllib.request.Request(url, headers={
            "Authorization": f"Bearer {access_token}",
            "Accept": "application/json",
            "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
        })

        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            body = ""
            try:
                body = e.read().decode("utf-8", errors="replace")[:500]
            except Exception:
                pass
            if e.code == 401:
                if os.path.exists(ACLED_TOKEN_CACHE):
                    os.remove(ACLED_TOKEN_CACHE)
                raise RuntimeError(f"ACLED token rejected (401). Body: {body}. "
                                   f"Retry to refresh.")
            if e.code == 403:
                raise RuntimeError(
                    f"ACLED denied the request with HTTP 403.\n\n"
                    f"Server said: {body}\n\n"
                    f"Most likely causes:\n"
                    f"  1) Your account isn't yet approved for API access "
                    f"(separate from website access; check at "
                    f"https://acleddata.com/dashboard for an 'API approved' "
                    f"flag, or email access@acleddata.com).\n"
                    f"  2) Free-tier monthly call limit reached.\n"
                    f"  3) Token has the wrong scope for /api/acled/read."
                )
            raise RuntimeError(f"ACLED HTTP {e.code}: {body}")

        page_events = data.get("data", []) or []
        if not page_events:
            break

        for e in page_events:
            try:
                lat = float(e.get("latitude"))
                lon = float(e.get("longitude"))
            except (TypeError, ValueError):
                continue
            all_events.append({
                "lat": round(lat, 4),
                "lon": round(lon, 4),
                "d": e.get("event_date"),
                "t": e.get("event_type") or "",
                "s": e.get("sub_event_type") or "",
                "f": int(e.get("fatalities") or 0),
                "c": e.get("country") or "",
                "l": e.get("location") or "",
                "i": e.get("iso3") or "",
            })

        # If this page wasn't full, we're done
        if len(page_events) < page_size:
            break

    result = {
        "events": all_events,
        "count": len(all_events),
        "days_back": days_back,
        "start": start.isoformat(),
        "end": end.isoformat(),
        "fetched_at": _utcnow_naive().isoformat() + "Z",
    }
    _write_cache(cache_key, json.dumps(result))
    return result


# ---------------------------------------------------------------------------
# INFORM Risk Index loader
# ---------------------------------------------------------------------------
# INFORM Risk is published as XLSX twice a year. We download two consecutive
# editions to compute a trend per country, parse out the overall INFORMRISK
# score + the three top-level dimensions, and cache as JSON.
#
# Sheet name convention: "INFORM Mid20XX (a-z)" or "INFORM 20XX". The XLSX
# typically has 3 header rows. Column 1 (B) is ISO3, column ~32 is INFORMRISK.
# We robustly find the columns by header text rather than positional indexing.

INFORM_CACHE_FILE = _here("inform_cache.json")
INFORM_CACHE_TTL = 30 * 86400  # refresh monthly

# Verified from https://drmkc.jrc.ec.europa.eu/inform-index/INFORM-Risk/Results-and-data
# The trend file is one ~19 MB workbook containing all years 2016-2025.
# The single-year file is ~2 MB and is the latest single edition.
# We prefer the trend file because it gives us both "current" and "previous"
# in a single download and avoids tracking which versioned URL is current.
INFORM_TREND_URL = (
    "https://drmkc.jrc.ec.europa.eu/inform-index/Portals/0/InfoRM/2025/"
    "INFORM2024_TREND_2015_2024_v70_ALL.xlsx"
)
INFORM_LATEST_URL = (
    "https://drmkc.jrc.ec.europa.eu/inform-index/Portals/0/InfoRM/2025/"
    "INFORM_Risk_Mid_2025_v071.xlsx"
)
INFORM_TREND_FILE = _here("inform_trend.xlsx")


def _inform_find_column(headers_grid, target_names):
    """Find a column index in an XLSX header grid (list of rows, each a list of
    cells). Returns the column index whose value (in any header row) matches
    any name in `target_names` (case-insensitive)."""
    targets = {n.strip().lower() for n in target_names}
    n_cols = max(len(r) for r in headers_grid) if headers_grid else 0
    for col in range(n_cols):
        for row in headers_grid:
            if col < len(row):
                val = str(row[col] or "").strip().lower()
                if val in targets:
                    return col
    return None


def _download_inform_file(url, local_path):
    """Download an INFORM XLSX from JRC to local_path."""
    if os.path.exists(local_path) and os.path.getsize(local_path) > 10_000:
        return local_path
    print(f"[INFORM] downloading {url}", file=sys.stderr)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (gdacs-dashboard)"})
    with urllib.request.urlopen(req, timeout=120) as resp:
        with open(local_path + ".part", "wb") as f:
            while True:
                chunk = resp.read(256 * 1024)
                if not chunk:
                    break
                f.write(chunk)
    os.rename(local_path + ".part", local_path)
    return local_path


def _parse_inform_sheet(ws, sheet_name):
    """Parse a single INFORM sheet (any year). Returns {ISO3: {score, hazard,
    vulnerability, coping}} or empty dict on failure."""
    rows = list(ws.iter_rows(values_only=True))
    if len(rows) < 5:
        return {}, "sheet has <5 rows"

    # INFORM workbooks vary: headers can be on row 1, 3, or 4 depending on
    # edition. Search the first 6 rows for one containing 'ISO3'.
    header_row_idx = None
    for i in range(min(6, len(rows))):
        if any(str(c or "").strip().upper() in ("ISO3", "ISO 3", "ISO_3") for c in rows[i]):
            header_row_idx = i
            break
    if header_row_idx is None:
        return {}, f"no ISO3 header found in first 6 rows of '{sheet_name}'"

    # Collect headers from the row we found + 1-2 rows above (for merged cells)
    look_rows = rows[max(0, header_row_idx - 2): header_row_idx + 1]

    iso3_col = _inform_find_column(look_rows, ["ISO3", "ISO 3", "ISO_3"])
    risk_col = _inform_find_column(look_rows, [
        "INFORMRISK", "INFORM RISK", "INFORM Risk", "INFORM",
        "Risk Index", "Risk"])
    hazard_col = _inform_find_column(look_rows, [
        "HAZARD & EXPOSURE", "Hazard & Exposure", "HAZARD_EXPOSURE",
        "Hazard and Exposure"])
    vuln_col = _inform_find_column(look_rows, ["VULNERABILITY", "Vulnerability"])
    coping_col = _inform_find_column(look_rows, [
        "LACK OF COPING CAPACITY", "Lack of Coping Capacity",
        "COPING CAPACITY", "Coping Capacity", "Lack of coping capacity"])

    if iso3_col is None or risk_col is None:
        return {}, (f"missing ISO3 (col {iso3_col}) or risk (col {risk_col}) "
                    f"in '{sheet_name}'")

    out = {}
    for row in rows[header_row_idx + 1:]:
        if not row or iso3_col >= len(row) or row[iso3_col] is None:
            continue
        iso3 = str(row[iso3_col]).strip().upper()
        if len(iso3) != 3 or not iso3.isalpha():
            continue
        if risk_col >= len(row) or row[risk_col] is None:
            continue
        try:
            score = float(row[risk_col])
        except (ValueError, TypeError):
            continue
        if not (0 <= score <= 10):
            continue
        def _maybe(col):
            if col is None or col >= len(row) or row[col] is None:
                return None
            try:
                v = float(row[col])
                return v if 0 <= v <= 10 else None
            except (ValueError, TypeError):
                return None
        out[iso3] = {
            "score": round(score, 2),
            "hazard": _maybe(hazard_col),
            "vulnerability": _maybe(vuln_col),
            "coping": _maybe(coping_col),
        }
    return out, None


def fetch_inform_data():
    """Load INFORM Risk data for the two most recent editions; compute trend.

    Strategy:
      1) If a fresh JSON cache exists, return it
      2) Else download the INFORM trend workbook from JRC (~19 MB, cached)
      3) Find the two most recent INFORM yearly sheets, parse both
      4) If trend file fails, fall back to the single-year "latest" file
         (which gives current data but no trend)

    Returns {
        "current": {ISO3: {score, hazard, vulnerability, coping}, ...},
        "previous": {ISO3: {score, ...}, ...},  # may be empty if no trend data
        "trends": {ISO3: {delta, direction}},
        "current_label": "2025 Mid",
        "previous_label": "2024" or None,
    }
    """
    if os.path.exists(INFORM_CACHE_FILE):
        age = time.time() - os.path.getmtime(INFORM_CACHE_FILE)
        if age < INFORM_CACHE_TTL:
            try:
                with open(INFORM_CACHE_FILE, "r") as f:
                    cached = json.load(f)
                # Sanity check the cache — skip if it's malformed or empty
                if cached.get("current") and len(cached["current"]) > 10:
                    return cached
            except (json.JSONDecodeError, OSError):
                pass  # fall through to re-fetch

    try:
        from openpyxl import load_workbook
    except ImportError:
        raise RuntimeError("openpyxl required. Run: pip install openpyxl")

    # ---- Primary: trend workbook with multiple years ----
    try:
        _download_inform_file(INFORM_TREND_URL, INFORM_TREND_FILE)
        wb = load_workbook(INFORM_TREND_FILE, data_only=True, read_only=True)

        # Find all INFORM yearly sheets. Sheet names look like "INFORM 2016",
        # "INFORM 2017", ..., possibly with extra labels like "(a-z)".
        import re
        year_sheets = []
        for name in wb.sheetnames:
            m = re.search(r'20\d{2}', name)
            if m and "inform" in name.lower():
                year_sheets.append((int(m.group(0)), name))
        year_sheets.sort(key=lambda x: x[0], reverse=True)

        if not year_sheets:
            raise RuntimeError(f"No INFORM yearly sheets found in trend file. "
                               f"Sheets: {wb.sheetnames[:10]}")

        # Parse current + previous
        cur_year, cur_name = year_sheets[0]
        cur_data, cur_err = _parse_inform_sheet(wb[cur_name], cur_name)
        if cur_err or not cur_data:
            wb.close()
            raise RuntimeError(f"Couldn't parse latest sheet '{cur_name}': {cur_err}")

        prev_data, prev_label = {}, None
        if len(year_sheets) > 1:
            prev_year, prev_name = year_sheets[1]
            prev_data, _prev_err = _parse_inform_sheet(wb[prev_name], prev_name)
            prev_label = str(prev_year)

        wb.close()

        trends = {}
        for iso3, info in cur_data.items():
            if iso3 in prev_data and prev_data[iso3]["score"] is not None:
                delta = info["score"] - prev_data[iso3]["score"]
                direction = "up" if delta > 0.15 else "down" if delta < -0.15 else "flat"
                trends[iso3] = {"delta": round(delta, 2), "direction": direction}

        result = {
            "current": cur_data,
            "previous": prev_data,
            "trends": trends,
            "current_label": str(cur_year),
            "previous_label": prev_label,
            "source": "trend file",
        }
        with open(INFORM_CACHE_FILE, "w") as f:
            json.dump(result, f)
        return result

    except (urllib.error.HTTPError, urllib.error.URLError) as e:
        print(f"[INFORM] trend file unreachable: {e}; trying latest single file",
              file=sys.stderr)
    except Exception as e:
        print(f"[INFORM] trend parse failed: {e}; trying latest single file",
              file=sys.stderr)

    # ---- Fallback: latest single-year file (no trend computed) ----
    latest_path = "inform_latest.xlsx"
    _download_inform_file(INFORM_LATEST_URL, latest_path)
    wb = load_workbook(latest_path, data_only=True, read_only=True)

    # Pick the first sheet that has an ISO3 column
    target_sheet = None
    for name in wb.sheetnames:
        if name.lower().startswith("inform"):
            target_sheet = name
            break
    if target_sheet is None:
        target_sheet = wb.sheetnames[0]

    cur_data, cur_err = _parse_inform_sheet(wb[target_sheet], target_sheet)
    wb.close()
    if cur_err or not cur_data:
        raise RuntimeError(f"Couldn't parse INFORM data: {cur_err}")

    result = {
        "current": cur_data,
        "previous": {},
        "trends": {},
        "current_label": "Mid 2025",
        "previous_label": None,
        "source": "latest single file (no trend data)",
    }
    with open(INFORM_CACHE_FILE, "w") as f:
        json.dump(result, f)
    return result


# ---------------------------------------------------------------------------
# Natural Earth admin-0 country polygons (for the INFORM choropleth)
# ---------------------------------------------------------------------------
# We fetch a 1:110m GeoJSON from a public CDN and cache. ~250 KB.

COUNTRIES_GEOJSON_URL = (
    "https://raw.githubusercontent.com/nvkelso/natural-earth-vector/master/"
    "geojson/ne_110m_admin_0_countries.geojson"
)
COUNTRIES_CACHE_FILE = _here("countries_cache.geojson")


def fetch_countries_geojson():
    """Cached fetch of world country boundaries."""
    if os.path.exists(COUNTRIES_CACHE_FILE):
        with open(COUNTRIES_CACHE_FILE, "r") as f:
            return f.read()
    print(f"[countries] downloading {COUNTRIES_GEOJSON_URL}", file=sys.stderr)
    req = urllib.request.Request(COUNTRIES_GEOJSON_URL, headers={
        "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
    })
    with urllib.request.urlopen(req, timeout=60) as resp:
        body = resp.read().decode("utf-8")
    with open(COUNTRIES_CACHE_FILE, "w") as f:
        f.write(body)
    return body


# ---------------------------------------------------------------------------
# S2S forecast files (LIS-S2S Standardized Anomalies; 557WW filename schema)
# ---------------------------------------------------------------------------
# Filename schema example:
#   PS.557WW_SC.U_DI.C_GP.LIS-S2S-SANOM_GR.C0P25DEG_AR.GLOBAL
#       _PA.RZSM_DD.20260401_FP.20260401-20260501_DF.TIF
#
# Fields we care about:
#   PA.<var>         physical attribute (RZSM = root-zone soil moisture)
#   DD.<YYYYMMDD>    initialization (initial condition / IC) date
#   FP.<start>-<end> forecast period covered by this file
#
# Lead types are derived from FP period length:
#   weekly  ~ 7 days
#   monthly ~ 28-31 days
#   sub-monthly other (rare; bucketed as 'other')

FCST_DIR = _here("FCST")
FCST_TILE_URLPATH = "fcst_tiles"
FCST_TILE_DIR = _here(FCST_TILE_URLPATH)


def _parse_557ww_filename(filename):
    """Parse a 557WW-style forecast filename. Returns dict or None.

    Returns: {ic, fp_start, fp_end, lead_type, lead_days, variable, path}
    """
    name = filename
    if name.endswith(".TIF") or name.endswith(".tif"):
        name = name[:-4]
    fields = {}
    for token in name.split("_"):
        if "." in token:
            k, _, v = token.partition(".")
            fields[k] = v

    if "DD" not in fields or "FP" not in fields:
        return None

    try:
        ic = dt.datetime.strptime(fields["DD"], "%Y%m%d").date()
    except ValueError:
        return None

    fp = fields["FP"]
    if "-" not in fp:
        return None
    fp_start_s, fp_end_s = fp.split("-", 1)
    try:
        fp_start = dt.datetime.strptime(fp_start_s, "%Y%m%d").date()
        fp_end = dt.datetime.strptime(fp_end_s, "%Y%m%d").date()
    except ValueError:
        return None

    days = (fp_end - fp_start).days
    if 5 <= days <= 10:
        lead_type = "weekly"
    elif 25 <= days <= 35:
        lead_type = "monthly"
    else:
        lead_type = "other"

    return {
        "ic": ic.isoformat(),
        "fp_start": fp_start.isoformat(),
        "fp_end": fp_end.isoformat(),
        "lead_type": lead_type,
        "lead_days": days,
        "variable": fields.get("PA", "UNKNOWN"),
        "filename": filename,
    }


def list_forecasts():
    """Walk FCST/ and return a catalog grouped by IC, lead_type, variable."""
    if not os.path.isdir(FCST_DIR):
        return {"ics": [], "directory": FCST_DIR, "exists": False}

    by_key = {}  # (ic, variable) -> list of file metadata
    for fname in sorted(os.listdir(FCST_DIR)):
        if not (fname.endswith(".TIF") or fname.endswith(".tif")):
            continue
        meta = _parse_557ww_filename(fname)
        if not meta:
            continue
        meta["path"] = os.path.join(FCST_DIR, fname)
        key = (meta["ic"], meta["variable"])
        by_key.setdefault(key, []).append(meta)

    # Group into a list of ICs, each with weekly / monthly / other leads
    ics = {}
    for (ic, variable), files in by_key.items():
        files.sort(key=lambda f: f["fp_start"])
        if ic not in ics:
            ics[ic] = {"ic": ic, "variables": {}}
        ics[ic]["variables"].setdefault(variable, {
            "weekly": [], "monthly": [], "other": [],
        })
        for f in files:
            ics[ic]["variables"][variable][f["lead_type"]].append({
                "fp_start": f["fp_start"],
                "fp_end": f["fp_end"],
                "lead_days": f["lead_days"],
                "filename": f["filename"],
            })

    return {
        "ics": sorted(ics.values(), key=lambda x: x["ic"], reverse=True),
        "directory": FCST_DIR,
        "exists": True,
        "count": sum(len(f) for f in by_key.values()),
    }


def render_forecast_tile(filename, sigma_clip=2.0):
    """Render a single 557WW forecast GeoTIFF as a colored PNG.

    Returns dict with: png_path, bounds [[s,w],[n,e]], stats {min, max, mean,
    valid_pixels, total_pixels}, sigma_clip.
    """
    try:
        import tifffile
        import numpy as np
        import math
        from PIL import Image
    except ImportError as e:
        raise RuntimeError(f"Missing dependency: {e}. "
                           f"Run: pip install tifffile numpy pillow")

    path = os.path.join(FCST_DIR, filename)
    if not os.path.exists(path):
        raise RuntimeError(f"File not found: {path}")

    # Read raster + georef tags in one pass. We need the tags to know what
    # geographic extent this file covers — file shapes vary (e.g., 720×1440
    # for full-global at 0.25°, or 600×1440 for the 90°N to -60°S land-only
    # subset that LIS-S2S sometimes uses).
    pixel_scale = None
    tiepoint = None
    with tifffile.TiffFile(path) as tif:
        page = tif.pages[0]
        for tag in page.tags.values():
            if tag.name == "ModelPixelScaleTag":
                pixel_scale = tag.value      # (dx, dy, dz) in degrees
            elif tag.name == "ModelTiepointTag":
                tiepoint = tag.value         # (i, j, k, x, y, z)
        arr = page.asarray()

    if arr.ndim == 3:
        arr = arr[0]  # take first band if multi-band
    arr = arr.astype(np.float32)

    # Standardized anomalies are unitless, almost always within ±5; anything
    # beyond ±10 is corrupted (we've seen sentinel-like -62.57 in some files).
    # GDAL_NODATA is -9999 (rarely emitted as a literal but possible).
    valid = np.isfinite(arr) & (arr > -10) & (arr < 10) & (arr != -9999)
    valid_count = int(valid.sum())
    total_count = int(arr.size)

    if valid_count == 0:
        raise RuntimeError(f"No valid pixels found in {filename}")

    valid_data = arr[valid]
    stats = {
        "min": float(valid_data.min()),
        "max": float(valid_data.max()),
        "mean": float(valid_data.mean()),
        "std": float(valid_data.std()),
        "valid_pixels": valid_count,
        "total_pixels": total_count,
    }

    # Clip to ±sigma_clip for the color scale (these are standardized
    # anomalies; ~99% of values fall within ±3 sigma). Replace NaN/invalid
    # with 0 in the working array so the colormap math doesn't propagate NaN.
    clipped = np.where(valid, np.clip(arr, -sigma_clip, sigma_clip), 0.0)
    norm = (clipped + sigma_clip) / (2 * sigma_clip)  # 0..1; 0.5 = neutral

    # Diverging colormap: negative (lower) → red,
    # positive (higher) → blue, neutral → white.
    # This matches the operational drought-monitor convention (USDM, SPI,
    # JRC Combined Drought Indicator): red = low, blue = high.
    # Stops: red (211,47,47) → white (255,255,255) → blue (33,102,172).
    r_below = 211 + (255 - 211) * (norm / 0.5)
    r_above = 255 - (255 - 33)  * ((norm - 0.5) / 0.5)
    g_below = 47  + (255 - 47)  * (norm / 0.5)
    g_above = 255 - (255 - 102) * ((norm - 0.5) / 0.5)
    b_below = 47  + (255 - 47)  * (norm / 0.5)
    b_above = 255 - (255 - 172) * ((norm - 0.5) / 0.5)
    r = np.clip(np.where(norm < 0.5, r_below, r_above), 0, 255).astype(np.uint8)
    g = np.clip(np.where(norm < 0.5, g_below, g_above), 0, 255).astype(np.uint8)
    b = np.clip(np.where(norm < 0.5, b_below, b_above), 0, 255).astype(np.uint8)

    rgba = np.zeros((*arr.shape, 4), dtype=np.uint8)
    rgba[..., 0] = np.where(valid, r, 0)
    rgba[..., 1] = np.where(valid, g, 0)
    rgba[..., 2] = np.where(valid, b, 0)
    rgba[..., 3] = np.where(valid, 200, 0)  # ~80% opaque; transparent where invalid

    img = Image.fromarray(rgba, mode="RGBA")

    # Compute geographic bounds from the GeoTIFF tags. The standard convention:
    # ModelTiepointTag = (i, j, k, x, y, z) maps pixel (i, j) to geographic
    # (x=lon, y=lat); ModelPixelScaleTag = (dx, dy, dz) is degrees per pixel.
    # The tiepoint almost always identifies the top-left corner (i=j=0).
    h, w = arr.shape
    if pixel_scale is not None and tiepoint is not None:
        i_ref, j_ref, _k, x_ref, y_ref, _z = tiepoint
        dx, dy, _dz = pixel_scale
        west  = x_ref - i_ref * dx
        north = y_ref + j_ref * dy   # y increases up; j increases down
        east  = west + w * dx
        south = north - h * dy
    else:
        # Fallback: assume full-global 0.25° (matches GR.C0P25DEG_AR.GLOBAL filename)
        print(f"[forecast] {filename} lacks georef tags; assuming -180,-90,180,90",
              file=sys.stderr)
        west, north, east, south = -180.0, 90.0, 180.0, -90.0

    # ------------------------------------------------------------------
    # Reproject equirectangular (EPSG:4326) RGBA into Web Mercator
    # (EPSG:3857) so it overlays correctly on Leaflet's default basemap.
    #
    # Leaflet's L.imageOverlay places corners at the bounds you give but
    # using the CURRENT MAP PROJECTION's pixel coords. The default basemap
    # is in Web Mercator, which has nonlinear vertical scaling: a row at
    # +60°N is only ~half the on-screen distance from the equator as the
    # equirectangular projection would put it. So if we feed Leaflet an
    # unprojected (equirectangular) PNG with global bounds, the image gets
    # vertically squished at high latitudes and the overlay misaligns with
    # the basemap.
    #
    # Fix: pre-warp the image into Web Mercator pixel space, then declare
    # Mercator-clipped bounds. Standard Mercator clip is ±85.0511287° lat.
    # ------------------------------------------------------------------
    MERC_LAT_MAX = 85.05112877980659  # standard Web Mercator clip

    def _lat_to_mercY(lat):
        """Web Mercator Y coordinate (normalized 0 at +85.05°, 1 at -85.05°)."""
        lat_r = math.radians(lat)
        y = math.log(math.tan(math.pi / 4 + lat_r / 2))
        # The world-extent y range is [-pi, +pi]; normalize to [0, 1]
        y_max = math.log(math.tan(math.pi / 4 + math.radians(MERC_LAT_MAX) / 2))
        return (y_max - y) / (2 * y_max)

    # We'll output a Mercator image with the same width and a height that
    # preserves equal pixel aspect at the equator: width spans 360° of
    # longitude, so 1 pixel = 360/w degrees. At the equator, 1 vertical
    # Mercator pixel covers the same ground distance. Total Mercator world
    # height in degrees-equivalent = 360 / cos(0) * 1 = 360, so a square
    # world is h_merc = w. We'll use w = w (1440), h_merc = w = 1440.
    h_merc = w
    # Output Mercator bounds — always the full Mercator world
    out_north = MERC_LAT_MAX
    out_south = -MERC_LAT_MAX
    # If the source data starts north of +85 or extends south of -85, we
    # just clip. If it doesn't reach those extremes (e.g. north=80), the
    # tile will be transparent above the source extent.

    # For each Mercator output row, find the corresponding source row in
    # the equirectangular image.
    src_top_lat = north
    src_bot_lat = south
    src_dy_per_row = (src_top_lat - src_bot_lat) / h  # positive

    # Build a row lookup: for each output row 0..h_merc-1, what source row?
    out_y = np.arange(h_merc)
    # Mercator y in projected meters-like units, but we work in normalized:
    # y_norm runs 0 at top (+85.05) to 1 at bottom (-85.05).
    y_norm = out_y / (h_merc - 1)  # 0..1
    # Convert normalized mercator y back to latitude
    y_max_proj = math.log(math.tan(math.pi/4 + math.radians(MERC_LAT_MAX)/2))
    y_proj = (1 - 2 * y_norm) * y_max_proj  # in projected coords
    out_lats = np.degrees(2 * (np.arctan(np.exp(y_proj)) - math.pi / 4))

    # Map each out_lat to source row index
    src_rows = ((src_top_lat - out_lats) / src_dy_per_row).astype(np.int32)
    valid_src = (src_rows >= 0) & (src_rows < h)

    # Build output RGBA by row-indexing into the source
    out_rgba = np.zeros((h_merc, w, 4), dtype=np.uint8)
    safe_src = np.where(valid_src, src_rows, 0)
    out_rgba[:, :, :] = rgba[safe_src, :, :]
    out_rgba[~valid_src, :, 3] = 0  # transparent above/below source coverage

    img = Image.fromarray(out_rgba, mode="RGBA")

    # Mercator bounds we declare to Leaflet. We span the full Mercator world
    # horizontally but only the rows that contain real data.
    bounds = [[float(max(south, -MERC_LAT_MAX)), float(west)],
              [float(min(north,  MERC_LAT_MAX)), float(east)]]
    # Since we built out_rgba to cover the full Mercator world height
    # (-85.05 to +85.05) and put transparent rows outside the source extent,
    # the bounds for Leaflet should reflect what the IMAGE covers:
    bounds = [[float(-MERC_LAT_MAX), float(west)],
              [float( MERC_LAT_MAX), float(east)]]

    # Save PNG
    os.makedirs(FCST_TILE_DIR, exist_ok=True)
    png_name = filename.replace(".TIF", ".png").replace(".tif", ".png")
    png_path = os.path.join(FCST_TILE_DIR, png_name)
    img.save(png_path, "PNG", optimize=True)

    return {
        "png_url": f"/{FCST_TILE_URLPATH}/{png_name}",
        "bounds": bounds,
        "stats": stats,
        "sigma_clip": sigma_clip,
        "shape": [h, w],
        "mercator": True,
    }



def parse_tle_for_satellites(tle_text, sat_ids):
    """Pull out TLE line pairs for our requested satellites (by NORAD id)."""
    wanted = {SATELLITES[s]["norad"]: s for s in sat_ids if s in SATELLITES}
    out = {}
    lines = [ln.rstrip() for ln in tle_text.splitlines() if ln.strip()]
    i = 0
    while i + 2 < len(lines):
        name, l1, l2 = lines[i], lines[i + 1], lines[i + 2]
        if l1.startswith("1 ") and l2.startswith("2 "):
            try:
                norad = int(l1[2:7])
                if norad in wanted:
                    sid = wanted[norad]
                    if sid not in out:
                        out[sid] = {"name": name.strip(), "line1": l1, "line2": l2}
            except ValueError:
                pass
            i += 3
        else:
            i += 1
    return out


def compute_ground_tracks(tle_pairs, hours_ahead=24, step_minutes=2):
    """Use sgp4 to compute lat/lon ground track points for each satellite,
    plus the left/right edges of the instrument swath.

    Returns {sat_id: {
        name, points: [[lat, lon, unix_ts], ...],
        left_edge:  [[lat, lon], ...],
        right_edge: [[lat, lon], ...],
        swath_km, instr,
    }}
    """
    try:
        from sgp4.api import Satrec, jday
    except ImportError:
        return {"error": "sgp4 is not installed. Run: pip install sgp4"}

    import math

    EARTH_R = 6371.0  # mean Earth radius in km

    def offset_point(lat_deg, lon_deg, bearing_deg, dist_km):
        """Forward great-circle offset (Haversine direct formula)."""
        lat = math.radians(lat_deg)
        lon = math.radians(lon_deg)
        brg = math.radians(bearing_deg)
        ang = dist_km / EARTH_R
        lat2 = math.asin(math.sin(lat) * math.cos(ang)
                         + math.cos(lat) * math.sin(ang) * math.cos(brg))
        lon2 = lon + math.atan2(
            math.sin(brg) * math.sin(ang) * math.cos(lat),
            math.cos(ang) - math.sin(lat) * math.sin(lat2)
        )
        return math.degrees(lat2), ((math.degrees(lon2) + 540) % 360) - 180

    def initial_bearing(lat1_d, lon1_d, lat2_d, lon2_d):
        """Initial great-circle bearing from point 1 to point 2 (degrees, 0=N)."""
        lat1, lat2 = math.radians(lat1_d), math.radians(lat2_d)
        dlon = math.radians(lon2_d - lon1_d)
        x = math.sin(dlon) * math.cos(lat2)
        y = (math.cos(lat1) * math.sin(lat2)
             - math.sin(lat1) * math.cos(lat2) * math.cos(dlon))
        return (math.degrees(math.atan2(x, y)) + 360) % 360

    tracks = {}
    now = _utcnow_naive()

    for sat_id, tle in tle_pairs.items():
        sat = Satrec.twoline2rv(tle["line1"], tle["line2"])
        meta = SATELLITES.get(sat_id, {})
        half_swath = meta.get("swath_km", 0) / 2.0
        tilt = meta.get("tilt_deg", 0)  # bias the centerline of the swath off-nadir

        points = []
        for minute in range(0, hours_ahead * 60, step_minutes):
            t = now + dt.timedelta(minutes=minute)
            jd, fr = jday(t.year, t.month, t.day, t.hour, t.minute, t.second)
            err, r, _v = sat.sgp4(jd, fr)
            if err != 0:
                continue
            x, y, z = r  # km in TEME (close enough to ECI for plotting)
            jd_total = jd + fr
            T = (jd_total - 2451545.0) / 36525.0
            gmst = (280.46061837 + 360.98564736629 * (jd_total - 2451545.0)
                    + 0.000387933 * T * T - T * T * T / 38710000.0)
            gmst_rad = math.radians(gmst % 360.0)
            cos_g, sin_g = math.cos(gmst_rad), math.sin(gmst_rad)
            xe =  cos_g * x + sin_g * y
            ye = -sin_g * x + cos_g * y
            ze = z
            lon = math.degrees(math.atan2(ye, xe))
            hyp = math.sqrt(xe * xe + ye * ye)
            lat = math.degrees(math.atan2(ze, hyp))
            points.append([round(lat, 3), round(lon, 3), int(t.timestamp())])

        # Compute swath edges by offsetting perpendicular to the velocity bearing
        # at each point. Bearing is approximated using the next point.
        left_edge, right_edge = [], []
        if half_swath > 0 and len(points) >= 2:
            for i, (lat, lon, _t) in enumerate(points):
                # Use forward difference for bearing (or backward for last point)
                if i < len(points) - 1:
                    nlat, nlon = points[i + 1][0], points[i + 1][1]
                else:
                    plat, plon = points[i - 1][0], points[i - 1][1]
                    nlat, nlon = lat + (lat - plat), lon + (lon - plon)
                brg = initial_bearing(lat, lon, nlat, nlon)
                # Right is bearing + 90, left is bearing - 90
                # Tilt biases everything (e.g. Sentinel-3 OLCI tilts 12.6 deg west)
                right = (brg + 90 + tilt) % 360
                left  = (brg - 90 + tilt) % 360
                rlat, rlon = offset_point(lat, lon, right, half_swath)
                llat, llon = offset_point(lat, lon, left,  half_swath)
                right_edge.append([round(rlat, 3), round(rlon, 3)])
                left_edge.append([round(llat, 3), round(llon, 3)])

        tracks[sat_id] = {
            "name": tle["name"],
            "points": points,
            "left_edge": left_edge,
            "right_edge": right_edge,
            "swath_km": meta.get("swath_km", 0),
            "instr": meta.get("instr", ""),
        }
    return tracks


# ---------------------------------------------------------------------------
# Overpass prediction & temporal-overlap analysis for a target point
# ---------------------------------------------------------------------------

def compute_overpasses(tle_pairs, target_lat, target_lon, days_ahead=7,
                       step_seconds=30, geometry_window_minutes=4):
    """For each satellite, find time windows when its swath covers the target.

    Each pass also includes a swath polygon (the actual ground footprint
    near the time of closest approach), so the frontend can plot the exact
    region observed during that pass. The polygon spans ±geometry_window_minutes
    around the time of closest approach.

    Returns {sat_id: {name, swath_km, instr, passes: [{start, end, duration_s,
        peak_distance_km, peak_time, centerline, swath_polygon}]}}.
    Times are ISO 8601 UTC strings.
    """
    try:
        from sgp4.api import Satrec, jday
    except ImportError:
        return {"error": "sgp4 not installed"}

    import math

    EARTH_R = 6371.0

    def gc_distance_km(lat1_d, lon1_d, lat2_d, lon2_d):
        lat1, lat2 = math.radians(lat1_d), math.radians(lat2_d)
        dlat = lat2 - lat1
        dlon = math.radians(lon2_d - lon1_d)
        a = math.sin(dlat / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin(dlon / 2) ** 2
        return 2 * EARTH_R * math.asin(min(1.0, math.sqrt(a)))

    def initial_bearing(lat1_d, lon1_d, lat2_d, lon2_d):
        lat1, lat2 = math.radians(lat1_d), math.radians(lat2_d)
        dlon = math.radians(lon2_d - lon1_d)
        x = math.sin(dlon) * math.cos(lat2)
        y = (math.cos(lat1) * math.sin(lat2)
             - math.sin(lat1) * math.cos(lat2) * math.cos(dlon))
        return (math.degrees(math.atan2(x, y)) + 360) % 360

    def cross_track_distance_km(lat_t, lon_t, lat_a, lon_a, lat_b, lon_b):
        """Perpendicular distance from target T to the great-circle arc A->B."""
        d_at = gc_distance_km(lat_a, lon_a, lat_t, lon_t) / EARTH_R  # in radians
        brg_at = math.radians(initial_bearing(lat_a, lon_a, lat_t, lon_t))
        brg_ab = math.radians(initial_bearing(lat_a, lon_a, lat_b, lon_b))
        return abs(math.asin(math.sin(d_at) * math.sin(brg_at - brg_ab))) * EARTH_R

    def offset_point(lat_deg, lon_deg, bearing_deg, dist_km):
        """Forward great-circle offset (Haversine direct formula)."""
        lat = math.radians(lat_deg)
        lon = math.radians(lon_deg)
        brg = math.radians(bearing_deg)
        ang = dist_km / EARTH_R
        lat2 = math.asin(math.sin(lat) * math.cos(ang)
                         + math.cos(lat) * math.sin(ang) * math.cos(brg))
        lon2 = lon + math.atan2(
            math.sin(brg) * math.sin(ang) * math.cos(lat),
            math.cos(ang) - math.sin(lat) * math.sin(lat2)
        )
        return math.degrees(lat2), ((math.degrees(lon2) + 540) % 360) - 180

    def propagate(t):
        """Run SGP4 at time t and return (lat, lon) or None on error."""
        jd, fr = jday(t.year, t.month, t.day, t.hour, t.minute, t.second)
        err, r, _v = sat.sgp4(jd, fr)
        if err != 0:
            return None
        x, y, z = r
        jd_total = jd + fr
        T = (jd_total - 2451545.0) / 36525.0
        gmst = (280.46061837 + 360.98564736629 * (jd_total - 2451545.0)
                + 0.000387933 * T * T - T * T * T / 38710000.0)
        gmst_rad = math.radians(gmst % 360.0)
        cos_g, sin_g = math.cos(gmst_rad), math.sin(gmst_rad)
        xe =  cos_g * x + sin_g * y
        ye = -sin_g * x + cos_g * y
        ze = z
        lon_deg = math.degrees(math.atan2(ye, xe))
        hyp = math.sqrt(xe * xe + ye * ye)
        lat_deg = math.degrees(math.atan2(ze, hyp))
        return lat_deg, lon_deg

    def build_pass_geometry(peak_t, half_swath, tilt_deg):
        """Build centerline + swath polygon for a pass, ±geometry_window_minutes
        around the peak. Returns (centerline, polygon) as lat/lon coordinate lists.
        """
        # Sample at 15-second resolution for a smooth polygon
        n = int((geometry_window_minutes * 60) // 15)
        center = []
        for k in range(-n, n + 1):
            tk = peak_t + dt.timedelta(seconds=k * 15)
            pos = propagate(tk)
            if pos:
                center.append([pos[0], pos[1]])

        if len(center) < 2:
            return [], []

        left, right = [], []
        for i, (clat, clon) in enumerate(center):
            if i < len(center) - 1:
                nlat, nlon = center[i + 1]
            else:
                plat, plon = center[i - 1]
                nlat, nlon = clat + (clat - plat), clon + (clon - plon)
            brg = initial_bearing(clat, clon, nlat, nlon)
            r_brg = (brg + 90 + tilt_deg) % 360
            l_brg = (brg - 90 + tilt_deg) % 360
            rlat, rlon = offset_point(clat, clon, r_brg, half_swath)
            llat, llon = offset_point(clat, clon, l_brg, half_swath)
            left.append([round(llat, 3), round(llon, 3)])
            right.append([round(rlat, 3), round(rlon, 3)])

        # Round centerline too
        centerline = [[round(c[0], 3), round(c[1], 3)] for c in center]
        # Polygon = walk left edge forward, right edge backward
        polygon = left + list(reversed(right))
        return centerline, polygon

    out = {}
    now = _utcnow_naive()
    total_steps = (days_ahead * 24 * 3600) // step_seconds

    # `sat` is referenced inside the propagate closure
    sat = None

    for sat_id, tle in tle_pairs.items():
        meta = SATELLITES.get(sat_id, {})
        half_swath = meta.get("swath_km", 0) / 2.0
        tilt = meta.get("tilt_deg", 0)
        if half_swath <= 0:
            continue

        sat = Satrec.twoline2rv(tle["line1"], tle["line2"])
        passes = []
        in_pass = False
        pass_start_t = None
        pass_min_dist = None
        pass_min_t = None
        prev_pos = None  # (t, lat, lon)

        def finalize_pass(end_time):
            """Close out the current pass and append it to the list."""
            centerline, polygon = build_pass_geometry(pass_min_t, half_swath, tilt)
            passes.append({
                "start": pass_start_t.isoformat() + "Z",
                "end": end_time.isoformat() + "Z",
                "duration_s": int((end_time - pass_start_t).total_seconds()),
                "peak_distance_km": round(pass_min_dist, 1),
                "peak_time": pass_min_t.isoformat() + "Z",
                "centerline": centerline,
                "swath_polygon": polygon,
            })

        for step in range(int(total_steps)):
            t = now + dt.timedelta(seconds=step * step_seconds)
            pos = propagate(t)
            if pos is None:
                continue
            lat, lon = pos

            # Cheap rejection: only do the expensive cross-track calc if the
            # nadir point is within (half_swath + 1500) km of the target.
            nadir_dist = gc_distance_km(lat, lon, target_lat, target_lon)
            if nadir_dist > half_swath + 1500:
                if in_pass:
                    finalize_pass(prev_pos[0])
                    in_pass = False
                prev_pos = (t, lat, lon)
                continue

            if prev_pos is not None:
                ct_dist = cross_track_distance_km(
                    target_lat, target_lon,
                    prev_pos[1], prev_pos[2], lat, lon
                )
            else:
                ct_dist = nadir_dist

            inside = ct_dist <= half_swath

            if inside and not in_pass:
                in_pass = True
                pass_start_t = t
                pass_min_dist = ct_dist
                pass_min_t = t
            elif inside and in_pass:
                if ct_dist < pass_min_dist:
                    pass_min_dist = ct_dist
                    pass_min_t = t
            elif not inside and in_pass:
                in_pass = False
                finalize_pass(t)

            prev_pos = (t, lat, lon)

        if in_pass and prev_pos is not None:
            finalize_pass(prev_pos[0])

        out[sat_id] = {
            "name": tle["name"],
            "swath_km": meta.get("swath_km", 0),
            "instr": meta.get("instr", ""),
            "passes": passes,
        }
    return out


def find_temporal_overlaps(overpass_data, gap_minutes=120):
    """Group passes into clusters where each pair is within gap_minutes.

    A "cluster" is a time window in which 2+ different satellites observe the
    same target. Returns a sorted list of clusters.
    """
    flat = []
    for sat_id, info in overpass_data.items():
        if sat_id == "error":
            continue
        for p in info["passes"]:
            flat.append({
                "sat_id": sat_id,
                "sat_name": info["name"],
                "instr": info["instr"],
                "swath_km": info["swath_km"],
                "peak_time": p["peak_time"],
                "start": p["start"],
                "end": p["end"],
                "peak_distance_km": p["peak_distance_km"],
            })

    # Sort by peak time
    flat.sort(key=lambda p: p["peak_time"])

    # Cluster: walk through; if next peak is within gap_minutes of cluster's
    # latest peak, add it; otherwise start a new cluster.
    clusters = []
    current = []
    current_latest = None
    gap = dt.timedelta(minutes=gap_minutes)

    for p in flat:
        peak = dt.datetime.fromisoformat(p["peak_time"].rstrip("Z"))
        if not current:
            current = [p]
            current_latest = peak
        elif peak - current_latest <= gap:
            current.append(p)
            current_latest = peak
        else:
            if len({x["sat_id"] for x in current}) >= 2:
                clusters.append(current)
            current = [p]
            current_latest = peak

    if current and len({x["sat_id"] for x in current}) >= 2:
        clusters.append(current)

    return clusters


# ---------------------------------------------------------------------------
# HTML page (template — SAT_META_PLACEHOLDER is replaced server-side)
# ---------------------------------------------------------------------------

HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>GDACS Disaster Dashboard</title>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.css">
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet.heat/0.2.0/leaflet-heat.min.js"></script>
<style>
  :root {
    --bg: #fafaf7;
    --surface: #ffffff;
    --surface-2: #f3f1ea;
    --text: #1a1a1a;
    --text-muted: #6b6b66;
    --border: rgba(0,0,0,0.12);
    --border-strong: rgba(0,0,0,0.25);
    --red: #E24B4A;
    --orange: #EF9F27;
    --green: #639922;
    --blue: #378ADD;
    --purple: #534AB7;
    --amber: #BA7517;
    --dark-green: #3B6D11;
    --gray: #888780;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #1c1c1a;
      --surface: #262624;
      --surface-2: #2f2f2c;
      --text: #f0efe9;
      --text-muted: #9a988f;
      --border: rgba(255,255,255,0.12);
      --border-strong: rgba(255,255,255,0.25);
    }
  }
  * { box-sizing: border-box; margin: 0; padding: 0; }
  body {
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", system-ui, sans-serif;
    background: var(--bg);
    color: var(--text);
    padding: 24px;
    max-width: 1320px;
    margin: 0 auto;
  }
  .header { display: flex; align-items: center; justify-content: space-between; flex-wrap: wrap; gap: 12px; margin-bottom: 1.25rem; }
  .title { font-size: 22px; font-weight: 500; }
  .subtitle { font-size: 13px; color: var(--text-muted); margin-top: 2px; }
  .right { display: flex; gap: 10px; align-items: center; flex-wrap: wrap; }
  .last-updated { font-size: 12px; color: var(--text-muted); }
  .btn {
    background: var(--surface); border: 0.5px solid var(--border-strong);
    border-radius: 8px; padding: 8px 16px; font-size: 14px; font-weight: 500;
    color: var(--text); cursor: pointer; display: inline-flex; align-items: center; gap: 6px;
    transition: background 0.15s;
  }
  .btn:hover { background: var(--surface-2); }
  .btn:disabled { opacity: 0.5; cursor: not-allowed; }
  .spin { display: inline-block; animation: spin 0.8s linear infinite; }
  @keyframes spin { to { transform: rotate(360deg); } }

  .controls-bar {
    background: var(--surface); border: 0.5px solid var(--border);
    border-radius: 12px; padding: 14px 16px; margin-bottom: 1rem;
    display: flex; flex-wrap: wrap; gap: 20px; align-items: flex-start;
  }
  .control-group { display: flex; flex-direction: column; gap: 6px; }
  .control-label { font-size: 11px; color: var(--text-muted); text-transform: uppercase; letter-spacing: 0.5px; }
  .control-row { display: flex; gap: 6px; align-items: center; flex-wrap: wrap; }
  select, input[type="date"] {
    background: var(--bg); border: 0.5px solid var(--border-strong);
    border-radius: 6px; padding: 6px 10px; font-size: 13px;
    color: var(--text); font-family: inherit;
  }

  .metrics {
    display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
    gap: 12px; margin-bottom: 1rem;
  }
  .metric { background: var(--surface-2); border-radius: 8px; padding: 12px 16px; }
  .metric-label { font-size: 12px; color: var(--text-muted); margin-bottom: 4px; }
  .metric-val { font-size: 26px; font-weight: 500; }

  .filters { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; }
  .chip {
    border: 0.5px solid var(--border); border-radius: 999px; padding: 5px 12px;
    font-size: 12px; cursor: pointer; background: var(--surface); color: var(--text-muted);
    transition: all 0.12s; user-select: none;
    display: inline-flex; align-items: center; gap: 6px;
  }
  .chip svg { width: 14px; height: 14px; flex-shrink: 0; color: currentColor; }
  .chip.active { color: white; border-color: transparent; }
  .chip[data-type="EQ"].active { background: var(--red); }
  .chip[data-type="TC"].active { background: var(--purple); }
  .chip[data-type="FL"].active { background: var(--blue); }
  .chip[data-type="VO"].active { background: var(--amber); }
  .chip[data-type="WF"].active { background: var(--dark-green); }
  .chip[data-type="DR"].active { background: var(--gray); }
  .chip[data-type="TS"].active { background: #0E7C86; }

  .layout { display: grid; grid-template-columns: 2.2fr 1fr; gap: 16px; }
  @media (max-width: 1000px) { .layout { grid-template-columns: 1fr; } }

  .map-wrap {
    border: 0.5px solid var(--border); border-radius: 12px;
    overflow: hidden; position: relative; height: 600px;
  }
  #map { width: 100%; height: 100%; background: var(--surface-2); }
  .legend {
    position: absolute; bottom: 12px; left: 12px;
    background: var(--surface); border: 0.5px solid var(--border);
    border-radius: 8px; padding: 8px 12px; font-size: 11px; z-index: 999;
  }
  .legend-row { display: flex; align-items: center; gap: 6px; margin-bottom: 4px; color: var(--text-muted); }
  .legend-row:last-child { margin-bottom: 0; }
  .dot { width: 10px; height: 10px; border-radius: 50%; }

  .right-panel { display: flex; flex-direction: column; gap: 12px; height: 600px; }
  .panel { border: 0.5px solid var(--border); border-radius: 12px; padding: 16px; display: flex; flex-direction: column; }
  .panel-title { font-size: 14px; font-weight: 500; margin-bottom: 12px; }
  .events-panel { flex: 2; min-height: 0; }
  .sat-panel { flex: 1; min-height: 0; }
  .events { flex: 1; overflow-y: auto; display: flex; flex-direction: column; gap: 6px; padding-right: 4px; }
  .sat-list { flex: 1; overflow-y: auto; display: flex; flex-direction: column; gap: 2px; padding-right: 4px; }

  .event-card {
    background: var(--surface); border: 0.5px solid var(--border); border-radius: 8px;
    padding: 10px 12px; display: flex; align-items: flex-start; gap: 10px;
    cursor: pointer; transition: border-color 0.12s;
  }
  .event-card:hover { border-color: var(--border-strong); }
  .alert-dot { width: 8px; height: 8px; border-radius: 50%; flex-shrink: 0; margin-top: 5px; }
  .event-icon { width: 20px; height: 20px; flex-shrink: 0; }
  .event-name { font-size: 13px; font-weight: 500; }
  .event-meta { font-size: 12px; color: var(--text-muted); margin-top: 2px; }
  .event-badge {
    border-radius: 4px; padding: 2px 7px; font-size: 11px; font-weight: 500;
    color: white; flex-shrink: 0; margin-top: 1px;
  }
  .overpass-btn {
    background: transparent; border: 0.5px solid var(--border); border-radius: 4px;
    padding: 2px 7px; font-size: 13px; color: var(--text-muted);
    cursor: pointer; flex-shrink: 0; margin-top: 1px;
    transition: all 0.12s;
  }
  .overpass-btn:hover { background: var(--surface-2); color: var(--text); border-color: var(--border-strong); }

  /* Overpass-analysis modal */
  .modal-backdrop {
    position: fixed; inset: 0; background: rgba(0,0,0,0.45); z-index: 10000;
    display: flex; align-items: flex-start; justify-content: center;
    padding: 40px 20px; overflow-y: auto;
  }
  .modal {
    background: var(--bg); border-radius: 12px; max-width: 760px; width: 100%;
    border: 0.5px solid var(--border-strong); padding: 20px 24px;
    box-shadow: 0 20px 60px rgba(0,0,0,0.3);
  }
  .modal-header {
    display: flex; align-items: center; justify-content: space-between;
    margin-bottom: 16px; padding-bottom: 12px; border-bottom: 0.5px solid var(--border);
  }
  .modal-title { font-size: 18px; font-weight: 500; }
  .modal-sub { font-size: 12px; color: var(--text-muted); margin-top: 2px; }
  .modal-close {
    background: transparent; border: 0.5px solid var(--border-strong);
    border-radius: 6px; width: 28px; height: 28px; cursor: pointer; color: var(--text);
    font-size: 14px;
  }
  .modal-section { margin-bottom: 20px; }
  .modal-section h3 { font-size: 13px; font-weight: 500; color: var(--text-muted);
                      text-transform: uppercase; letter-spacing: 0.5px; margin-bottom: 10px; }
  .pass-row {
    display: grid; grid-template-columns: 1fr auto auto; gap: 12px;
    padding: 8px 10px; border-radius: 6px; font-size: 13px;
    border: 0.5px solid var(--border); background: var(--surface);
    margin-bottom: 4px;
  }
  .pass-sat { display: flex; align-items: center; gap: 8px; }
  .pass-bar { width: 12px; height: 12px; border-radius: 3px; flex-shrink: 0; }
  .pass-time { color: var(--text-muted); font-variant-numeric: tabular-nums; }
  .pass-dist { font-size: 11px; color: var(--text-muted); }
  .overlap-cluster {
    border: 0.5px solid var(--border-strong); border-radius: 8px; padding: 10px 12px;
    margin-bottom: 8px; background: var(--surface);
  }
  .cluster-time {
    font-size: 13px; font-weight: 500; margin-bottom: 6px; color: var(--text);
  }
  .cluster-span { font-size: 11px; color: var(--text-muted); margin-left: 6px; font-weight: 400; }
  .cluster-sats { display: flex; flex-wrap: wrap; gap: 6px; }
  .cluster-pill {
    font-size: 11px; padding: 3px 8px; border-radius: 999px;
    color: white; font-weight: 500;
  }
  .modal-loading { text-align: center; padding: 40px; color: var(--text-muted); }
  .empty-overlaps {
    text-align: center; padding: 16px; color: var(--text-muted); font-size: 13px;
    background: var(--surface-2); border-radius: 6px;
  }
  .filter-row {
    display: flex; align-items: center; gap: 12px; flex-wrap: wrap;
    background: var(--surface-2); padding: 12px 14px; border-radius: 8px;
  }
  .filter-label-lg { font-size: 13px; color: var(--text); flex-shrink: 0; }
  .filter-label-lg span { color: var(--text-muted); margin-left: 4px; font-variant-numeric: tabular-nums; }
  .filter-row input[type="range"] { flex: 1; min-width: 200px; accent-color: var(--blue); }
  .btn-small {
    background: var(--surface); border: 0.5px solid var(--border-strong); border-radius: 6px;
    padding: 4px 10px; font-size: 12px; cursor: pointer; color: var(--text);
  }
  .btn-small:hover { background: var(--surface-2); }
  .filter-meta {
    font-size: 12px; color: var(--text-muted); margin-top: 6px; padding: 0 4px;
  }
  .nisar-btn {
    display: block; margin-top: 4px; font-size: 11px; padding: 2px 6px;
    color: var(--purple); border-color: var(--purple);
  }
  .nisar-btn:hover { background: rgba(83,74,183,0.08); }
  .nisar-btn:disabled { opacity: 0.5; cursor: wait; }
  .nisar-result-banner {
    background: linear-gradient(90deg, rgba(83,74,183,0.12), rgba(83,74,183,0.04));
    border: 0.5px solid var(--purple); color: var(--text); padding: 10px 14px;
    border-radius: 8px; font-size: 13px; margin-bottom: 14px;
  }
  .nisar-result-banner a { color: var(--purple); text-decoration: underline; cursor: pointer; }

  /* Pill-style checkbox toggle */
  .toggle-pill {
    display: inline-flex; align-items: center; gap: 6px;
    border: 0.5px solid var(--border-strong); border-radius: 999px;
    padding: 4px 12px; font-size: 13px; cursor: pointer; user-select: none;
    background: var(--surface);
  }
  .toggle-pill input { cursor: pointer; }
  .toggle-pill:has(input:checked) { background: var(--surface-2); border-color: var(--text); }

  /* INFORM Risk choropleth legend (sits next to satellite legend on map) */
  .inform-legend {
    position: absolute; top: 12px; right: 12px; z-index: 999;
    background: var(--surface); border: 0.5px solid var(--border);
    border-radius: 8px; padding: 10px 12px; font-size: 11px;
    min-width: 140px;
  }
  .inform-legend-title { font-weight: 500; margin-bottom: 6px; font-size: 12px; }
  .inform-legend-sub { color: var(--text-muted); font-size: 10px; margin-bottom: 6px; }
  .inform-legend-row { display: flex; align-items: center; gap: 6px; margin-bottom: 3px; }
  .inform-swatch { width: 18px; height: 10px; border-radius: 2px; flex-shrink: 0; }

  /* ACLED legend — stacks below INFORM legend on the right */
  .acled-legend {
    position: absolute; top: 12px; left: 12px; z-index: 999;
    background: var(--surface); border: 0.5px solid var(--border);
    border-radius: 8px; padding: 10px 12px; font-size: 11px;
    min-width: 150px;
  }
  .acled-legend-title { font-weight: 500; margin-bottom: 4px; font-size: 12px; }
  .acled-legend-sub { color: var(--text-muted); font-size: 10px; margin-bottom: 6px; }
  .acled-legend-row { display: flex; align-items: center; gap: 6px; margin-bottom: 3px; }
  .acled-swatch { width: 12px; height: 12px; border-radius: 50%; flex-shrink: 0; }
  .acled-legend-mode { color: var(--text-muted); font-size: 10px; margin-top: 6px;
                       padding-top: 6px; border-top: 0.5px solid var(--border); }

  /* S2S Forecast legend (sits at bottom-left of map; doesn't conflict with ACLED top-left) */
  .fcst-legend {
    position: absolute; bottom: 12px; left: 12px; z-index: 999;
    background: var(--surface); border: 0.5px solid var(--border);
    border-radius: 8px; padding: 10px 12px; font-size: 11px;
    min-width: 200px;
  }
  .fcst-legend-title { font-weight: 500; margin-bottom: 2px; font-size: 12px; }
  .fcst-legend-sub { color: var(--text-muted); font-size: 10px; margin-bottom: 8px; }
  .fcst-legend-bar {
    height: 12px; border-radius: 2px; margin-bottom: 4px;
    background: linear-gradient(to right,
      rgb(211,47,47) 0%, rgb(255,255,255) 50%, rgb(33,102,172) 100%);
    border: 0.5px solid var(--border);
  }
  .fcst-legend-axis {
    display: flex; justify-content: space-between; font-size: 9px;
    color: var(--text-muted); line-height: 1.1;
  }
  .fcst-legend-axis span { text-align: center; }
  .fcst-legend-axis span:first-child { text-align: left; color: rgb(211,47,47); }
  .fcst-legend-axis span:last-child { text-align: right; color: rgb(33,102,172); }
  .fcst-legend-stats {
    margin-top: 8px; padding-top: 6px; border-top: 0.5px solid var(--border);
    font-size: 10px; color: var(--text-muted);
  }

  /* Conflict events section in modal */
  .conflict-section h3 { color: var(--coral, #c43a31); }
  .conflict-summary {
    display: flex; gap: 16px; margin-bottom: 10px; flex-wrap: wrap;
    font-size: 13px;
  }
  .conflict-summary-item { display: flex; flex-direction: column; }
  .conflict-summary-num { font-size: 18px; font-weight: 500; }
  .conflict-summary-lbl { font-size: 11px; color: var(--text-muted); }
  .conflict-event-row {
    background: var(--surface); border: 0.5px solid var(--border); border-radius: 8px;
    padding: 8px 12px; font-size: 12px; margin-bottom: 4px;
    display: grid; grid-template-columns: auto 1fr auto auto; gap: 10px; align-items: center;
  }
  .conflict-type-pill {
    display: inline-block; border-radius: 4px; padding: 1px 6px;
    font-size: 10px; font-weight: 500; color: white; white-space: nowrap;
  }
  .conflict-fatalities { font-weight: 500; color: #c43a31; }
  .conflict-meta { color: var(--text-muted); font-size: 11px; }
  .empty-conflict {
    text-align: center; padding: 14px; color: var(--text-muted); font-size: 13px;
    background: var(--surface-2); border-radius: 6px;
  }

  /* INFORM risk tooltip (when hovering/clicking a country) */
  .inform-country-popup { font-size: 13px; line-height: 1.5; min-width: 200px; }
  .inform-country-popup h4 { margin: 0 0 6px 0; font-size: 14px; }
  .inform-row { display: flex; justify-content: space-between; gap: 12px; }
  .inform-row span:first-child { color: var(--text-muted); }
  .inform-trend-up { color: #c43a31; }
  .inform-trend-down { color: #2d8a3e; }
  .inform-trend-flat { color: var(--text-muted); }

  .sat-row {
    display: flex; align-items: center; gap: 8px; padding: 6px 8px;
    border-radius: 6px; cursor: pointer; font-size: 13px;
    transition: background 0.12s;
  }
  .sat-row:hover { background: var(--surface-2); }
  .sat-row input[type="checkbox"] { cursor: pointer; }
  .sat-color { width: 14px; height: 3px; border-radius: 2px; flex-shrink: 0; }
  .sat-name { flex: 1; }
  .sat-time { font-size: 11px; color: var(--text-muted); }

  .empty { text-align: center; padding: 2rem; color: var(--text-muted); font-size: 13px; }
  .error { background: rgba(226,75,74,0.1); color: var(--red); padding: 12px; border-radius: 8px; font-size: 13px; }

  /* Custom map markers — SVG icons in a circular badge */
  .gdacs-marker {
    width: 30px; height: 30px; border-radius: 50%;
    display: flex; align-items: center; justify-content: center;
    box-shadow: 0 0 0 2px white, 0 1px 4px rgba(0,0,0,0.4);
    cursor: pointer;
  }
  .gdacs-marker svg { width: 18px; height: 18px; color: white; }
  .gdacs-marker.red { background: var(--red); }
  .gdacs-marker.orange { background: var(--orange); }
  .gdacs-marker.green { background: var(--green); }
</style>
</head>
<body>
  <div class="header">
    <div>
      <div class="title">GDACS Disaster Dashboard</div>
      <div class="subtitle">Live events from the Global Disaster Alert and Coordination System</div>
    </div>
    <div class="right">
      <span class="last-updated" id="last-updated"></span>
      <button class="btn" id="fetch-btn" onclick="fetchData()">
        <span id="btn-icon">⟳</span> <span>Refresh</span>
      </button>
    </div>
  </div>

  <!-- Inline SVG icon symbols, referenced by <use> below.
       We use stroke + fill = "currentColor" so the icon picks up text color. -->
  <svg width="0" height="0" style="position:absolute;">
    <defs>
      <!-- Earthquake: epicenter + concentric arcs -->
      <symbol id="icon-EQ" viewBox="0 0 24 24">
        <circle cx="12" cy="14" r="1.8" fill="currentColor"/>
        <path d="M7.5 14 a4.5 4.5 0 0 1 9 0 M4 14 a8 8 0 0 1 16 0"
              fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>
      </symbol>
      <!-- Cyclone: spiral -->
      <symbol id="icon-TC" viewBox="0 0 24 24">
        <path d="M12 4 a8 8 0 1 1 -7.5 5.5 M12 8 a4 4 0 1 1 -3.5 6"
              fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>
        <circle cx="12" cy="12" r="1.6" fill="currentColor"/>
      </symbol>
      <!-- Flood: stacked waves -->
      <symbol id="icon-FL" viewBox="0 0 24 24">
        <path d="M2 9 q3 -3 6 0 t6 0 t6 0 M2 14 q3 -3 6 0 t6 0 t6 0 M2 19 q3 -3 6 0 t6 0 t6 0"
              fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>
      </symbol>
      <!-- Volcano: triangle with rising plume -->
      <symbol id="icon-VO" viewBox="0 0 24 24">
        <path d="M3 20 L9 9 L12 13 L15 9 L21 20 Z" fill="currentColor"/>
        <path d="M12 5 q1.6 1 0 2.5 t0 2.5" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"/>
      </symbol>
      <!-- Wildfire: flame -->
      <symbol id="icon-WF" viewBox="0 0 24 24">
        <path d="M12 22 c-4.5 0 -7.5 -3 -7.5 -7.5 c0 -3 2 -4.5 3.5 -6 c0 2.5 1.5 3.5 2.5 3.5 c-1 -3.5 1 -6 4 -9 c0 4 4.5 5.5 4.5 11 c0 4.5 -2.5 8 -7 8 z"
              fill="currentColor"/>
      </symbol>
      <!-- Drought: sun + cracked ground -->
      <symbol id="icon-DR" viewBox="0 0 24 24">
        <circle cx="12" cy="9" r="3.2" fill="currentColor"/>
        <path d="M12 3 v2 M12 13 v1.5 M5 9 h2 M17 9 h2 M7.2 4.2 L8.5 5.5 M15.5 12.5 L16.8 13.8 M7.2 13.8 L8.5 12.5 M15.5 5.5 L16.8 4.2"
              stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/>
        <path d="M3 20 L8 18 L12 21 L16 18 L21 20"
              fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/>
      </symbol>
      <!-- Tsunami: single curling wave crest over a shoreline -->
      <symbol id="icon-TS" viewBox="0 0 24 24">
        <path d="M2 15 C4 9, 8 9, 9 13 C10 17, 13 17, 14 12 C15 7, 19 5, 22 9"
              fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
        <path d="M2 20 H22" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>
      </symbol>
    </defs>
  </svg>

  <div class="controls-bar">
    <div class="control-group">
      <span class="control-label">Date range</span>
      <div class="control-row">
        <select id="date-range" onchange="onDateRangeChange()">
          <option value="1">Last 24 hours</option>
          <option value="3">Last 3 days</option>
          <option value="7" selected>Last 7 days</option>
          <option value="30">Last 30 days</option>
          <option value="90">Last 90 days</option>
          <option value="custom">Custom…</option>
        </select>
        <input type="date" id="date-from" style="display:none;" onchange="fetchData()">
        <input type="date" id="date-to" style="display:none;" onchange="fetchData()">
      </div>
    </div>

    <div class="control-group" style="flex:1; min-width: 280px;">
      <span class="control-label">Disaster types</span>
      <div class="filters">
        <div class="chip active" data-type="EQ" onclick="toggleFilter('EQ',this)"><svg><use href="#icon-EQ"/></svg>Earthquakes</div>
        <div class="chip active" data-type="TC" onclick="toggleFilter('TC',this)"><svg><use href="#icon-TC"/></svg>Cyclones</div>
        <div class="chip active" data-type="FL" onclick="toggleFilter('FL',this)"><svg><use href="#icon-FL"/></svg>Floods</div>
        <div class="chip active" data-type="VO" onclick="toggleFilter('VO',this)"><svg><use href="#icon-VO"/></svg>Volcanoes</div>
        <div class="chip active" data-type="WF" onclick="toggleFilter('WF',this)"><svg><use href="#icon-WF"/></svg>Wildfires</div>
        <div class="chip active" data-type="DR" onclick="toggleFilter('DR',this)"><svg><use href="#icon-DR"/></svg>Droughts</div>
        <div class="chip active" data-type="TS" onclick="toggleFilter('TS',this)"><svg><use href="#icon-TS"/></svg>Tsunamis</div>
      </div>
    </div>

    <div class="control-group">
      <span class="control-label">Context layers</span>
      <div class="control-row">
        <label class="toggle-pill">
          <input type="checkbox" id="inform-toggle" onchange="toggleInformLayer(this.checked)">
          <span>INFORM Risk</span>
        </label>
        <label class="toggle-pill">
          <input type="checkbox" id="acled-toggle" onchange="toggleAcledLayer(this.checked)">
          <span>ACLED Conflict</span>
        </label>
        <label class="toggle-pill">
          <input type="checkbox" id="fcst-toggle" onchange="toggleForecastLayer(this.checked)">
          <span>S2S Forecast</span>
        </label>
      </div>
      <div class="control-row" id="fcst-picker" style="display:none;margin-top:6px;">
        <select id="fcst-ic" onchange="onForecastSelectionChange()" style="font-size:12px;"></select>
        <select id="fcst-variable" onchange="onForecastSelectionChange()" style="font-size:12px;"></select>
        <select id="fcst-leadtype" onchange="onForecastSelectionChange()" style="font-size:12px;"></select>
        <select id="fcst-lead" onchange="onForecastSelectionChange()" style="font-size:12px;min-width:180px;"></select>
        <select id="fcst-sigma" onchange="onForecastSelectionChange()" style="font-size:12px;" title="Color scale clip (standard deviations)">
          <option value="0.25">±0.25σ</option>
          <option value="0.5">±0.5σ</option>
          <option value="0.75">±0.75σ</option>
          <option value="1">±1σ</option>
          <option value="1.25">±1.25σ</option>
          <option value="1.5">±1.5σ</option>
          <option value="1.75">±1.75σ</option>
          <option value="2" selected>±2σ</option>
          <option value="2.5">±2.5σ</option>
          <option value="3">±3σ</option>
          <option value="4">±4σ</option>
        </select>
        <button id="fcst-anim-btn" class="btn-small" onclick="toggleFcstAnimation()" style="font-size:12px;" title="Animate through all available dates for this variable">▶ Animate</button>
        <select id="fcst-anim-speed" style="font-size:12px;" title="Animation speed">
          <option value="1500">Slow</option>
          <option value="800" selected>Normal</option>
          <option value="400">Fast</option>
        </select>
        <span id="fcst-anim-label" style="font-size:11px;color:var(--text-muted);min-width:100px;"></span>
      </div>
    </div>
  </div>

  <div class="metrics">
    <div class="metric"><div class="metric-label">Total events</div><div class="metric-val" id="m-total">—</div></div>
    <div class="metric"><div class="metric-label">Red alerts</div><div class="metric-val" id="m-red" style="color:var(--red);">—</div></div>
    <div class="metric"><div class="metric-label">Orange alerts</div><div class="metric-val" id="m-orange" style="color:var(--orange);">—</div></div>
    <div class="metric"><div class="metric-label">Green alerts</div><div class="metric-val" id="m-green" style="color:var(--green);">—</div></div>
  </div>

  <div class="layout">
    <div class="map-wrap">
      <div id="map"></div>
      <div class="legend">
        <div class="legend-row"><div class="dot" style="background:var(--red);"></div> Red alert</div>
        <div class="legend-row"><div class="dot" style="background:var(--orange);"></div> Orange alert</div>
        <div class="legend-row"><div class="dot" style="background:var(--green);"></div> Green alert</div>
      </div>
    </div>
    <div class="right-panel">
      <div class="panel events-panel">
        <div class="panel-title" id="list-title">Events</div>
        <div class="events" id="events-container"><div class="empty">Loading…</div></div>
      </div>
      <div class="panel sat-panel">
        <div class="panel-title">Satellite tracks (next 24h)</div>
        <div class="sat-list" id="sat-list"></div>
      </div>
    </div>
  </div>

<script>
const TYPE_COLORS = { EQ:'#E24B4A', TC:'#534AB7', FL:'#378ADD', VO:'#BA7517', WF:'#3B6D11', DR:'#888780', TS:'#0E7C86' };
const TYPE_NAMES = { EQ:'Earthquake', TC:'Cyclone', FL:'Flood', VO:'Volcano', WF:'Wildfire', DR:'Drought', TS:'Tsunami' };
const ALERT_COLORS = { Red:'#E24B4A', Orange:'#EF9F27', Green:'#639922' };

let allEvents = [];
let activeFilters = new Set(['EQ','TC','FL','VO','WF','DR','TS']);
let activeSatellites = new Set();
let satTracks = {};   // id -> { name, points, polylines: [Leaflet polyline...] }
const satMeta = SAT_META_PLACEHOLDER;

const map = L.map('map', { zoomControl: true, worldCopyJump: true }).setView([20, 0], 2);
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
  attribution: '© OpenStreetMap',
  maxZoom: 18
}).addTo(map);

// Custom panes so layer stacking is explicit:
//   400 = overlayPane (default vector default)
//   acledPane (350)   = ACLED conflict — UNDER markers
//   markerPane (600)  = GDACS markers (default for L.marker)
//   informPane (300)  = INFORM choropleth — UNDER everything (default basemap is 200)
map.createPane('informPane');
map.getPane('informPane').style.zIndex = 300;
map.createPane('acledPane');
map.getPane('acledPane').style.zIndex = 350;
map.createPane('acledHeatPane');
map.getPane('acledHeatPane').style.zIndex = 355;

const markerLayer = L.layerGroup().addTo(map);
const trackLayer = L.layerGroup().addTo(map);

function buildSatList() {
  const container = document.getElementById('sat-list');
  container.innerHTML = '';
  Object.entries(satMeta).forEach(([id, info]) => {
    const row = document.createElement('label');
    row.className = 'sat-row';
    row.innerHTML = `
      <input type="checkbox" data-sat="${id}" onchange="toggleSat('${id}', this.checked)">
      <div class="sat-color" style="background:${info.color};"></div>
      <span class="sat-name">${info.name}</span>
      <span class="sat-time">${info.swath_km} km · ${info.instr}</span>
    `;
    container.appendChild(row);
  });
}

function onDateRangeChange() {
  const v = document.getElementById('date-range').value;
  const fromEl = document.getElementById('date-from');
  const toEl = document.getElementById('date-to');
  if (v === 'custom') {
    fromEl.style.display = '';
    toEl.style.display = '';
    if (!fromEl.value || !toEl.value) return;  // wait until both are set
  } else {
    fromEl.style.display = 'none';
    toEl.style.display = 'none';
  }
  fetchData();
}

function getDateParams() {
  const v = document.getElementById('date-range').value;
  const today = new Date();
  const fmt = d => d.toISOString().slice(0, 10);
  if (v === 'custom') {
    return {
      from: document.getElementById('date-from').value || null,
      to:   document.getElementById('date-to').value   || null,
    };
  }
  const days = parseInt(v, 10);
  const from = new Date(today.getTime() - days * 24 * 60 * 60 * 1000);
  return { from: fmt(from), to: fmt(today) };
}

function toggleFilter(type, el) {
  if (activeFilters.has(type)) { activeFilters.delete(type); el.classList.remove('active'); }
  else { activeFilters.add(type); el.classList.add('active'); }
  renderEvents();
}

async function fetchData() {
  const btn = document.getElementById('fetch-btn');
  const icon = document.getElementById('btn-icon');
  btn.disabled = true;
  icon.innerHTML = '<span class="spin">⟳</span>';

  // Invalidate the ACLED layer cache — date range may have changed
  invalidateAcledData();

  try {
    const { from, to } = getDateParams();
    const qs = new URLSearchParams();
    if (from) qs.set('from', from);
    if (to)   qs.set('to', to);
    const resp = await fetch('/api/gdacs?' + qs.toString(), { cache: 'no-store' });
    if (!resp.ok) throw new Error('Server returned ' + resp.status);
    const data = await resp.json();
    allEvents = (data.features || []).map(f => {
      const p = f.properties || {};
      const coords = f.geometry && f.geometry.coordinates;
      return {
        id: p.eventid,
        name: p.name || p.eventname || 'Unknown event',
        type: p.eventtype || '?',
        alert: p.alertlevel || 'Green',
        country: p.country || '',
        date: p.fromdate ? p.fromdate.split('T')[0] : '',
        lat: coords ? coords[1] : null,
        lon: coords ? coords[0] : null,
        url: (p.url && p.url.report) ? p.url.report : null
      };
    });
    updateMetrics();
    renderEvents();
    document.getElementById('last-updated').textContent =
      'Updated ' + new Date().toLocaleTimeString();
  } catch (e) {
    document.getElementById('events-container').innerHTML =
      '<div class="error">Could not load data: ' + e.message + '</div>';
  }

  btn.disabled = false;
  icon.textContent = '⟳';
}

function updateMetrics() {
  document.getElementById('m-total').textContent = allEvents.length;
  document.getElementById('m-red').textContent = allEvents.filter(e=>e.alert==='Red').length;
  document.getElementById('m-orange').textContent = allEvents.filter(e=>e.alert==='Orange').length;
  document.getElementById('m-green').textContent = allEvents.filter(e=>e.alert==='Green').length;
}

function makeMarkerIcon(type, alert) {
  const cls = (alert || 'Green').toLowerCase();
  const html = `<div class="gdacs-marker ${cls}"><svg><use href="#icon-${type}"/></svg></div>`;
  return L.divIcon({ html, className: '', iconSize: [30, 30], iconAnchor: [15, 15] });
}

function renderEvents() {
  const filtered = allEvents.filter(e => activeFilters.has(e.type));
  document.getElementById('list-title').textContent = 'Events (' + filtered.length + ' shown)';

  markerLayer.clearLayers();
  filtered.forEach(e => {
    if (e.lat != null && e.lon != null) {
      const marker = L.marker([e.lat, e.lon], { icon: makeMarkerIcon(e.type, e.alert) });
      const linkHTML = e.url ? '<br><a href="' + e.url + '" target="_blank">View report</a>' : '';
      marker.bindPopup('<b>' + e.name + '</b><br>' +
        (TYPE_NAMES[e.type] || e.type) + ' · ' + e.alert + ' alert<br>' +
        e.country + '<br>' + e.date + linkHTML);
      marker.addTo(markerLayer);
    }
  });

  const container = document.getElementById('events-container');
  if (!filtered.length) {
    container.innerHTML = '<div class="empty">No events match current filters.</div>';
    return;
  }

  const order = {Red:0, Orange:1, Green:2};
  const sorted = [...filtered].sort((a,b) => (order[a.alert]||2) - (order[b.alert]||2));

  container.innerHTML = sorted.map(e => {
    const typeColor = TYPE_COLORS[e.type] || '#888';
    const alertColor = ALERT_COLORS[e.alert] || '#639922';
    return '<div class="event-card">' +
      '<div class="alert-dot" style="background:' + alertColor + ';"></div>' +
      '<svg class="event-icon" style="color:' + typeColor + ';"><use href="#icon-' + e.type + '"/></svg>' +
      '<div style="flex:1;min-width:0;cursor:pointer;" onclick="zoomTo(' + e.lat + ',' + e.lon + ')">' +
        '<div class="event-name">' + escapeHtml(e.name) + '</div>' +
        '<div class="event-meta">' + (e.country ? escapeHtml(e.country) + ' · ' : '') + e.date + '</div>' +
      '</div>' +
      '<button class="overpass-btn" title="Find satellite overpasses for this event" ' +
        'onclick="runOverpassAnalysis(' + e.lat + ',' + e.lon + ',\'' +
        escapeHtml(e.name).replace(/\'/g,"\\'") + '\')">↗</button>' +
      '<div class="event-badge" style="background:' + typeColor + ';">' + (TYPE_NAMES[e.type]||e.type) + '</div>' +
    '</div>';
  }).join('');
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}

function zoomTo(lat, lon) {
  if (lat && lon) map.flyTo([lat, lon], 5, { duration: 1.2 });
}

// ---------- Overpass analysis ----------

// Module-level state for the active overpass analysis
let overpassData = null;          // raw API response
let overpassEvent = null;         // {name, lat, lon}
let overpassMaxDistKm = null;     // null = no filter
let overpassLayer = L.layerGroup().addTo(map);  // map overlay for pass swaths
let nisarLayer = L.layerGroup().addTo(map);     // map overlay for NISAR soil moisture imagery
let nisarOverlays = [];                          // [{imageOverlay, marker, info}]

// INFORM Risk choropleth state
let informData = null;         // {current, previous, trends, current_label, previous_label}
let informLayer = null;        // L.geoJSON layer
let informLegend = null;       // legend DOM element

function informColor(score) {
  // Color scale matching INFORM Risk class breaks: Low/Medium/High/Very High
  if (score == null) return '#bbb';
  if (score >= 6.5) return '#7a0c1f';   // Very High
  if (score >= 5.0) return '#c43a31';   // High
  if (score >= 3.5) return '#e89e3c';   // Medium
  return '#f4d57a';                       // Low
}

function informClassLabel(score) {
  if (score == null) return 'No data';
  if (score >= 6.5) return 'Very High';
  if (score >= 5.0) return 'High';
  if (score >= 3.5) return 'Medium';
  return 'Low';
}

function trendArrow(direction, delta) {
  if (!direction || direction === 'flat') return '<span class="inform-trend-flat">→ no change</span>';
  if (direction === 'up') return '<span class="inform-trend-up">↑ +' + delta.toFixed(2) + '</span>';
  return '<span class="inform-trend-down">↓ ' + delta.toFixed(2) + '</span>';
}

async function toggleInformLayer(on) {
  if (on) {
    if (!informLayer) {
      try {
        // Fetch both INFORM scores and country geometries in parallel
        const [iResp, gResp] = await Promise.all([
          fetch('/api/inform_data'),
          fetch('/api/countries_geojson'),
        ]);
        const iData = await iResp.json();
        if (iData.error) { alert('INFORM load failed: ' + iData.error); return; }
        const geojson = await gResp.json();
        informData = iData;

        informLayer = L.geoJSON(geojson, {
          pane: 'informPane',
          style: (feature) => {
            const iso3 = (feature.properties.ISO_A3 || feature.properties.ADM0_A3 || '').toUpperCase();
            const score = (iData.current[iso3] || {}).score;
            return {
              fillColor: informColor(score),
              fillOpacity: score == null ? 0.15 : 0.55,
              color: 'rgba(0,0,0,0.4)',
              weight: 0.5,
            };
          },
          onEachFeature: (feature, layer) => {
            const iso3 = (feature.properties.ISO_A3 || feature.properties.ADM0_A3 || '').toUpperCase();
            const name = feature.properties.NAME || feature.properties.ADMIN || iso3;
            const cur = iData.current[iso3];
            const prev = iData.previous[iso3];
            const trend = iData.trends[iso3];

            if (cur) {
              const popup = `
                <div class="inform-country-popup">
                  <h4>${escapeHtml(name)} <span style="color:${informColor(cur.score)};">●</span></h4>
                  <div class="inform-row"><span>INFORM Risk (${iData.current_label})</span><span><b>${cur.score.toFixed(2)}</b> · ${informClassLabel(cur.score)}</span></div>
                  ${prev ? '<div class="inform-row"><span>Previous (' + iData.previous_label + ')</span><span>' + prev.score.toFixed(2) + '</span></div>' : ''}
                  ${trend ? '<div class="inform-row"><span>Trend</span><span>' + trendArrow(trend.direction, trend.delta) + '</span></div>' : ''}
                  <hr style="border:none;border-top:1px solid var(--border);margin:6px 0;">
                  ${cur.hazard != null ? '<div class="inform-row"><span>Hazard &amp; Exposure</span><span>' + cur.hazard.toFixed(1) + '</span></div>' : ''}
                  ${cur.vulnerability != null ? '<div class="inform-row"><span>Vulnerability</span><span>' + cur.vulnerability.toFixed(1) + '</span></div>' : ''}
                  ${cur.coping != null ? '<div class="inform-row"><span>Lack of Coping</span><span>' + cur.coping.toFixed(1) + '</span></div>' : ''}
                </div>
              `;
              layer.bindPopup(popup);
            } else {
              layer.bindPopup('<b>' + escapeHtml(name) + '</b><br><span style="color:var(--text-muted)">No INFORM data</span>');
            }
          },
        });
      } catch (e) {
        alert('Failed to load INFORM choropleth: ' + e.message);
        document.getElementById('inform-toggle').checked = false;
        return;
      }
    }
    informLayer.addTo(map);
    if (informLayer.bringToBack) informLayer.bringToBack();

    // Show legend
    if (!informLegend) {
      informLegend = document.createElement('div');
      informLegend.className = 'inform-legend';
      informLegend.innerHTML = `
        <div class="inform-legend-title">INFORM Risk</div>
        <div class="inform-legend-sub">${informData.current_label}</div>
        <div class="inform-legend-row"><div class="inform-swatch" style="background:#7a0c1f;"></div>Very High (≥6.5)</div>
        <div class="inform-legend-row"><div class="inform-swatch" style="background:#c43a31;"></div>High (5.0–6.5)</div>
        <div class="inform-legend-row"><div class="inform-swatch" style="background:#e89e3c;"></div>Medium (3.5–5.0)</div>
        <div class="inform-legend-row"><div class="inform-swatch" style="background:#f4d57a;"></div>Low (≤3.5)</div>
        <div class="inform-legend-row"><div class="inform-swatch" style="background:#bbb;"></div>No data</div>
      `;
      document.querySelector('.map-wrap').appendChild(informLegend);
    } else {
      informLegend.style.display = '';
    }
  } else {
    if (informLayer) map.removeLayer(informLayer);
    if (informLegend) informLegend.style.display = 'none';
  }
}

// ----- ACLED global layer (heatmap at low zoom, pins at high zoom) -----

const ACLED_TYPE_COLORS = {
  'Battles': '#7a0c1f',
  'Explosions/Remote violence': '#c43a31',
  'Violence against civilians': '#d95a4c',
  'Riots': '#e89e3c',
  'Protests': '#3a7ec2',
  'Strategic developments': '#888780',
};
const ACLED_HEAT_TO_PINS_ZOOM = 6;  // switch threshold

let acledData = null;       // {events: [...], count, days_back, start, end}
let acledHeatLayer = null;  // L.heatLayer
let acledPinsLayer = null;  // L.layerGroup with circleMarkers (canvas-rendered)
let acledLegend = null;
let acledOn = false;

function acledMarkerRadius(fatalities) {
  // Square-root scale, capped — keeps single huge incidents from dominating
  if (!fatalities || fatalities <= 0) return 3;
  return Math.min(3 + Math.sqrt(fatalities) * 1.4, 14);
}

async function toggleAcledLayer(on) {
  acledOn = on;
  if (on) {
    // Need data for current date range
    if (!acledData) {
      try {
        const days = getDaysBackForAcled();
        const btnLabel = document.querySelector('label.toggle-pill:has(#acled-toggle) span');
        if (btnLabel) btnLabel.textContent = 'ACLED Conflict (loading…)';
        const resp = await fetch('/api/acled_global?days_back=' + days);
        const data = await resp.json();
        if (data.error) {
          alert('ACLED layer failed: ' + data.error);
          document.getElementById('acled-toggle').checked = false;
          acledOn = false;
          if (btnLabel) btnLabel.textContent = 'ACLED Conflict';
          return;
        }
        acledData = data;
        if (btnLabel) btnLabel.textContent = `ACLED Conflict (${data.count.toLocaleString()})`;
      } catch (e) {
        alert('ACLED layer failed: ' + e.message);
        document.getElementById('acled-toggle').checked = false;
        acledOn = false;
        return;
      }
    }
    renderAcledLayer();
    showAcledLegend();
  } else {
    hideAcledLayer();
    hideAcledLegend();
    const btnLabel = document.querySelector('label.toggle-pill:has(#acled-toggle) span');
    if (btnLabel) btnLabel.textContent = 'ACLED Conflict';
  }
}

function getDaysBackForAcled() {
  const v = document.getElementById('date-range').value;
  if (v === 'custom') {
    const from = document.getElementById('date-from').value;
    const to = document.getElementById('date-to').value;
    if (from && to) {
      const ms = new Date(to) - new Date(from);
      return Math.max(1, Math.min(90, Math.round(ms / 86400000)));
    }
    return 7;
  }
  return Math.max(1, Math.min(90, parseInt(v, 10) || 7));
}

function renderAcledLayer() {
  hideAcledLayer();
  if (!acledData || !acledData.events.length) return;

  const z = map.getZoom();
  if (z < ACLED_HEAT_TO_PINS_ZOOM) {
    // Heatmap: weight by sqrt(fatalities + 1) so deadly incidents pop
    const points = acledData.events.map(e => [e.lat, e.lon, Math.sqrt((e.f || 0) + 1)]);
    acledHeatLayer = L.heatLayer(points, {
      radius: 18,
      blur: 22,
      maxZoom: ACLED_HEAT_TO_PINS_ZOOM,
      minOpacity: 0.35,
      pane: 'acledHeatPane',
      gradient: {
        0.0: '#3a7ec2', 0.3: '#e89e3c', 0.6: '#c43a31', 1.0: '#7a0c1f',
      },
    }).addTo(map);
  } else {
    // Pins: canvas-rendered circleMarkers
    const renderer = L.canvas({ padding: 0.5, pane: 'acledPane' });
    acledPinsLayer = L.layerGroup();
    // Only show events in current viewport bounds to keep things fast
    const bounds = map.getBounds().pad(0.2);
    let shown = 0;
    for (const e of acledData.events) {
      if (!bounds.contains([e.lat, e.lon])) continue;
      const color = ACLED_TYPE_COLORS[e.t] || '#888780';
      const r = acledMarkerRadius(e.f);
      const m = L.circleMarker([e.lat, e.lon], {
        renderer, radius: r, pane: 'acledPane',
        color: 'rgba(255,255,255,0.7)', weight: 1,
        fillColor: color, fillOpacity: 0.85,
      });
      m.bindPopup(() => {
        const fatHTML = e.f > 0
          ? '<span style="color:#c43a31;font-weight:500;">' + e.f + ' killed</span><br>'
          : '';
        return `<div style="font-size:13px;line-height:1.5;">
          <b>${escapeHtml(e.s || e.t)}</b><br>
          ${fatHTML}
          ${escapeHtml(e.l || e.c)} · ${e.d}
        </div>`;
      });
      m.addTo(acledPinsLayer);
      shown++;
      if (shown > 8000) break;  // hard cap for safety
    }
    acledPinsLayer.addTo(map);
  }
}

function hideAcledLayer() {
  if (acledHeatLayer) { map.removeLayer(acledHeatLayer); acledHeatLayer = null; }
  if (acledPinsLayer) { map.removeLayer(acledPinsLayer); acledPinsLayer = null; }
}

function showAcledLegend() {
  if (acledLegend) { acledLegend.style.display = ''; return; }
  acledLegend = document.createElement('div');
  acledLegend.className = 'acled-legend';
  acledLegend.innerHTML = `
    <div class="acled-legend-title">ACLED Conflict Events</div>
    <div class="acled-legend-sub" id="acled-legend-sub">${acledData ? acledData.count.toLocaleString() + ' events · last ' + acledData.days_back + ' days' : ''}</div>
    <div class="acled-legend-row"><div class="acled-swatch" style="background:#7a0c1f;"></div>Battles</div>
    <div class="acled-legend-row"><div class="acled-swatch" style="background:#c43a31;"></div>Explosions/Remote</div>
    <div class="acled-legend-row"><div class="acled-swatch" style="background:#d95a4c;"></div>Civilian violence</div>
    <div class="acled-legend-row"><div class="acled-swatch" style="background:#e89e3c;"></div>Riots</div>
    <div class="acled-legend-row"><div class="acled-swatch" style="background:#3a7ec2;"></div>Protests</div>
    <div class="acled-legend-row"><div class="acled-swatch" style="background:#888780;"></div>Strategic</div>
    <div class="acled-legend-mode" id="acled-mode-readout"></div>
  `;
  document.querySelector('.map-wrap').appendChild(acledLegend);
  updateAcledModeReadout();
}

function hideAcledLegend() {
  if (acledLegend) acledLegend.style.display = 'none';
}

function updateAcledModeReadout() {
  const el = document.getElementById('acled-mode-readout');
  if (!el) return;
  const z = map.getZoom();
  if (z < ACLED_HEAT_TO_PINS_ZOOM) {
    el.textContent = `Heatmap mode · zoom in (${ACLED_HEAT_TO_PINS_ZOOM}+) for pins`;
  } else {
    el.textContent = `Pin mode · zoom out for heatmap`;
  }
}

// Re-render on zoom (heat ↔ pins) and on pan when in pin mode
map.on('zoomend', () => {
  if (!acledOn) return;
  renderAcledLayer();
  updateAcledModeReadout();
});
map.on('moveend', () => {
  if (!acledOn) return;
  if (map.getZoom() >= ACLED_HEAT_TO_PINS_ZOOM) {
    renderAcledLayer();  // pins are viewport-bounded, so refresh
  }
});

// Invalidate when user changes the date range — refetch on next toggle-on
function invalidateAcledData() {
  acledData = null;
  if (acledOn) {
    // Re-fetch immediately for the new range
    document.getElementById('acled-toggle').checked = false;
    acledOn = false;
    hideAcledLayer();
    hideAcledLegend();
    // Re-tick to trigger reload
    setTimeout(() => {
      document.getElementById('acled-toggle').checked = true;
      toggleAcledLayer(true);
    }, 100);
  }
}

// ----- S2S Forecast Layer (LIS-S2S Standardized Anomalies from FCST/) -----
let forecastCatalog = null;          // {ics: [...], count}
let forecastOverlay = null;          // L.imageOverlay
let forecastLegend = null;           // DOM element
let forecastCurrentMeta = null;      // result from /api/forecasts/render
let fcstAnimTimer = null;            // setTimeout handle for the animation loop
let fcstAnimPlaying = false;         // whether the animation is currently running

const FCST_VAR_LABELS = {
  RZSM: 'Root Zone Soil Moisture',
  SFMC: 'Surface Soil Moisture',
  TWS:  'Terrestrial Water Storage',
};

function fcstLeadTypeLabel(t) {
  return { weekly: 'Weekly', monthly: 'Monthly', other: 'Sub-monthly' }[t] || t;
}

async function loadForecastCatalog() {
  if (forecastCatalog) return forecastCatalog;
  try {
    const resp = await fetch('/api/forecasts/list');
    forecastCatalog = await resp.json();
    return forecastCatalog;
  } catch (e) {
    alert('Could not load forecast catalog: ' + e.message);
    return null;
  }
}

function populateForecastPickers() {
  if (!forecastCatalog || !forecastCatalog.exists) return;

  const icSel = document.getElementById('fcst-ic');
  const varSel = document.getElementById('fcst-variable');
  const ltSel = document.getElementById('fcst-leadtype');
  const leadSel = document.getElementById('fcst-lead');

  // Capture what's currently selected BEFORE rebuilding the <option> lists.
  // Rebuilding innerHTML resets a <select> to its first option unless we
  // explicitly restore the previous value afterward — without this, any
  // rebuild (triggered by ANY of the four pickers changing) silently
  // discards whatever the user just picked and snaps back to the default.
  const prevIc = icSel.value;
  const prevVar = varSel.value;
  const prevLt = ltSel.value;
  const prevLead = leadSel.value;

  // Initialization dates
  icSel.innerHTML = forecastCatalog.ics.map(i =>
    '<option value="' + i.ic + '">IC ' + i.ic + '</option>'
  ).join('');
  icSel.value = forecastCatalog.ics.some(i => i.ic === prevIc)
    ? prevIc
    : (forecastCatalog.ics[0] ? forecastCatalog.ics[0].ic : '');

  // Variables for selected IC
  const ic = forecastCatalog.ics.find(i => i.ic === icSel.value) || forecastCatalog.ics[0];
  if (!ic) return;
  const vars = Object.keys(ic.variables);
  varSel.innerHTML = vars.map(v =>
    '<option value="' + v + '">' + (FCST_VAR_LABELS[v] || v) + '</option>'
  ).join('');
  varSel.value = vars.includes(prevVar) ? prevVar : vars[0];

  // Lead types available for the chosen variable
  const varData = ic.variables[varSel.value];
  const ltOptions = [];
  for (const lt of ['weekly', 'monthly', 'other']) {
    if (varData[lt] && varData[lt].length) ltOptions.push(lt);
  }
  ltSel.innerHTML = ltOptions.map(lt =>
    '<option value="' + lt + '">' + fcstLeadTypeLabel(lt) + ' (' + varData[lt].length + ')</option>'
  ).join('');
  ltSel.value = ltOptions.includes(prevLt) ? prevLt : ltOptions[0];

  // Specific lead periods for chosen lead type
  const leads = varData[ltSel.value] || [];
  leadSel.innerHTML = leads.map(l =>
    '<option value="' + l.filename + '">' + l.fp_start + ' → ' + l.fp_end +
    ' (' + l.lead_days + 'd)</option>'
  ).join('');
  const leadFilenames = leads.map(l => l.filename);
  leadSel.value = leadFilenames.includes(prevLead) ? prevLead : (leadFilenames[0] || '');
}

async function renderSelectedForecast() {
  const leadSel = document.getElementById('fcst-lead');
  const filename = leadSel.value;
  if (!filename) return;

  const sigma = document.getElementById('fcst-sigma').value || '2';

  // Loading state
  const label = document.querySelector('#fcst-toggle').parentElement;
  if (label) label.style.opacity = '0.5';

  try {
    const url = '/api/forecasts/render?filename=' + encodeURIComponent(filename) +
                '&sigma_clip=' + encodeURIComponent(sigma);
    const resp = await fetch(url);
    const data = await resp.json();
    if (data.error) {
      alert('Forecast render failed: ' + data.error);
      if (label) label.style.opacity = '';
      return;
    }
    forecastCurrentMeta = data;

    // Replace existing overlay if any
    if (forecastOverlay) map.removeLayer(forecastOverlay);
    forecastOverlay = L.imageOverlay(data.png_url, data.bounds, { opacity: 0.7 });
    forecastOverlay.addTo(map);

    // Try to keep it underneath GDACS markers
    if (forecastOverlay.bringToBack) forecastOverlay.bringToBack();

    updateForecastLegend(data);
  } catch (e) {
    alert('Forecast render failed: ' + e.message);
  }
  if (label) label.style.opacity = '';
}

function updateForecastLegend(data) {
  if (!forecastLegend) {
    forecastLegend = document.createElement('div');
    forecastLegend.className = 'fcst-legend';
    document.querySelector('.map-wrap').appendChild(forecastLegend);
  }

  const sigma = data.sigma_clip;
  const filename = document.getElementById('fcst-lead').value || '';
  const fpMatch = filename.match(/FP\.([\d-]+)/);
  const fpLabel = fpMatch ? fpMatch[1].replace('-', ' → ') : '';

  // Derive the variable from the actual filename being rendered (PA.<var>)
  // rather than trusting the picker alone — keeps the legend correct even
  // if the pickers and rendered overlay ever get out of sync.
  const varMatch = filename.match(/PA\.([A-Za-z0-9]+)/);
  const varCode = varMatch ? varMatch[1] : document.getElementById('fcst-variable').value;
  const varLabel = FCST_VAR_LABELS[varCode] || varCode || 'Anomaly';

  forecastLegend.innerHTML = `
    <div class="fcst-legend-title">${varLabel} anomaly</div>
    <div class="fcst-legend-sub">${fpLabel}</div>
    <div class="fcst-legend-bar"></div>
    <div class="fcst-legend-axis">
      <span>−${sigma}σ<br>lower</span>
      <span>0</span>
      <span>+${sigma}σ<br>higher</span>
    </div>
    <div class="fcst-legend-stats">
      μ ${data.stats.mean.toFixed(2)} · σ ${data.stats.std.toFixed(2)} ·
      ${(100 * data.stats.valid_pixels / data.stats.total_pixels).toFixed(0)}% land
    </div>
  `;
  forecastLegend.style.display = '';
}

async function onForecastSelectionChange() {
  // Manually changing IC/variable/lead-type/lead invalidates whatever
  // animation was running over the old set of dates.
  stopFcstAnimation();
  // Repopulate pickers downstream of whichever changed
  populateForecastPickers();
  if (document.getElementById('fcst-toggle').checked) {
    await renderSelectedForecast();
  }
}

// ----- S2S Forecast animation: step through every lead date for the
// currently selected IC + variable + lead-type, re-rendering the overlay
// each frame. -----

function fcstAnimGetLeadOptions() {
  const leadSel = document.getElementById('fcst-lead');
  return Array.from(leadSel.options).map(o => ({ value: o.value, text: o.text }));
}

function setFcstPickersDisabled(disabled) {
  ['fcst-ic', 'fcst-variable', 'fcst-leadtype', 'fcst-lead'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.disabled = disabled;
  });
}

function updateFcstAnimLabel(idx, total, text) {
  const label = document.getElementById('fcst-anim-label');
  if (label) label.textContent = `${idx + 1}/${total} · ${text}`;
}

async function toggleFcstAnimation() {
  if (fcstAnimPlaying) {
    stopFcstAnimation();
  } else {
    await startFcstAnimation();
  }
}

async function startFcstAnimation() {
  if (!document.getElementById('fcst-toggle').checked) return;

  const options = fcstAnimGetLeadOptions();
  if (options.length < 2) {
    alert('Only one date is available for this variable/lead type — nothing to animate through.');
    return;
  }

  fcstAnimPlaying = true;
  setFcstPickersDisabled(true);
  const btn = document.getElementById('fcst-anim-btn');
  if (btn) btn.textContent = '⏸ Pause';

  const leadSel = document.getElementById('fcst-lead');
  let idx = Math.max(0, options.findIndex(o => o.value === leadSel.value));

  const stepFrame = async () => {
    if (!fcstAnimPlaying) return;
    leadSel.value = options[idx].value;
    updateFcstAnimLabel(idx, options.length, options[idx].text);
    await renderSelectedForecast();
    // renderSelectedForecast is async and awaits a fetch; the user may have
    // hit Pause while it was in flight, so re-check before scheduling more.
    if (!fcstAnimPlaying) return;
    idx = (idx + 1) % options.length;  // loop back to the start
    const speed = parseInt(document.getElementById('fcst-anim-speed').value, 10) || 800;
    fcstAnimTimer = setTimeout(stepFrame, speed);
  };

  await stepFrame();
}

function stopFcstAnimation() {
  fcstAnimPlaying = false;
  if (fcstAnimTimer) { clearTimeout(fcstAnimTimer); fcstAnimTimer = null; }
  setFcstPickersDisabled(false);
  const btn = document.getElementById('fcst-anim-btn');
  if (btn) btn.textContent = '▶ Animate';
}

async function toggleForecastLayer(on) {
  const picker = document.getElementById('fcst-picker');
  if (on) {
    const catalog = await loadForecastCatalog();
    if (!catalog || !catalog.exists) {
      alert('No FCST/ directory found. Place forecast .TIF files in ./FCST and try again.');
      document.getElementById('fcst-toggle').checked = false;
      return;
    }
    if (!catalog.count) {
      alert('FCST/ exists but contains no recognized 557WW-format TIF files.');
      document.getElementById('fcst-toggle').checked = false;
      return;
    }
    populateForecastPickers();
    picker.style.display = '';
    await renderSelectedForecast();
  } else {
    stopFcstAnimation();
    const label = document.getElementById('fcst-anim-label');
    if (label) label.textContent = '';
    picker.style.display = 'none';
    if (forecastOverlay) { map.removeLayer(forecastOverlay); forecastOverlay = null; }
    if (forecastLegend) forecastLegend.style.display = 'none';
  }
}

// ACLED conflict-nearby state
let conflictData = null;       // {events: [...], count, radius_km, days_back}
let conflictError = null;      // string

async function runOverpassAnalysis(lat, lon, eventName) {
  const enabled = Array.from(activeSatellites);
  if (!enabled.length) {
    alert('Enable at least one satellite in the panel below the map first, then try again.');
    return;
  }

  overpassEvent = { name: eventName, lat, lon };
  overpassData = null;
  overpassMaxDistKm = null;
  conflictData = null;
  conflictError = null;
  overpassLayer.clearLayers();

  showOverpassModal();  // loading state

  const days = 7;
  const gapMin = 120;  // group passes within 2h of each other
  const overpassUrl = '/api/overpasses?lat=' + lat + '&lon=' + lon +
              '&sats=' + enabled.join(',') + '&days=' + days + '&gap_min=' + gapMin;
  const conflictUrl = '/api/acled_nearby?lat=' + lat + '&lon=' + lon +
              '&radius_km=100&days_back=30';

  // Fire both in parallel
  const overpassPromise = fetch(overpassUrl).then(r => r.json()).then(d => {
    if (d.error) throw new Error(d.error);
    overpassData = d;
  }).catch(e => { throw e; });

  const conflictPromise = fetch(conflictUrl).then(r => r.json()).then(d => {
    if (d.error) { conflictError = d.error; return; }
    conflictData = d;
  }).catch(e => { conflictError = e.message; });

  try {
    await overpassPromise;
    // Re-render with overpass data; conflict may still be pending
    showOverpassModal();
    drawOverpassesOnMap();
  } catch (e) {
    showOverpassModal(e.message);
    return;
  }

  // When conflict resolves, re-render the conflict section
  await conflictPromise;
  renderModalBody();
}

function fmtTime(iso) {
  const d = new Date(iso);
  return d.toLocaleString(undefined, {
    weekday: 'short', month: 'short', day: 'numeric',
    hour: '2-digit', minute: '2-digit', timeZoneName: 'short'
  });
}

function fmtMinutes(secondsBetween) {
  const m = Math.round(secondsBetween / 60);
  if (m < 60) return m + ' min';
  const h = Math.floor(m / 60);
  return h + 'h ' + (m % 60) + 'm';
}

function passesPassFilter(p) {
  return overpassMaxDistKm === null || p.peak_distance_km <= overpassMaxDistKm;
}

function getFilteredFlatPasses() {
  if (!overpassData) return [];
  const out = [];
  Object.entries(overpassData.overpasses).forEach(([sat_id, info]) => {
    info.passes.forEach(p => {
      if (passesPassFilter(p)) out.push({ sat_id, sat_name: info.name, ...p });
    });
  });
  out.sort((a, b) => new Date(a.peak_time) - new Date(b.peak_time));
  return out;
}

function getFilteredOverlaps() {
  // Re-cluster filtered passes using the original gap_minutes setting
  if (!overpassData) return [];
  const flat = getFilteredFlatPasses();
  if (flat.length < 2) return [];
  const gapMs = overpassData.gap_minutes * 60 * 1000;
  const clusters = [];
  let cur = [flat[0]];
  let curLatest = new Date(flat[0].peak_time).getTime();
  for (let i = 1; i < flat.length; i++) {
    const t = new Date(flat[i].peak_time).getTime();
    if (t - curLatest <= gapMs) {
      cur.push(flat[i]);
      curLatest = t;
    } else {
      if (new Set(cur.map(p => p.sat_id)).size >= 2) clusters.push(cur);
      cur = [flat[i]];
      curLatest = t;
    }
  }
  if (new Set(cur.map(p => p.sat_id)).size >= 2) clusters.push(cur);
  return clusters;
}

function drawOverpassesOnMap() {
  overpassLayer.clearLayers();
  if (!overpassData || !overpassEvent) return;

  // Draw a marker at the event location
  L.marker([overpassEvent.lat, overpassEvent.lon], {
    icon: L.divIcon({
      html: '<div style="width:14px;height:14px;border-radius:50%;background:white;border:3px solid #000;box-shadow:0 0 0 1px white;"></div>',
      className: '', iconSize: [14, 14], iconAnchor: [7, 7]
    })
  }).addTo(overpassLayer).bindPopup('<b>' + escapeHtml(overpassEvent.name) + '</b>');

  const passes = getFilteredFlatPasses();

  // Helper to split a list of [lat, lon] points at antimeridian crossings
  function splitAtAntimeridian(pts) {
    const segs = [[]];
    let prev = null;
    pts.forEach(p => {
      if (prev !== null && Math.abs(p[1] - prev) > 180) segs.push([]);
      segs[segs.length - 1].push(p);
      prev = p[1];
    });
    return segs.filter(s => s.length > 1);
  }

  passes.forEach(p => {
    const color = satMeta[p.sat_id] ? satMeta[p.sat_id].color : '#888';

    // Filled swath polygon, semi-transparent
    if (p.swath_polygon && p.swath_polygon.length > 3) {
      // Polygon = left edge forward then right edge reversed; check whether
      // any segment crosses antimeridian. If so, skip the polygon and draw
      // edges as separate polylines instead (simpler than splitting polygons).
      const lons = p.swath_polygon.map(pt => pt[1]);
      let crosses = false;
      for (let i = 1; i < lons.length; i++) {
        if (Math.abs(lons[i] - lons[i-1]) > 180) { crosses = true; break; }
      }
      if (!crosses) {
        const poly = L.polygon(p.swath_polygon, {
          color, weight: 1, fillColor: color, fillOpacity: 0.25
        });
        const tooltip = '<b>' + escapeHtml(p.sat_name) + '</b><br>' +
          fmtTime(p.peak_time) + '<br>' +
          p.peak_distance_km + ' km from centerline · ' + fmtMinutes(p.duration_s);
        poly.bindPopup(tooltip);
        poly.addTo(overpassLayer);
      }
    }

    // Centerline (dashed) for clarity
    if (p.centerline && p.centerline.length > 1) {
      splitAtAntimeridian(p.centerline).forEach(seg => {
        L.polyline(seg, {
          color, weight: 2, opacity: 0.9, dashArray: '5 4'
        }).addTo(overpassLayer);
      });
    }
  });

  // Auto-fit if we have passes
  if (passes.length > 0) {
    const allPts = [];
    passes.forEach(p => p.centerline && p.centerline.forEach(c => allPts.push(c)));
    allPts.push([overpassEvent.lat, overpassEvent.lon]);
    if (allPts.length > 1) {
      // Don't auto-fit if it would zoom out too much; only if the existing
      // view doesn't already show the event
      const bounds = L.latLngBounds(allPts);
      if (!map.getBounds().contains([overpassEvent.lat, overpassEvent.lon])) {
        map.fitBounds(bounds, { padding: [40, 40], maxZoom: 6 });
      }
    }
  }
}

function clearOverpassOverlay() {
  overpassLayer.clearLayers();
  overpassData = null;
  overpassEvent = null;
}

async function fetchNisarSoilMoisture(lat, lon, peakTime) {
  // Disable button + show loading state
  const btn = event && event.target;
  if (btn) { btn.disabled = true; btn.textContent = 'Fetching…'; }

  try {
    const url = '/api/nisar_soil_moisture?lat=' + lat + '&lon=' + lon;
    const resp = await fetch(url);
    const data = await resp.json();

    if (data.error) {
      alert('NISAR fetch failed:\n\n' + data.error);
      if (btn) { btn.disabled = false; btn.textContent = 'Soil moisture'; }
      return;
    }

    // Add image overlay to the map
    const img = L.imageOverlay(data.png_url, data.bounds, { opacity: 0.85 });
    img.addTo(nisarLayer);

    // Add a small marker at the target pixel showing the value
    const valueText = data.value_at_target !== null
      ? `Soil moisture: ${(data.value_at_target * 100).toFixed(1)}% vol`
      : 'Soil moisture at target: no valid retrieval';
    const statsText = data.stats.mean !== null
      ? `Window mean: ${(data.stats.mean * 100).toFixed(1)}% (${data.stats.valid_count}/${data.stats.total_count} valid pixels)`
      : 'No valid pixels in window';
    const granuleTime = data.granule.time_start.split('T')[0];

    const popup = `
      <div style="font-size:13px;line-height:1.4;">
        <b>NISAR L3 Soil Moisture (Beta)</b><br>
        ${valueText}<br>
        ${statsText}<br>
        <span style="color:#888;font-size:11px;">Granule from ${granuleTime}</span><br>
        <span style="color:#888;font-size:11px;">Resolution: 200 m EASE-Grid 2.0</span>
      </div>
    `;
    img.bindPopup(popup);
    nisarOverlays.push({ imageOverlay: img, info: data });

    // Fit map to the new overlay
    map.fitBounds(data.bounds, { padding: [40, 40], maxZoom: 12 });

    // Show the value briefly in the modal too
    const modalBody = document.getElementById('modal-body-container');
    if (modalBody) {
      const banner = document.createElement('div');
      banner.className = 'nisar-result-banner';
      banner.innerHTML = `✓ ${valueText} · ${statsText} · <a href="#" onclick="clearNisarOverlays();return false;">Clear</a>`;
      modalBody.insertBefore(banner, modalBody.firstChild);
    }

    if (btn) { btn.disabled = false; btn.textContent = '✓ Loaded'; }
  } catch (e) {
    alert('NISAR fetch failed: ' + e.message);
    if (btn) { btn.disabled = false; btn.textContent = 'Soil moisture'; }
  }
}

function clearNisarOverlays() {
  nisarLayer.clearLayers();
  nisarOverlays = [];
  document.querySelectorAll('.nisar-result-banner').forEach(el => el.remove());
}

function onMaxDistChange(value) {
  overpassMaxDistKm = value === '' || value === 'any' ? null : parseFloat(value);
  document.getElementById('max-dist-readout').textContent =
    overpassMaxDistKm === null ? 'any' : '≤ ' + overpassMaxDistKm + ' km';
  renderModalBody();
  drawOverpassesOnMap();
}

function showOverpassModal(errorMsg) {
  // Remove any existing modal
  const old = document.getElementById('overpass-modal');
  if (old) old.remove();

  const backdrop = document.createElement('div');
  backdrop.id = 'overpass-modal';
  backdrop.className = 'modal-backdrop';
  backdrop.onclick = (e) => { if (e.target === backdrop) backdrop.remove(); };

  const lat = overpassEvent ? overpassEvent.lat : 0;
  const lon = overpassEvent ? overpassEvent.lon : 0;
  const name = overpassEvent ? overpassEvent.name : '';

  backdrop.innerHTML = `
    <div class="modal" onclick="event.stopPropagation()">
      <div class="modal-header">
        <div>
          <div class="modal-title">Satellite overpass analysis</div>
          <div class="modal-sub">${escapeHtml(name)} · ${lat.toFixed(2)}, ${lon.toFixed(2)}</div>
        </div>
        <button class="modal-close" onclick="document.getElementById('overpass-modal').remove()">×</button>
      </div>
      <div id="modal-body-container"></div>
    </div>
  `;
  document.body.appendChild(backdrop);
  renderModalBody(errorMsg);
}

function renderModalBody(errorMsg) {
  const container = document.getElementById('modal-body-container');
  if (!container) return;

  if (errorMsg) {
    container.innerHTML = `<div class="error">${escapeHtml(errorMsg)}</div>`;
    return;
  }
  if (!overpassData) {
    container.innerHTML = '<div class="modal-loading">Computing overpasses for the next 7 days…</div>';
    return;
  }

  const passes = getFilteredFlatPasses();
  const overlaps = getFilteredOverlaps();
  const totalPassCount = Object.values(overpassData.overpasses)
    .reduce((s, info) => s + info.passes.length, 0);

  // Slider control
  const sliderHTML = `
    <div class="filter-row">
      <label class="filter-label-lg">Max distance from centerline:
        <span id="max-dist-readout">${overpassMaxDistKm === null ? 'any' : '≤ ' + overpassMaxDistKm + ' km'}</span>
      </label>
      <input type="range" min="10" max="1200" step="10"
             value="${overpassMaxDistKm === null ? 1200 : overpassMaxDistKm}"
             oninput="onMaxDistChange(this.value === '1200' ? 'any' : this.value)">
      <button class="btn-small" onclick="onMaxDistChange('any')">Any</button>
    </div>
    <div class="filter-meta">${passes.length} of ${totalPassCount} overpasses match · ${overlaps.length} multi-sat overlaps</div>
  `;

  // Overlaps section
  let overlapsHTML;
  if (!overlaps.length) {
    overlapsHTML = '<div class="empty-overlaps">No multi-satellite overlaps within the current filter.</div>';
  } else {
    overlapsHTML = overlaps.map(cluster => {
      const start = new Date(cluster[0].peak_time);
      const end   = new Date(cluster[cluster.length-1].peak_time);
      const span  = (end - start) / 1000;
      const pills = cluster.map(p => {
        const color = satMeta[p.sat_id] ? satMeta[p.sat_id].color : '#888';
        return '<span class="cluster-pill" style="background:' + color + ';">' +
          escapeHtml(p.sat_name) + ' · ' + p.peak_distance_km + ' km' +
        '</span>';
      }).join('');
      return '<div class="overlap-cluster">' +
        '<div class="cluster-time">' + fmtTime(cluster[0].peak_time) +
          '<span class="cluster-span">' +
            (span < 60 ? 'simultaneous' : 'within ' + fmtMinutes(span)) +
          '</span>' +
        '</div>' +
        '<div class="cluster-sats">' + pills + '</div>' +
      '</div>';
    }).join('');
  }

  // Passes section
  let passesHTML;
  if (!passes.length) {
    passesHTML = '<div class="empty-overlaps">No overpasses match the current filter.</div>';
  } else {
    passesHTML = passes.map(p => {
      const color = satMeta[p.sat_id] ? satMeta[p.sat_id].color : '#888';
      const nisarBtn = (p.sat_id === 'NISAR')
        ? '<button class="btn-small nisar-btn" onclick="fetchNisarSoilMoisture(' +
            overpassEvent.lat + ',' + overpassEvent.lon + ',\'' + escapeHtml(p.peak_time) + '\')">' +
            'Soil moisture</button>'
        : '';
      return '<div class="pass-row">' +
        '<div class="pass-sat">' +
          '<div class="pass-bar" style="background:' + color + ';"></div>' +
          '<div>' +
            '<div>' + escapeHtml(p.sat_name) + '</div>' +
            '<div class="pass-dist">' + p.peak_distance_km + ' km from centerline</div>' +
          '</div>' +
        '</div>' +
        '<div class="pass-time">' + fmtTime(p.peak_time) + '</div>' +
        '<div class="pass-dist">' + fmtMinutes(p.duration_s) + nisarBtn + '</div>' +
      '</div>';
    }).join('');
  }

  // Build conflict section (loads in parallel with overpasses)
  const ACLED_TYPE_COLORS = {
    'Battles': '#7a0c1f',
    'Explosions/Remote violence': '#c43a31',
    'Violence against civilians': '#d95a4c',
    'Riots': '#e89e3c',
    'Protests': '#3a7ec2',
    'Strategic developments': '#888780',
  };

  let conflictHTML;
  if (conflictError) {
    conflictHTML = '<div class="empty-conflict">ACLED unavailable: ' + escapeHtml(conflictError) + '</div>';
  } else if (conflictData === null) {
    conflictHTML = '<div class="empty-conflict">Loading conflict events…</div>';
  } else if (conflictData.count === 0) {
    conflictHTML = '<div class="empty-conflict">No ACLED conflict events within ' +
      conflictData.radius_km + ' km in the last ' + conflictData.days_back + ' days.</div>';
  } else {
    const evs = conflictData.events;
    const totalFat = evs.reduce((s, e) => s + (e.fatalities || 0), 0);
    const typeCounts = {};
    evs.forEach(e => { typeCounts[e.event_type] = (typeCounts[e.event_type] || 0) + 1; });
    const typeSummary = Object.entries(typeCounts)
      .sort((a, b) => b[1] - a[1])
      .slice(0, 3)
      .map(([t, n]) => n + ' ' + t)
      .join(' · ');

    // Top 10 events by date (already sorted desc by event_date from server)
    const top = evs.slice(0, 10);
    const rows = top.map(e => {
      const color = ACLED_TYPE_COLORS[e.event_type] || '#888780';
      const fatHTML = e.fatalities > 0
        ? '<span class="conflict-fatalities">' + e.fatalities + ' killed</span>'
        : '<span class="conflict-meta">no fatalities</span>';
      return '<div class="conflict-event-row">' +
        '<span class="conflict-type-pill" style="background:' + color + ';">' +
          escapeHtml(e.sub_event_type || e.event_type) + '</span>' +
        '<div>' +
          '<div>' + escapeHtml(e.location || e.country) + '</div>' +
          '<div class="conflict-meta">' + e.event_date + ' · ' + escapeHtml(e.actor1 || 'Unknown actor') +
            ' · ' + e.distance_km + ' km away</div>' +
        '</div>' +
        '<div>' + fatHTML + '</div>' +
        '<button class="btn-small" onclick="zoomTo(' + e.latitude + ',' + e.longitude + ')">View</button>' +
      '</div>';
    }).join('');

    const moreNote = evs.length > 10
      ? '<div class="conflict-meta" style="margin-top:6px;text-align:center;">+ ' + (evs.length - 10) + ' more events not shown</div>'
      : '';

    conflictHTML = `
      <div class="conflict-summary">
        <div class="conflict-summary-item">
          <span class="conflict-summary-num">${evs.length}</span>
          <span class="conflict-summary-lbl">events in last ${conflictData.days_back} days</span>
        </div>
        <div class="conflict-summary-item">
          <span class="conflict-summary-num" style="color:#c43a31;">${totalFat}</span>
          <span class="conflict-summary-lbl">total fatalities</span>
        </div>
        <div class="conflict-summary-item" style="flex:1;min-width:180px;">
          <span class="conflict-summary-lbl" style="margin-top:4px;">Breakdown</span>
          <span style="font-size:12px;">${escapeHtml(typeSummary)}</span>
        </div>
      </div>
      ${rows}
      ${moreNote}
    `;
  }

  container.innerHTML = `
    <div class="modal-section">${sliderHTML}</div>
    <div class="modal-section conflict-section">
      <h3>Recent conflict activity (within 100 km, last 30 days)</h3>
      ${conflictHTML}
    </div>
    <div class="modal-section">
      <h3>Multi-satellite overlaps (within ${overpassData.gap_minutes/60} h)</h3>
      ${overlapsHTML}
    </div>
    <div class="modal-section">
      <h3>All matching overpasses</h3>
      ${passesHTML}
    </div>
    <div class="modal-section" style="text-align:right;">
      <button class="btn-small" onclick="clearOverpassOverlay(); document.getElementById('overpass-modal').remove();">
        Clear map overlay
      </button>
    </div>
  `;
}

async function toggleSat(id, on) {
  const checkbox = document.querySelector(`input[data-sat="${id}"]`);
  if (on) {
    activeSatellites.add(id);
    if (!satTracks[id]) {
      try {
        const resp = await fetch('/api/satellite?id=' + encodeURIComponent(id));
        const data = await resp.json();
        if (data.error) {
          alert(data.error);
          checkbox.checked = false;
          activeSatellites.delete(id);
          return;
        }
        satTracks[id] = data;
      } catch (e) {
        alert('Failed to load satellite track: ' + e.message);
        checkbox.checked = false;
        return;
      }
    }
    drawTrack(id);
  } else {
    activeSatellites.delete(id);
    eraseTrack(id);
  }
}

function drawTrack(id) {
  const track = satTracks[id];
  if (!track || !track.points) return;
  const color = satMeta[id].color;
  const swathKm = track.swath_km || 0;

  // Helper: split a list of [lat,lon] points into segments at antimeridian crossings
  function splitSegments(pts) {
    const segs = [[]];
    let prev = null;
    pts.forEach(p => {
      if (prev !== null && Math.abs(p[1] - prev) > 180) segs.push([]);
      segs[segs.length - 1].push(p);
      prev = p[1];
    });
    return segs.filter(s => s.length > 1);
  }

  track.polylines = [];

  // 1) Swath polygons (filled, semi-transparent), drawn UNDER the centerline
  if (swathKm > 0 && track.left_edge.length && track.right_edge.length) {
    // Walk both edges in parallel; whenever EITHER side wraps the antimeridian,
    // close out the current polygon and start a new one.
    let polyL = [], polyR = [];
    let prevL = null, prevR = null;

    const flush = () => {
      if (polyL.length >= 2) {
        const ring = polyL.concat(polyR.slice().reverse());
        const poly = L.polygon(ring, {
          color, weight: 0, fillColor: color, fillOpacity: 0.18
        });
        poly.bindTooltip(track.name + ' swath: ' + swathKm + ' km (' + track.instr + ')',
                         { sticky: true });
        poly.addTo(trackLayer);
        track.polylines.push(poly);
      }
      polyL = []; polyR = [];
    };

    for (let i = 0; i < track.left_edge.length; i++) {
      const l = track.left_edge[i], r = track.right_edge[i];
      if (prevL !== null && (Math.abs(l[1] - prevL) > 180 || Math.abs(r[1] - prevR) > 180)) {
        flush();
      }
      polyL.push(l); polyR.push(r);
      prevL = l[1]; prevR = r[1];
    }
    flush();
  }

  // 2) Centerline (dashed)
  splitSegments(track.points.map(p => [p[0], p[1]])).forEach(seg => {
    const line = L.polyline(seg, { color, weight: 2, opacity: 0.85, dashArray: '4 3' })
      .addTo(trackLayer);
    track.polylines.push(line);
  });

  // 3) "Now" marker at the satellite's current position
  if (track.points.length) {
    const [lat0, lon0] = track.points[0];
    const startMarker = L.circleMarker([lat0, lon0], {
      radius: 5, fillColor: color, color: 'white', weight: 2, fillOpacity: 1
    });
    startMarker.bindPopup('<b>' + track.name + '</b><br>' +
      track.instr + ' · ' + swathKm + ' km swath<br>Position now');
    startMarker.addTo(trackLayer);
    track.polylines.push(startMarker);
  }
}

function eraseTrack(id) {
  const track = satTracks[id];
  if (track && track.polylines) {
    track.polylines.forEach(p => trackLayer.removeLayer(p));
    track.polylines = [];
  }
}

// Init
buildSatList();
setInterval(fetchData, 24 * 60 * 60 * 1000);  // auto-refresh every 24h
fetchData();
</script>
</body>
</html>
"""


def render_html():
    """Inject server-side metadata into the HTML template."""
    sat_meta = {sid: {
        "name": info["name"],
        "color": info["color"],
        "swath_km": info["swath_km"],
        "instr": info["instr"],
    } for sid, info in SATELLITES.items()}
    return HTML_PAGE.replace("SAT_META_PLACEHOLDER", json.dumps(sat_meta))


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    def _json(self, status, payload):
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)
        params = parse_qs(parsed.query)
        path = parsed.path

        if path in ("/", "/index.html"):
            body = render_html().encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        elif path == "/api/gdacs":
            try:
                fromdate = params.get("from", [None])[0]
                todate = params.get("to", [None])[0]
                data = fetch_gdacs(fromdate, todate)
                body = data.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Access-Control-Allow-Origin", "*")
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                self.wfile.write(body)
            except Exception as e:
                self._json(502, {"error": str(e)})

        elif path == "/api/satellite":
            sat_id = params.get("id", [""])[0]
            if sat_id not in SATELLITES:
                self._json(400, {"error": f"Unknown satellite: {sat_id}"})
                return
            try:
                tle_text = fetch_tle()
                tle_pairs = parse_tle_for_satellites(tle_text, [sat_id])
                if not tle_pairs:
                    self._json(404, {"error": (
                        f"No TLE found for {sat_id} in Celestrak's 'active' catalog. "
                        f"The NORAD id may have changed.")})
                    return
                tracks = compute_ground_tracks(tle_pairs, hours_ahead=24, step_minutes=2)
                if "error" in tracks:
                    self._json(500, tracks)
                    return
                self._json(200, tracks[sat_id])
            except Exception as e:
                self._json(502, {"error": str(e)})

        elif path == "/api/overpasses":
            try:
                lat = float(params.get("lat", [""])[0])
                lon = float(params.get("lon", [""])[0])
            except (ValueError, IndexError):
                self._json(400, {"error": "Need numeric lat & lon"})
                return
            sat_ids_csv = params.get("sats", [""])[0]
            if not sat_ids_csv:
                self._json(400, {"error": "No satellites specified"})
                return
            sat_ids = [s for s in sat_ids_csv.split(",") if s in SATELLITES]
            if not sat_ids:
                self._json(400, {"error": "No valid satellites in 'sats'"})
                return
            try:
                days = int(params.get("days", ["7"])[0])
            except ValueError:
                days = 7
            try:
                gap_min = int(params.get("gap_min", ["120"])[0])
            except ValueError:
                gap_min = 120

            try:
                tle_text = fetch_tle()
                tle_pairs = parse_tle_for_satellites(tle_text, sat_ids)
                if not tle_pairs:
                    self._json(404, {"error": "No TLEs found for the requested satellites"})
                    return
                overpasses = compute_overpasses(tle_pairs, lat, lon, days_ahead=days,
                                                step_seconds=30)
                if "error" in overpasses:
                    self._json(500, overpasses)
                    return
                overlaps = find_temporal_overlaps(overpasses, gap_minutes=gap_min)
                self._json(200, {
                    "target": {"lat": lat, "lon": lon},
                    "days_ahead": days,
                    "gap_minutes": gap_min,
                    "overpasses": overpasses,
                    "overlaps": overlaps,
                })
            except Exception as e:
                self._json(502, {"error": str(e)})

        elif path == "/api/nisar_check":
            # Test the token against the actual NISAR download endpoint, not
            # the EDL profile API — the profile API at /api/users/user has
            # different auth rules than the data endpoints (it requires a
            # client_id query param even with a Bearer token), so it's not a
            # reliable test of whether your token will work for data access.
            # Per CMR docs: "URS tokens must have either a Bearer or a client
            # id section. The Authorization: Bearer flag is only for EDL(URS)
            # tokens which do not need to define a client."
            issues, token = _diagnose_token()
            if not token:
                self._json(401, {
                    "ok": False,
                    "error": "Token file problem: " + " ".join(issues),
                    "fix": (
                        f"Visit https://urs.earthdata.nasa.gov/users/tokens "
                        f"(or profile -> Generate Token tab). Click 'Generate Token'. "
                        f"Copy the long opaque string ONLY (no 'Bearer ' prefix). "
                        f"Save it as ./{NISAR_TOKEN_FILE}, one line."
                    ),
                })
                return

            # Find a NISAR granule URL we can probe (HEAD request — no download)
            try:
                # Use a recent granule from the global catalog — no spatial filter
                search = cmr_search_nisar(0, 0, page_size=1)  # bbox at (0,0) but we'll fall back to non-spatial
                granules = search["granules"]
                if not granules:
                    # Try pure non-spatial just to find any granule
                    diag_url = (f"{CMR_URL}?short_name=NISAR_L3_SME2_BETA_V1"
                               f"&page_size=1&sort_key=-start_date")
                    req = urllib.request.Request(diag_url, headers={
                        "Accept": "application/json",
                        "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
                    })
                    with urllib.request.urlopen(req, timeout=15) as resp:
                        cmr_data = json.loads(resp.read().decode("utf-8"))
                    entries = cmr_data.get("feed", {}).get("entry", [])
                    if not entries:
                        self._json(503, {
                            "ok": False,
                            "error": "No NISAR granules found anywhere in CMR to test against."
                        })
                        return
                    test_url = None
                    for link in entries[0].get("links", []):
                        href = link.get("href", "")
                        if href.endswith(".h5"):
                            test_url = href
                            break
                else:
                    test_url = granules[0]["download_url"]

                if not test_url:
                    self._json(503, {
                        "ok": False,
                        "error": "Found a NISAR granule but no .h5 download URL on it."
                    })
                    return
            except Exception as e:
                self._json(502, {"ok": False, "error": f"CMR test failed: {e}"})
                return

            # Now do a HEAD request against the actual download URL with our token.
            # Walk redirects manually, same way the real downloader does, so we
            # accurately reproduce the auth path. We stop at the first 200, the
            # first non-2xx/3xx, or after 10 hops.
            current_url = test_url
            visited = []
            cookies = {}
            final_status = None
            final_body = ""

            for _hop in range(10):
                visited.append(current_url)
                req_headers = {
                    "Authorization": f"Bearer {token}",
                    "User-Agent": "Mozilla/5.0 (gdacs-dashboard)",
                    "Accept": "*/*",
                }
                if cookies:
                    req_headers["Cookie"] = "; ".join(f"{k}={v}" for k, v in cookies.items())

                class NoRedirect(urllib.request.HTTPRedirectHandler):
                    def http_error_301(self, *a, **kw): return None
                    def http_error_302(self, *a, **kw): return None
                    def http_error_303(self, *a, **kw): return None
                    def http_error_307(self, *a, **kw): return None
                    def http_error_308(self, *a, **kw): return None

                opener = urllib.request.build_opener(NoRedirect)
                # Use HEAD to avoid downloading the whole granule
                req = urllib.request.Request(current_url, headers=req_headers, method="HEAD")
                try:
                    resp = opener.open(req, timeout=30)
                    final_status = resp.getcode()
                except urllib.error.HTTPError as e:
                    final_status = e.code
                    resp = e

                # Some servers don't support HEAD on redirects → fall back to GET
                # but read 0 bytes
                if final_status == 405 and req.get_method() == "HEAD":
                    req = urllib.request.Request(current_url, headers=req_headers)
                    try:
                        resp = opener.open(req, timeout=30)
                        final_status = resp.getcode()
                    except urllib.error.HTTPError as e:
                        final_status = e.code
                        resp = e

                # Capture cookies
                for k, v in resp.getheaders():
                    if k.lower() == "set-cookie":
                        pair = v.split(";", 1)[0].strip()
                        if "=" in pair:
                            n, val = pair.split("=", 1)
                            cookies[n.strip()] = val.strip()

                if final_status in (301, 302, 303, 307, 308):
                    location = resp.getheader("Location")
                    if not location:
                        break
                    current_url = urllib.request.urljoin(current_url, location)
                    resp.close()
                    continue

                try:
                    final_body = resp.read(400).decode("utf-8", errors="replace")
                except Exception:
                    pass
                resp.close()
                break

            if final_status in (200, 204):
                self._json(200, {
                    "ok": True,
                    "message": "Token works for NISAR downloads.",
                    "token_length": len(token),
                    "token_preview": token[:8] + "..." + token[-4:],
                    "hops_followed": len(visited),
                    "warnings": issues,
                })
            else:
                self._json(final_status or 502, {
                    "ok": False,
                    "error": (
                        f"Token failed against the actual NISAR download endpoint "
                        f"(HTTP {final_status} after {len(visited)} hops). "
                        f"This is the test that actually matters — if this fails, "
                        f"downloads from the dashboard will also fail."
                    ),
                    "diagnostics": [
                        f"Token length: {len(token)} chars",
                        f"Token preview: {token[:8]}...{token[-4:]}",
                        f"Hop chain: {' -> '.join(visited)}",
                        f"Final response preview: {final_body[:300]}",
                    ],
                    "next_steps": (
                        "If the response mentions 'application not authorized' or "
                        "redirects you to an auth/login page, you need to approve "
                        "the ASF Cumulus Distribution app: visit "
                        "https://search.earthdata.nasa.gov/search?q=NISAR_L3_SME2 "
                        "in a browser, click any download link, and approve when prompted. "
                        "If the response says 'invalid token' or 'expired', generate a "
                        "fresh User Token at https://urs.earthdata.nasa.gov/users/tokens"
                    ),
                })

        elif path == "/api/nisar_soil_moisture":
            try:
                lat = float(params.get("lat", [""])[0])
                lon = float(params.get("lon", [""])[0])
            except (ValueError, IndexError):
                self._json(400, {"error": "Need numeric lat & lon"})
                return

            token = _read_edl_token()
            if not token:
                self._json(401, {"error": (
                    "No Earthdata Login token found. Create a token at "
                    "https://urs.earthdata.nasa.gov/profile (User Token tab) "
                    "and save it as './nisar_token.txt' (one line, no quotes)."
                )})
                return

            # Default lookback is 180 days — NISAR Beta coverage is sparse,
            # 60 days is often not enough.
            now = _utcnow_naive()
            start_iso = params.get("start", [(now - dt.timedelta(days=180)).strftime("%Y-%m-%dT00:00:00Z")])[0]
            end_iso = params.get("end", [now.strftime("%Y-%m-%dT23:59:59Z")])[0]

            try:
                search = cmr_search_nisar(lat, lon, start_iso, end_iso, page_size=20)
            except Exception as e:
                self._json(502, {"error": f"CMR search failed: {e}"})
                return

            granules = search["granules"]
            if not granules:
                # Build a diagnostic error message
                window_count = search.get("total_in_window", 0)
                first_global = search.get("first_global_time")

                if window_count > 0:
                    msg = (f"Found {window_count} NISAR L3 SME2 granule(s) in the "
                           f"last 180 days, but none cover ({lat:.2f}, {lon:.2f}). "
                           f"NISAR Beta acquisitions are concentrated in cal/val regions; "
                           f"global coverage isn't yet uniform.")
                elif first_global is None:
                    msg = (f"Found no NISAR L3 SME2 granules anywhere in CMR for the "
                           f"last 180 days. Either the collection name has changed, or "
                           f"production is paused. Check "
                           f"https://search.earthdata.nasa.gov/search?q=NISAR_L3_SME2 "
                           f"to verify.")
                else:
                    msg = (f"NISAR L3 SME2 granules exist (most recent: {first_global[:10]}), "
                           f"but none in the last 180 days near ({lat:.2f}, {lon:.2f}). "
                           f"Try a different event location closer to a cal/val site.")

                self._json(404, {"error": msg, "diagnostic": search})
                return

            # Try the most recent granule first; on failure, try the next one
            last_err = None
            for g in granules[:3]:
                if not g["download_url"]:
                    continue
                try:
                    h5_path = download_nisar_granule(g["download_url"], token)
                    result = render_nisar_subset(h5_path, lat, lon, half_size_km=10)
                    result["granule"] = {
                        "id": g["id"],
                        "title": g["title"],
                        "time_start": g["time_start"],
                        "time_end": g["time_end"],
                    }
                    result["granules_searched"] = len(granules)
                    result["search_method"] = search["method"]
                    self._json(200, result)
                    return
                except Exception as e:
                    last_err = f"{g['title']}: {e}"
                    print(f"[NISAR] granule fetch failed: {last_err}", file=sys.stderr)
                    continue

            # If every granule attempt failed with 401, the issue is auth.
            is_auth_problem = last_err and "401" in last_err
            if is_auth_problem:
                self._json(401, {"error": (
                    f"Found {len(granules)} matching NISAR granule(s), but every "
                    f"download was rejected with 401 Unauthorized.\n\n"
                    f"This almost always means one of two things:\n\n"
                    f"1) Your Earthdata Login token in nisar_token.txt is invalid "
                    f"or expired. Test it: open http://localhost:{PORT}/api/nisar_check\n\n"
                    f"2) Your EDL account hasn't approved ASF's NISAR distribution "
                    f"app. Visit https://search.earthdata.nasa.gov/search?q=NISAR_L3_SME2 "
                    f"in a browser, click any granule's download link, and approve "
                    f"the ASF Cumulus app when prompted. Then retry here.\n\n"
                    f"Last error: {last_err}"
                )})
                return

            self._json(502, {"error": f"All granule attempts failed. Last error: {last_err}"})

        elif path == "/api/acled_global":
            try:
                days_back = int(params.get("days_back", ["7"])[0])
            except ValueError:
                days_back = 7
            # Clamp — global pulls can be heavy
            days_back = max(1, min(days_back, 90))
            try:
                data = fetch_acled_global(days_back=days_back)
                self._json(200, data)
            except RuntimeError as e:
                self._json(401, {"error": str(e)})
            except Exception as e:
                self._json(502, {"error": f"ACLED global fetch failed: {e}"})

        elif path == "/api/acled_nearby":
            try:
                lat = float(params.get("lat", [""])[0])
                lon = float(params.get("lon", [""])[0])
            except (ValueError, IndexError):
                self._json(400, {"error": "Need numeric lat & lon"})
                return
            try:
                radius_km = int(params.get("radius_km", ["100"])[0])
                days_back = int(params.get("days_back", ["30"])[0])
            except ValueError:
                radius_km, days_back = 100, 30

            try:
                events = fetch_acled_nearby(lat, lon, radius_km=radius_km,
                                            days_back=days_back)
                self._json(200, {
                    "events": events,
                    "count": len(events),
                    "radius_km": radius_km,
                    "days_back": days_back,
                })
            except RuntimeError as e:
                self._json(401, {"error": str(e)})
            except Exception as e:
                self._json(502, {"error": f"ACLED fetch failed: {e}"})

        elif path == "/api/inform_data":
            try:
                data = fetch_inform_data()
                self._json(200, data)
            except RuntimeError as e:
                self._json(503, {"error": str(e)})
            except Exception as e:
                self._json(502, {"error": f"INFORM load failed: {e}"})

        elif path == "/api/countries_geojson":
            try:
                body = fetch_countries_geojson().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/geo+json")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "public, max-age=86400")
                self.end_headers()
                self.wfile.write(body)
            except Exception as e:
                self._json(502, {"error": f"countries fetch failed: {e}"})

        elif path == "/api/forecasts/list":
            try:
                catalog = list_forecasts()
                self._json(200, catalog)
            except Exception as e:
                self._json(502, {"error": f"Forecast list failed: {e}"})

        elif path == "/api/forecasts/render":
            filename = params.get("filename", [""])[0]
            if not filename or "/" in filename or "\\" in filename or ".." in filename:
                self._json(400, {"error": "Bad or missing 'filename' param"})
                return
            try:
                sigma = float(params.get("sigma_clip", ["2.0"])[0])
            except ValueError:
                sigma = 2.0
            try:
                result = render_forecast_tile(filename, sigma_clip=sigma)
                self._json(200, result)
            except Exception as e:
                self._json(502, {"error": f"Forecast render failed: {e}"})

        elif path.startswith("/" + NISAR_TILE_URLPATH + "/") or \
             path.startswith("/" + FCST_TILE_URLPATH + "/"):
            # Serve cached NISAR or forecast PNG tiles. The URL has the form
            # /<urlpath>/<filename>; map it back to the absolute disk path.
            url_path = path.lstrip("/")  # e.g. "fcst_tiles/foo.png"
            if ".." in url_path or "/" not in url_path:
                self.send_response(404); self.end_headers(); return
            url_dir, _, fname = url_path.partition("/")
            if url_dir == NISAR_TILE_URLPATH:
                disk_path = os.path.join(NISAR_TILE_DIR, fname)
            elif url_dir == FCST_TILE_URLPATH:
                disk_path = os.path.join(FCST_TILE_DIR, fname)
            else:
                self.send_response(404); self.end_headers(); return
            if not os.path.exists(disk_path):
                self.send_response(404); self.end_headers(); return
            with open(disk_path, "rb") as f:
                body = f.read()
            self.send_response(200)
            self.send_header("Content-Type", "image/png")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "public, max-age=3600")
            self.end_headers()
            self.wfile.write(body)

        else:
            self.send_response(404)
            self.end_headers()

    def log_message(self, fmt, *args):
        sys.stderr.write("[%s] %s\n" % (self.log_date_time_string(), fmt % args))


def main():
    server = HTTPServer(("127.0.0.1", PORT), Handler)

    def short(p):
        """Format a path relative to the script dir for display."""
        return os.path.relpath(p, _SCRIPT_DIR)

    print("=" * 60)
    print("  GDACS Disaster Dashboard v3")
    print("=" * 60)
    print(f"  Open in browser: http://localhost:{PORT}")
    print(f"  Data directory:  {_SCRIPT_DIR}")
    print(f"  GDACS cache:     {short(GDACS_CACHE_PREFIX)}.*.json")
    print(f"  TLE cache:       {short(TLE_CACHE)}")
    print(f"  NISAR cache:     {short(NISAR_CACHE_DIR)}/, {short(NISAR_TILE_DIR)}/")
    try:
        import sgp4  # noqa
        print("  Satellite tracks: ENABLED (sgp4 found)")
    except ImportError:
        print("  Satellite tracks: DISABLED — run 'pip install sgp4' to enable")

    # NISAR status
    nisar_deps = []
    for mod in ("h5py", "numpy", "PIL", "pyproj"):
        try:
            __import__(mod)
        except ImportError:
            nisar_deps.append(mod if mod != "PIL" else "Pillow")
    has_token = os.path.exists(NISAR_TOKEN_FILE)
    if nisar_deps:
        print(f"  NISAR soil moisture: DISABLED — pip install {' '.join(nisar_deps)}")
    elif not has_token:
        print(f"  NISAR soil moisture: needs {short(NISAR_TOKEN_FILE)} (Earthdata Login token)")
        print(f"                       Get one at https://urs.earthdata.nasa.gov/profile")
    else:
        print("  NISAR soil moisture: ENABLED")

    # ACLED conflict status
    if os.path.exists(ACLED_CRED_FILE):
        creds = _acled_load_creds()
        if creds and ("email" in creds or "access_token" in creds):
            print(f"  ACLED conflict data: ENABLED ({short(ACLED_CRED_FILE)} found)")
        else:
            print(f"  ACLED conflict data: {short(ACLED_CRED_FILE)} is malformed")
    else:
        print(f"  ACLED conflict data: needs {short(ACLED_CRED_FILE)}")
        print(f"                       Format: {{\"email\":\"you@x.com\",\"password\":\"...\"}}")
        print(f"                       Register at https://acleddata.com/register")

    # INFORM status
    try:
        __import__("openpyxl")
        print(f"  INFORM Risk Index:   ENABLED (cache: {short(INFORM_CACHE_FILE)})")
    except ImportError:
        print("  INFORM Risk Index:   DISABLED — pip install openpyxl")

    # S2S Forecast status
    try:
        __import__("tifffile")
        if os.path.isdir(FCST_DIR):
            n_tifs = sum(1 for f in os.listdir(FCST_DIR)
                         if f.endswith(".TIF") or f.endswith(".tif"))
            print(f"  S2S Forecast:        ENABLED ({n_tifs} files in {short(FCST_DIR)}/)")
        else:
            print(f"  S2S Forecast:        {short(FCST_DIR)}/ does not exist — "
                  f"create it and add 557WW .TIF files")
    except ImportError:
        print("  S2S Forecast:        DISABLED — pip install tifffile")

    print("  Press Ctrl+C to stop")
    print("=" * 60)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down.")
        server.server_close()


if __name__ == "__main__":
    main()
