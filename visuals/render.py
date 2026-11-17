#!/usr/bin/env python3
"""Render one of the SVG pictures in visuals/ to PNG, light, dark or both, whole
or cropped, so it can be looked at. Adapted from TOPAK's diagram family
(skills/generating-corpus-diagrams/scripts/render.py).

Light is rasterized by rsvg-convert, which reads the presentation attributes.
Dark needs a browser, because the dark theme is CSS custom properties switched
by svg[data-theme=dark], which rsvg ignores: the script inserts that attribute,
wraps the SVG in an HTML page and screenshots it with headless Chrome.

A crop rewrites the viewBox, so it is exact and works in both themes. Crop by
a text needle (the first <text> whose content contains it) or by coordinates
in SVG units.

  uv run python visuals/render.py visuals/Government_authority.svg
  uv run python visuals/render.py visuals/Government_authority_poster_1789.svg --needle "Congress holds" --h 900 --width 1800
  uv run python visuals/render.py visuals/Government_depth1.svg --theme dark --y 0 --h 600

Writes PNGs to --out (default: gov-tla-render/<name>/ under $TMPDIR) and prints their paths.
"""
import argparse
import html
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

DARK_BG = '#12151b'
CHROME_CANDIDATES = [
    os.environ.get('CHROME', ''),
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/Applications/Chromium.app/Contents/MacOS/Chromium',
    'google-chrome', 'google-chrome-stable', 'chromium', 'chromium-browser',
]


def die(msg):
    print(f'render: {msg}', file=sys.stderr)
    sys.exit(2)


def size(svg):
    m = re.search(r'<svg\b[^>]*\bwidth="([\d.]+)(?:pt|px)?"[^>]*\bheight="([\d.]+)(?:pt|px)?"', svg)
    if not m:
        die('root <svg> has no width and height')
    return float(m.group(1)), float(m.group(2))


def viewbox(svg):
    m = re.search(r'<svg\b[^>]*\bviewBox="([^"]+)"', svg)
    return [float(v) for v in m.group(1).split()] if m else None


def find_needle(svg, needle):
    for m in re.finditer(r'<text\b([^>]*)>(.*?)</text>', svg, re.S):
        text = html.unescape(re.sub(r'<[^>]+>', '', m.group(2)))
        if needle in text:
            y = re.search(r'\by="([-\d.]+)"', m.group(1))
            return float(y.group(1))
    die(f'needle not found in any <text>: {needle!r}')


def crop(svg, x, y, w, h):
    def fix(tag):
        tag = re.sub(r'\bwidth="[^"]+"', f'width="{w:.0f}"', tag, count=1)
        tag = re.sub(r'\bheight="[^"]+"', f'height="{h:.0f}"', tag, count=1)
        return re.sub(r'\bviewBox="[^"]*"', f'viewBox="{x:.0f} {y:.0f} {w:.0f} {h:.0f}"', tag, count=1)
    return re.sub(r'<svg\b[^>]*>', lambda m: fix(m.group(0)), svg, count=1)


def find_chrome():
    for c in CHROME_CANDIDATES:
        if c and os.path.isabs(c) and os.path.exists(c):
            return c
        if c and shutil.which(c):
            return shutil.which(c)
    return None


def light(svg_path, out_png, out_w):
    if not shutil.which('rsvg-convert'):
        die('rsvg-convert not found (macOS: brew install librsvg; Debian: apt install librsvg2-bin)')
    subprocess.run(['rsvg-convert', '-w', str(out_w), str(svg_path), '-o', str(out_png)], check=True)


def dark(svg_text, work, out_png, w, h, out_w):
    chrome = find_chrome()
    if not chrome:
        die('no Chrome or Chromium found; set CHROME=/path/to/chrome')
    svg_text = re.sub(r'<svg\b', '<svg data-theme="dark"', svg_text, count=1)
    (work / 'dark.svg').write_text(svg_text, encoding='utf-8')
    (work / 'dark.html').write_text(
        f'<html><body style="margin:0;background:{DARK_BG}">'
        f'<img src="dark.svg" width="{w:.0f}" height="{h:.0f}" style="display:block"></body></html>',
        encoding='utf-8')
    scale = out_w / w
    subprocess.run([chrome, '--headless=new', '--hide-scrollbars', f'--force-device-scale-factor={scale:.4f}',
                    f'--window-size={int(w)},{int(h)}', f'--screenshot={out_png}',
                    (work / 'dark.html').resolve().as_uri()], check=True, capture_output=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('svg', help='path to an SVG in visuals/')
    ap.add_argument('--theme', choices=['light', 'dark', 'both'], default='both')
    ap.add_argument('--needle', help='crop around the first <text> containing this string')
    ap.add_argument('--above', type=float, default=120, help='with --needle: SVG units kept above the text')
    ap.add_argument('--x', type=float, help='crop left, SVG units (default 0)')
    ap.add_argument('--y', type=float, help='crop top, SVG units')
    ap.add_argument('--w', type=float, help='crop width, SVG units (default: whole width)')
    ap.add_argument('--h', type=float, help='crop height, SVG units (default 900 when cropping)')
    ap.add_argument('--width', type=int, default=1300, help='output PNG width in pixels (default 1300)')
    ap.add_argument('--out', help='output directory')
    a = ap.parse_args()

    path = pathlib.Path(a.svg)
    if not path.exists():
        die(f'{path} not found')
    svg = path.read_text(encoding='utf-8')
    vb = viewbox(svg)
    W, H = (vb[2], vb[3]) if vb else size(svg)
    x0, y0 = (vb[0], vb[1]) if vb else (0.0, 0.0)
    # Graphviz sizes its root in pt with a matching viewBox; a crop needs the two to agree, so
    # the root is first rewritten to the viewBox's units.
    svg = crop(svg, x0, y0, W, H)
    ident = path.stem
    tag = 'whole'
    if a.needle or a.y is not None:
        y = max(y0, find_needle(svg, a.needle) - a.above) if a.needle else a.y
        x = a.x if a.x is not None else x0
        w = min(a.w or W, x0 + W - x)
        h = min(a.h or 900, y0 + H - y)
        svg = crop(svg, x, y, w, h)
        W, H = w, h
        tag = f'y{int(y)}'
    out = pathlib.Path(a.out) if a.out else pathlib.Path(tempfile.gettempdir()) / 'gov-tla-render' / ident
    out.mkdir(parents=True, exist_ok=True)
    work = pathlib.Path(tempfile.mkdtemp(prefix=f'{ident}-', dir=out))
    src = work / 'light.svg'
    src.write_text(svg, encoding='utf-8')
    width = min(a.width, int(W * 2))
    if a.theme in ('light', 'both'):
        png = out / f'{ident}-{tag}-light.png'
        light(src, png, width)
        print(png)
    if a.theme in ('dark', 'both'):
        png = out / f'{ident}-{tag}-dark.png'
        dark(svg, work, png, W, H, width)
        print(png)


if __name__ == '__main__':
    main()
