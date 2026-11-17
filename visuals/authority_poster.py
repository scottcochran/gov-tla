#!/usr/bin/env python3
"""Render Government.tla's authority graph as a print poster (24 x 36 in).

The edges come from the model, not from this file: the founding graph is
the initial state TLC computes, and each amendment's effect is read off the
step that ratifies it in simulated behaviours. This file supplies only the
layout (where each node sits and how each edge is routed) and the plain
English names of the edges; it stops if the model has an edge the layout
does not place, so the poster cannot silently drift from the spec.

Writes visuals/Government_authority_poster_YEAR.html (1789 unless --year is
given), and, if Node.js with Playwright is available, the .pdf (vector, print
size) and .png (preview) beside it. Run it from anywhere:

    uv run python visuals/authority_poster.py [--year YEAR]
"""

import argparse
import html
import os
import shutil
import subprocess
from collections import defaultdict

import tlaviz

# ---------------------------------------------------------------------------
# Design tokens (reference palette; the three grant kinds validate all-pairs)

INK, INK2, MUTED = '#0b0b0b', '#52514e', '#898781'
SURFACE, PLANE, HAIRLINE, PARCHMENT = '#fcfcfb', '#f9f9f7', '#e1e0d9', '#f0efec'
KIND = {'Power': '#2a78d6', 'Select': '#eb6834', 'Amend': '#1baf7a', 'Control': INK2}
CRITICAL = '#d03b3b'

NAMES = {
    'Ordain': 'Ordain', 'Ratify': 'Ratify', 'Propose': 'Propose',
    'ArtI': 'Article I', 'ArtII': 'Article II', 'ArtIII': 'Article III',
    'ElectHouse': 'Elect the House', 'ElectSenate': 'Elect the Senate',
    'AppointElectors': 'Appoint electors', 'ContingentElection': 'Contingent election',
    'Nominate': 'Nominate', 'Consent': 'Consent',
    'Presentment': 'Presentment of bills', 'Override': 'Override a veto',
    'Appropriate': 'The purse', 'Impeach': 'Impeach and remove',
    'AdviseTreaties': 'Consent to treaties', 'DeclareWar': 'Declare war',
    'Veto': 'Veto', 'Convene': 'Special session',
    'Adjourn': 'Adjourn Congress',
    'Exceptions': 'Limit appellate jurisdiction', 'Organize': 'Set size, pay and lower courts',
    'Review': 'Judicial review', 'PresideTrial': "Preside at a President's trial",
    'Pardon': 'Pardon', 'Sue': 'Sue', 'ApplyForConvention': 'Apply for a convention',
    'ConfirmVP': 'Confirm a Vice President', 'DecideInability': 'Decide a contested inability',
    'NominateVP': 'Nominate a Vice President', 'Succession': 'Succession',
    'PresideSenate': 'Tie-breaking vote', 'DeclareInability': 'Declare inability',
}


def esc(s):
    return html.escape(str(s), quote=True)


# ---------------------------------------------------------------------------
# SVG primitives

def defs():
    out = ['<defs>']
    for kind, colour in {**KIND, 'removed': '#c3c2b7'}.items():
        out.append(f'<marker id="arrow-{kind}" viewBox="0 0 12 12" refX="10" refY="6" '
                   f'markerWidth="18" markerHeight="18" markerUnits="userSpaceOnUse" '
                   f'orient="auto"><path d="M0,0 L12,6 L0,12 z" fill="{colour}"/></marker>')
    out.append('</defs>')
    return ''.join(out)


def node(x, y, w, h, text, kind='branch', sub=None, size=30):
    if kind == 'source':
        shape = (f'<rect x="{x - w / 2}" y="{y - h / 2}" width="{w}" height="{h}" rx="{h / 2}" '
                 f'fill="{SURFACE}" stroke="{INK}" stroke-width="2"/>')
    elif kind == 'text':
        f = 22
        shape = (f'<path d="M{x - w / 2},{y - h / 2} h{w - f} l{f},{f} v{h - f} h{-w} z" '
                 f'fill="{PARCHMENT}" stroke="{INK}" stroke-width="2"/>'
                 f'<path d="M{x + w / 2 - f},{y - h / 2} v{f} h{f}" fill="none" '
                 f'stroke="{INK}" stroke-width="2"/>')
    elif kind == 'body':
        shape = (f'<rect x="{x - w / 2}" y="{y - h / 2}" width="{w}" height="{h}" rx="14" '
                 f'fill="{SURFACE}" stroke="{INK}" stroke-width="2" stroke-dasharray="10 7"/>')
    else:
        shape = (f'<rect x="{x - w / 2}" y="{y - h / 2}" width="{w}" height="{h}" rx="6" '
                 f'fill="{SURFACE}" stroke="{INK}" stroke-width="3.5"/>')
    dy = -8 if sub else 0
    label = (f'<text x="{x}" y="{y + dy}" text-anchor="middle" dominant-baseline="central" '
             f'font-size="{size}" font-weight="700" fill="{INK}">{esc(text)}</text>')
    if sub:
        label += (f'<text x="{x}" y="{y + 24}" text-anchor="middle" dominant-baseline="central" '
                  f'font-size="19" fill="{INK2}">{esc(sub)}</text>')
    return shape + label


def edge(d, kind, statute=False, removed=False, width=4):
    colour = '#c3c2b7' if removed else KIND[kind]
    marker = 'removed' if removed else kind
    dash = ' stroke-dasharray="14 9"' if statute else (' stroke-dasharray="3 7"' if removed else '')
    return (f'<path d="{d}" fill="none" stroke="{SURFACE}" stroke-width="{width + 10}" '
            f'stroke-linejoin="round"/>'
            f'<path d="{d}" fill="none" stroke="{colour}" stroke-width="{width}" '
            f'stroke-linejoin="round"{dash} marker-end="url(#arrow-{marker})"/>')


def label(x, y, text, size=22, anchor='middle', weight=500, colour=INK, halo=True):
    stroke = (f' stroke="{SURFACE}" stroke-width="12" stroke-linejoin="round" '
              f'paint-order="stroke"') if halo else ''
    return (f'<text x="{x}" y="{y}" text-anchor="{anchor}" dominant-baseline="central" '
            f'font-size="{size}" font-weight="{weight}" fill="{colour}"{stroke}>{esc(text)}</text>')


def svg(width, height, body, title, top=0):
    return (f'<svg viewBox="0 {top} {width} {height}" role="img" aria-label="{esc(title)}" '
            f'xmlns="http://www.w3.org/2000/svg">{defs()}{body}</svg>')


# ---------------------------------------------------------------------------
# Panel A: the grant layer, as a chain read top to bottom

# (from, to, label): (path, label x, label y[, anchor[, text]])
GRANT_LAYOUT = {
    ('People', 'Constitution', 'Ordain'):
        ('M350,345 V290 Q350,270 370,270 H470 Q490,270 490,263', 420, 270),
    ('States', 'Constitution', 'Ratify'): ('M880,200 H758', 819, 200),
    ('Constitution', 'Congress', 'ArtI'): ('M600,255 V444', 600, 350),
    ('Constitution', 'VicePresident', 'ArtI'):
        ('M450,235 H210 Q190,235 190,255 V710 Q190,730 210,730 H467', 200, 600, 'start'),
    ('Constitution', 'Executive', 'ArtII'):
        ('M450,205 H150 Q130,205 130,225 V955 Q130,975 150,975 H452', 140, 860, 'start'),
    ('Constitution', 'Judiciary', 'ArtIII'):
        ('M450,175 H90 Q70,175 70,195 V1230 Q70,1250 90,1250 H452', 80, 1110, 'start'),
    ('People', 'Congress', 'ElectHouse'):
        ('M300,415 V470 Q300,490 320,490 H452', 300, 448),
    ('People', 'Congress', 'ElectSenate'):            # from XVII on
        ('M390,415 V442 Q390,462 410,462 H452', 392, 432, 'start'),
    ('States', 'Congress', 'ElectSenate'):            # until XVII
        ('M910,238 V450 Q910,470 890,470 H748', 910, 300),
    ('Congress', 'States', 'Propose'):
        ('M740,500 H950 Q970,500 970,480 V246', 970, 420),
    ('States', 'VicePresident', 'AppointElectors'):
        ('M1010,238 V710 Q1010,730 990,730 H733', 870, 730),
    ('States', 'Executive', 'AppointElectors'):
        ('M1050,238 V940 Q1050,960 1030,960 H748', 900, 960),
    ('Congress', 'VicePresident', 'ContingentElection'): ('M600,548 V682', 600, 619),
    ('Congress', 'VicePresident', 'ConfirmVP'):       # from XXV on
        ('M560,548 V682', 548, 619, 'end', 'Confirm'),
    ('VicePresident', 'Executive', 'Succession'): ('M600,770 V904', 600, 841),
    ('Executive', 'VicePresident', 'NominateVP'):     # from XXV on
        ('M640,912 V778', 652, 841, 'start', 'Nominate'),
    ('Congress', 'Executive', 'ContingentElection'):
        ('M460,540 H400 Q380,540 380,560 V925 Q380,945 400,945 H452', 380, 885),
    ('Congress', 'Judiciary', 'Consent'):
        ('M460,515 H340 Q320,515 320,535 V1195 Q320,1215 340,1215 H452', 330, 1110, 'start'),
    ('Executive', 'Judiciary', 'Nominate'): ('M600,1008 V1174', 600, 1095),
}
# Where an edge moves over to make room for another.
MAKE_ROOM = {
    ('Congress', 'VicePresident', 'ConfirmVP'):
        {('Congress', 'VicePresident', 'ContingentElection'):
             ('M640,548 V682', 652, 619, 'start')},
    ('Executive', 'VicePresident', 'NominateVP'):
        {('VicePresident', 'Executive', 'Succession'): ('M560,770 V904', 548, 841, 'end')},
}
# Drawn first, so the edges crossing them pass over with a gap.
UNDER = {('Congress', 'Executive', 'ContingentElection'), ('Congress', 'Judiciary', 'Consent')}


def grant_panel(edges):
    grant = {(e['from'], e['to'], e['label']): e for e in edges if e['kind'] != 'Control'}
    layout = dict(GRANT_LAYOUT)
    for k, moves in MAKE_ROOM.items():
        if k in grant:
            layout.update(moves)
    missing = set(grant) - set(layout)
    if missing:
        raise SystemExit(f'The model has grant edges the poster layout does not place: '
                         f'{missing}; add them to GRANT_LAYOUT.')
    body = []
    order = sorted(grant, key=lambda k: k not in UNDER)
    for k in order:
        body.append(edge(layout[k][0], grant[k]['kind']))
    for k in order:
        _, lx, ly, *rest = layout[k]
        anchor = rest[0] if rest else 'middle'
        text = rest[1] if len(rest) > 1 else NAMES[k[2]]
        body.append(label(lx, ly, text, anchor=anchor))
    body.append(node(350, 380, 180, 70, 'People', 'source'))
    body.append(node(980, 200, 200, 76, 'States', 'source'))
    body.append(node(600, 200, 300, 110, 'Constitution', 'text', size=32))
    body.append(node(600, 500, 280, 96, 'Congress'))
    body.append(node(600, 730, 250, 80, 'Vice President', size=27))
    body.append(node(600, 960, 280, 96, 'Executive', sub='the President'))
    body.append(node(600, 1230, 280, 96, 'Judiciary', sub='the Supreme Court'))
    return svg(1100, 1148, ''.join(body), 'Grant layer of the authority graph', top=140)


# ---------------------------------------------------------------------------
# Panel B: the control layer, one arrow per direction, width = number of checks

POS = {'Congress': (500, 360), 'Executive': (175, 1080), 'Judiciary': (825, 1080),
       'VicePresident': (500, 720)}
SIZE = {'VicePresident': (230, 76)}
NODE_W, NODE_H = 260, 96


def _trim(n, x1, y1, pad):
    """Point where the segment from node n toward (x1,y1) leaves its box."""
    (x0, y0), (w, h) = POS[n], SIZE.get(n, (NODE_W, NODE_H))
    dx, dy = x1 - x0, y1 - y0
    tx = (w / 2 + pad) / abs(dx) if dx else float('inf')
    ty = (h / 2 + pad) / abs(dy) if dy else float('inf')
    t = min(tx, ty)
    return x0 + dx * t, y0 + dy * t


def arrow(a, b, n, offset):
    (x0, y0), (x1, y1) = POS[a], POS[b]
    length = ((x1 - x0) ** 2 + (y1 - y0) ** 2) ** 0.5
    ux, uy = (x1 - x0) / length, (y1 - y0) / length
    px, py = -uy * offset, ux * offset          # perpendicular shift
    sx, sy = _trim(a, x1, y1, 14)
    ex, ey = _trim(b, x0, y0, 14)
    sx, sy, ex, ey = sx + px, sy + py, ex + px, ey + py
    w = 3 * n
    head = 22 + w
    bx, by = ex - ux * head, ey - uy * head
    half = w / 2 + 11
    poly = (f'{ex:.1f},{ey:.1f} {bx - uy * half:.1f},{by + ux * half:.1f} '
            f'{bx + uy * half:.1f},{by - ux * half:.1f}')
    return (f'<line x1="{sx:.1f}" y1="{sy:.1f}" x2="{bx:.1f}" y2="{by:.1f}" '
            f'stroke="{KIND["Control"]}" stroke-width="{w}"/>'
            f'<polygon points="{poly}" fill="{KIND["Control"]}"/>')


def checks_block(x, y, rows, anchor='start'):
    """rows: list of (header, count, [names]). Returns SVG text lines."""
    out, line = [], y
    for header, count, names in rows:
        out.append(f'<text x="{x}" y="{line}" text-anchor="{anchor}" font-size="23" '
                   f'font-weight="700" fill="{INK}">{esc(header)} '
                   f'<tspan font-size="34" font-weight="800">{count}</tspan></text>')
        line += 40
        for name in names:
            out.append(f'<text x="{x}" y="{line}" text-anchor="{anchor}" font-size="21" '
                       f'fill="{INK2}">{esc(name)}</text>')
            line += 30
        line += 22
    return ''.join(out)


def display(n):
    return 'Vice President' if n == 'VicePresident' else n


def control_panel(edges):
    pairs = defaultdict(list)
    for e in edges:
        if e['kind'] == 'Control':
            pairs[(e['from'], e['to'])].append(NAMES[e['label']])
    known = {('States', 'Congress'), ('People', 'Judiciary')}
    for (a, b) in pairs:
        if not ({a, b} <= set(POS) or (a, b) in known):
            raise SystemExit(f'Control edge {a} -> {b} has no place in the poster layout.')

    def n(a, b):
        return len(pairs.get((a, b), []))

    def rows(*dirs):
        return [(f'{display(a)} → {display(b)}', n(a, b), pairs[(a, b)])
                for a, b in dirs if n(a, b)]

    body = []
    for a, b in [('Congress', 'Executive'), ('Executive', 'Congress'),
                 ('Congress', 'Judiciary'), ('Judiciary', 'Congress'),
                 ('Executive', 'Judiciary'), ('Judiciary', 'Executive'),
                 ('Congress', 'VicePresident'), ('VicePresident', 'Congress'),
                 ('VicePresident', 'Executive')]:
        if n(a, b):
            body.append(arrow(a, b, n(a, b), 22 if 'VicePresident' not in (a, b) else 14))
    # sources
    body.append(edge('M780,130 Q690,130 655,300', 'Control', width=3))
    body.append(label(800, 215, NAMES['ApplyForConvention'], size=19))
    body.append(node(870, 110, 180, 66, 'States', 'source', size=26))
    body.append(edge('M825,1330 V1144', 'Control', width=3))
    body.append(label(825, 1240, NAMES['Sue'], size=19))
    body.append(node(825, 1360, 180, 66, 'People', 'source', size=26))
    for name, (x, y) in POS.items():
        w, h = SIZE.get(name, (NODE_W, NODE_H))
        body.append(node(x, y, w, h, display(name), size=26 if name in SIZE else 30))

    body.append(checks_block(20, 110, rows(('VicePresident', 'Congress'),
                                           ('Congress', 'VicePresident'),
                                           ('VicePresident', 'Executive'))))
    body.append(checks_block(20, 412, rows(('Congress', 'Executive'),
                                           ('Executive', 'Congress'))))
    body.append(checks_block(980, 440, rows(('Congress', 'Judiciary'),
                                            ('Judiciary', 'Congress')), anchor='end'))
    body.append(checks_block(500, 1195, rows(('Executive', 'Judiciary')), anchor='middle'))
    body.append(checks_block(500, 905, rows(('Judiciary', 'Executive')), anchor='middle'))
    return svg(1000, 1325, ''.join(body), 'Control layer of the authority graph', top=72), pairs


# ---------------------------------------------------------------------------
# Panel C: amendments that rewired the graph

def amendment_panel(added, dropped):
    want_add = {('People', 'Congress', 'ElectSenate'),
                ('Executive', 'VicePresident', 'NominateVP'),
                ('Congress', 'VicePresident', 'ConfirmVP'),
                ('VicePresident', 'Executive', 'DeclareInability'),
                ('Congress', 'Executive', 'DecideInability')}
    want_drop = {('States', 'Congress', 'ElectSenate')}
    got_add = {(e['from'], e['to'], e['label']) for e in added}
    got_drop = {(e['from'], e['to'], e['label']) for e in dropped}
    if got_add != want_add or got_drop != want_drop:
        raise SystemExit(f'Amendments in the model differ from the poster: added {got_add}, '
                         f'dropped {got_drop}')
    b = []
    # XVII
    b.append(edge('M110,128 Q110,300 205,348', 'Select', removed=True))
    b.append(label(110, 225, 'Elect the Senate', size=20, colour=MUTED))
    b.append(label(110, 255, '(removed)', size=18, colour=MUTED))
    b.append(edge('M390,128 Q390,300 295,348', 'Select'))
    b.append(label(390, 225, 'Elect the Senate', size=20))
    b.append(label(390, 255, '(added)', size=18, colour=INK2))
    b.append(node(110, 95, 170, 62, 'States', 'source', size=24))
    b.append(node(390, 95, 170, 62, 'People', 'source', size=24))
    b.append(node(250, 385, 220, 80, 'Congress', size=26))
    # XXV
    b.append(edge('M700,135 Q620,200 625,337', 'Select'))
    b.append(label(640, 225, 'Confirm', size=20, anchor='end'))
    b.append(edge('M820,135 Q900,200 895,337', 'Control'))
    b.append(label(885, 210, 'Decide', size=20, anchor='start'))
    b.append(label(885, 238, 'inability', size=20, anchor='start'))
    b.append(edge('M805,370 H728', 'Select'))
    b.append(label(767, 335, 'Nominate', size=20))
    b.append(edge('M715,402 H795', 'Control'))
    b.append(label(757, 448, 'Declare inability', size=20))
    b.append(node(760, 95, 200, 80, 'Congress', size=26))
    b.append(node(620, 385, 190, 80, 'Vice President', size=22))
    b.append(node(900, 385, 180, 80, 'Executive', size=24))
    for x, head, lines in (
            (250, 'XVII · 1913', ['Senators are chosen by the People,', 'no longer by the States.']),
            (760, 'XXV · 1967', ['The President nominates a Vice President;',
                                 'Congress confirms and settles inability.'])):
        b.append(label(x, 18, head, size=26, weight=800, halo=False))
        for i, line in enumerate(lines):
            b.append(label(x, 505 + 32 * i, line, size=21, colour=INK2, halo=False))
    return svg(1000, 580, ''.join(b), 'Edges changed by the Seventeenth and Twenty-fifth Amendments',
               top=-20)


# ---------------------------------------------------------------------------
# Panel D: what an enabling act adds

def statute_panel():
    b = []
    b.append(edge('M150,98 Q150,250 380,262', 'Control', statute=True, width=3))
    b.append(label(150, 190, 'enable · consent · fund · impeach', size=19, anchor='start'))
    b.append(edge('M500,98 V214', 'Control', statute=True, width=3))
    b.append(label(500, 160, 'nominate head · remove · direct', size=19))
    b.append(edge('M850,98 Q850,250 620,262', 'Control', statute=True, width=3))
    b.append(label(850, 195, 'review', size=19, anchor='end'))
    for x, name in ((150, 'Congress'), (500, 'Executive'), (850, 'Judiciary')):
        b.append(node(x, 60, 220, 72, name, size=25))
    b.append(node(500, 260, 220, 76, 'An agency', 'body', size=25))
    return svg(1000, 310, ''.join(b), 'Edges an enabling act adds')


FORBIDDEN = [  # Forbidden(e) in Government.tla, with what Sever(e) leaves
    ('Congress appoints an inferior officer', 'Buckley v. Valeo (1976)', 'edge struck'),
    ('Congress removes an officer who executes the laws', 'Bowsher v. Synar (1986)',
     'the officer loses its executive power'),
    ('A legislative veto over an agency', 'INS v. Chadha (1983)', 'edge struck'),
    ('For-cause protection for a head with executive power',
     'Seila Law (2020); Trump v. Slaughter (2026)', 'the head serves at will'),
    ("Cutting a sitting judge's pay", 'United States v. Will (1980)', 'edge struck'),
]


# ---------------------------------------------------------------------------
# Facts computed from the graph

def reach(edges, start, exclude=()):
    seen, frontier = set(), {start}
    while frontier:
        nxt = {e['to'] for e in edges if e['from'] in frontier and e['to'] not in exclude}
        frontier = nxt - seen
        seen |= nxt
    return seen


def facts(edges):
    grant = [e for e in edges if e['kind'] != 'Control']
    control = [e for e in edges if e['kind'] == 'Control']
    branches = ['Congress', 'Executive', 'Judiciary']
    out_c = sum(1 for e in control if e['from'] == 'Congress' and e['to'] in branches)
    in_c = sum(1 for e in control if e['to'] == 'Congress' and e['from'] in branches)
    inner = [e for e in grant if e['from'] not in ('People', 'States')
             and e['to'] not in ('People', 'States')]
    on_cycle = [e for e in inner if e['from'] in reach(inner, e['to'])]
    # a cycle's nodes: those that reach, and are reached from, a node on it
    loops = {frozenset({e['from']} | {v for v in reach(inner, e['from'])
                                      if e['from'] in reach(inner, v)})
             for e in on_cycle}
    door = [e for e in edges if e['kind'] in ('Power', 'Amend')]
    bypass = reach(door, 'People', exclude={'Constitution'}) & set(branches)
    return dict(total=len(edges), grant=len(grant), control=len(control),
                kinds={k: sum(1 for e in edges if e['kind'] == k) for k in KIND},
                out_c=out_c, in_c=in_c, loops=[sorted(l) for l in loops], bypass=len(bypass))


# ---------------------------------------------------------------------------
# The page

CSS = f"""
@page {{ size: 24in 36in; margin: 0; }}
* {{ box-sizing: border-box; margin: 0; padding: 0; }}
html, body {{ width: 2304px; height: 3456px; background: {PLANE}; }}
body {{ font-family: Inter, system-ui, -apple-system, "Segoe UI", sans-serif; color: {INK};
        padding: 84px 120px 56px; display: flex; flex-direction: column; gap: 32px;
        -webkit-print-color-adjust: exact; print-color-adjust: exact; }}
svg {{ display: block; width: 100%; height: auto; font-family: inherit; }}
.kicker {{ font-size: 26px; font-weight: 700; letter-spacing: .14em; text-transform: uppercase;
           color: {INK2}; }}
h1 {{ font-size: 140px; font-weight: 800; letter-spacing: -.035em; line-height: .95;
      margin-top: 22px; }}
.deck {{ font-size: 40px; line-height: 1.3; color: {INK2}; max-width: 1750px; margin-top: 30px; }}
.deck b {{ color: {INK}; font-weight: 700; }}
.stats {{ display: grid; grid-template-columns: repeat(3, 1fr); gap: 32px; }}
.stat {{ background: {SURFACE}; border: 1px solid rgba(11,11,11,.10); border-radius: 16px;
         padding: 30px 40px 32px; }}
.stat .n {{ font-size: 104px; font-weight: 800; letter-spacing: -.04em; line-height: 1; }}
.stat .n small {{ font-size: 60px; font-weight: 700; color: {INK2}; }}
.stat .t {{ font-size: 29px; line-height: 1.35; color: {INK2}; margin-top: 14px; }}
.stat .t b {{ color: {INK}; }}
.row {{ display: grid; gap: 32px; }}
.row.main {{ grid-template-columns: 1100fr 1000fr; }}
.row.small {{ grid-template-columns: 1fr 1fr; }}
.panel {{ background: {SURFACE}; border: 1px solid rgba(11,11,11,.10); border-radius: 16px;
          padding: 40px 44px 36px; display: flex; flex-direction: column; }}
.panel h2 {{ font-size: 50px; font-weight: 800; letter-spacing: -.02em; line-height: 1.1; }}
.panel .lede {{ font-size: 28px; line-height: 1.4; color: {INK2}; margin: 14px 0 24px; }}
.panel .lede b {{ color: {INK}; }}
.panel .fig {{ margin-top: 0; }}
.legend {{ display: flex; flex-wrap: wrap; gap: 10px 28px; font-size: 23px; color: {INK2};
           margin-bottom: 18px; align-items: center; }}
.legend span {{ display: inline-flex; align-items: center; gap: 12px; }}
.legend svg {{ width: 44px; height: 14px; }}
.tag {{ font-family: "JetBrains Mono", monospace; font-size: .82em; color: {INK2};
        background: {PARCHMENT}; border-radius: 6px; padding: 1px 8px; }}
.sub2 {{ display: grid; grid-template-columns: 1fr 1fr; font-size: 26px; font-weight: 700;
         margin-bottom: 4px; }}
.sub2 span:last-child {{ text-align: right; }}
.sub2 em {{ font-style: normal; font-weight: 500; color: {INK2}; }}
ul.struck {{ list-style: none; margin-top: 22px; display: grid; gap: 12px; }}
ul.struck li {{ display: grid; grid-template-columns: 40px 1fr; gap: 6px 14px;
                font-size: 24px; line-height: 1.3; }}
ul.struck .ic {{ width: 34px; height: 34px; margin-top: 1px; }}
ul.struck .case {{ color: {INK2}; font-size: 22px; }}
footer {{ margin-top: auto; display: flex; justify-content: space-between; gap: 60px;
          font-size: 22px; line-height: 1.45; color: {MUTED}; border-top: 1px solid {HAIRLINE};
          padding-top: 26px; }}
footer p {{ max-width: 1800px; }}
footer b {{ color: {INK2}; }}
"""


def swatch(kind, dash=None):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<svg viewBox="0 0 56 14"><line x1="2" y1="7" x2="54" y2="7" stroke="{KIND[kind]}" '
            f'stroke-width="5"{d}/></svg>')


def stop_icon():
    return (f'<svg class="ic" viewBox="0 0 34 34" aria-hidden="true">'
            f'<circle cx="17" cy="17" r="14" fill="none" stroke="{CRITICAL}" stroke-width="3.5"/>'
            f'<line x1="7" y1="27" x2="27" y2="7" stroke="{CRITICAL}" stroke-width="3.5"/></svg>')


def page(year, edges, added, dropped, check_note):
    f = facts(edges)
    in_force = [x for x, y in sorted(RATIFIED.items(), key=lambda i: i[1]) if y <= year]
    if year == FOUNDING:
        graph_of, as_of = 'the founding graph', 'the Constitution of 1789 with the Bill of Rights'
        force = 'Both came later.'
    else:
        graph_of = f'the graph of {year}'
        as_of = f'the Constitution as amended through {year}'
        force = (f'In {year} {"both are" if len(in_force) == len(RATIFIED) else "only " + in_force[0] + " is" if in_force else "neither is"} in force.')
    source = ('<span class="tag">Government.tla</span> in gov-tla. The founding graph (1789, '
              'with the Bill of Rights) is the initial state TLC computes')
    if in_force:
        source += ('; each amendment ratified by ' + str(year) + ', '
                   + ', '.join(f'{x} ({RATIFIED[x]})' for x in in_force)
                   + ', is applied as the model\'s <span class="tag">Ratify</span> step rewrites '
                   'it. The model treats no other amendment as changing the graph.')
    else:
        source += '.'
    control_svg, pairs = control_panel(edges)
    legend = ''.join(
        f'<span>{swatch(k)}{t}</span>' for k, t in
        (('Power', '<b>Power</b>&nbsp;confers authority'),
         ('Select', '<b>Select</b>&nbsp;fills an office'),
         ('Amend', '<b>Amend</b>&nbsp;writes the text')))
    struck = ''.join(
        f'<li>{stop_icon()}<div><b>{esc(what)}</b><br>'
        f'<span class="case">{esc(case)} · {esc(after)}</span></div></li>'
        for what, case, after in FORBIDDEN)
    note = f' {check_note}' if check_note else ''
    if f['loops']:
        names = ' and '.join({'Executive': 'President'}.get(n, display(n)) for n in f['loops'][0])
        chain_caveat = ' with a single loop'
        loop_text = (f'<b>grant cycle among government bodies</b>, the {names}: since XXV '
                     'the President nominates a successor, skipping the People and the States.')
        back_text = ('Two point back up: Article V (Congress → States) and XXV '
                     '(President → Vice President).')
    else:
        chain_caveat = ''
        loop_text = ('<b>grant cycles among government bodies.</b> Every loop of authority '
                     'closes through the People or the States.')
        back_text = 'Only Article V points back up, from Congress to the States.'
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>Who Answers to Whom</title>
<style>{CSS}</style></head>
<body>
<header>
  <div class="kicker">gov-tla &nbsp;·&nbsp; Government.tla &nbsp;·&nbsp; a TLA+ model of the U.S. Constitution &nbsp;·&nbsp; {year}</div>
  <h1>Who answers to whom</h1>
  <p class="deck">{as_of[0].upper() + as_of[1:]}, as a graph: <b>{f['total']} edges</b> of authority among the People,
  the States, the text and the government. Power flows <b>down</b> one chain{chain_caveat};
  checks run <b>in a circle</b>, and Congress holds most of them.</p>
</header>

<section class="stats">
  <div class="stat"><div class="n">{f['total']}</div>
    <div class="t"><b>edges in {graph_of}:</b> {f['grant']} say where authority comes
    from, {f['control']} let one branch act on another.</div></div>
  <div class="stat"><div class="n">{f['out_c']} <small>vs</small> {f['in_c']}</div>
    <div class="t"><b>checks Congress holds</b> on the other two branches, against the checks
    they hold on Congress.</div></div>
  <div class="stat"><div class="n">{len(f['loops'])}</div>
    <div class="t">{loop_text}</div></div>
</section>

<section class="row main">
  <div class="panel">
    <h2>Where authority comes from</h2>
    <p class="lede">The <b>grant layer</b>: {f['grant']} edges, running <b>downward</b> from the
    Constitution to the courts. {back_text}</p>
    <div class="legend">{legend}</div>
    <div class="fig">{grant_panel(edges)}</div>
  </div>
  <div class="panel">
    <h2>How the branches check each other</h2>
    <p class="lede">The <b>control layer</b>: {f['control']} edges. Every branch can act on each of
    the others, so checks form a cycle. Arrow width is the number of checks;
    Congress's arrows are the widest on both sides.</p>
    <div class="fig">{control_svg}</div>
  </div>
</section>

<section class="row small">
  <div class="panel">
    <h2>Amendments rewire the graph</h2>
    <p class="lede">Text edges change only by Article V. Two amendments in the model move them. {force}</p>
    <div class="fig">{amendment_panel(added, dropped)}</div>
  </div>
  <div class="panel">
    <h2>Statutes add; courts prune</h2>
    <p class="lede">Agencies and lower courts exist only by statute (dashed edges). Congress
    can enact an edge the text forbids. Once someone sues, the court strikes it:</p>
    <div class="fig">{statute_panel()}</div>
    <ul class="struck">{struck}</ul>
  </div>
</section>

<footer>
  <p><b>Source:</b> {source} Judicial review is
  Marbury's reading of Articles III and VI, not text. Vote thresholds and persons are
  abstracted away.{note} A model for study, not
  legal advice.</p>
  <p style="text-align:right; white-space:nowrap">Generated by<br>
  <span class="tag">authority_poster.py</span></p>
</footer>
</body></html>"""


FOUNDING = 1789
# Year each amendment in the model was ratified. The model decides what an
# amendment does to the graph; this table only says when it happened.
RATIFIED = {'XVII': 1913, 'XXV': 1967}


def amendment_effects():
    """(edges added, edges dropped) by each amendment, read off the text
    edges just before and just after the step that ratifies it."""
    effects = {}
    for seed in range(1, 300):
        trace = tlaviz.simulate('Government', seed, 40)
        for (_, prev), (action, state) in zip(trace, trace[1:]):
            before, now = dict(prev['amendment']), dict(state['amendment'])
            for x in now:
                if now[x] == 'Ratified' and before[x] != 'Ratified' and x not in effects:
                    old = {e for e in prev['edges'] if e.get('basis') == 'Text'}
                    new = {e for e in state['edges'] if e.get('basis') == 'Text'}
                    effects[x] = (new - old, old - new)
        if set(effects) == set(RATIFIED):
            return effects
    raise SystemExit(f'No simulated behaviour ratified {set(RATIFIED) - set(effects)}.')


RENDER_JS = r"""
const { chromium } = require('playwright');
(async () => {
  const [html, pdf, png] = process.argv.slice(1);
  const browser = await chromium.launch();
  const page = await browser.newPage({ viewport: { width: 2304, height: 3456 },
                                       deviceScaleFactor: 1 });
  await page.goto('file://' + html);
  await page.evaluate(() => document.fonts.ready);
  const h = await page.evaluate(() => document.documentElement.scrollHeight);
  if (h > 3456) console.error(`warning: content is ${h}px tall, taller than the page`);
  await page.pdf({ path: pdf, width: '24in', height: '36in', printBackground: true });
  await page.screenshot({ path: png });
  await browser.close();
})();
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--year', type=int, default=FOUNDING,
                        help='draw the graph as amended through this year '
                             f'(default: {FOUNDING}, the founding graph)')
    parser.add_argument('--check-note', default='',
                        help='a sentence for the footer, e.g. the result of a TLC run')
    args = parser.parse_args()

    if args.year < FOUNDING:
        raise SystemExit(f'The model starts in {FOUNDING}.')

    print('Reading the founding graph from TLC...')
    init = tlaviz.simulate('Government', 0, 0)[0][1]
    if {x for x, _ in init['amendment']} != set(RATIFIED):
        raise SystemExit(f'Government.tla models amendments {[x for x, _ in init["amendment"]]}; '
                         f'add their years to RATIFIED.')
    founding = set(init['edges'])

    print('Reading what each amendment changes from simulated behaviours...')
    effects = amendment_effects()
    graph = set(founding)
    for x in sorted(RATIFIED, key=RATIFIED.get):
        if RATIFIED[x] <= args.year:
            adds, drops = effects[x]
            graph = (graph - drops) | adds
    edges = [dict(e) for e in sorted(graph, key=tlaviz.fmt)]
    added = [dict(e) for x in effects for e in effects[x][0]]
    dropped = [dict(e) for x in effects for e in effects[x][1]]

    out = f'Government_authority_poster_{args.year}'
    path = os.path.join(tlaviz.VISUALS, f'{out}.html')
    with open(path, 'w') as fh:
        fh.write(page(args.year, edges, added, dropped, args.check_note))
    print(f'Generated visuals/{out}.html')

    if shutil.which('node'):
        r = subprocess.run(['node', '-e', RENDER_JS, path,
                            os.path.join(tlaviz.VISUALS, f'{out}.pdf'),
                            os.path.join(tlaviz.VISUALS, f'{out}.png')],
                           capture_output=True, text=True,
                           env={**os.environ, 'NODE_PATH': subprocess.run(
                               ['npm', 'root', '-g'], capture_output=True,
                               text=True).stdout.strip()})
        if r.returncode == 0:
            print(r.stderr.strip() or f'Generated visuals/{out}.pdf (24 x 36 in) and visuals/{out}.png')
            return
        print('Could not render with Playwright:', r.stderr.strip().splitlines()[-1:])
    print(f'Open visuals/{out}.html in a browser and print it to PDF at 24 x 36 in.')


if __name__ == '__main__':
    main()
