"""Shared helpers for the gov-tla visualization scripts.

The four modules have state spaces in the millions, so unlike a small game
the whole graph cannot be dumped and drawn. Instead these helpers drive TLC
on a wrapper module that bounds the run:

  * bfs_graph()  - breadth-first search to a fixed depth, dumped as DOT
  * simulate()   - one random behaviour of a fixed length, from a seed

and parse what TLC prints back into Python values, so that each state can be
shown as "what differs from the initial state" instead of the full record.
"""

import os
import re
import shutil
import subprocess
import tempfile
from collections import deque

ROOT = os.path.dirname(os.path.abspath(__file__))
JAR = os.environ.get('TLA2TOOLS', os.path.join(ROOT, 'tools', 'tla2tools.jar'))
MODULES = ['Constitution', 'Executive', 'Judiciary', 'Government']


# ---------------------------------------------------------------------------
# TLC values

class Atom(str):
    """A model value or an identifier such as TRUE."""


class TSet(tuple):
    pass


class TSeq(tuple):
    pass


class TRec(tuple):
    """A record: a tuple of (field, value) pairs."""

    def get(self, key, default=None):
        return dict(self).get(key, default)


class TFun(tuple):
    """A function written k1 :> v1 @@ k2 :> v2: a tuple of (key, value) pairs."""


_TOKEN = re.compile(r'''
    \s*(?:
      (?P<str>"(?:[^"\\]|\\.)*")
    | (?P<num>-?\d+)
    | (?P<sym><<|>>|\|->|:>|@@|[{}\[\](),])
    | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
    )''', re.VERBOSE)


def _tokens(text):
    pos, out = 0, []
    text = text.strip()
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m or m.end() == pos:
            raise ValueError(f'cannot parse TLC value near: {text[pos:pos + 40]!r}')
        pos = m.end()
        kind = m.lastgroup
        out.append((kind, m.group(kind)))
    return out


def parse_value(text):
    toks = _tokens(text)
    i = 0

    def peek():
        return toks[i][1] if i < len(toks) else None

    def take(expected=None):
        nonlocal i
        kind, val = toks[i]
        if expected is not None and val != expected:
            raise ValueError(f'expected {expected!r}, got {val!r} in {text[:80]!r}')
        i += 1
        return kind, val

    def items(close, parse_item):
        out = []
        if peek() == close:
            take(close)
            return out
        while True:
            out.append(parse_item())
            if peek() == ',':
                take(',')
                continue
            take(close)
            return out

    def record_field():
        _, name = take()
        take('|->')
        return (name, value())

    def value():
        kind, tok = take()
        if kind == 'str':
            return bytes(tok[1:-1], 'utf-8').decode('unicode_escape')
        if kind == 'num':
            return int(tok)
        if kind == 'id':
            return {'TRUE': True, 'FALSE': False}.get(tok, Atom(tok))
        if tok == '{':
            return TSet(items('}', value))
        if tok == '<<':
            return TSeq(items('>>', value))
        if tok == '[':
            return TRec(items(']', record_field))
        if tok == '(':
            first = value()
            if peek() != ':>':
                take(')')
                return first
            pairs = []
            while True:
                take(':>')
                pairs.append((first, value()))
                if peek() == '@@':
                    take('@@')
                    first = value()
                    continue
                take(')')
                return TFun(pairs)
        raise ValueError(f'unexpected {tok!r} in {text[:80]!r}')

    v = value()
    if i != len(toks):
        raise ValueError(f'trailing input in {text[:80]!r}')
    return v


def parse_state(text):
    """Parse TLC's '/\\ var = value' listing of one state into a dict."""
    state, name, buf = {}, None, []
    for line in text.splitlines():
        m = re.match(r'/\\ (\w+) = (.*)', line)
        if m:
            if name:
                state[name] = parse_value('\n'.join(buf))
            name, buf = m.group(1), [m.group(2)]
        elif name and line.strip():
            buf.append(line)
    if name:
        state[name] = parse_value('\n'.join(buf))
    return state


# ---------------------------------------------------------------------------
# Showing a state as its difference from another

def fmt(v):
    if isinstance(v, bool):
        return 'TRUE' if v else 'FALSE'
    if isinstance(v, TSet):
        return '{' + ', '.join(fmt(x) for x in v) + '}'
    if isinstance(v, TSeq):
        return '⟨' + ', '.join(fmt(x) for x in v) + '⟩'
    if isinstance(v, TRec):
        r = dict(v)
        if {'from', 'to', 'label'} <= r.keys():           # a Government edge
            if r['from'] == 'None':
                return '—'
            return f"{r['from']}→{r['to']} {r['label']}"
        return '[' + ', '.join(f'{k}: {fmt(x)}' for k, x in v) + ']'
    if isinstance(v, TFun):
        return '(' + ', '.join(f'{fmt(k)}↦{fmt(x)}' for k, x in v) + ')'
    return str(v)


def flatten(state):
    """Records and functions become dotted paths; everything else is a leaf."""
    out = {}

    def walk(path, v):
        if isinstance(v, (TRec, TFun)) and len(v) and not _is_edge(v):
            for k, x in v:
                walk(f'{path}.{fmt(k)}', x)
        else:
            out[path] = v

    for name, v in state.items():
        walk(name, v)
    return out


def _is_edge(v):
    return isinstance(v, TRec) and {'from', 'to', 'label'} <= dict(v).keys()


def _compound_set(v):
    return isinstance(v, TSet) and any(isinstance(x, (TRec, TFun, TSeq, TSet)) for x in v)


def diff_lines(base, state, max_items=4):
    """Lines describing how state differs from base, one fact per line.

    Returns (path, text) pairs so that callers can tell which variable a
    line belongs to."""
    a, b = flatten(base), flatten(state)
    lines = []
    for path in b:
        old, new = a.get(path), b[path]
        if old == new:
            continue
        if _compound_set(new) or _compound_set(old):
            added = [x for x in new if x not in (old or ())]
            removed = [x for x in (old or ()) if x not in new]
            for sign, xs in (('+', added), ('−', removed)):
                for x in xs[:max_items]:
                    lines.append((path, f'{path} {sign} {fmt(x)}'))
                if len(xs) > max_items:
                    lines.append((path, f'{path} {sign} … {len(xs) - max_items} more'))
        else:
            lines.append((path, f'{path}: {fmt(new)}'))
    return lines


def changes(prev, state):
    """'path: old → new' lines for one step."""
    a, b = flatten(prev), flatten(state)
    out = []
    for path in b:
        if a.get(path) == b[path]:
            continue
        old, new = a.get(path), b[path]
        if _compound_set(new) or _compound_set(old):
            for x in new:
                if x not in (old or ()):
                    out.append(f'{path} + {fmt(x)}')
            for x in old or ():
                if x not in new:
                    out.append(f'{path} − {fmt(x)}')
        else:
            out.append(f'{path}: {fmt(old)} → {fmt(new)}')
    return out


# ---------------------------------------------------------------------------
# Colour by who acted

CATEGORIES = {
    # name: (fill colour, legend text)
    'init':        ('lightyellow', 'Initial state'),
    'legislative': ('lightblue',   'Congress (either house)'),
    'executive':   ('lightsalmon', 'President / executive'),
    'judicial':    ('lightgreen',  'Courts'),
    'impeachment': ('lightcoral',  'Impeachment and trial'),
    'people':      ('plum',        'People and States (elections, Art. V, suits)'),
    'lapse':       ('lightgray',   'Time, death, resignation'),
    'other':       ('white',       'Other'),
}

_ACTIONS = {
    'legislative': '''Convene Adjourn Introduce PassChamber FailChamber Override
        FailOverride BecomeLawUnsigned ConfirmVP RejectVP Consent Reject
        ProposeByCongress CongressDecides DeclareWar CreateAgency AbolishAgency
        CongressRemovesHead ConfirmHead RejectHead RatifyTreaty RejectTreaty
        EstablishCourt AbolishCourt SetSeats SetSalary SetExceptions ConfirmJudge
        RejectJudge ConfirmChief RejectChief Pass BillFails ContingentElection
        ContingentElectionVP
        Lapse''',
    'executive': '''Sign Veto PocketVeto Nominate NominateVP RecessAppoint
        DeclareInability DeclareAble CabinetDeclares ConveneByPresident NominateHead
        AppointInferior ActAsHead PresidentRemovesHead PresidentRemovesInferior
        Pardon Negotiate NominateJudge NominateChief Remove Succeed''',
    'judicial': 'Decide Appeal AppellateDecide Close Review',
    'impeachment': 'Impeach Convict Acquit',
    'people': '''Elect ApplyForConvention ProposeByConvention Ratify File Sue
        ElectPresident ElectVicePresident Propose''',
    'lapse': '''Tick PresidentVacates VicePresidentVacates OfficerResigns
        ActingTick ActingExpires Resign TermExpires PresidentLeaves
        VicePresidentLeaves''',
}
ACTION_CATEGORY = {a: cat for cat, names in _ACTIONS.items() for a in names.split()}

_NODE_CATEGORY = {'Congress': 'legislative', 'Executive': 'executive',
                  'VicePresident': 'executive',
                  'Judiciary': 'judicial', 'People': 'people', 'States': 'people'}


def action_name(action, state):
    """TLC names an action after the disjunct of Next it came from, and
    cannot split one that quantifies over a variable. In Government that is
    \\E e \\in edges : Sue(e) \\/ Exercise(e); the edge that fired tells
    them apart."""
    if action == 'Next' and _is_edge(state.get('last', ())):
        return 'Sue' if state['last'].get('label') == 'Sue' else 'Exercise'
    return action


def category(action, state=None):
    if action is None:
        return 'init'
    if action in ('Exercise', 'Propose') and state and _is_edge(state.get('last', ())):
        # Government: an inert power, or an amendment proposed by Congress or
        # by a convention the States applied for - colour by who holds the edge.
        return _NODE_CATEGORY.get(state['last'].get('from'), 'other')
    return ACTION_CATEGORY.get(action, 'other')


def add_legend(dot, used):
    with dot.subgraph(name='cluster_legend') as s:
        s.attr(label='Who acted', fontname='Helvetica', fontsize='11', style='rounded')
        prev = None
        for cat, (colour, text) in CATEGORIES.items():
            if cat not in used:
                continue
            s.node(f'legend_{cat}', text, shape='box', style='filled', fillcolor=colour,
                   fontname='Helvetica', fontsize='10')
            if prev:
                s.edge(prev, f'legend_{cat}', style='invis')
            prev = f'legend_{cat}'


def html_escape(s):
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def clip(s, width=64):
    return s if len(s) <= width else s[:width - 1] + '…'


# ---------------------------------------------------------------------------
# Running TLC

def _base_config(module):
    """The module's own .cfg with only SPECIFICATION and CONSTANTS kept:
    the visualizers explore behaviour, they do not re-check properties."""
    keep, out = False, []
    with open(os.path.join(ROOT, f'{module}.cfg')) as f:
        for line in f:
            word = line.split('\\*')[0].strip().split(' ')[0]
            if word.isupper() and word:
                keep = word in {'SPECIFICATION', 'CONSTANT', 'CONSTANTS', 'INIT', 'NEXT'}
            if keep:
                out.append(line)
    return ''.join(out)


def _run_tlc(module, extra_defs, extra_cfg, args, workdir):
    if not os.path.exists(JAR):
        raise SystemExit(f'{JAR} not found: run ./install-tla.sh first')
    if not shutil.which('java'):
        raise SystemExit('java not found on PATH')
    viz = f'{module}_viz'
    with open(os.path.join(workdir, f'{viz}.tla'), 'w') as f:
        f.write(f'---- MODULE {viz} ----\nEXTENDS {module}, TLC\n{extra_defs}\n====\n')
    with open(os.path.join(workdir, f'{viz}.cfg'), 'w') as f:
        f.write(_base_config(module) + '\n' + extra_cfg + '\n')
    cmd = ['java', '-XX:+UseParallelGC', f'-DTLA-Library={ROOT}', '-jar', JAR,
           '-nowarning', '-metadir', os.path.join(workdir, 'meta'),
           *args, '-config', f'{viz}.cfg', f'{viz}.tla']
    proc = subprocess.run(cmd, cwd=workdir, capture_output=True, text=True)
    return proc.stdout + proc.stderr


def bfs_graph(module, depth, dot_out=None):
    """Explore every behaviour of up to `depth` steps.

    Returns (states, edges, dist): states maps a fingerprint to a parsed
    state, edges is a list of (src, dst, action), and dist maps each state
    to its distance in steps from an initial state. States one step beyond
    the bound are expanded too, so that edges between in-bound states are
    complete, and then dropped."""
    with tempfile.TemporaryDirectory() as work:
        dump = os.path.join(work, 'states.dot')
        out = _run_tlc(module,
                       f'VizWithinDepth == TLCGet("level") <= {depth + 1}',
                       'CONSTRAINT VizWithinDepth',
                       ['-workers', 'auto', '-dump', 'dot,actionlabels,colorize', dump],
                       work)
        if not os.path.exists(dump):
            raise SystemExit('TLC did not produce a state graph:\n' + out[-3000:])
        with open(dump) as f:
            content = f.read()
        if dot_out:
            shutil.copy(dump, dot_out)

    lab = r'"((?:[^"\\]|\\.)*)"'
    states, edges = {}, []
    init = set()
    for m in re.finditer(r'^(-?\d+) \[label=' + lab + r'(.*)$', content, re.M):
        nid, label, rest = m.groups()
        text = label.replace('\\n', '\n').replace('\\"', '"').replace('\\\\', '\\')
        if not text.startswith('/\\'):
            continue                     # a legend entry, not a state
        states[nid] = parse_state(text)
        if 'filled' in rest:
            init.add(nid)                # TLC fills the initial states
    for m in re.finditer(r'^(-?\d+) -> (-?\d+) \[label=' + lab, content, re.M):
        src, dst, action = m.groups()
        if src in states and dst in states:
            edges.append((src, dst, action_name(action, states[dst])))
    edges = list(dict.fromkeys(edges))   # one per (src, dst, action), not per vote count

    succ = {}
    for src, dst, action in edges:
        succ.setdefault(src, []).append(dst)
    dist = {n: 0 for n in init}
    queue = deque(init)
    while queue:
        n = queue.popleft()
        for m in succ.get(n, []):
            if m not in dist:
                dist[m] = dist[n] + 1
                queue.append(m)
    keep = {n for n, d in dist.items() if d <= depth}
    states = {n: s for n, s in states.items() if n in keep}
    edges = [e for e in edges if e[0] in keep and e[1] in keep]
    return states, edges, {n: dist[n] for n in keep}


def simulate(module, seed, steps):
    """One random behaviour of `steps` steps (fewer if it deadlocks).

    Returns a list of (action, state); the first action is None."""
    with tempfile.TemporaryDirectory() as work:
        out = _run_tlc(module,
                       f'VizShorterThan == TLCGet("level") < {steps}',
                       'INVARIANT VizShorterThan',
                       ['-simulate', '-depth', str(steps + 2), '-seed', str(seed),
                        '-workers', '1'],
                       work)
    blocks = re.split(r'^State \d+: ', out, flags=re.M)[1:]
    initial = re.search(r'violated by the initial state:\n', out)
    if not blocks and initial:            # steps == 0: TLC prints the state alone
        blocks = ['<Initial predicate>\n' + out[initial.end():]]
    if not blocks:
        raise SystemExit('TLC produced no behaviour:\n' + out[-3000:])
    trace = []
    for block in blocks:
        header, _, body = block.partition('\n')
        body = re.split(r'\n\s*\n', body)[0]
        name = re.match(r'<(\w+)', header)
        action = None if header.startswith('<Initial') or not name else name.group(1)
        state = parse_state(body)
        trace.append((action_name(action, state), state))
    return trace
