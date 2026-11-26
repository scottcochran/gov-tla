"""B6 — SenateRules.tla: the filibuster, cloture at three-fifths, the reconciliation clock and the nuclear option.

The picture of the floor (each measure's stage) and of the rules (each kind's cloture threshold, which only falls),
the README's two tables whole with the module header beside them, the mutation x property matrix read from the named
TLC results file with the seven- and five-Senator rows kept apart, the witnesses, the temporal rows, and the
theorems with their hypotheses read from the proof results file.

Build-time reads and checks (each raises corpus.CorpusError, so the generator prints ERROR):
  - corpus.RESULTS["SenateRules"]: both files parse; every row is as expected; no row is sampled;
  - the README summary table's SenateRules counts equal the counts read from the results files;
  - every digest on the results files' Modules: and Rows: lines equals the file in the tree now, and the proof
    results file names the TLC results file by its current sha256;
  - README § SenateRules.tla: its two tables, the seven/five sentence, What it shows, the proof paragraph and
    Abstracted are read from the README and must have the expected shape;
  - the module header's PROPERTIES, MUTATIONS and WITNESSES entries are read from specs/SenateRules.tla; the
    witnesses it names must be the witness rows of the results file;
  - the threshold operators drawn as arithmetic must be defined in the module as drawn.
"""
import re

from lib import Canvas, STATUS, text_width
import corpus as C

ID, SLUG = "B6", "senate-rules"

W = 3400
S = 14
MOD = "SenateRules"
SPEC = "specs/SenateRules.tla"
PROOF = "specs/SenateRules_proof.tla"
ROWS = "rows/SenateRules-rows.txt"
CFG = "specs/SenateRules.cfg"
EARLIER = "results/SenateRules-results-2026.11.19.txt"   # the earlier TLC file of the same date, compared only


# ---------------------------------------------------------------------------------------------- layout helpers
def row_cards(c, x, y, w, gap, specs, size=S):
    n = len(specs)
    cw = (w - (n - 1) * gap) / n
    h = max(c.card(0, 0, cw, t, b, draw=False, size=size, status=k.get("status")) for t, b, _, k in specs)
    for i, (t, b, acc, k) in enumerate(specs):
        c.card(x + i * (cw + gap), y, cw, t, b, accent=acc, h=h, size=size, **k)
    return h


def band(c, x, y, title, accent="ink", status=None, extra=""):
    c.text(x, y + 22, title, 22, accent, bold=True)
    if status:
        c.status(x + text_width(title, 22, True) + 20, y + 4, status, extra)
    return y + 54


def status_strip(c, x0, x1, y, items):
    c.text(x0, y + 15, "Status", 15, "faint", bold=True)
    px0 = x0 + 80
    px = px0
    for lab, pills in items:
        lw = text_width(lab, 13.5, True) + 8
        pws = []
        for key, extra in pills:
            if isinstance(key, tuple):
                pws.append(text_width(key[0], 11.5, True) + 18)
            else:
                pws.append(text_width(STATUS[key][0] + (f" · {extra}" if extra else ""), 11.5, True) + 18)
        need = lw + sum(pws) + 10 * (len(pws) - 1)
        if px + need > x1:
            px = px0
            y += 34
        c.text(px, y + 15, lab, 13.5, "ink", bold=True)
        px += lw
        for key, extra in pills:
            if isinstance(key, tuple):
                px += c.pill(px, y, key[0], key[1], 11.5, dash=key[2]) + 10
            else:
                px += c.status(px, y, key, extra) + 10
        px += 26
    return y + 42


def n(x):
    return f"{x:,}"


def need(cond, rel, what):
    if not cond:
        raise C.CorpusError(f"{rel}: {what}")


# ---------------------------------------------------------------------------------------------- build-time reads
def readme_section():
    lines = C.read("README.md").splitlines()
    head = "### `SenateRules.tla` — the filibuster"
    need(head in lines, "README.md", f"no heading {head!r}")
    i = lines.index(head)
    j = next((k for k in range(i + 1, len(lines)) if lines[k].startswith("## ") or lines[k].startswith("### ")),
             None)
    need(j, "README.md", "the SenateRules.tla section has no end")
    return lines[i + 1:j]


def md_table(sec, header, ncols):
    need(header in sec, "README.md", f"§ SenateRules.tla: no table headed {header!r}")
    i = sec.index(header)
    need(sec[i + 1].startswith("|---"), "README.md", f"table {header!r} has no rule line")
    rows = []
    for ln in sec[i + 2:]:
        if not ln.startswith("|"):
            break
        cells = [x.strip() for x in ln.strip().strip("|").split("|")]
        need(len(cells) == ncols, "README.md", f"table row does not have {ncols} cells: {ln!r}")
        rows.append(cells)
    need(rows, "README.md", f"table {header!r} is empty")
    return rows


def paragraphs(sec):
    """Blank-line-separated blocks of the section, each joined into one line; bullets kept as separate items."""
    out, cur = [], []
    for ln in sec + [""]:
        if not ln.strip():
            if cur:
                out.append(cur)
            cur = []
        else:
            cur.append(ln)
    return out


def readme_parts(sec):
    blocks = paragraphs(sec)
    parts = {}
    for b in blocks:
        text = " ".join(x.strip() for x in b)
        if text.startswith("With seven Senators"):
            parts["seven"] = text
        elif text.startswith("The proof ("):
            parts["proof"] = text
        elif text.startswith("Abstracted:"):
            parts["abstracted"] = text
        elif text.startswith("Not constitutional text"):
            parts["opening"] = text
        elif b[0].startswith("- ") and "shows" in parts and "bullets" not in parts:
            items, cur = [], []
            for ln in b:
                if ln.startswith("- "):
                    if cur:
                        items.append(" ".join(cur))
                    cur = [ln[2:].strip()]
                else:
                    need(ln.startswith("  "), "README.md", f"What it shows: bullet line not indented: {ln!r}")
                    cur.append(ln.strip())
            items.append(" ".join(cur))
            parts["bullets"] = items
        elif text == "What it shows:":
            parts["shows"] = True
    for k in ("seven", "proof", "abstracted", "opening", "bullets"):
        need(k in parts, "README.md", f"§ SenateRules.tla: no {k!r} paragraph of the expected shape")
    need(len(parts["bullets"]) == 2, "README.md", "§ SenateRules.tla, What it shows: not two bullets")
    return parts


def header_lines():
    """The module header comment's content lines (between the '(****' lines), '(*' and '*)' removed."""
    lines = C.read(SPEC).splitlines()
    need(lines[1].startswith("(****") and lines[0].startswith("----"), SPEC, "header comment not at line 2")
    end = next((i for i in range(2, len(lines)) if lines[i].startswith("(****")), None)
    need(end, SPEC, "header comment not closed")
    out = []
    for ln in lines[2:end]:
        need(ln.startswith("(*") and ln.rstrip().endswith("*)"), SPEC, f"header line not '(* ... *)': {ln!r}")
        out.append(ln.rstrip()[2:-2].rstrip())
    return out


def join(parts):
    s = ""
    for p in parts:
        p = p.strip()
        if s.endswith("-") and p[:1].isalpha():
            s += p
        else:
            s += (" " if s else "") + p
    return re.sub(r"\s+", " ", s)


def header_section(hl, start, raw=False):
    """Entries of a header section (PROPERTIES, MUTATIONS, WITNESSES): {names: text}, in order."""
    i = next((k for k, ln in enumerate(hl) if ln.startswith(" " + start)), None)
    need(i is not None, SPEC, f"header has no {start} section")
    entries, cur = [], None
    for ln in hl[i + 1:]:
        if not ln.strip():
            break
        m = re.match(r"^   (\w+(?:, \w+)*)\s+(\S.*)$", ln)
        if m and not ln.startswith("    "):
            cur = [m.group(1), [m.group(2)]]
            entries.append(cur)
        elif re.match(r"^\s{6,}\S", ln) and cur:
            cur[1].append(ln)
        elif not entries:
            continue          # the section heading's own continuation line
        else:
            raise C.CorpusError(f"{SPEC}: header {start} line does not parse: {ln!r}")
    need(entries, SPEC, f"header {start} section has no entries")
    if raw:
        return [(name, body[0]) for name, body in entries]
    return [(name, join(body)) for name, body in entries]


def header_para(hl, start):
    i = next((k for k, ln in enumerate(hl) if ln.startswith(" " + start)), None)
    need(i is not None, SPEC, f"header has no {start!r} paragraph")
    body = []
    for ln in hl[i:]:
        if not ln.strip():
            break
        body.append(ln)
    return join(body)


def senators(res, row):
    over = [o for o in row["overrides"] if o.startswith("Senators=")]
    if over:
        s = over[0].split("=", 1)[1]
    else:
        m = re.search(r"Senators = (\{[^}]*\})", res["constants"])
        need(m, res["_rel"], "no Senators in Constants: line")
        s = m.group(1)
    return len([x for x in s.strip("{}").split(",") if x.strip()])


def read_all():
    tf, pf = C.RESULTS[MOD]
    t, p = C.tlc_results(tf), C.proof_results(pf)
    t["_rel"] = tf
    need(t["as_expected"] == t["total"] and not t["not"] and not t["error"], tf, "not every row is as expected")
    need(not any(r["kind"] == "SIMULATE" or r["sampled"] for r in t["rows"]), tf,
         "a sampled row: this diagram draws none")
    for res, rel in ((t, tf), (p, pf)):
        for f, digest in res["modules"].items():
            need(C.sha256(f"specs/{f}") == digest, rel, f"{f} has moved since it was checked")
    need(C.sha256(t["rows_file"]) == t["rows_sha"] and t["rows_file"] == ROWS, tf, "the row list has moved")
    need(p["tlc_file"] == tf and C.sha256(tf) == p["tlc_sha"], pf, f"does not name {tf} at its current digest")
    summ = C.readme_summary()[MOD]
    read = dict(rows=t["total"], mutations=len(C.mutations(t)), witnesses=len(C.witnesses(t)),
                obligations=p["obligations"])
    for k, v in read.items():
        need(summ[k] == v, "README.md", f"summary table: SenateRules {k} is {summ[k]}, the results files give {v}")
    return tf, pf, t, p, summ


def check_operators():
    """The arithmetic the picture draws must be the module's."""
    spec = C.read(SPEC)
    for d in ("Majority(n)       == 2 * n > N", "ThreeFifths(n)    == 5 * n >= 3 * N",
              "TwoThirdsOf(n, p) == 3 * n >= 2 * p", "/\\ Majority(present)"):
        need(d in spec, SPEC, f"definition drawn as arithmetic not found: {d!r}")


def compare_earlier(tf, t):
    """The earlier TLC results file of the same date, beside the named one: what differs."""
    e = C.tlc_results(EARLIER)
    lines_e = C.read(EARLIER).splitlines()
    lines_t = C.read(tf).splitlines()
    need(len(lines_e) == len(lines_t), EARLIER, "not the same number of lines as the named file")
    diff = [i + 1 for i, (a, b) in enumerate(zip(lines_e, lines_t)) if a != b]
    rows_same = [(r["name"], r["verdict"], r["states"]) for r in e["rows"]] == \
                [(r["name"], r["verdict"], r["states"]) for r in t["rows"]]
    spec_now = C.sha256(SPEC)
    return dict(e=e, diff=diff, rows_same=rows_same,
                e_spec_current=e["modules"].get("SenateRules.tla") == spec_now,
                e_rows_current=e["rows_sha"] == C.sha256(ROWS))


# ---------------------------------------------------------------------------------------------- the diagram
def build():
    tf, pf, T, P, summ = read_all()
    check_operators()
    sec = readme_section()
    prov = md_table(sec, "| Rule | Where |", 2)
    mtab = md_table(sec, "| Mutation | Removes | Earlier law | Breaks |", 4)
    rp = readme_parts(sec)
    hl = header_lines()
    hprops = header_section(hl, "PROPERTIES")
    hmuts = dict(header_section(hl, "MUTATIONS"))
    hwits = header_section(hl, "WITNESSES")
    h_live = header_para(hl, "LIVENESS.")
    h_dead = header_para(hl, "DEADLOCK.")
    h_abs = header_para(hl, "ABSTRACTED:")
    earlier = compare_earlier(tf, T)
    rows_txt = C.read(ROWS).splitlines()
    const_note = join([ln[1:] for ln in rows_txt if ln.startswith("# Constants:") or
                       (ln.startswith("# bill, one nomination"))])
    need(const_note.startswith(" Constants: seven Senators") or const_note.startswith("Constants: seven Senators"),
         ROWS, "the Constants: comment is not where expected")
    const_note = const_note.strip()

    muts = C.mutations(T)
    need(set(muts) == set(hmuts) == {r[0].strip("`") for r in mtab}, SPEC,
         f"the mutations of the results {muts}, the header {list(hmuts)} and the README table differ")
    wit_rows = C.witnesses(T)

    c = Canvas(ID, "`SenateRules.tla`: the filibuster — cloture at three-fifths, the reconciliation clock and the "
               "nuclear option — and why a bare majority need not prevail",
               "Not constitutional text: the Senate's own rules under Art. I §5 cl. 2, layered on simple-majority "
               "passage, as of 1975 (README § `SenateRules.tla`). Each measure moves from debate to a vote; "
               "debate closes by cloture at three-fifths or, for a reconciliation bill, by the statutory clock; the "
               "threshold falls only by amending the rule on two-thirds or by a majority's precedent (the nuclear "
               f"option). **TLC checks {T['total']} rows, every one as expected, and TLAPS proves the five safety "
               f"properties for a Senate of any size in {n(P['obligations'])} obligations.** The filibuster is drawn "
               "as the failure of a leads-to: **`MajorityPrevails` is a COUNTEREXAMPLE under `FairSpec` and holds "
               "under `NuclearSpec`; it and the other temporal rows are checked, not proved.** This models the "
               "rules' procedure: it is an exercise, not law (README, opening).",
               W, "README.md (opening; § How the specs are written and checked: the words, the summary table, What "
               "is not proved; § SenateRules.tla: its opening, the rule table, the mutation table, the seven/five "
               "sentence, What it shows, the proof paragraph, Abstracted; § Running, scripts/tlc_rows.py's letter "
               "suffix); specs/SenateRules.tla (header: PROPERTIES, MUTATIONS, WITNESSES, LIVENESS, DEADLOCK, "
               "ABSTRACTED; Majority, ThreeFifths, TwoThirdsOf, Meets, ClotureCarries, TimeLimited, PassCarries, "
               "RulesCarry, Proceed, InvokeCloture, DebateExpires, Pass, Reject, Nuclear, AmendRule, Safety, the "
               "Never… witnesses, Backed, MajorityPrevails, ReconciliationPrevails, FloorVotes, ClockRuns, "
               "MajorityGoesNuclear, FairSpec, SpecNoClock, NuclearSpec, NoBehaviour); specs/SenateRules.cfg; "
               "specs/SenateRules_proof.tla (header: THEOREMS, ASSUMPTIONS, INDUCTIVE STRENGTHENING, NOT PROVED; "
               f"ThresholdOnlyFalls; the Mut…Admits lemmas); {ROWS} (header); {tf}; {pf}; {EARLIER} (compared "
               "only); specs/ and rows/ digests compared at build time")
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    live_rows = [r for r in T["rows"] if r["kind"] == "PROPERTY"]
    live_props = []
    for r in live_rows:
        if r["prop"] not in live_props:
            live_props.append(r["prop"])
    items = [(f"{MOD}.tla", [("checked", f"{T['total']} rows, all as expected"),
                             ("proved", f"{n(P['obligations'])} obligations, {len(P['theorems'])} theorems")]),
             ("Mutations", [((f"{len(muts)} mutations", "violet", None), "")]),
             ("Witnesses", [("checked", f"{len(wit_rows)}, each violated as required")]),
             ("Temporal rows", [("notproved", p) for p in live_props]),
             ("Sampled rows", [(("none", "grey", "4 3"), "")]),
             ("Abstracted (README § Abstracted)", [("abstracted", "who the Senators are, the thirty hours, "
                                                    "amendments, holds, the Byrd rule …")])]
    y = status_strip(c, X0, X1, y, items)
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row list. "
                "**Proved** means TLAPS discharged every obligation for every value of the constants the module's "
                "named assumptions admit. **Sampled** means random simulation found no error, and is never cited "
                "as a check; this module has no sampled row. \"None of these is a claim about law or practice\" "
                "(README § How the specs are written and checked).", 14.5, "muted") + 34

    # ---- band 1: the picture
    y = band(c, X0, y, "The mechanism: each measure's stage on the floor, and each kind's cloture threshold, which "
             "only falls (`SenateRules.tla` `Next`)")
    gP, gD, gC = 250, 400, 330
    wP, wD, wC, wR = 280, 470, 290, 300
    FX = X0
    xP = FX + 40
    xD = xP + wP + gP
    xC = xD + wD + gD
    xR = xC + wC + gC
    FL_W = xR + wR + 40 - FX
    stages = {
        "P": ("`\"Pending\"`", ["Every measure in `Init`, with `support[m] = 0`.", "`Measures` = `Legislation`, "
              "`Nominations` and `Reconciliations` (`KindsDisjoint`)."], "teal"),
        "D": ("`\"Debate\"`", ["`support[m]` is fixed by `Proceed(m, n)`: \"no Senator changes sides\" (header "
              "ABSTRACTED).", "`Backed(m)`: in Debate with `Majority(support[m])`, the premise of "
              "`MajorityPrevails`.", "[[red|The filibuster]]: under `FairSpec`, \"a bill with a majority short of "
              "three-fifths is debated forever\" (header LIVENESS)."], "teal"),
        "C": ("`\"Closed\"`", ["Debate is over, by cloture or by the clock.", "`ClosedOnThreeFifths` reads "
              "Closed, Passed and Rejected together."], "teal"),
        "A": ("`\"Passed\"`", ["The goal of `MajorityPrevails` and `ReconciliationPrevails`.", "`PassedShort`: "
              "passed short of three-fifths (the witnesses)."], "teal"),
        "R": ("`\"Rejected\"`", ["Closed without a majority.", "`NeverRejected` is violated: reached."], "teal"),
    }
    hs = max(c.card(0, 0, w, stages[k][0], stages[k][1], draw=False, size=S) for k, w in
             (("P", wP), ("D", wD), ("C", wC)))
    hr = max(c.card(0, 0, wR, stages[k][0], stages[k][1], draw=False, size=S) for k in ("A", "R"))
    vgap = 110
    col_h = 2 * hr + vgap
    ftop = y + 24
    loop_room = 96
    yc = max(ftop + 40 + col_h / 2, ftop + 40 + loop_room + hs / 2)
    f_bottom = max(yc + col_h / 2, yc + hs / 2) + 40
    c.region(FX, ftop, FL_W, f_bottom - ftop, "The floor: `stage[m]` for each measure (`Stages`)", "teal")
    ys = yc - hs / 2
    yA = yc - col_h / 2
    yR = yA + hr + vgap
    for k, x, w in (("P", xP, wP), ("D", xD, wD), ("C", xC, wC)):
        c.card(x, ys, w, stages[k][0], stages[k][1], accent=stages[k][2], h=hs, size=S)
    c.card(xR, yA, wR, stages["A"][0], stages["A"][1], accent="teal", h=hr, size=S)
    c.card(xR, yR, wR, stages["R"][0], stages["R"][1], accent="teal", h=hr, size=S)
    # arrows on the floor, numbered: the key below explains each
    c.arrow([(xP + wP + 6, yc), (xD - 6, yc)], "teal", label="1 `Proceed(m, n)`", lpos=0.5)
    c.arrow([(xD + wD + 6, yc - 34), (xC - 6, yc - 34)], "teal", label="2 `InvokeCloture(m)`", lpos=0.5)
    c.arrow([(xD + wD + 6, yc + 34), (xC - 6, yc + 34)], "teal", label="3 `DebateExpires(m)`: the clock",
            lpos=0.5)
    xm = xC + wC + gC / 2
    c.arrow([(xC + wC + 6, yc - 34), (xm, yc - 34), (xm, yA + hr / 2), (xR - 6, yA + hr / 2)], "teal",
            label="4 `Pass(m)`", lpos=0.86)
    c.arrow([(xC + wC + 6, yc + 34), (xm, yc + 34), (xm, yR + hr / 2), (xR - 6, yR + hr / 2)], "teal",
            label="5 `Reject(m)`", lpos=0.86)
    # the filibuster: debate that is never closed
    lx0, lx1 = xD + wD * 0.22, xD + wD * 0.78
    c.arrow([(lx0, ys - 4), (lx0, ys - 62), (lx1, ys - 62), (lx1, ys - 6)], "red", dash="7 5",
            label="4 of 7 under `FairSpec`: no step is forced", lpos=0.5)

    # the ladder of counts, right of the floor
    LX = FX + FL_W + 40
    LW = X1 - LX
    c.region(LX, ftop, LW, f_bottom - ftop, "Votes at the rows' constants (the diagram's arithmetic from the "
             "operators)", "teal")
    ly = ftop + 30
    ly += c.para(LX + 22, ly, LW - 44, "`Majority(n) == 2 * n > N`; `ThreeFifths(n) == 5 * n >= 3 * N` (\"of the "
                 "Senators duly chosen and sworn\"); `TwoThirdsOf(n, p) == 3 * n >= 2 * p` (\"of those present and "
                 "voting\"), with a quorum, `Majority(present)`, present.", 13.5, "ink") + 10
    cw_, ch_ = 50, 28
    lab_w = 205
    ladders = [
        (7, [("`Majority(n)`", lambda k: 2 * k > 7), ("`ThreeFifths(n)`", lambda k: 5 * k >= 21),
             ("`TwoThirdsOf(n, 4)`", lambda k: k <= 4 and 3 * k >= 8),
             ("`TwoThirdsOf(n, 7)`", lambda k: 3 * k >= 14)]),
        (5, [("`Majority(n)`", lambda k: 2 * k > 5), ("`ThreeFifths(n)`", lambda k: 5 * k >= 15)]),
    ]
    for N_, rows_ in ladders:
        c.text(LX + 22, ly + 16, f"**N = {N_}**" + (" (the rows' default)" if N_ == 7 else
                                                    " (rows c5-safety, pq5-*)"), 14, "ink")
        ly += 28
        for lab, pred in rows_:
            c.text(LX + 22, ly + 19, lab, 13.5, "ink")
            least = None
            for k in range(N_ + 1):
                ok = pred(k)
                if ok and least is None:
                    least = k
                c.rect(LX + 22 + lab_w + k * cw_, ly, cw_ - 6, ch_, "teal" if ok else "grey", tint=ok, rx=4,
                       sw=1.2)
                c.text(LX + 22 + lab_w + k * cw_ + (cw_ - 6) / 2, ly + 19, str(k), 13, "ink" if ok else "faint",
                       anchor="middle")
            most = max(k for k in range(N_ + 1) if pred(k))
            rng = f"n ≥ {least}" if most == N_ else f"{least} ≤ n ≤ {most}"
            c.text(LX + 22 + lab_w + (N_ + 1) * cw_ + 6, ly + 19, rng, 13.5, "teal", bold=True)
            ly += ch_ + 8
        ly += 8
    ly += c.para(LX + 22, ly, LW - 44, "README: \"" + rp["seven"] + "\" `TwoThirdsOf(n, 4)`: four present, the "
                 "least quorum of seven; `AmendRule` needs `ayes <= present`.", 13.5, "muted")
    need(ly < f_bottom - 10, "B6 layout", "the ladder does not fit beside the floor")

    # the rules and the flags, below
    y = f_bottom + 50
    RW = 1560
    rtop = y
    w35, wM = 380, 380
    x35 = X0 + 40
    xM = X0 + RW - 40 - wM
    rules_cards = {
        "3": ("`\"ThreeFifths\"`", ["`Init`: \"the rules as of 1975\" for both `Kinds`, `\"Legislation\"` and "
              "`\"Nomination\"`.", "A reconciliation bill has no threshold: \"never needed, not modelled\" "
              "(header ABSTRACTED)."], "teal"),
        "M": ("`\"Majority\"`", ["`changedBy[k]` records the route: `\"Precedent\"` or `\"Rules\"`.", "Never "
              "raised again: \"raising the threshold again (it only falls)\" (header ABSTRACTED)."], "teal"),
    }
    hrc = max(c.card(0, 0, w35, t, b, draw=False, size=S) for t, b, _ in rules_cards.values())
    r_cy = rtop + 50 + hrc / 2 + 10
    r_bottom = r_cy + hrc / 2 + 50
    c.region(X0, rtop, RW, r_bottom - rtop, "The rules: `cloture[k]` for each kind k, and how it fell "
             "(`changedBy[k]`)", "teal")
    c.card(x35, r_cy - hrc / 2, w35, *rules_cards["3"][:2], accent="teal", h=hrc, size=S)
    c.card(xM, r_cy - hrc / 2, wM, *rules_cards["M"][:2], accent="teal", h=hrc, size=S)
    a0, a1 = x35 + w35 + 6, xM - 6
    dcx = xD + wD / 2
    need(a0 + 80 < dcx < a1 - 80, "B6 layout", "the Debate card is not above the Nuclear arrow")
    c.arrow([(a0, r_cy - 30), (a1, r_cy - 30)], "teal", label="6 `Nuclear(m)`: a precedent",
            lpos=(dcx - a0) / (a1 - a0))
    c.arrow([(a0, r_cy + 34), (a1, r_cy + 34)], "teal", label="7 `AmendRule(k, ayes, present)`: a rule", lpos=0.5)
    # Nuclear is taken during debate on m: a connector from the Debate card to the arrow's label
    c.line(dcx, ys + hs + 4, dcx, r_cy - 30 - 14, "teal", sw=1.6, dash="3 4")
    c.label(dcx, (ys + hs + r_cy - 30) / 2 + 20, "during debate on m, a majority backing m", "teal", 12.5)

    # the flags: one per property, set by one action each
    FXX = X0 + RW + 40
    FWW = X1 - FXX
    setters = {"ClotureThreshold": ("shortCloture", "2"), "DebateEndsByCloture": ("debateCut", "3"),
               "MajorityFloor": ("minorityPassage", "4"), "RulesByTwoThirds": ("shortRulesChange", "7"),
               "ClosedOnThreeFifths": (None, "2, 3, 6, 7")}
    need([nm for nm, _ in hprops] == list(setters), SPEC, f"header PROPERTIES are {[x for x, _ in hprops]}")
    fspecs = []
    hraw = dict(header_section(hl, "PROPERTIES", raw=True))
    for nm, txt in hprops:
        flag, by = setters[nm]
        title = f"`{nm}`" + (f" · flag `{flag}`" if flag else " · not a flag")
        # an entry opens with its citation (Rule ..., Art. ...) where it has one, two spaces before the text
        cm = re.match(r"^((?:Rule|Art\.) .*?)(?:\s{2,}|$)", hraw[nm])
        quote = f"{cm.group(1)}: \"{txt[len(cm.group(1)) + 1:]}\"" if cm else f"\"{txt}\""
        need(not cm or txt.startswith(cm.group(1) + " "), SPEC, f"PROPERTIES {nm}: citation does not parse")
        fspecs.append((title, [f"Header: {quote}", (f"Set only by step {by}, never cleared." if flag else
                               "A state predicate. Proof module header, in effect: a measure leaves Debate only by step 2 or "
                               "3, and steps 6 and 7 only lower a threshold.")],
                       "teal", {}))
    fh = max(c.card(0, 0, (FWW - 4 * 16) / 5, t, b, draw=False, size=13.5) for t, b, _, _ in fspecs)
    c.region(FXX, rtop, FWW, max(r_bottom - rtop, fh + 56), "The five safety properties (header PROPERTIES), "
             "each with what can break it", "teal")
    fbot = rtop + max(r_bottom - rtop, fh + 56)
    row_cards(c, FXX + 16, rtop + 30, FWW - 32, 16, fspecs, size=13.5)
    y = max(r_bottom, fbot) + 30

    # the key: one card per numbered step
    key = [
        ("1 `Proceed(m, n)`", ["\"A measure is taken up, with the support it will have throughout\" (comment).",
         "Guard: `stage[m] = \"Pending\"`; any `n` in `Counts` = `0..N`.", "Abstracted: \"the motion to proceed "
         "and its own cloture (Proceed is one unconditional step)\"."], "teal"),
        ("2 `InvokeCloture(m)`", ["Rule XXII: cloture by three-fifths (README rule table).", "Guard: in Debate, "
         "not in `Reconciliations`, `ClotureCarries(m)`: `Meets(cloture[Kind(m)], support[m])`.", "Raises "
         "`shortCloture` if the votes are short of the threshold in force.",
         "[[violet|M_PREVIOUS_QUESTION]]: `Majority(support[m])` carries cloture."], "teal"),
        ("3 `DebateExpires(m)`", ["Budget Act of 1974 §310(e): reconciliation debate limited by statute.",
         "Guard: in Debate, `TimeLimited(m)`: `m \\in Reconciliations`.", "Raises `debateCut` if `m` is not a "
         "reconciliation bill.", "[[violet|M_TIME_LIMIT]]: every measure's debate runs out."], "teal"),
        ("4 `Pass(m)`", ["Passage (or confirmation) by a majority.", "Guard: Closed, `PassCarries(m)`: "
         "`Majority(support[m])`.", "Raises `minorityPassage` if `m` lacks a majority.",
         "[[violet|M_NO_MAJORITY]]: a closed measure passes on any count."], "teal"),
        ("5 `Reject(m)`", ["Guard: Closed, `~Majority(support[m])`.", "Raises no flag; no mutation touches it."],
         "teal"),
        ("6 `Nuclear(m)`", ["Precedents of 2013 and 2017: \"a point of order … the chair rules against it, and "
         "the majority that supports m overturns the ruling. A precedent, not a rule\" (comment).", "Guard: in "
         "Debate, not reconciliation, `cloture[Kind(m)] = \"ThreeFifths\"`, `Majority(support[m])`.",
         "Both precedents \"are both the one step Nuclear(m) for a nomination; the module does not split them\" "
         "(header). No mutation touches it."], "teal"),
        ("7 `AmendRule(k, ayes, present)`", ["Rule XXII cl. 2, Rule V cl. 2: two-thirds present and voting.",
         "Guard: `cloture[k] = \"ThreeFifths\"`, `Majority(present)`, `ayes <= present`, `RulesCarry`: "
         "`TwoThirdsOf(ayes, present)`.", "Raises `shortRulesChange` if short of two-thirds.",
         "[[violet|M_CONSTITUTIONAL_OPTION]]: `Majority(ayes)` carries it."], "teal"),
    ]
    c.text(X0, y + 16, "Key to the numbered steps: each step's guard, the flag it raises, and the mutation that "
           "removes its check (`SenateRules.tla`, the actions and the checks each mutation removes)", 16, "ink",
           bold=True)
    y += 30
    y += row_cards(c, X0, y, WW, 18, [(t, b, a, {}) for t, b, a in key], size=13.5) + 50

    # ---- band 2: the rule table, whole, and Abstracted
    y = band(c, X0, y, "The README's rule table, every row and column (README § `SenateRules.tla`)")
    tw = 1700
    y_tab = y
    th = c.table(X0, y, [("Rule", 1040), ("Where", tw - 1040)], [list(r) for r in prov], size=14)
    cx = X0 + tw + 30
    c.card(cx, y_tab, X1 - cx, "Not constitutional text (README § `SenateRules.tla`, opening; header)",
           ["\"" + rp["opening"] + "\"", "`SenateRules.cfg`, for ad hoc runs: `SPECIFICATION Spec`, seven "
            "Senators, one bill, one nomination, one reconciliation bill, `INVARIANTS TypeOK Safety`; \"The checked "
            f"results come from {ROWS}\"."], "blue", h=th, size=14)
    y += th + 30
    abs_txt = rp["abstracted"]
    y += row_cards(c, X0, y, WW, 30, [
        ("README § `SenateRules.tla`, Abstracted", ["\"" + abs_txt[len("Abstracted: "):] + "\""], "grey",
         {"status": "abstracted"}),
        ("The module header, ABSTRACTED", ["\"" + h_abs[len("ABSTRACTED: "):] + "\""], "grey",
         {"status": "abstracted"}),
        ("The two lists compared (the diagram's comparison)", ["The header names four things the README's list "
         "does not: the motion to proceed's \"own cloture\", \"what may be reconciled\", \"cloture on a "
         "reconciliation bill (never needed, not modelled)\" and \"the House\".", "Everything the README lists "
         "the header lists too. Neither list contradicts the other."], "grey", {}),
    ], size=14) + 50

    # ---- band 3: mutations, whole, then the matrix
    y = band(c, X0, y, "The README's mutation table, every row and column, beside the module header and the "
             f"verdicts read from `{tf[8:]}`")
    # results by (mut, prop, senators)
    cells = {}
    for r in T["rows"]:
        if r["kind"] in ("INVARIANT", "DEADLOCK") and r["spec"] == "Spec" and not r["prop"].startswith("Never"):
            key_ = (r["mut"], r["prop"] if r["kind"] == "INVARIANT" else "DEADLOCK " + r["prop"], senators(T, r))
            need(key_ not in cells, tf, f"two rows for {key_}")
            cells[key_] = r
    props = []
    for (m_, p_, s_) in cells:
        if p_ not in props:
            props.append(p_)
    sizes = sorted({s_ for (_, _, s_) in cells}, reverse=True)
    need(sizes == [7, 5], tf, f"Senate sizes {sizes}, not [7, 5]")

    def breaks_at(mut, s_):
        return [p_ for p_ in props if (mut, p_, s_) in cells and cells[(mut, p_, s_)]["verdict"] == "COUNTEREXAMPLE"]

    def names(s_):
        return re.findall(r"`(\w+)`", s_)

    def hdr_breaks(mut):
        m = re.search(r"Breaks (\w+(?:(?:,| and) \w+)*)\.", hmuts[mut])
        need(m, SPEC, f"header MUTATIONS: no 'Breaks ...' for {mut}")
        return re.split(r", | and ", m.group(1))

    disagreements = []
    rows = []
    for r in mtab:
        mut = r[0].strip("`")
        rb, hb = names(r[3]), hdr_breaks(mut)
        t7, t5 = breaks_at(mut, 7), breaks_at(mut, 5)
        agree = set(rb) == set(hb) == set(t7)
        if not agree:
            disagreements.append(mut)
        five = ("no row" if not any((mut, p_, 5) in cells for p_ in props) else
                (", ".join(t5) if t5 else "none: [[teal|HOLDS]] on " +
                 ", ".join(f"`{p_}`" for p_ in props if (mut, p_, 5) in cells)))
        rows.append({"cells": [r[0].strip("`"), r[1], r[2], r[3], "\"" + hmuts[mut] + "\"",
                               ", ".join(f"[[red|{x}]]" for x in t7) or "none", five,
                               "[[teal|all three agree]]" if agree else "[[red|disagree]]"],
                     "accent": None if agree else "red"})
        if rows[-1]["accent"] is None:
            rows[-1] = rows[-1]["cells"]
    cols = [("Mutation", 300, {"mono": True, "bold": True}), ("Removes", 330), ("Earlier law", 360),
            ("Breaks", 330), ("Module header, MUTATIONS (the whole entry)", 900),
            ("COUNTEREXAMPLE at 7 Senators (results)", 330), ("At 5 Senators (results)", 380)]
    cols.append(("README, header and results (the diagram's check)", WW - sum(x[1] for x in cols)))
    y += c.table(X0, y, cols, rows, size=13.5, anchor="mutations") + 24
    y += c.para(X0, y, WW, "README § `SenateRules.tla`: \"" + rp["seven"] + "\" The rows header expects it: \"With "
                "five Senators, where a majority is three-fifths, M_PREVIOUS_QUESTION HOLDS on ClotureThreshold and "
                "ClosedOnThreeFifths\" (`" + ROWS + "`).", 13.5, "muted") + 40

    y = band(c, X0, y, f"Every mutation by every property, read from `{tf[8:]}` at build time: the seven- and "
             "five-Senator rows apart")
    row_keys = [(m_, s_) for s_ in sizes for m_ in ["none"] + muts if any((m_, p_, s_) in cells for p_ in props)]
    expect_ce = {r[0].strip("`"): set(names(r[3])) for r in mtab}
    mrows = []
    for m_, s_ in row_keys:
        cl = [f"{m_} · {s_} Senators"]
        bad = False
        for p_ in props:
            r = cells.get((m_, p_, s_))
            if r is None:
                cl.append("")
                continue
            v = r["verdict"]
            want = "DEADLOCK" if p_.startswith("DEADLOCK") else (
                "COUNTEREXAMPLE" if (s_ == 7 and p_ in expect_ce.get(m_, set())) else "HOLDS")
            acc = {"HOLDS": "teal", "COUNTEREXAMPLE": "red", "DEADLOCK": "teal"}[v]
            txt = f"[[{acc}|{v}]] · {n(r['states'])}"
            if v != want:
                bad = True
                txt += " · [[red|README disagrees]]"
            cl.append(txt)
        if bad:
            disagreements.append(f"{m_}@{s_}")
        mrows.append({"cells": cl, "accent": "red"} if bad else
                     ({"cells": cl, "accent": "grey"} if s_ == 5 else cl))
    first = 330
    pw = (WW - first) / len(props)
    mcols = [("Mut · Senate", first, {"mono": True, "bold": True})] + \
            [(p_.replace("DEADLOCK ", "") + (" (deadlock check on)" if p_.startswith("DEADLOCK") else ""), pw)
             for p_ in props]
    y += c.table(X0, y, mcols, mrows, size=13.5, anchor="matrix") + 24
    y += c.para(X0, y, WW, "Each cell: the verdict and the distinct states the results file records. Empty: no row runs. Grey rows: five Senators "
                "(`Senators={s1,s2,s3,s4,s5}` on the row). A cell would be marked red where its verdict differs "
                "from the README's Breaks cell; " + ("none is." if not disagreements else
                                                   "see the red rows.") + " \"" + h_dead + "\" (header).",
                13.5, "muted") + 40

    # ---- band 4: witnesses
    y = band(c, X0, y, "Witnesses: each `Never…` property must be violated unmutated, so what it forbids is "
             "reachable", status="checked", extra="existential, never proved")
    hw = {}
    for names_, txt in hwits:
        for nm in [x.strip() for x in names_.split(",")]:
            hw[nm] = txt
    need(set(hw) == {r["prop"] for r in wit_rows}, SPEC,
         f"header WITNESSES {sorted(hw)} are not the witness rows {[r['prop'] for r in wit_rows]}")
    shows = " ".join(rp["bullets"])
    sentences = re.split(r"(?<=[.:])\s+(?=[A-Z`])", shows)
    wrows = []
    for r in wit_rows:
        said = [s for s in sentences if f"`{r['prop']}`" in s]
        wrows.append([r["prop"], "\"" + hw[r["prop"]] + "\"",
                      " ".join("\"" + s + "\"" for s in said) if said else "not named in the section",
                      f"`{r['name']}`", f"[[red|{r['verdict']}]]", n(r["states"]), "checked, as expected"])
    wcols = [("Witness", 330, {"mono": True, "bold": True}), ("Module header, WITNESSES", 900),
             ("README § SenateRules.tla, What it shows", 900), ("Row", 300), ("Verdict", 230),
             ("Distinct states", 170)]
    wcols.append(("Status", WW - sum(x[1] for x in wcols)))
    y += c.table(X0, y, wcols, wrows, size=13.5, anchor="witnesses") + 24
    y += c.para(X0, y, WW, f"The README's summary table counts {summ['witnesses']} witnesses; the section's prose "
                "names two of them. All eight run under `Spec` (no fairness) with `Mut = \"none\"` at seven "
                "Senators. \"Witnesses and counterexamples are existential, and stay with TLC\" (README § What is "
                "not proved).", 13.5, "muted") + 40

    # ---- band 5: temporal rows
    y = band(c, X0, y, "The filibuster as the failure of a leads-to: the temporal rows", status="notproved",
             extra="checked by TLC at seven Senators")
    # each row's reading, in the module header's words (LIVENESS)
    reading = {
        "l-fair-majority": "\"a bill with a majority short of three-fifths is debated forever. That is the "
                           "filibuster\"",
        "l-pq-majority": "\"It HOLDS under M_PREVIOUS_QUESTION and M_TIME_LIMIT\"",
        "l-time-majority": "\"It HOLDS under M_PREVIOUS_QUESTION and M_TIME_LIMIT\"",
        "l-nuclear-majority": "\"a majority facing a filibuster eventually goes nuclear: the filibuster delays "
                              "only a majority that declines to end it\"",
        "l-fair-reconciliation": "\"ReconciliationPrevails HOLDS under FairSpec\"",
        "l-noclock-reconciliation": "\"and fails without the clock (SpecNoClock)\"",
        "l-fair-nobehaviour": "\"NoBehaviour is violated under each fair spec, so each has a behaviour\"",
        "l-nuclear-nobehaviour": "the same, under `NuclearSpec`",
    }
    need(set(reading) == {r["name"] for r in live_rows}, tf, "the PROPERTY rows are not the ones this diagram reads")
    lrows = []
    for r in live_rows:
        lrows.append([r["name"], r["mut"], r["spec"], f"`{r['prop']}`",
                      f"[[{'red' if r['verdict'] == 'COUNTEREXAMPLE' else 'teal'}|{r['verdict']}]]",
                      n(r["states"]) if r["states"] is not None else "count not recorded",
                      "as expected" if r["ok"] else "[[red|NOT as expected]]", reading[r["name"]],
                      "checked, not proved"])
    lcols = [("Row", 300, {"mono": True, "bold": True}), ("Mut", 300, {"mono": True}),
             ("Spec", 200, {"mono": True}), ("Property", 290), ("Verdict", 220), ("Distinct states", 200),
             ("Row list (read)", 170), ("The module header, LIVENESS, on this row", 1100)]
    lcols.append(("Status (README § What is not proved; proof module NOT PROVED)", WW - sum(x[1] for x in lcols)))
    y += c.table(X0, y, lcols, lrows, size=13.5) + 24
    y += row_cards(c, X0, y, WW, 24, [
        ("The properties and the fair specs (`SenateRules.tla`, Liveness)", [
            "`MajorityPrevails == \\A m \\in Measures : Backed(m) ~> (stage[m] = \"Passed\")`",
            "`ReconciliationPrevails`: the same over `Reconciliations`.",
            "`FloorVotes`: weak fairness on `InvokeCloture(m)` and `Pass(m)`, \"The floor's obligation: a vote "
            "that would carry is taken.\"",
            "`ClockRuns`: weak fairness on `DebateExpires(m)`, \"The statute's: limited debate runs out.\"",
            "`MajorityGoesNuclear`: weak fairness on `Nuclear(m)`, \"Not an obligation of anyone: the majority's "
            "choice to end a filibuster.\"",
            "`FairSpec == Spec /\\ FloorVotes /\\ ClockRuns`; `SpecNoClock == Spec /\\ FloorVotes`; "
            "`NuclearSpec == FairSpec /\\ MajorityGoesNuclear`.",
            "`NoBehaviour == <>(shortCloture /\\ ~shortCloture)`: violated, so each fair spec has a behaviour."],
         "amber", {}),
        ("The module header, LIVENESS", ["\"" + h_live[len("LIVENESS. "):] + "\""], "amber", {}),
        ("README § `SenateRules.tla`, What it shows", rp["bullets"], "amber", {}),
        ("Why each verdict (the diagram's reading of the operators, at seven Senators)", [
            "`FairSpec`, unmutated: at 4 of 7, step 2 is never enabled (`ThreeFifths` needs 5), step 3 is not "
            "for a bill, and step 6 is enabled but has no fairness. Weak fairness forces nothing, so debate can "
            "go on forever: [[red|COUNTEREXAMPLE]].",
            "[[violet|M_PREVIOUS_QUESTION]] or [[violet|M_TIME_LIMIT]]: step 2 or 3 stays enabled for a backed "
            "measure, fairness takes it, then step 4: [[teal|HOLDS]].",
            "`NuclearSpec`: step 6 is taken, the threshold falls to a majority, then steps 2 and 4: "
            "[[teal|HOLDS]].",
            "`SpecNoClock`: nothing forces step 3 for a reconciliation bill: [[red|COUNTEREXAMPLE]]."],
         "amber", {}),
    ], size=13.5) + 50

    # ---- band 6: the proofs
    y = band(c, X0, y, f"The proofs: every theorem in `{pf[8:]}`, with its hypotheses", status="proved",
             extra=f"{n(P['obligations'])} obligations")
    ce_by_prop = {}
    for (m_, p_, s_), r in cells.items():
        if s_ == 7 and r["verdict"] == "COUNTEREXAMPLE":
            ce_by_prop.setdefault(p_, set()).add(m_)
    ind = {
        "TypeOK": "Under every mutation; cited by every lemma that reads a function after an EXCEPT.",
        "ClotureThreshold": "A flag set by `InvokeCloture`; inductive with `TypeOK` alone (`NextClotureThreshold`).",
        "DebateEndsByCloture": "A flag set by `DebateExpires`; inductive with `TypeOK` alone "
                               "(`NextDebateEndsByCloture`).",
        "MajorityFloor": "A flag set by `Pass`; inductive with `TypeOK` alone (`NextMajorityFloor`).",
        "RulesByTwoThirds": "A flag set by `AmendRule`; inductive with `TypeOK` alone (`NextRulesByTwoThirds`).",
        "ClosedOnThreeFifths": "Inductive with `TypeOK` as stated (`InvC`, `NextInvC`): a measure leaves Debate "
                               "only by `InvokeCloture` or `DebateExpires`, and \"a threshold only falls\" "
                               "(`ThresholdOnlyFalls`).",
        "Safety": "By the five theorems above, and PTL.",
    }
    trows = []
    for th_ in P["theorems"]:
        m = re.fullmatch(r"Spec => \[\](\w+)", th_["prove"])
        need(m, pf, f"{th_['name']} does not prove Spec => []P: {th_['prove']!r}")
        prop = m.group(1)
        hyp = set(re.findall(r'Mut # "(\w+)"', ", ".join(th_["assume"])))
        if prop == "Safety":
            ce = {m_ for p_, ms in ce_by_prop.items() for m_ in ms}
            agree = th_["assume"] == ['Mut = "none"'] and ce == set(muts)
            ce_txt = f"each of the {len(ce)} mutations breaks a conjunct"
        else:
            ce = ce_by_prop.get(prop, set())
            agree = hyp == ce
            ce_txt = ", ".join(sorted(ce)) or "none"
        if not agree:
            disagreements.append(th_["name"])
        trows.append([th_["name"], ", ".join(th_["assume"]) or "none: every mutation", th_["prove"], ce_txt,
                      "[[blue|yes]]" if agree else "[[red|no]]", ind.get(prop, "")])
    tcols = [("Theorem", 360, {"mono": True, "bold": True}), ("ASSUME (read)", 560, {"mono": True}),
             ("PROVE (read)", 380, {"mono": True}), ("Mutations with a COUNTEREXAMPLE on it, 7 Senators (read)", 470,
                                                     {"mono": True}),
             ("Hypotheses are exactly those (the proof header's claim, checked here)", 330)]
    tcols.append(("Inductive strengthening (proof module header, in prose)", WW - sum(x[1] for x in tcols)))
    y += c.table(X0, y, tcols, trows, size=13.5, anchor="theorems") + 24
    y += row_cards(c, X0, y, WW, 24, [
        (f"Lemmas ({len(P['lemmas'])}, read)", [", ".join(f"`{x}`" for x in P["lemmas"]),
         "One lemma per mutation, `Mut…Admits`, says what it lets through; \"the counterexamples themselves are "
         "TLC's\" (proof module)."], "blue", {}),
        ("Assumptions (proof module header)", ["\"The base module's named ASSUME FiniteSenate, and only for TypeOK "
         "(the count 0 is a count of the Senate). MutOK and KindsDisjoint are not used. So the theorems hold for a "
         "Senate of any size and any number of bills, nominations and reconciliation bills.\"", "README: \""
         + rp["proof"] + "\""], "blue", {}),
        ("The prover and what was proved (read)", [f"**{n(P['obligations'])} obligations, all proved**, "
         f"{P['date']}.", f"Prover: {P['prover'].split(' sha256')[0]}; backends: {P['backends']}.",
         "Modules by sha256: " + ", ".join(f"`{k}`" for k in P["modules"]) + ", each equal to the tree now "
         "(checked at build time).", f"Names `{P['tlc_file'][8:]}` by its sha256, also equal now."], "blue",
         {"status": "proved"}),
        ("Not proved (proof module header, NOT PROVED)", ["`MajorityPrevails` and `ReconciliationPrevails`: "
         "\"each is a leads-to quantified over measures, and the pinned prover has no sound route for a "
         "quantified leads-to\". Checked by TLC, with `NoBehaviour`.", "\"Reachability (the Never... witnesses) "
         "and the mutations' counterexamples: existential, so TLC's.\""], "amber", {"status": "notproved"}),
    ], size=13.5) + 50

    # ---- band 7: the constants, and the two TLC results files of 2026.11.19
    e = earlier
    y = band(c, X0, y, "The constants, and the two TLC results files dated 2026.11.19")
    y += row_cards(c, X0, y, WW, 30, [
        (f"The constants (`{ROWS}`, header)", ["\"" + const_note[len("Constants: "):] + "\"",
         f"Results file Constants: `{T['constants'].split(' (')[0]}`.",
         "Three rows override `Senators` with five (`c5-safety`, `pq5-cloture`, `pq5-threefifths`)."], "teal",
         {"status": "checked"}),
        ("What differs between the two files (read at build time)", [
            f"`{EARLIER[8:]}` and `{tf[8:]}` differ on lines " + ", ".join(map(str, e["diff"])) + " only: the "
            "title, and the `Modules:` and `Rows:` digests.",
            "The earlier title ends \"" + e["e"]["title"][len(T["title"]):] + "\"; the named file's does not.",
            ("Every row, verdict and state count is the same." if e["rows_same"] else
             "[[red|The rows differ.]]"),
            ("The earlier file's `SenateRules.tla` and row-list digests are not those of the files in the tree "
             "now; the named file's are." if not (e["e_spec_current"] or e["e_rows_current"]) else
             "[[red|The earlier file's digests match the tree now.]]")], "grey", {}),
        ("Why there are two (README § Running)", ["`scripts/tlc_rows.py` \"never overwrites\" a results file. "
         "\"A rerun that reproduces a file says so; one that differs is written beside it with a letter "
         "suffix.\"", f"`corpus.RESULTS` names `{tf[8:]}`, and this diagram draws from it alone."], "grey", {}),
    ], size=14) + 10

    if disagreements:
        print(f"  NOTE B6 disagreements drawn red: {disagreements}")
    return c
