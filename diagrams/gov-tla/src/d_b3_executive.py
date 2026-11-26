"""B3 — Executive.tla: Article II and the administrative state.

The module's three machines (the office and Amendment XXV; the agencies Congress charters, their heads, inferior
officers and acting officers; the other powers and impeachment) as a picture; the README's provisions, abstracted
and mutation tables whole; the mutation x property matrix, the witnesses and the liveness rows read from the named
TLC results file; the theorems, hypotheses and lemmas read from the named proof results file.

Build-time reads and checks (each raises corpus.CorpusError, so the generator prints ERROR, like a gate):
  - the named results files parse, every row is as expected, and their digests match specs/ and rows/ now;
  - the proof results file names the TLC results file by its current sha256;
  - the README section's tables and lists parse in the shape drawn here;
  - the module header's MUTATIONS block and the results file's Expected: line name a broken property for every
    mutation the results file runs;
  - KnownCharters in Executive.tla holds six charter records of the shape drawn.
Disagreements between the README, the header, the Expected: line, the TLC verdicts and the proof hypotheses are
drawn, marked red, and never reconciled.
"""
import re

from lib import Canvas, STATUS, text_width
import corpus as C

ID, SLUG = "B3", "executive"
MOD = "Executive"

W = 3600
S = 14
SPEC = "specs/Executive.tla"
PROOF = "specs/Executive_proof.tla"
CFG = "specs/Executive.cfg"
README_HEAD = "### `Executive.tla` — Article II and the administrative state"


# ---------------------------------------------------------------------------------------------- layout helpers
def row_cards(c, x, y, w, gap, specs, size=S):
    n = len(specs)
    cw = (w - (n - 1) * gap) / n
    h = max(c.card(0, 0, cw, t, b, draw=False, size=size, status=k.get("status")) for t, b, _, k in specs)
    for i, (t, b, acc, k) in enumerate(specs):
        c.card(x + i * (cw + gap), y, cw, t, b, accent=acc, h=h, size=size, **k)
    return h


def cards_at(c, specs, y, size=S):
    """Cards at given x and width on one row, all drawn at the height of the tallest. specs: (x, w, title, body,
    accent, kwargs). Returns the height."""
    h = max(c.card(0, 0, w, t, b, draw=False, size=size, status=k.get("status")) for _, w, t, b, _, k in specs)
    for x, w, t, b, acc, k in specs:
        c.card(x, y, w, t, b, accent=acc, h=h, size=size, **k)
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


def plain(s):
    """README markdown to the library's rich text: *italic* has no rendering here, so its asterisks go."""
    return re.sub(r"(?<!\*)\*(?!\*)([^*]+?)(?<!\*)\*(?!\*)", r"\1", s)


def names_in(s):
    return re.findall(r"`([A-Za-z_][A-Za-z0-9_]*)`", s)


# ---------------------------------------------------------------------------------------------- build-time reads
def read_readme():
    lines = C.read("README.md").splitlines()
    need(README_HEAD in lines, "README.md", f"no heading {README_HEAD!r}")
    i0 = lines.index(README_HEAD) + 1
    i1 = next(i for i in range(i0, len(lines)) if lines[i].startswith("### "))
    sec = lines[i0:i1]

    def table(header):
        need(header in sec, "README.md", f"§ Executive.tla: no table header {header!r}")
        k = sec.index(header)
        ncol = header.count("|") - 1
        need(re.fullmatch(r"\|(---\|)+", sec[k + 1]), "README.md", f"no rule under {header!r}")
        rows = []
        for ln in sec[k + 2:]:
            if not ln.startswith("|"):
                break
            cells = [x.strip() for x in ln.strip().strip("|").split(" | ")]
            need(len(cells) == ncol, "README.md", f"row of {ncol} cells expected: {ln[:70]!r}")
            rows.append(cells)
        need(rows, "README.md", f"empty table {header!r}")
        return rows

    def bullets(lead):
        need(lead in sec, "README.md", f"§ Executive.tla: no {lead!r}")
        k = sec.index(lead) + 2
        need(sec[k - 1] == "", "README.md", f"no blank line after {lead!r}")
        out = []
        while k < len(sec) and sec[k].strip():
            if sec[k].startswith("- "):
                out.append(sec[k][2:])
            else:
                need(sec[k].startswith("  ") and out, "README.md", f"bad list line {sec[k]!r}")
                out[-1] += " " + sec[k].strip()
            k += 1
        need(out, "README.md", f"empty list after {lead!r}")
        return out

    def para(start):
        k = next((j for j, ln in enumerate(sec) if ln.startswith(start)), None)
        need(k is not None, "README.md", f"§ Executive.tla: no paragraph starting {start!r}")
        out = []
        while k < len(sec) and sec[k].strip():
            out.append(sec[k].strip())
            k += 1
        return " ".join(out)

    r = {
        "intro": para("The Constitution creates no bureaus."),
        "provisions": table("| Provision | Where |"),
        "abstracted": bullets("Abstracted:"),
        "mutations": table("| Mutation | Check removed | Reverts to | Breaks |"),
        "witnesses": bullets("Witnesses (each violated):"),
        "changed": bullets("Three properties changed meaning:"),
        "new": para("`TreatiesByTwoThirds` is new."),
        "liveness": para("**Liveness.**"),
    }
    # the intro's two charter bullets follow the paragraph that ends "six real statutes:"
    k = next(j for j, ln in enumerate(sec) if ln.startswith("`KnownCharters`, six real statutes:"))
    ch = []
    for ln in sec[k + 2:]:
        if not ln.strip():
            break
        if ln.startswith("- "):
            ch.append(ln[2:])
        else:
            ch[-1] += " " + ln.strip()
    need(len(ch) == 2, "README.md", "§ Executive.tla: two charter bullets expected")
    r["charters"] = ch
    r["intro"] = " ".join(sec[j].strip() for j in range(0, k + 1) if sec[j].strip())
    # the findings paragraph about this module
    allx = C.read("README.md")
    m = re.search(r"^\*\*One the prover found\.\*\* (In `Executive\.tla`.+?)\n\n", allx, re.M | re.S)
    need(m, "README.md", "§ Findings: no 'One the prover found.' paragraph about Executive.tla")
    r["finding"] = " ".join(m.group(1).split())
    opening = allx.split("\n## ", 1)[0]
    need("This is an exercise, not law." in opening, "README.md", "opening: no 'This is an exercise, not law.'")
    return r


def header_block(src, start, stop):
    """Lines of the module header between a line starting `(* start` and one starting `(* stop`, unboxed."""
    lines = src.splitlines()
    i0 = next((i for i, ln in enumerate(lines) if ln.startswith("(* " + start)), None)
    need(i0 is not None, SPEC, f"header: no {start!r} block")
    out = []
    for ln in lines[i0:]:
        if out and stop and ln.startswith("(* " + stop):
            break
        if ln.startswith("(****"):
            break
        need(ln.startswith("(*") and ln.rstrip().endswith("*)"), SPEC, f"header line not boxed: {ln[:60]!r}")
        out.append(ln[2:].rstrip()[:-2].rstrip())
        if not stop:
            continue
    return out


def read_spec(props):
    src = C.read(SPEC)
    # MUTATIONS block: each mutation and the properties after "Breaks"
    blk = header_block(src, "MUTATIONS", "DEADLOCK")
    muts, cur = {}, None
    for ln in blk[1:]:
        m = re.match(r"^\s{1,4}(M_[A-Z0-9_]+)\s+(.*)$", ln)
        if m:
            cur = m.group(1)
            muts[cur] = m.group(2).strip()
        elif cur and ln.strip() and not ln.strip().startswith("Every other"):
            muts[cur] += " " + ln.strip()
        elif ln.strip().startswith("Every other"):
            cur = None
    breaks = {}
    for k, v in muts.items():
        need("Breaks" in v, SPEC, f"header: {k} names no 'Breaks'")
        after = v.split("Breaks", 1)[1]
        got = [p for p in re.findall(r"[A-Za-z]+", after) if p in props]
        need(got, SPEC, f"header: {k} breaks no known property")
        breaks[k] = got
    # ABSTRACTED paragraph
    ab = header_block(src, "ABSTRACTED:", None)
    text = " ".join(x.strip() for x in ab)
    need(text.startswith("ABSTRACTED: "), SPEC, "header: ABSTRACTED block")
    text = text[len("ABSTRACTED: "):]
    first, sep, rest = text.partition(". The statutes")
    need(sep, SPEC, "header ABSTRACTED: no '. The statutes' sentence")
    items, depth, cur = [], 0, ""
    for ch in first:
        depth += (ch == "(") - (ch == ")")
        cur += ch
        if ch == ";" and depth == 0:
            items.append(cur[:-1].strip())
            cur = ""
    items.append(cur.strip())
    tail = ("The statutes" + rest).split(". The Federal Reserve")
    need(len(tail) == 2, SPEC, "header ABSTRACTED: no 'The Federal Reserve' sentence")
    after = [tail[0] + ".", "The Federal Reserve" + tail[1]]
    # KnownCharters
    m = re.search(r"^KnownCharters ==\n(.*?)\}\n", src, re.M | re.S)
    need(m, SPEC, "no KnownCharters block")
    charters, label = [], None
    for ln in m.group(1).splitlines():
        s = ln.strip().lstrip("{").strip()
        if s.startswith("\\*"):
            label = s[2:].strip()
            continue
        r = re.match(r'^\[branch \|-> "(\w+)",\s+executesLaw \|-> (TRUE|FALSE),\s+removal \|-> "(\w+)",\s+'
                     r'vesting \|-> "(\w+)"\]', s)
        if r:
            need(label, SPEC, "KnownCharters: a record with no comment above it")
            charters.append(dict(label=label, branch=r.group(1), executes=r.group(2) == "TRUE",
                                 removal=r.group(3), vesting=r.group(4)))
            label = None
    need(len(charters) == 6, SPEC, f"KnownCharters: six records expected, found {len(charters)}")
    # ASSUME names
    assumes = re.findall(r"^ASSUME (\w+)\s+==", src, re.M)
    need(len(assumes) == 6, SPEC, f"six named ASSUMEs expected, found {assumes}")
    noearlier = sorted(k for k, v in muts.items() if "No earlier text" in v)
    wb = header_block(src, "REACHABILITY WITNESSES", "ABSTRACTED")
    need(wb and wb[0].startswith(" REACHABILITY WITNESSES (Never..., each must be VIOLATED under \"none\"):"), SPEC,
         "header: REACHABILITY WITNESSES block")
    wpara = " ".join(x.strip() for x in wb[1:] if x.strip())
    return dict(breaks=breaks, noearlier=noearlier, witnesses=wpara, abstracted=items, abstracted_after=after, charters=charters, assumes=assumes)


def read_expected(t, props):
    """The results file's Expected: line, the part naming what each mutation breaks."""
    e = t["expected"]
    m = re.search(r"HOLDS on every other: (.+?)\. Every Never", e)
    need(m, C.RESULTS[MOD][0], "Expected: line has no per-mutation list")
    out = {}
    for item in m.group(1).split("; "):
        toks = re.findall(r"[A-Za-z_0-9]+", item)
        ms = [x for x in toks if x.startswith("M_")]
        ps = [x for x in toks if x in props]
        need(ms and ps, C.RESULTS[MOD][0], f"Expected: item does not parse: {item!r}")
        for x in ms:
            out[x] = ps
    return out


def read_all():
    tf, pf = C.RESULTS[MOD]
    t, p = C.tlc_results(tf), C.proof_results(pf)
    for res, rel in ((t, tf), (p, pf)):
        for f, digest in res["modules"].items():
            need(C.sha256(f"specs/{f}") == digest, rel, f"{f} has moved since it was checked")
    need(C.sha256(t["rows_file"]) == t["rows_sha"], tf, f"{t['rows_file']} has moved since the run")
    need(p["tlc_file"] == tf and C.sha256(tf) == p["tlc_sha"], pf, f"names {p['tlc_file']}, not {tf} now")
    need(t["as_expected"] == t["total"] and not t["not"] and not t["error"], tf, "not every row is as expected")
    need(p["module"] == MOD, pf, "not the Executive proof")
    return t, p, tf, pf


def charter_verdict(ch):
    """The diagram's evaluation of Chartered(c) (Executive.tla) on one record: the checks that refuse it."""
    out = []
    if ch["executes"] and ch["branch"] != "Executive":
        out.append(("Bowsher", "M_GRH"))
    if ch["removal"] == "ForCause" and ch["executes"]:
        out.append(("Slaughter", "M_HUMPHREY"))
    if ch["vesting"] == "Congress" and ch["executes"]:
        out.append(("Buckley", "M_FECA"))
    return out


# ---------------------------------------------------------------------------------------------- the diagram
def build():
    t, p, tf, pf = read_all()
    R = read_readme()
    muts_all, props, cells = C.matrix(t, "Spec")
    safety = [x for x in props if x not in ("Safety", "TypeOK")]
    need(len(safety) == 12, tf, f"twelve safety properties expected in the matrix, found {len(safety)}")
    H = read_spec(set(safety))
    E = read_expected(t, set(safety))
    muts = muts_all[1:]
    wit = C.witnesses(t)
    live = [r for r in t["rows"] if r["kind"] == "PROPERTY" and not r["prop"].startswith("Never")]
    dead = [r for r in t["rows"] if r["kind"] == "DEADLOCK"]
    sims = [r for r in t["rows"] if r["kind"] == "SIMULATE"]
    readme_muts = {r[0].strip("`"): r for r in R["mutations"]}
    readme_breaks = {k: names_in(v[3]) for k, v in readme_muts.items()}
    tlc_breaks = {m: [q for q in safety if "COUNTEREXAMPLE" in cells.get((m, q), set())] for m in muts}
    thm = {x["name"]: x for x in p["theorems"]}
    hyp = {}
    for x in p["theorems"]:
        for a in x["assume"]:
            mm = re.fullmatch(r'Mut # "(M_\w+)"', a)
            if mm:
                hyp.setdefault(mm.group(1), []).append(x["name"][:-len("Always")])
    need(set(readme_muts) == set(muts), "README.md", f"mutation table {sorted(readme_muts)} vs results {sorted(muts)}")
    need(set(H["breaks"]) == set(muts), SPEC, f"header mutations {sorted(H['breaks'])} vs results {sorted(muts)}")
    need(set(E) == set(muts), tf, "Expected: line does not name every mutation")

    disagree = []
    for m in muts:
        srcs = {"README": set(readme_breaks[m]), "header": set(H["breaks"][m]), "Expected": set(E[m]),
                "TLC": set(tlc_breaks[m]), "proof": set(hyp.get(m, []))}
        if len({frozenset(v) for v in srcs.values()}) > 1:
            disagree.append(m)

    live_rows = [r for r in live if r["prop"] == "ActingEventuallyEnds"]
    n_live_ok = sum(1 for r in live_rows if r["verdict"] == "HOLDS")

    c = Canvas(ID, "`Executive.tla`: Article II and the administrative state, from the statutes Congress may pass to "
               "removal and acting officers, each rule a check TLC shows the model depends on and TLAPS proves",
               "The Constitution creates no bureaus, so `Init` has none: Congress charters agencies from the constant "
               "`Charters`, and the model asks who appoints their officers, who may remove them, which branch they "
               "belong to, and how long an acting officer serves, beside the office of President under Amendment XXV "
               "and the pardon, treaty, war and convening powers. "
               f"**{n(t['total'])} TLC rows, every one as expected, and {n(p['obligations'])} proof obligations, every "
               f"one proved**, read from the two named results files when this diagram is built. "
               "**The one liveness property, `ActingEventuallyEnds`, is checked, not proved**; the witnesses and "
               "counterexamples are TLC's. This models the text's procedure: it is an exercise, not law.",
               W, f"README.md § `Executive.tla` — Article II and the administrative state (its opening, the two "
               f"charter bullets, the provisions table, Abstracted, the mutation table, Witnesses, Three properties "
               f"changed meaning, Liveness), § How the specs are written and checked (the words, What is not "
               f"proved), § Findings (One the prover found), opening; {SPEC} (header: PROPERTIES, LIVENESS, "
               f"MUTATIONS, DEADLOCK, REACHABILITY WITNESSES, ABSTRACTED; the ASSUMEs, KnownCharters, the checks, "
               f"Init, the actions, the safety properties, the Never… witnesses, ActingEventuallyEnds, ClockRuns, "
               f"LimitBinds, SpecLive, SpecNoClock, SpecNoLimit, NoBehaviour, DaysBound); {CFG}; {PROOF} (header: "
               f"THEOREMS, ASSUMPTIONS, INDUCTIVE STRENGTHENING, NOT PROVED); {t['rows_file']} (header and section "
               f"comments); {tf}; {pf}; digests compared at build time")
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    y = status_strip(c, X0, X1, y, [
        ("Executive.tla", [("checked", f"{n(t['total'])} rows, all as expected"),
                           ("proved", f"{n(p['obligations'])} obligations")]),
        (f"Safety properties ({len(safety)})", [("proved", f"{len(safety)} theorems, TypeOK, SafeAlways")]),
        (f"Mutations ({len(muts)})", [("checked", "each breaks what it must")]),
        (f"Witnesses ({len(wit)})", [("checked", "existential, not proved")]),
        ("ActingEventuallyEnds", [("notproved", f"{n_live_ok} rows under SpecLive")]),
        ("Deadlock audit", [("checked", f"{len(dead)} row")]),
        ("Sampled rows", [((f"{len(sims)} in this file", "grey", "4 3"), "")]),
        ("README's Abstracted list", [("abstracted", "")]),
    ])
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row list. "
                "**Proved** means TLAPS discharged every obligation for every value of the constants the module's "
                "named assumptions admit. **Sampled** means random simulation found no error, and is never cited as "
                "a check. \"None of these is a claim about law or practice\" (README § How the specs are written and "
                "checked). \"This is an exercise, not law\" (README, opening): the cases and statutes named below "
                "are the model's mutations and charters, not a statement of what the law is.", 14.5, "muted") + 34

    # ================================================================ band 1: the picture
    y = band(c, X0, y, "The mechanism: three machines over one President, one Congress and the agencies it charters "
             "(`Next == OfficeSteps \\/ AgencySteps \\/ TrialSteps \\/ OtherSteps`, in `Executive.tla`)")
    y += c.para(X0, y, WW, "Actions in code font as the module names them; [[violet|violet]] names the mutation that "
                "removes a guard; a flag (`congressAppointed`, `congressRemoved`, `warWithoutStatute`, `treatyShort`) "
                "is raised by the one step that could violate its property. Solid arrows move authority or a seat; "
                "dashed arrows only remove one. At the rows' constants there is one agency, `a1`.", 14, "muted") + 30
    LX = X0 + 30
    LW = WW - 60

    # ---- lane 1: the office and Amendment XXV
    top1 = y + 14
    cw, gap = 292, 124
    sx = [LX + i * (cw + gap) for i in range(5)]
    ct = top1 + 140
    states = [
        ('`"SelfDeclared"`', ["§3: \"the President wrote to Congress\" (`Inability`)."]),
        ('`"None"`', ["\"the President exercises the office\". `Init` starts here, and `Elect`, "
                      "`PresidentVacates` and `Convict` of either officer return here."]),
        ('`"CabinetDeclared"`', ["§4: \"VP and a majority of principal officers\"."]),
        ('`"Contested"`', ["\"the President wrote that no inability exists; four days to re-declare\"."]),
        ('`"BeforeCongress"`', ["\"they did; Congress decides, two-thirds each\"."]),
    ]
    hs = max(c.card(0, 0, cw, tt, b, draw=False, size=S) for tt, b in states)
    for i, (tt, b) in enumerate(states):
        c.card(sx[i], ct, cw, tt, b, accent="blue" if i == 1 else "teal", h=hs, size=S)
    a1y, a2y = ct - 48, ct - 92
    d1 = ct + hs + 50
    ym = ct + hs / 2
    c.arrow([(sx[1] - 6, ct + hs * 0.33), (sx[0] + cw + 6, ct + hs * 0.33)], "teal", label="①")
    c.arrow([(sx[0] + cw + 6, ct + hs * 0.70), (sx[1] - 6, ct + hs * 0.70)], "teal", label="②")
    c.arrow([(sx[1] + cw + 6, ym), (sx[2] - 6, ym)], "teal", label="③")
    c.arrow([(sx[2] + cw + 6, ym), (sx[3] - 6, ym)], "teal", label="④")
    c.arrow([(sx[3] + cw + 6, ym), (sx[4] - 6, ym)], "teal", label="⑥")
    c.arrow([(sx[3] + cw / 2, ct - 6), (sx[3] + cw / 2, a1y), (sx[1] + cw * 0.68, a1y), (sx[1] + cw * 0.68, ct - 6)],
            "teal", label="⑤", lpos=0.5)
    c.arrow([(sx[4] + cw / 2, ct - 6), (sx[4] + cw / 2, a2y), (sx[1] + cw * 0.32, a2y), (sx[1] + cw * 0.32, ct - 6)],
            "teal", label="⑧", lpos=0.5)
    c.arrow([(sx[4] + cw / 2, ct + hs + 6), (sx[4] + cw / 2, d1), (sx[2] + cw / 2, d1), (sx[2] + cw / 2, ct + hs + 6)],
            "teal", label="⑦", lpos=0.5)
    mw = sx[4] + cw - LX
    key = [
        "① `DeclareInability` (§3): needs `president # NoOne` and `VPToAct`, a Vice President in office, which "
        "[[violet|M_NOVP]] removes.",
        "② `DeclareAble` from `\"SelfDeclared\"`: under §3 the President's declaration ends the inability.",
        "③ `CabinetDeclares` (§4): needs a President, a Vice President and `Cabinet # {}`, a head of a live "
        "Executive-branch agency.",
        "④ `DeclareAble` from `\"CabinetDeclared\"`: the President contests, and four days open.",
        "⑤ `DeclareAble` from `\"Contested\"`: the four days pass and the President resumes.",
        "⑥ `CabinetDeclares` from `\"Contested\"`: they re-declare, and the question goes to Congress.",
        "⑦ `CongressDecides(v)` with `TwoThirds(v)`: two-thirds of each House keeps the VP acting.",
        "⑧ `CongressDecides(v)` with less: the President resumes. The four- and twenty-one-day windows are "
        "nondeterministic choice (README, Abstracted).",
    ]
    ky = d1 + 30
    hk = c.card(LX, ky, mw, "The arrows: `inability` under Amend. XXV §§3–4 (`Executive.tla` `OfficeSteps`)", key,
                accent="teal", size=S, bullets=False)
    rx = LX + mw + 60
    rw = LX + LW - rx
    gw = (rw - 30) / 2
    oc = [
        ("`Elect(p, v)`", ["`p` and `v` in `Eligible`, `TwoPeople(p, v)`, which [[violet|M_SAMEPERSON]] removes, "
         "and `EligibleOfficer` of both. Seats both; `inability` is `\"None\"`.", "Elections and the Electoral "
         "College are abstracted: `Elect` picks a ticket (module header, ABSTRACTED)."], "teal"),
        ("`Executive` (Art. II §1, Amend. XXV)", ["`IF Acting THEN vicePresident ELSE president`, with `Acting == "
         "inability # \"None\"`: the VP as Acting President has the full power.", "It guards nominating, removing, "
         "pardoning, negotiating and convening, and the President's vesting in `Appointer`."], "teal"),
        ("`PresidentVacates`", ["Death or resignation (§1): the VP becomes President and the Vice Presidency stays "
         "empty; filling it (§2) is in `Constitution.tla`."], "teal"),
        ("`OneExecutive`, the property decided here", ["President and VP are two people, and the VP acts only while "
         "there is a President to be unable and a VP to act: `Elect`'s and `DeclareInability`'s guards decide it "
         "(module header).", "Broken by [[violet|M_SAMEPERSON]] and [[violet|M_NOVP]]."], "blue"),
    ]
    oy = top1 + 30
    h_o1 = max(c.card(0, 0, gw, a, b, draw=False, size=S) for a, b, _ in oc[:2])
    h_o2 = max(c.card(0, 0, gw, a, b, draw=False, size=S, status="proved" if i == 1 else None)
               for i, (a, b, _) in enumerate(oc[2:]))
    c.card(rx, oy, gw, oc[0][0], oc[0][1], accent="teal", h=h_o1, size=S)
    c.card(rx + gw + 30, oy, gw, oc[1][0], oc[1][1], accent="teal", h=h_o1, size=S)
    c.card(rx, oy + h_o1 + 24, gw, oc[2][0], oc[2][1], accent="teal", h=h_o2, size=S)
    c.card(rx + gw + 30, oy + h_o1 + 24, gw, oc[3][0], oc[3][1], accent="blue", h=h_o2, size=S, status="proved")
    bot1 = max(ky + hk, oy + h_o1 + 24 + h_o2) + 30
    c.region(X0, top1, WW, bot1 - top1, "The office: one President, and the Vice President acting under Amend. XXV "
             "§§3–4 (`president`, `vicePresident`, `inability`)", "teal")
    y = bot1 + 60

    # ---- lane 2: the administrative state
    top2 = y
    ya = top2 + 40
    tw_ch = 1640
    ch_cols = [("Statute (the comment above it in `KnownCharters`)", 520), ("branch", 140),
               ("executesLaw", 140), ("removal", 130), ("vesting", 130),
               ("`Chartered(c)` (the diagram's evaluation)", tw_ch - 1060)]
    ch_rows = []
    for ch in H["charters"]:
        v = charter_verdict(ch)
        verdict = ("[[teal|admitted]]" if not v else
                   "[[red|refused]] by the " + " and ".join(f"{a} check" for a, _ in v) + "; admitted under "
                   + ", ".join(f"[[violet|{m}]]" for _, m in v))
        ch_rows.append({"cells": [ch["label"], f"`\"{ch['branch']}\"`", "`TRUE`" if ch["executes"] else "`FALSE`",
                                  f"`\"{ch['removal']}\"`", f"`\"{ch['vesting']}\"`", verdict],
                        "accent": "red" if v else "teal"})
    n_ok = sum(1 for ch in H["charters"] if not charter_verdict(ch))
    need(n_ok == 3, SPEC, f"three KnownCharters admitted expected (README § Executive.tla), found {n_ok}")
    c.text(LX, ya + 8, "`CONSTANT Charters <- KnownCharters` (`Executive.cfg`, every row): six real statutes",
           16, "teal", bold=True)
    h_ch = c.table(LX, ya + 24, ch_cols, ch_rows, size=13.5, accent="teal")
    chx = LX + tw_ch + 90
    chw = 860
    recx = chx + chw + 90
    recw = LX + LW - recx
    hA = cards_at(c, [
        (chx, chw, "`CreateAgency(a, c)`: guard `Chartered(c)`", [
            "Art. I §8 cl. 18: `~Live(a)` and `Chartered(c)`; the charter's four fields are copied into `Blank`.",
            "Bowsher: `c.executesLaw => c.branch = \"Executive\"`, which [[violet|M_GRH]] removes.",
            "Slaughter: `c.removal = \"ForCause\" => ~c.executesLaw`, which [[violet|M_HUMPHREY]] "
            "removes.",
            "Buckley: `c.vesting = \"Congress\" => ~c.executesLaw`, which [[violet|M_FECA]] removes.",
            "`AbolishAgency(a)` returns the record to `Blank`."], "teal", {}),
        (recx, recw, "`agency[a]` (`AgencyRecord`)", [
            "From the statute: `exists`, `branch`, `executesLaw`, `removal` (`\"AtWill\"` or `\"ForCause\"`), "
            "`vesting` (`President`, `Head`, `Courts` or `Congress`).",
            "Seats, filled below: `head`, `headNominee`, `acting`, `actingDays`, `inferior`.",
            "Decided at `CreateAgency`: `ExecutionIsExecutive` and `UnitaryExecutive` (module header)."],
         "teal", {}),
    ], ya, size=S)
    hA = max(hA, h_ch + 24)
    c.arrow([(LX + tw_ch + 6, ya + 24 + h_ch / 2), (chx - 6, ya + 24 + h_ch / 2)], "teal", label="`c`")
    c.arrow([(chx + chw + 6, ya + 24 + h_ch / 2), (recx - 6, ya + 24 + h_ch / 2)], "teal")

    # row B: the principal officer
    yb = ya + hA + 110
    nbw, cbw = 560, 620
    nbx = LX
    cbx = nbx + nbw + 100
    rgx = cbx + cbw + 100
    rgw = LX + LW - rgx
    rcw = (rgw - 2 * 24 - 2 * 22) / 3
    rem = [
        (rgx + 24, rcw, "`PresidentRemovesHead(a, cause)`", [
            "`Executive # NoOne`, an Executive-branch agency only, and `(removal = \"ForCause\") => cause`: at will, "
            "or for cause where the statute says so (the action's comment: Myers, Seila Law, Slaughter)."],
         "teal", {}),
        (rgx + 24 + rcw + 22, rcw, "`CongressRemovesHead(a)`", [
            "By joint resolution, short of impeachment: `OwnOfficer(a)`, a Legislative-branch agency only, which "
            "[[violet|M_JOINTRES]] removes. Raises `congressRemoved` if the head executes the laws (Bowsher)."],
         "teal", {}),
        (rgx + 24 + 2 * (rcw + 22), rcw, "`Resign(a)`", ["The head leaves. Each of the three sets `head = NoOne`."],
         "teal", {}),
    ]
    hB_in = max(c.card(0, 0, w, tt, b, draw=False, size=S) for _, w, tt, b, _, _ in rem)
    hB = max(hB_in + 60, max(c.card(0, 0, w, tt, b, draw=False, size=S) for w, tt, b in [
        (nbw, "`NominateHead(a, p)`", ["Art. II §2 cl. 2. `Executive # NoOne`, the head and nominee seats empty, and "
                                       "`EligibleOfficer(p)`."]),
        (cbw, "`ConfirmHead(a)` · `RejectHead(a)`", ["A majority of the Senate consents; eligibility is checked again "
         "here. Seats the head, and ends any acting service (`acting = NoOne`, `actingDays = 0`). `RejectHead` "
         "clears the nominee."])]))
    c.card(nbx, yb, nbw, "`NominateHead(a, p)`", ["Art. II §2 cl. 2. `Executive # NoOne`, the head and nominee "
           "seats empty, and `EligibleOfficer(p)`."], accent="teal", h=hB, size=S)
    c.card(cbx, yb, cbw, "`ConfirmHead(a)` · `RejectHead(a)`", ["A majority of the Senate consents; eligibility is "
           "checked again here. Seats the head, and ends any acting service (`acting = NoOne`, `actingDays = 0`). "
           "`RejectHead` clears the nominee."], accent="teal", h=hB, size=S)
    c.region(rgx, yb, rgw, hB, "Removal of a head: the seat is vacant again", "teal", dash="7 5")
    for x, w, tt, b, acc, k in rem:
        c.card(x, yb + 34, w, tt, b, accent=acc, h=hB - 34 - 22, size=S, **k)
    c.arrow([(nbx + nbw + 6, yb + hB / 2), (cbx - 6, yb + hB / 2)], "teal", label="`headNominee`")
    c.arrow([(cbx + cbw + 6, yb + hB / 2), (rgx - 6, yb + hB / 2)], "teal", label="`head`")
    ry = yb - 48
    c.arrow([(rgx + rgw / 2, yb - 4), (rgx + rgw / 2, ry), (nbx + nbw / 2, ry), (nbx + nbw / 2, yb - 6)], "teal",
            dash="7 5", label="`head = NoOne`: the office may be filled again", lpos=0.5)

    # row C: inferior and acting officers
    yc = yb + hB + 100
    tkw = 600
    tkx = rgx
    exx = tkx + tkw + 100
    exw = 600
    pix = exx + exw + 90
    piw = LX + LW - pix
    hC = cards_at(c, [
        (nbx, nbw, "`AppointInferior(a, p)`", [
            "`EligibleOfficer(p)` and `Appointer(a)`: whoever the statute vested is there (President: `Executive # "
            "NoOne`; Head: a head; Courts and Congress: always, abstracted).",
            "Raises `congressAppointed` when the vesting is Congress and the agency executes the laws (Buckley)."],
         "teal", {}),
        (cbx, cbw, "`ActAsHead(a)`", [
            "FVRA, 5 U.S.C. 3345(a): `OfficeVacant(a)`, which [[violet|M_ACTWHILEFILLED]] removes; no one acting; the "
            "first assistant (`inferior`) acts, from day 0.", "Decides `ActingIsNotHead`."], "teal", {}),
        (tkx, tkw, "`ActingTick(a)`: one day", [
            "While `WithinLimit(a)`, `actingDays < ActingLimit`, which [[violet|M_PREFVRA]] removes. FVRA, 5 U.S.C. "
            "3346: 210 days; the rows use 1, and 2 for liveness.", "Decides `ActingIsTemporary`. `ClockRuns` is "
            "weak fairness on it."], "teal", {}),
        (exx, exw, "`ActingExpires(a)`", [
            "At `actingDays = ActingLimit` the acting officer leaves and the count resets.", "`LimitBinds` is weak "
            "fairness on it: \"the Executive ends acting service at the limit\" (README, Liveness)."], "teal", {}),
        (pix, piw, "`PresidentRemovesInferior(a)`", [
            "`Executive # NoOne`, an Executive-branch agency only. Removing the first assistant also ends their "
            "acting service."], "teal", {}),
    ], yc, size=S)
    c.arrow([(nbx + nbw + 6, yc + hC / 2), (cbx - 6, yc + hC / 2)], "teal", label="`inferior`")
    c.arrow([(cbx + cbw + 6, yc + hC / 2), (tkx - 6, yc + hC / 2)], "teal", label="`acting`")
    c.arrow([(tkx + tkw + 6, yc + hC / 2), (exx - 6, yc + hC / 2)], "teal", label="at the limit")
    c.arrow([(cbx + cbw / 2, yb + hB + 6), (cbx + cbw / 2, yc - 6)], "teal", dash="7 5",
            label="a confirmed head ends acting service", lpos=0.5)
    bot2 = yc + hC + 30
    c.region(X0, top2, WW, bot2 - top2, "The administrative state: statutes, appointment, removal and acting service "
             "(`agency`, `AgencySteps`)", "teal")
    y = bot2 + 60

    # ---- lane 3: the other powers and impeachment
    top3 = y
    y3 = top3 + 40
    h3 = row_cards(c, LX, y3, LW, 24, [
        ("`EligibleOfficer(p)`: who may be seated", [
            "`NotDisqualified(p)` (Art. I §3 cl. 7), which [[violet|M_DISQUAL]] removes; `NotMember(p)` (Art. I §6 "
            "cl. 2), which [[violet|M_PLACEMEN]] removes; and no other office here.", "Checked at `Elect`, "
            "`NominateHead`, `ConfirmHead` and `AppointInferior`, the only steps that seat someone new. Decides "
            "`Incompatibility` and `Disqualification`."], "teal", {}),
        ("`Impeach(p)` · `Convict(p, dq)` · `Acquit(p)`", [
            "Art. II §4, Art. I §§2–3. A majority of the House impeaches an officer; the Senate tries one at a time.",
            "Two-thirds convict: removal from every office (`Purge`), the VP succeeds a convicted President, and the "
            "judgment may extend to disqualification (`dq`)."], "teal", {}),
        ("`Pardon(k)`", [
            "Art. II §2 cl. 1. `Executive # NoOne` and `PardonReaches(k)` over `Offences` (`Federal`, `State`, "
            "`Impeachment`): not State, which [[violet|M_STATECRIME]] removes; not impeachment, which "
            "[[violet|M_DANBY]] removes.", "A pardon is recorded by the offence it reaches. Decides `PardonScope`."],
         "teal", {}),
        ("`Negotiate(t)` · `RatifyTreaty(t, v)` · `RejectTreaty(t)`", [
            "Art. II §2 cl. 2. The Executive negotiates; ratification needs `TreatyVote(v)`, two-thirds, which "
            "[[violet|M_AUG6]] makes a majority.", "Raises `treatyShort` on less than two-thirds. Decides "
            "`TreatiesByTwoThirds`; its rows run with `Treaties = {t1}`."], "teal", {}),
        ("`DeclareWar(v)`", [
            "Art. I §8 cl. 11: \"declaring war (or, by the same route, peace)\". `WarAuthorised(v)` is a majority; "
            "under [[violet|M_PREROGATIVE]] the Executive alone suffices.", "Raises `warWithoutStatute` without "
            "a majority. Decides `WarIsCongressional`."], "teal", {}),
        ("`Adjourn` · `Convene` · `ConveneByPresident`", [
            "Art. II §3: the President may convene Congress (`Executive # NoOne`). Same effect as `Convene`; \"the "
            "point is who may do it\".", "\"No state is terminal (Congress can always adjourn or convene)\" "
            "(module header, DEADLOCK)."], "teal", {}),
    ])
    bot3 = y3 + h3 + 30
    c.region(X0, top3, WW, bot3 - top3, "Who may hold office, the trial, and the other powers (`TrialSteps`, "
             "`OtherSteps`)", "teal")
    y = bot3 + 70

    # ================================================================ band 2: provisions and abstractions
    y = band(c, X0, y, "The README's provisions table, every row, and what is abstracted (README § `Executive.tla`)")
    ptw = 2380
    h_pt = c.table(X0, y, [("Provision", 1290), ("Where", ptw - 1290)],
                   [[plain(a), plain(b)] for a, b in R["provisions"]], size=13.5)
    h_in = c.card(X0 + ptw + 30, y, WW - ptw - 30, "The section's opening (README § `Executive.tla`)",
                  [plain(R["intro"])] + [plain(b) for b in R["charters"]], accent="blue", size=S)
    y += max(h_pt, h_in) + 30
    ab_rd = [plain(x) for x in R["abstracted"]]
    ab_hd = [x for x in H["abstracted"]] + H["abstracted_after"]
    y += row_cards(c, X0, y, WW, 30, [
        ("Abstracted: the README's list", ab_rd + ["Drawn as abstracted, never as modelled."], "grey",
         {"status": "abstracted", "dash": "2 3"}),
        ("ABSTRACTED: the module header's paragraph, item by item (`Executive.tla`)", ab_hd, "grey",
         {"status": "abstracted", "dash": "2 3"}),
        ("The two lists side by side (the diagram's comparison)", [
            f"The README lists {len(ab_rd)} items; the header's sentence lists {len(H['abstracted'])}, then names "
            "the statutes Congress may attempt and two things not modelled.",
            "Only in the header: elections and the Electoral College, treaty negotiation detail, one impeachment "
            "trial at a time, courts and congressional appointers always available, the Federal Reserve and the "
            "Youngstown framework.", "Both say vote counts, presentment, who is pardoned, the XXV windows and time "
            "apart from the acting officer's day count."], "grey", {}),
    ]) + 30
    # constants
    rows_txt = C.read(t["rows_file"])
    consts = [ln[len("# const: "):] for ln in rows_txt.splitlines() if ln.startswith("# const: ")]
    need(consts and "; ".join(consts) == t["constants"].split(" (")[0], t["rows_file"],
         "the rows header's constants differ from the results file's Constants: line")
    cfg = C.read(CFG)
    need("CONSTANT Charters <- KnownCharters" in cfg, CFG, "no 'CONSTANT Charters <- KnownCharters'")
    need(t["config"] == ["CONSTANT Charters <- KnownCharters"], tf, "Config: line is not the Charters substitution")
    cfg_tr = re.search(r"^\s*Treaties\s*=\s*(\{[^}]*\})", cfg, re.M)
    need(cfg_tr, CFG, "no Treaties constant")
    y += row_cards(c, X0, y, WW, 30, [
        ("The rows' constants (`rows/Executive-rows.txt` header; the results file's Constants: line)",
         ["; ".join("`" + x + "`" for x in consts) + ".", "Every row: `CONSTANT Charters <- KnownCharters` (Config: line). "
          "Treaty rows (`M_AUG6`, `TreatiesByTwoThirds`, `NeverTreaty`, `Safety`, `TypeOK`) override `Treaties = "
          "{t1}`; `M_PREFVRA` rows run under the constraint `DaysBound`, \"its day count being otherwise "
          "unbounded\" (Expected: line)."], "teal", {"status": "checked"}),
        ("`Executive.cfg`: for the visualization tools and ad hoc runs", [
            "\"The checked results come from rows/Executive-rows.txt (scripts/tlc_rows.py), which writes its own "
            "configurations\" (its comment).", f"It sets `Treaties = {cfg_tr.group(1)}` where the rows' default is "
            "`Treaties = {}`, runs `SPECIFICATION Spec` with `TypeOK` and `Safety`, and says liveness needs "
            "`SPECIFICATION SpecLive`."], "grey", {}),
        ("The module's named assumptions (`Executive.tla` ASSUMEs)", [
            ", ".join(f"`{a}`" for a in H["assumes"]) + ".", "The proof uses all but `MutKnown`, so \"the theorems "
            "hold for every set of persons, agencies and treaties, every set of charters drawn from CharterRecord "
            "and every ActingLimit in Nat\"; the rows' constants and `DaysBound` \"are TLC's business and are not "
            "assumed\" (`Executive_proof.tla` header, ASSUMPTIONS)."], "blue", {"status": "proved"}),
    ]) + 70

    # ================================================================ band 3: mutations
    y = band(c, X0, y, "The README's mutation table, every row, beside what each other record says the mutation "
             "breaks (the four right-hand columns are read at build time)")
    mcols = [("Mutation", 200, {"mono": True, "bold": True}), ("Check removed", 520), ("Reverts to", 520),
             ("Breaks (README)", 330), ("Breaks (module header, MUTATIONS)", 330),
             ("Breaks (results file, Expected: line)", 330),
             ("COUNTEREXAMPLE in the TLC results (read)", 330), ("Theorems assuming it absent (proof results)", 0)]
    mcols.append(("All five agree (the diagram's check)", 0))
    fixed = sum(x[1] for x in mcols)
    rest = WW - fixed
    mcols[7] = (mcols[7][0], rest - 220)
    mcols[8] = (mcols[8][0], 220)

    def code(xs):
        return ", ".join(f"`{x}`" for x in xs) if xs else "none"

    mrows = []
    for r in R["mutations"]:
        m = r[0].strip("`")
        ok = m not in disagree
        mrows.append({"cells": [m, plain(r[1]), plain(r[2]), plain(r[3]), code(H["breaks"][m]), code(E[m]),
                                code(tlc_breaks[m]), code([x + "Always" for x in hyp.get(m, [])]),
                                "[[teal|yes]]" if ok else "[[red|NO: drawn as each says]]"],
                      "accent": None if ok else "red"})
    mrows = [x if x["accent"] else x["cells"] for x in mrows]
    y += c.table(X0, y, mcols, mrows, size=13.5, accent="violet") + 20
    y += c.para(X0, y, WW, ("**No disagreement**: for every mutation, the README's Breaks cell, the module header, the "
                "results file's Expected: line, the properties TLC found a counterexample to, and the theorems "
                "whose hypotheses exclude it name the same properties." if not disagree else
                "[[red|Disagreement]] in " + ", ".join(f"`{m}`" for m in disagree) + ": each source is drawn as "
                "it stands.") + " The README's \"Reverts to\" column is drawn as it stands, \"—\" included: "
                "a mutation is earlier law, doctrine or practice, or no history at all.", 14, "muted") + 40

    # the matrix
    y = band(c, X0, y, "Mutation × property: every INVARIANT and DEADLOCK row of `Spec`, read from "
             f"`{tf[8:]}` (verdict and distinct states)")
    dl = {r["mut"]: r for r in dead}
    mprops = props + ["DEADLOCK Safety"]
    hsz = 12.5
    first_w = 190
    widths = [max(text_width(q, hsz, True) + 26, 150) for q in mprops]
    scale = (WW - first_w) / sum(widths)
    widths = [w * scale for w in widths]
    xcols = [("Mut", first_w, {"mono": True, "bold": True})] + [(q, w) for q, w in zip(mprops, widths)]
    xrows = []
    bad_cells = 0
    by = {}
    for r in t["rows"]:
        if r["spec"] == "Spec" and r["kind"] in ("INVARIANT", "DEADLOCK") and not r["prop"].startswith("Never"):
            key = (r["mut"], r["prop"] if r["kind"] == "INVARIANT" else "DEADLOCK Safety")
            by.setdefault(key, []).append(r)
    for m in muts_all:
        row = [m]
        flag = False
        for q in mprops:
            rs = by.get((m, q), [])
            if not rs:
                row.append("")
                continue
            parts = []
            for r in rs:
                acc = "red" if r["verdict"] == "COUNTEREXAMPLE" else "teal"
                st = n(r["states"]) if r["states"] is not None else "count not recorded"
                parts.append(f"[[{acc}|{r['verdict']}]] {st}")
            cell = "\n".join(parts)
            if q in safety and m != "none":
                expect = q in readme_breaks[m]
                got = any(r["verdict"] == "COUNTEREXAMPLE" for r in rs)
                if expect != got:
                    cell += "\n[[red|≠ README Breaks]]"
                    flag = True
                    bad_cells += 1
            if m == "none" and any(r["verdict"] != "HOLDS" for r in rs):
                cell += "\n[[red|≠ README]]"
                flag = True
                bad_cells += 1
            row.append(cell)
        xrows.append({"cells": row, "accent": "red"} if flag else ({"cells": row, "accent": "blue"} if m == "none"
                                                                     else row))
    y += c.table(X0, y, xcols, xrows, size=13, hsize=hsz, accent="violet") + 20
    n_x = sum(len(v) for v in by.values())
    y += c.para(X0, y, WW, f"{n_x} rows; each cell gives the verdict and its distinct states. An empty cell is a "
                "pair no row runs (`Safety`, `TypeOK` and the deadlock audit run under `none` only). The `none` row "
                "(blue) is the text. Treaty rows run at `Treaties = {t1}`, hence the larger counts; `M_PREFVRA`'s run "
                "under `DaysBound`. "
                + ("**Every COUNTEREXAMPLE is in a column the README's Breaks cell names, and every column it names "
                   "has one**: no cell is marked." if not bad_cells else
                   f"[[red|{bad_cells} cells differ from the README's Breaks cell]] and are marked."), 14,
                "muted") + 30
    y += row_cards(c, X0, y, WW, 30, [
        ("Three properties changed meaning (README § `Executive.tla`)", [plain(x) for x in R["changed"]]
         + [plain(R["new"])], "violet", {}),
        ("One the prover found (README § Findings)", [plain(R["finding"])], "pink", {}),
        ("What each mutation reverts to (module header, MUTATIONS)", [
            f"{len(muts) - len(H['noearlier'])} are earlier law or practice: placemen in the Commons, the pre-1998 reading of the Vacancies Act, "
            "the FEC of 1974, Gramm–Rudman–Hollings, the 1921 Act's joint resolution, Humphrey's Executor until "
            "Slaughter, Danby's pardon (1679), the Crown's prerogative, the draft of 6 August 1787.",
            f"{len(H['noearlier'])} say \"No earlier text\": " + code(H["noearlier"]) + "; the README's Reverts "
            "to cell for each is \"" + "\", \"".join(sorted({readme_muts[m][2] for m in H["noearlier"]})) + "\"."],
         "violet", {}),
    ]) + 70

    # ================================================================ band 4: witnesses
    y = band(c, X0, y, f"Witnesses: {len(wit)} `Never…` properties, each violated under `Mut = \"none\"`, read from "
             "the results file", status="checked", extra="existential, never proved")
    phrase = {
        "NeverAgency": "an agency created", "NeverAbolished": "one abolished", "NeverHead": "a head confirmed",
        "NeverPresidentRemoves": "one removed by the President",
        "NeverCongressRemoves": "Congress removing its own officer",
        "NeverActing": "an acting officer serving", "NeverActingExpires": "one timing out",
        "NeverCongressAppoints": "Congress appointing a non-executing body's officer",
        "NeverProtectedHead": "a for-cause-protected head", "NeverDisqualified": "a disqualification",
        "NeverSelfDeclared": "a voluntary", "NeverCabinetDeclared": "an involuntary inability declaration",
        "NeverCongressSustains": "a contest before Congress sustained", "NeverCongressRestores": "one lost",
        "NeverSuccession": "the VP succeeding", "NeverWar": "war declared", "NeverTreaty": "a treaty ratified",
        "NeverPardon": "a pardon", "NeverPresidentConvenes": "the President convening Congress",
    }
    wtxt = " ".join(R["witnesses"]).replace("\n", " ")
    wtxt = " ".join(wtxt.split())
    need({r["prop"] for r in wit} == set(phrase), tf, f"witness rows {sorted(r['prop'] for r in wit)} are not the "
         "nineteen this diagram maps")
    for v in phrase.values():
        need(v in wtxt, "README.md", f"§ Executive.tla Witnesses: no phrase {v!r}")
    ww1 = 860
    hwl = c.card(X0, y, ww1, "Witnesses (each violated): the README's list", [plain(x) for x in R["witnesses"]],
                 accent="green", size=S)
    hwl += 24 + c.card(X0, y + hwl + 24, ww1, "REACHABILITY WITNESSES: the module header's list (`Executive.tla`)",
                       [H["witnesses"], "Each \"must be VIOLATED under `\"none\"`\" (its heading). The rows run "
                        "state witnesses as INVARIANT rows and step witnesses as PROPERTY rows (Expected: line)."],
                       accent="green", size=S)
    wcols = [("Row", 250, {"mono": True}), ("Witness", 300, {"mono": True, "bold": True}), ("Kind", 130),
             ("The README's phrase (the diagram's join)", 560), ("Verdict", 200), ("Distinct states", 220)]
    wcols.append(("What the kind means", WW - ww1 - 30 - sum(x[1] for x in wcols)))
    wrows = []
    for r in wit:
        wrows.append([r["name"], r["prop"], r["kind"], f"\"{phrase[r['prop']]}\"",
                      f"[[green|{r['verdict']}]]", n(r["states"]) if r["states"] is not None else "count not recorded",
                      "a state predicate" if r["kind"] == "INVARIANT" else "`[][...]_vars`, which names a step"])
    hwt = c.table(X0 + ww1 + 30, y, wcols, wrows, size=13.5, accent="green")
    y += max(hwl, hwt) + 20
    y += c.para(X0, y, WW, "A witness is checked, never proved: a run that reaches a state is evidence it is reachable "
                "at those constants (README § How …, What is not proved). TLC records no distinct-state count for a "
                "PROPERTY row's counterexample. \"State predicates are INVARIANT rows; [][...]_vars ones, which name "
                "a step, are PROPERTY rows\" (`Executive.tla`, before the witnesses).", 14, "muted") + 70

    # ================================================================ band 5: liveness
    y = band(c, X0, y, "Liveness: `ActingEventuallyEnds`, checked under the fair spec and shown to need both "
             "fairness conditions", status="notproved")
    lcols = [("Row", 250, {"mono": True}), ("Spec", 180, {"mono": True, "bold": True}),
             ("Constant override", 200, {"mono": True}), ("PROPERTY", 280, {"mono": True}), ("Verdict", 200),
             ("Distinct states", 220), ("What the row shows (`Executive.tla`, rows header)", 1100)]
    lcols.append(("Status", WW - sum(x[1] for x in lcols)))
    meaning = {
        ("SpecLive", "ActingEventuallyEnds"): "Under `ClockRuns` and `LimitBinds` every acting officer's service ends.",
        ("SpecNoClock", "ActingEventuallyEnds"): "Without `ClockRuns` the days need not pass: acting service can "
                                                 "last for ever.",
        ("SpecNoLimit", "ActingEventuallyEnds"): "Without `LimitBinds` the limit can be reached and service not "
                                                 "ended.",
        ("SpecLive", "NoBehaviour"): "`NoBehaviour == <>FALSE` is violated, so the fair spec has a behaviour and "
                                     "the HOLDS is not vacuous.",
    }
    lrows = []
    for r in live:
        k = (r["spec"], r["prop"])
        need(k in meaning, tf, f"a liveness row this diagram does not explain: {r['name']}")
        st = ("[[amber|Checked, not proved]]" if r["prop"] == "ActingEventuallyEnds" and r["verdict"] == "HOLDS"
              else "Checked · TLC")
        lrows.append([r["name"], r["spec"], " ".join(r["overrides"]) or "(defaults)", r["prop"],
                      f"[[{'red' if r['verdict'] == 'COUNTEREXAMPLE' else 'teal'}|{r['verdict']}]]",
                      n(r["states"]) if r["states"] is not None else "count not recorded", meaning[k], st])
    y += c.table(X0, y, lcols, lrows, size=13.5, accent="amber") + 24
    y += row_cards(c, X0, y, WW, 30, [
        ("The fair spec (`Executive.tla`, Liveness)", [
            "`ActingEventuallyEnds == \\A a \\in Agencies : (agency[a].acting # NoOne) ~> (agency[a].acting = NoOne)`"
            ": the Take Care Clause read with the FVRA.",
            "`SpecLive == Spec /\\ ClockRuns /\\ LimitBinds`; `SpecNoClock` drops `ClockRuns`; `SpecNoLimit` drops "
            "`LimitBinds`. Each is weak fairness for every agency.", "`Spec` has no fairness: the liveness claim "
            "is under `SpecLive` only (module header, LIVENESS)."], "amber", {}),
        ("README § `Executive.tla`, Liveness", [plain(R["liveness"])], "amber", {}),
        ("Why it is not proved (`Executive_proof.tla` header, NOT PROVED)", [
            "\"a leads-to quantified over Agencies inside the temporal body, with fairness on ActingTick(a) and "
            "ActingExpires(a) for each a\": the case the method's prover habits record as having no sound route "
            "in this prover.", "\"checked by TLC at one agency and ActingLimit = 1 and 2, with each fairness "
            "condition shown necessary and the fair spec non-empty.\""], "amber", {"status": "notproved"}),
    ]) + 70

    # ================================================================ band 6: proofs
    y = band(c, X0, y, f"The proofs: {len(p['theorems'])} theorems read from `{pf[8:]}`, each `Spec => []P` under "
             "the hypotheses it names", status="proved", extra=f"{n(p['obligations'])} obligations")
    pcols = [("THEOREM", 420, {"mono": True, "bold": True}), ("ASSUME (the mutations it assumes absent)", 640),
             ("PROVE", 470, {"mono": True}),
             ("Mutations with a COUNTEREXAMPLE on P (TLC results, read)", 640),
             ("Hypotheses = counterexamples? (the diagram's check)", 360)]
    pcols.append(("Strengthened by (`Executive_proof.tla` header, INDUCTIVE STRENGTHENING)",
                  WW - sum(x[1] for x in pcols)))
    streng = {
        "OneExecutive": "`DistinctOffices` and `ActingSeated`, each inductive alone",
        "Incompatibility": "`NoNewOfficer`: `NotIn(Congress)`, no case split",
        "Disqualification": "`NotIn(disqualified)` with `DistinctOffices`; `ConvictRemoves`",
        "ActingIsNotHead": "inductive alone, decided by `OfficeVacant`",
        "ActingIsTemporary": "inductive alone, decided by `WithinLimit`",
        "ExecutionIsExecutive": "`StatuteFrame`",
        "UnitaryExecutive": "`StatuteFrame`",
        "NoCongressionalAppointment": "`CongressVestingOK`: the Buckley check written over the state",
        "CongressDoesNotRemoveExecutors": "`ExecutionIsExecutive`",
        "PardonScope": "inductive alone (`FlagFrame`)",
        "WarIsCongressional": "inductive alone (`FlagFrame`)",
        "TreatiesByTwoThirds": "inductive alone (`FlagFrame`)",
        "TypeOK": "cited by every lemma, under every mutation",
        "Safety": "the twelve together, under `Mut = \"none\"`",
    }
    prow = []
    covered = set()
    for x in p["theorems"]:
        pm = re.fullmatch(r"Spec => \[\](\w+)", x["prove"])
        need(pm, pf, f"{x['name']}: PROVE is not 'Spec => []P'")
        q = pm.group(1)
        covered.add(q)
        need(q in streng, pf, f"{x['name']}: a property this diagram does not draw")
        hm = sorted(re.fullmatch(r'Mut # "(M_\w+)"', a).group(1) for a in x["assume"]
                    if re.fullmatch(r'Mut # "(M_\w+)"', a))
        if q in safety:
            ce = sorted(m for m in muts if "COUNTEREXAMPLE" in cells.get((m, q), set()))
            agree = "[[teal|yes]]" if ce == hm else "[[red|NO]]"
            if ce != hm:
                disagree.append(x["name"])
            ce_s = code(ce)
        elif q == "TypeOK":
            ce_s = "run under `none` only: " + "/".join(cells.get(("none", "TypeOK"), {"none"}))
            agree = "— (no mutation breaks it; proved under every one)"
        else:
            ce_s = "run under `none` only: " + "/".join(cells.get(("none", "Safety"), {"none"}))
            agree = "— (`SafeAlways` assumes `Mut = \"none\"`)"
        prow.append([x["name"], ", ".join(f"`{a}`" for a in x["assume"]) or "none: every mutation",
                     x["prove"], ce_s, agree, streng[q]])
    need(covered >= set(safety), pf, "a safety property with no theorem")
    y += c.table(X0, y, pcols, prow, size=13.5, accent="blue") + 24
    lem = p["lemmas"]
    admits = [x for x in lem if x.startswith("Mut") and x.endswith("Admits")]
    need(len(admits) == len(muts), pf, f"one Mut…Admits lemma per mutation expected: {len(admits)} vs {len(muts)}")
    others = [x for x in lem if x not in admits]
    y += row_cards(c, X0, y, WW, 30, [
        (f"The {len(lem)} lemmas (proof results, LEMMAS)", [
            f"Invariants and frames ({len(others)}): " + ", ".join(f"`{x}`" for x in others) + ".",
            f"One per mutation, what it admits ({len(admits)}): " + ", ".join(f"`{x}`" for x in admits) + "."],
         "blue", {}),
        ("The prover and the run (proof results header)", [
            f"Prover: {p['prover']}.", f"Backends: {p['backends']}.",
            f"Command: `{p['command']}`.", f"Result: all {n(p['obligations'])} obligations proved, under the "
            f"theorems' hypotheses. It names `{tf[8:]}` by sha256 for the counterexamples and the witnesses, and "
            "this diagram checked that digest."], "blue", {"status": "proved"}),
        ("What the words say (proof results, Words:)", [
            p["words"].rstrip(".") + ".", "Not proved here: `ActingEventuallyEnds`, the witnesses and the "
            "mutations' counterexamples, which are existential and stay with TLC (`Executive_proof.tla` header, "
            "NOT PROVED)."], "amber", {}),
    ]) + 30

    if disagree:
        y += c.para(X0, y, WW, "[[red|Disagreements found at build time]]: " + ", ".join(f"`{d}`" for d in disagree),
                    15, "ink") + 20
    return c
