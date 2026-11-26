"""B5 — Elections.tla: the presidential cycle, each rule one guard that TLC shows the model depends on and TLAPS proves.

The picture of the module's machines (the States, the electors, the count, the House and the Senate, noon on
20 January, the offices, acting, the term), the README's two tables whole, the mutation x property matrix read from
the named TLC results file one line per (mutation, constants), the witnesses, the PROPERTY rows, the theorems with
their hypotheses, the README's findings for the module, the row constants and Elections.cfg beside c-cfg-safety,
and one band from docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md.

Build-time reads (each raises corpus.CorpusError on a shape it does not expect, so the generator prints ERROR):
  - the TLC and proof results files corpus.RESULTS names for Elections, through corpus.py;
  - README.md § `Elections.tla` (its tables, lists and paragraphs) and § Findings, "In `Elections.tla`";
  - specs/Elections.tla's header (MUTATIONS) and its Stages and Clocks; specs/Elections.cfg's CONSTANTS;
  - rows/Elections-rows.txt's `# const:` block and its rows (for the constraint the results file does not print);
  - specs/Elections_proof.tla's text, for where its first end-of-module line falls among its lemmas.
"""
import re

from lib import Canvas, STATUS, text_width
import corpus as C

ID, SLUG = "B5", "elections"

W = 3600
S = 14
MOD = "Elections"
TF, PF = C.RESULTS[MOD]


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


def md(s):
    """README markdown to the library's rich text: *italic* has no style here, so its asterisks are dropped."""
    return re.sub(r"(?<![*\w])\*(?!\*)([^*]+?)\*(?![*\w])", r"\1", s)


def camel(name, maxw, size=12.5):
    """A long TLA+ name broken at its capitals into lines that fit a matrix header."""
    parts = re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z]*|[a-z]+|[0-9]+", name)
    need("".join(parts) == name, "diagram", f"cannot split {name}")
    lines, cur = [], ""
    for p in parts:
        if cur and text_width(cur + p, size, True) > maxw:
            lines.append(cur)
            cur = p
        else:
            cur += p
    lines.append(cur)
    return "\n".join(lines)


# ---------------------------------------------------------------------------------------------- build-time reads
README_HEAD = "### `Elections.tla` — the presidential cycle"


def readme_blocks():
    """README § Elections.tla as blocks: ('table', header, rows), ('list', [items]), ('para', text)."""
    lines = C.read("README.md").splitlines()
    need(README_HEAD in lines, "README.md", "no Elections.tla section")
    i = lines.index(README_HEAD) + 1
    j = i
    while j < len(lines) and not lines[j].startswith("### "):
        j += 1
    sec = lines[i:j]
    blocks, cur = [], []
    for ln in sec + [""]:
        if ln.strip():
            cur.append(ln)
            continue
        if not cur:
            continue
        if all(x.startswith("|") for x in cur):
            rows = [[cell.strip() for cell in x.strip().strip("|").split("|")] for x in cur]
            need(len(rows) > 2 and set(rows[1]) <= {"---"}, "README.md", f"table without a rule: {cur[0]!r}")
            need(all(len(r) == len(rows[0]) for r in rows), "README.md", f"ragged table: {cur[0]!r}")
            blocks.append(("table", rows[0], rows[2:]))
        elif cur[0].startswith("- "):
            items = []
            for x in cur:
                if x.startswith("- "):
                    items.append(x[2:].strip())
                else:
                    need(x.startswith("  ") and items, "README.md", f"list line does not continue: {x!r}")
                    items[-1] += " " + x.strip()
            blocks.append(("list", [md(t) for t in items]))
        else:
            blocks.append(("para", md(" ".join(x.strip() for x in cur))))
        cur = []
    return blocks


def readme_section():
    b = readme_blocks()
    out = {}

    def after(prefix, kind):
        for k, blk in enumerate(b):
            if blk[0] == "para" and blk[1].startswith(prefix):
                need(k + 1 < len(b) and b[k + 1][0] == kind, "README.md", f"no {kind} after {prefix!r}")
                return blk[1], b[k + 1]
        raise C.CorpusError(f"README.md § Elections.tla: no paragraph {prefix!r}")

    tables = [blk for blk in b if blk[0] == "table"]
    need(len(tables) == 2, "README.md", f"§ Elections.tla has {len(tables)} tables, not 2")
    need(tables[0][1] == ["Provision", "Where"], "README.md", "provisions table header")
    need(tables[1][1] == ["Mutation", "Removes", "Earlier text, doctrine or practice", "Breaks"], "README.md",
         "mutation table header")
    out["provisions"], out["mutations"] = tables[0][2], tables[1][2]
    out["intro"] = [blk for blk in b[:3]]
    need(b[0][0] == "para" and b[1][0] == "list" and b[2][0] == "para", "README.md", "opening is not para, list, para")
    out["abstracted"] = after("Abstracted:", "list")[1][1]
    out["readings_head"], rd = after("Three readings are fixed", "list")
    out["readings"] = rd[1]
    out["witnesses"] = after("Witnesses (each violated):", "list")[1][1]
    out["liveness_head"], lv = after("**Liveness.**", "list")
    out["liveness_fails"] = lv[1]
    for k, blk in enumerate(b):
        if blk[0] == "para" and blk[1].startswith("**Liveness.**"):
            need(b[k + 2][0] == "para", "README.md", "no paragraph after the liveness list")
            out["liveness_tail"] = b[k + 2][1]
    paras = {blk[1].split(".**")[0] + ".**": blk[1] for blk in b if blk[0] == "para" and blk[1].startswith("**")}
    for key in ("**`CountCanClose`.**", "**Proof.**", "**Rows.**"):
        need(key in paras, "README.md", f"no paragraph {key}")
    out["canclose"], out["proof"], out["rows"] = paras["**`CountCanClose`.**"], paras["**Proof.**"], paras["**Rows.**"]
    safety = [blk[1] for blk in b if blk[0] == "para" and blk[1].startswith("`Safety` is the conjunction")]
    need(len(safety) == 1, "README.md", "no `Safety` is the conjunction ... sentence")
    out["safety"] = safety[0]
    need(b[-1][0] == "para" and b[-1][1].startswith("The rows cannot reach"), "README.md", "last paragraph")
    out["cannot"] = b[-1][1]
    return out


def readme_findings():
    lines = C.read("README.md").splitlines()
    k = [i for i, ln in enumerate(lines) if ln.startswith("**In `Elections.tla`**")]
    need(len(k) == 1, "README.md", "§ Findings: no single 'In `Elections.tla`' paragraph")
    i = k[0]
    head = []
    while lines[i].strip():
        head.append(lines[i].strip())
        i += 1
    items = []
    i += 1
    while i < len(lines) and not lines[i].startswith("## "):
        ln = lines[i]
        if ln.startswith("- "):
            items.append(ln[2:].strip())
        elif ln.startswith("  ") and items:
            items[-1] += " " + ln.strip()
        else:
            need(not ln.strip(), "README.md", f"§ Findings, Elections: unexpected line {ln!r}")
        i += 1
    need(len(items) >= 5, "README.md", "§ Findings, Elections: too few items")
    return md(" ".join(head)), [md(t) for t in items]


def header_comment():
    """specs/Elections.tla's header comment as plain lines (the '(* ... *)' frame removed)."""
    lines = C.read("specs/Elections.tla").splitlines()
    out = []
    for ln in lines[2:]:
        if ln.startswith("(****"):
            break
        m = re.fullmatch(r"\(\* ?(.*?)\s*\*\)", ln)
        need(m, "specs/Elections.tla", f"header line not framed: {ln[:50]!r}")
        out.append(m.group(1))
    return out


def header_breaks(props):
    """The module header's MUTATIONS section: {mutation: (text, [properties named in it])}."""
    hc = header_comment()
    s = [i for i, x in enumerate(hc) if x.startswith("MUTATIONS")]
    e = [i for i, x in enumerate(hc) if x.startswith("Every other (mutation, property) pair")]
    need(len(s) == 1 and len(e) == 1 and s[0] < e[0], "specs/Elections.tla", "header has no MUTATIONS section")
    out, cur = {}, None
    for x in hc[s[0] + 1:e[0]]:
        m = re.match(r"^\s{2}(M_[A-Z0-9_]+)\s+(.*)$", x)
        if m:
            cur = m.group(1)
            out[cur] = m.group(2).strip()
        else:
            need(cur and x.startswith("  "), "specs/Elections.tla", f"MUTATIONS line: {x!r}")
            out[cur] += " " + x.strip()
    res = {}
    for k, v in out.items():
        named = [p for p in props if re.search(rf"\b{p}\b", v)]
        res[k] = (v, named)
    return res


def spec_enum(name):
    """A Stages/Clocks set of the module: [(value, comment)]."""
    lines = C.read("specs/Elections.tla").splitlines()
    k = [i for i, ln in enumerate(lines) if ln.startswith(f"{name} == {{")]
    need(len(k) == 1, "specs/Elections.tla", f"no {name} == {{ ... }}")
    out = []
    i = k[0]
    closed = False
    while i < len(lines):
        ln = lines[i]
        m = re.search(r'"(\w+)"\s*([,}])\s*\\\*\s*(.*)$', ln)
        if m and not closed:
            out.append([m.group(1), m.group(3).strip()])
            closed = m.group(2) == "}"
        elif re.match(r"^\s+\\\*", ln) and out:
            out[-1][1] += " " + ln.strip()[2:].strip()
        else:
            break
        i += 1
    need(closed and out, "specs/Elections.tla", f"{name} does not parse")
    return out


def cfg_constants():
    lines = C.read("specs/Elections.cfg").splitlines()
    need("CONSTANTS" in lines, "specs/Elections.cfg", "no CONSTANTS")
    out = {}
    for ln in lines[lines.index("CONSTANTS") + 1:]:
        if not ln.strip():
            break
        m = re.fullmatch(r"\s+(\w+)\s+=\s+(.+?)\s*", ln)
        need(m, "specs/Elections.cfg", f"constant line {ln!r}")
        out[m.group(1)] = m.group(2)
    spec = [ln.split()[1] for ln in lines if ln.startswith("SPECIFICATION")]
    inv = lines[lines.index("INVARIANTS") + 1:] if "INVARIANTS" in lines else []
    return out, spec, [x.strip() for x in inv if x.strip()]


def rows_file(rel):
    text = C.read(rel).splitlines()
    consts, rows, binds = {}, {}, []
    state = None
    for ln in text:
        if ln.startswith("# const: "):
            k, _, v = ln[len("# const: "):].partition(" = ")
            consts[k] = v
        elif ln.startswith("# Each mutation runs against every property"):
            state = "wait"
        elif state in ("wait", "in"):
            m = re.match(r"^#   (M_[A-Z0-9_, ]+?)\s{2,}(.+)$", ln)
            if m:
                binds.append([m.group(1).strip(), m.group(2).strip()])
                state = "in"
            elif state == "in":
                state = None
        if ln.strip() and not ln.startswith("#"):
            f = ln.split()
            need(len(f) >= 6, rel, f"row {ln[:40]!r}")
            rows[f[0]] = dict(mut=f[1], spec=f[2], kind=f[3], prop=f[4], expected=f[5], opts=f[6:])
    need(len(consts) == 14 and binds, rel, "no # const: block or no binding-constants list")
    return consts, rows, binds


def read_all():
    t, p = C.tlc_results(TF), C.proof_results(PF)
    need(C.newest("tlc", MOD) == TF and C.newest("proof", MOD) == PF, "corpus.RESULTS",
         "Elections' named results files are not the newest committed ones")
    for res, rel in ((t, TF), (p, PF)):
        for f, digest in res["modules"].items():
            need(C.sha256(f"specs/{f}") == digest, rel, f"{f} has moved since it was checked")
    need(C.sha256(t["rows_file"]) == t["rows_sha"], TF, "the row list has moved since the run")
    need(p["tlc_file"] == TF and C.sha256(TF) == p["tlc_sha"], PF, "does not name the TLC results file drawn")
    need(t["as_expected"] == t["total"] and not t["not"] and not t["error"], TF, "not every row is as expected")
    return t, p


# ---------------------------------------------------------------------------------------------- the diagram
def build():
    t, p = read_all()
    R = readme_section()
    find_head, find_items = readme_findings()
    summary = C.readme_summary()[MOD]
    muts = C.mutations(t)
    wit = C.witnesses(t)
    rows_rel = t["rows_file"]
    rconsts, rrows, rbinds = rows_file(rows_rel)
    need(set(rrows) == {r["name"] for r in t["rows"]}, rows_rel, "rows file and results file name different rows")
    for r in t["rows"]:
        rr = rrows[r["name"]]
        need(rr["mut"] == r["mut"] and rr["prop"] == r["prop"] and rr["expected"] == r["verdict"]
             and [o for o in rr["opts"] if not o.startswith("constraint=")] == r["overrides"], rows_rel,
             f"row {r['name']} differs from its results line")

    # the nineteen, in Safety's order (the theorems' order)
    props19 = [th["name"][:-len("Always")] for th in p["theorems"]
               if th["name"].endswith("Always") and th["name"] not in ("TypeOKAlways", "SafeAlways",
                                                                         "ExecutiveIsFilledAlways")]
    need(len(props19) == 19, PF, f"{len(props19)} safety theorems, not nineteen")
    hb = header_breaks(props19 + ["ExecutiveIsFilled"])
    need(sorted(hb) == sorted(muts), "specs/Elections.tla", "header MUTATIONS and the results' mutations differ")

    inv_rows = [r for r in t["rows"] if r["kind"] == "INVARIANT" and r["spec"] == "Spec"
                and not r["prop"].startswith("Never")]
    mprops = ["TypeOK", "Safety"] + props19
    need({r["prop"] for r in inv_rows} == set(mprops), TF, "INVARIANT rows on Spec name other properties")
    other_specs = sorted({r["spec"] for r in t["rows"] if r["kind"] == "INVARIANT"} - {"Spec"})
    need(not other_specs, TF, f"INVARIANT rows on specs other than Spec: {other_specs}")

    # CE by mutation, with constants (INVARIANT on Spec) and on PROPERTY rows
    ce = {}
    for r in t["rows"]:
        if r["mut"] != "none" and r["verdict"] == "COUNTEREXAMPLE":
            ce.setdefault(r["mut"], []).append(r)
    readme_mut = {}
    for row in R["mutations"]:
        m = re.fullmatch(r"`(M_[A-Z0-9_]+)`", row[0])
        need(m, "README.md", f"mutation cell {row[0]!r}")
        readme_mut[m.group(1)] = row
    need(list(readme_mut) == muts, "README.md", "the mutation table's mutations are not the results file's, in order")

    def names_in(s):
        return [x for x in re.findall(r"`(\w+)`", s) if x in props19 + ["ExecutiveIsFilled"]]

    ok_mut = {}
    for m in muts:
        rb = set(names_in(readme_mut[m][3]))
        hd = set(hb[m][1])
        rs = {r["prop"] for r in ce.get(m, [])}
        ok_mut[m] = (rb == hd == rs, rb, hd, rs)

    obl = p["obligations"]
    W_N = len(wit)
    live = [r for r in t["rows"] if r["kind"] == "PROPERTY" and not r["prop"].startswith("Never")]
    dead_rows = [r for r in t["rows"] if r["kind"] == "DEADLOCK"]
    need(all(r["verdict"] == "HOLDS" for r in dead_rows), TF, "a DEADLOCK row that is not HOLDS")
    thm = {th["name"]: th for th in p["theorems"]}
    need("ExecutiveIsFilledAlways" in thm, PF, "no ExecutiveIsFilledAlways")
    eif = thm["ExecutiveIsFilledAlways"]

    # the proof module's text: where its first end-of-module line falls
    ptext = C.read("specs/Elections_proof.tla").splitlines()
    ends = [i + 1 for i, ln in enumerate(ptext) if re.fullmatch(r"={4,}\s*", ln)]
    need(len(ends) >= 1, "specs/Elections_proof.tla", "no end-of-module line")
    lem_line = {}
    for i, ln in enumerate(ptext):
        m = re.match(r"^LEMMA\s+(\w+)\s*==", ln)
        if m:
            lem_line[m.group(1)] = i + 1
    need(sorted(lem_line) == sorted(p["lemmas"]), PF, "the LEMMAS line and the proof module's LEMMAs differ")
    after_end = [x for x in p["lemmas"] if lem_line[x] > ends[0]]
    thm_after = [i + 1 for i, ln in enumerate(ptext) if ln.startswith("THEOREM") and i + 1 > ends[0]]
    admits = [x for x in p["lemmas"] if x.startswith("Mut") and x.endswith("Admits")]
    hyps = sum(len([a for a in th["assume"] if a.startswith("Mut #")]) for th in p["theorems"])

    # ------------------------------------------------------------------ canvas
    c = Canvas(ID, "`Elections.tla`: the presidential cycle from the appointment of electors to noon on 20 January "
               "and the next election day, each rule one guard that TLC shows the model depends on and TLAPS proves",
               f"The States appoint electors, the electors vote on one day, Congress counts and announces or sends "
               f"the choice to the House and the Senate, and at noon on 20 January the old term ends whether or not "
               f"anyone was chosen (README § `Elections.tla`). Each of {len(muts)} mutations removes one guard, and "
               f"TLC finds its counterexample at the constants where the guard binds: **{n(t['total'])} rows, every "
               f"one as expected**. TLAPS proves the nineteen safety properties under exactly the mutations that "
               f"break them, and `ExecutiveIsFilled` under `FairSpec` by one WF1 step: **{n(obl)} obligations, all "
               f"proved**. **Not proved**, and TLC's: the witnesses, the counterexamples, that weaker fairness fails "
               f"and that `FairSpec` has a behaviour. This models the text's procedure; **it is an exercise, not "
               f"law** (README, opening).",
               W, "README.md (opening; § How the specs are written and checked, its summary table and What is not "
               "proved; § Modules, `Elections.tla` — the presidential cycle: its opening, provisions table, "
               "Abstracted, Three readings, mutation table, Safety, Witnesses, CountCanClose, Liveness, Proof, Rows; "
               "§ Findings, In `Elections.tla`); specs/Elections.tla (header: PROPERTIES, LIVENESS, MUTATIONS, "
               "DEADLOCK, REACHABILITY WITNESSES, ABSTRACTED; Stages, Clocks; the checks; the college, count, "
               "contingent, noon, acting and term actions; the safety, witness and liveness operators); "
               "specs/Elections.cfg; specs/Elections_proof.tla (header: THEOREMS, ASSUMPTIONS, INDUCTIVE "
               "STRENGTHENING, NOT PROVED; the theorems; the liveness section; the end-of-module lines); "
               f"{rows_rel} (header comments, # const: block, rows); {TF}; {PF}; scripts/proof_results.py "
               "(statements); docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md § 2, § 7.6, § 8")
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    live_ce = [r for r in live if r["verdict"] == "COUNTEREXAMPLE"]
    items = [("Elections.tla", [("checked", f"{n(t['total'])} rows"), ("proved", f"{n(obl)} obligations")]),
             ("Nineteen safety properties", [("proved", "each under its mutations' absence"),
                                             ("checked", "HOLDS unmutated")]),
             ("ExecutiveIsFilled", [("proved", "one WF1 step, FairSpec"), ("checked", "HOLDS under FairSpec")]),
             (f"Weaker fairness fails; FairSpec has a behaviour ({len(live_ce)} PROPERTY rows)", [("notproved", "")]),
             (f"No terminal state ({len(dead_rows)} DEADLOCK rows)", [("notproved", "")]),
             ("Witnesses", [("checked", f"{W_N}, existential")]),
             ("Mutations' counterexamples", [("checked", f"{len(muts)} mutations, existential")]),
             ("Mut…Admits lemmas", [((f"{len(after_end)} of {len(admits)} after the first end-of-module line",
                                      "red", "6 4"), "")]),
             ("Flip tests", [(("No results file", "red", "2 3"), "")])]
    y = status_strip(c, X0, X1, y, items)
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row list. "
                "**Proved** means TLAPS discharged every obligation for every value of the constants the module's "
                "named assumptions admit. **Sampled** means random simulation found no error; this module has no "
                "sampled row. \"None of these is a claim about law or practice\" (README § How the specs are written "
                "and checked). The README's summary table gives `Elections.tla` "
                f"{n(summary['rows'])} rows, {summary['mutations']} mutations, {summary['witnesses']} witnesses and "
                f"{n(summary['obligations'])} obligations; the results files give {n(t['total'])}, {len(muts)}, "
                f"{W_N} and {n(obl)}" + (" (equal)." if (summary['rows'], summary['mutations'], summary['witnesses'],
                                                         summary['obligations']) == (t['total'], len(muts), W_N, obl)
                                          else " ([[red|they differ]]).") + "", 14.5, "muted") + 30

    # ---- band 0: README opening, and the two clocks
    y = band(c, X0, y, "One election, then the next: the module is `Constitution.tla`'s and `Executive.tla`'s "
             "one `Elect` step, drawn out (README § `Elections.tla`, opening)")
    intro = R["intro"]
    stages, clocks = spec_enum("Stages"), spec_enum("Clocks")
    need([s for s, _ in stages] == ["Appointing", "Voting", "Voted", "Counting", "Counted"], "specs/Elections.tla",
         "Stages are not the five drawn")
    need([s for s, _ in clocks] == ["Founding", "BeforeNoon", "FirstHalf", "SecondHalf"], "specs/Elections.tla",
         "Clocks are not the four drawn")
    lw = 980
    h0 = c.card(X0, y, lw, "What the module is (README § `Elections.tla`)", [intro[0][1]] + intro[1][1] +
                [intro[2][1]], accent="teal", size=S)
    # the two clocks, as lanes of small cards
    gx = X0 + lw + 60
    gw = X1 - gx
    sw = (gw - 4 * 70) / 5
    c.text(gx, y + 16, "`stage`: where the election stands (`Stages`)", 16, "teal", bold=True)
    sy = y + 30
    sh = max(c.card(0, 0, sw, f"`{v}`", [cm], draw=False, size=13, bullets=False) for v, cm in stages)
    for i, (v, cm) in enumerate(stages):
        c.card(gx + i * (sw + 70), sy, sw, f"`{v}`", [cm], accent="teal", h=sh, size=13, bullets=False)
    for i, act in enumerate(["ElectionDayEnds", "ElectorsAdjourn", "OpenCount", "Announce"]):
        ax = gx + i * (sw + 70) + sw
        c.arrow([(ax + 4, sy + sh / 2), (ax + 66, sy + sh / 2)], "teal")
        c.text(ax + 35, sy + sh + 20, f"`{act}`", 12.5, "teal", anchor="middle")
    ry = sy + sh + 46
    c.arrow([(gx + 4 * (sw + 70) + sw / 2, sy + sh + 4), (gx + 4 * (sw + 70) + sw / 2, ry),
             (gx + sw / 2, ry), (gx + sw / 2, sy + sh + 6)], "teal", dash="7 5",
            label="`OpenElection` clears the college and the lists: \"whatever the last election left undecided is "
                  "moot\"", lpos=0.5, lsize=12.5)
    cy0 = ry + 40
    c.text(gx, cy0 + 16, "`clock`: where the term stands (`Clocks`)", 16, "teal", bold=True)
    cy1 = cy0 + 80
    cw4 = (gw - 3 * 110) / 4
    ch = max(c.card(0, 0, cw4, f"`{v}`", [cm], draw=False, size=13, bullets=False) for v, cm in clocks)
    for i, (v, cm) in enumerate(clocks):
        c.card(gx + i * (cw4 + 110), cy1, cw4, f"`{v}`", [cm], accent="teal", h=ch, size=13, bullets=False)
    # Founding -> FirstHalf and BeforeNoon -> FirstHalf by the noon steps; FirstHalf -> SecondHalf Midterm;
    # SecondHalf -> BeforeNoon OpenElection
    xa = lambda i: gx + i * (cw4 + 110)
    c.arrow([(xa(1) + cw4 + 4, cy1 + ch / 2), (xa(2) - 4, cy1 + ch / 2)], "teal")
    c.arrow([(xa(2) + cw4 + 4, cy1 + ch / 2), (xa(3) - 4, cy1 + ch / 2)], "teal")
    c.text(xa(2) + cw4 + 55, cy1 + ch / 2 - 10, "`Midterm`", 12.5, "teal", anchor="middle")
    by = cy1 + ch + 34
    c.arrow([(xa(3) + cw4 / 2, cy1 + ch + 4), (xa(3) + cw4 / 2, by), (xa(1) + cw4 / 2, by),
             (xa(1) + cw4 / 2, cy1 + ch + 6)], "teal", label="`OpenElection`: election day again", lpos=0.5)
    ty = cy1 - 24
    c.arrow([(xa(0) + cw4 / 2, cy1 - 4), (xa(0) + cw4 / 2, ty), (xa(2) + cw4 * 0.3, ty),
             (xa(2) + cw4 * 0.3, cy1 - 4)], "teal")
    c.text(xa(1) + cw4 + 55, cy1 + ch / 2 - 10, "noon", 12.5, "teal", anchor="middle")
    c.text(xa(1) + cw4 / 2, ty - 8, "at the first noon: `NoonInaugurates`, `NoonSucceeds` or `NoonVacant` "
           "(`TermEnds`: once the count is open, finished or not)", 12.5, "teal", anchor="middle")
    y = max(y + h0, by + 30) + 50

    # ---- band 1: the picture
    y = band(c, X0, y, "The mechanism: who acts at each stage, the guard each rule is, and the mutation that "
             "removes it (`Elections.tla`, by its sections)")
    y += c.para(X0, y, WW, "Each card is one section of the module. A guard is drawn as `Guard` "
                "([[violet|M_X]] → `Property`): the mutation that removes it, and the safety property its removal "
                "must break (module header, MUTATIONS). Brown cards are the States and the electors; teal is the "
                "mechanism. Numbered arrows are what moves; the key is below the picture.", 14, "muted") + 30
    bus = 90                            # a reserved vertical lane at the right for arrow 5
    gap = 150
    cw = (WW - bus - 3 * gap) / 4
    cx = [X0 + i * (cw + gap) for i in range(4)]
    V = lambda m: f"[[violet|{m}]]"
    states_card = ("The States appoint — Art. II §1 cl. 2, cl. 4", [
        "`Appoint(e, c)`: a State fills seat `e` \"in such Manner as the Legislature thereof may direct\" with an "
        "elector pledged to `c`.",
        f"`AppointmentOpen`: only while `stage = \"Appointing\"`, election day ({V('M_FAILED_CHOICE')} → "
        "`AppointedOnElectionDay`).",
        f"`MayBeElector(e)`: no one in `Officers` ({V('M_OFFICER_ELECTOR')} → `ElectorsHoldNoOffice`).",
        "`ElectionDayEnds`: a seat not filled by now stays empty (New York, 1789).",
        "Abstracted: an elector is a seat some State fills; winner-take-all, districts and the popular vote are "
        "whatever pledges the seats get."], "brown", {})
    electors_card = ("The electors vote — Amend. XII; Chiafalo (2020)", [
        "`Vote(e, p, v)`: an appointed elector who has not voted names `p` for President and `v` for Vice "
        "President, \"in distinct ballots\".",
        f"`PollsOpen`: only while `stage = \"Voting\"`, one day ({V('M_LATE_VOTE')} → `SameDay`).",
        f"`TwoNames(p, v)`: two persons ({V('M_SAME_NAME')} → `CountCanClose`).",
        f"`Habitation(e, p, v)`: one at least not of the elector's State ({V('M_HABITATION')} → "
        "`OneNotAnInhabitant`).",
        f"`Faithful(e, p)`: an elector in `Binding` votes the pledge, **bound**; one outside it may depart, "
        f"**faithless** ({V('M_FAITHLESS')} → `PledgesBind`).",
        "`ElectorsAdjourn`: an elector who has not voted has cast no vote."], "brown", {})
    count_card = ("Congress counts — Amend. XII, XX §§1–2, 3 U.S.C. §15", [
        f"`OpenCount(new)`: `Seated(new)`, the Congress that assembled on 3 January ({V('M_PRE_XX')} → "
        "`NewCongressCounts`).",
        f"`Sustain(e, g, both)`: `Concur(both)`, both Houses ({V('M_PRESIDING')} → `CountIsCongress`). Ground "
        "`\"NotAppointed\"` takes `e` out of `Appointed`, the whole number; `\"NotRegular\"` does not.",
        f"`Announce(p, v)`: `PResult`, `VResult`, a majority of `Whole` ({V('M_PRE_XII')}, {V('M_PLURALITY')} → "
        f"`ElectorsChoose`; {V('M_ENTITLED')} → `DevolvesOnlyWithoutMajority`) and `TwoPersons(p, v)` "
        f"({V('M_ONE_PERSON')} → `PresidentNotVP`). The certificates are then spent.",
        "No one carries: `pList` = `PTop`, the three highest; `vList` = `VTop`, the two highest.",
        "`CountCanClose`: no guard decides it (README § `Elections.tla`, CountCanClose)."], "teal", {})
    house_card = ("The House chooses the President — Amend. XII", [
        "`HouseChooses(c, Q, Y)`: by States; `Q` present, `Y` for `c`; before noon or after it.",
        f"`OnList(c, pList)` ({V('M_OFF_LIST')} → `ChoiceFromTheList`); `HouseQuorum(Q)`, two-thirds of `States` "
        f"({V('M_HOUSE_QUORUM')}); `HouseCarries(Q, Y)`, a majority of all ({V('M_HOUSE_PRESENT')}) → `HouseVote`.",
        "A ballot that chooses no one is a stuttering step (thirty-five of them in 1801)."], "teal", {})
    senate_card = ("The Senate chooses the Vice President — Amend. XII", [
        f"`SenateChooses(c, Q, Y)`: `OnList(c, vList)` ({V('M_OFF_LIST')}); `SenateQuorum(Q)`, two-thirds "
        f"({V('M_SENATE_QUORUM')}); `SenateCarries(Q, Y)`, a majority of the whole number "
        f"({V('M_SENATE_PRESENT')}) → `SenateVote`."], "teal", {})
    noon_card = ("Noon on 20 January — Amend. XX §§1, 3; XXII", [
        "`TermEnds`: the clock is `Founding` or `BeforeNoon` and the count is open, finished or not. Exactly one "
        "of three steps is then enabled:",
        "`NoonInaugurates`: `Qualified(pElect)`; the President elect takes office, the Vice President elect too "
        f"if `VQualified`. `TermAllowed` ({V('M_XXII')}, {V('M_XXII_SERVICE')} → `TwoTermLimit`).",
        "`NoonSucceeds`: the President elect has died (`ElectGone`) and the Vice President elect becomes "
        f"President ({V('M_XX3_BECOMES')} → `VPElectBecomesOnlyOnDeath`).",
        "`NoonVacant`: no President: none chosen, or failed to qualify, or dead with no Vice President elect.",
        f"`VQualified`: `MeetsArticleII` ({V('M_UNQUALIFIED')} → `Qualifications`), `NotDisabled` "
        f"({V('M_XIV3')} → `Disability`)."], "teal", {})
    office_card = ("The offices: `president`, `vicePresident`, `acting`", [
        "`Qualify`, `VPQualify`: in the term, a President elect or Vice President elect qualifies late, \"until a "
        "President shall have qualified\"; whoever acted gives way (3 U.S.C. §19(c)).",
        f"`TwoPersons` at every seating ({V('M_ONE_PERSON')} → `PresidentNotVP`); `Qualified` where the office is "
        "taken.",
        "`ActingOrder`: no one acts while there is a President; the Vice President before the statute's officer.",
        "`InOffice` = the three seats; `Qualifications` and `Disability` are over it."], "teal", {})
    acting_card = ("Acting as President — Amend. XX §3, 3 U.S.C. §19", [
        "`VPActs`: no President, no one acting, a Vice President: `acting' = vicePresident`.",
        f"`SuccessorActs`: `Statute` ({V('M_NO_STATUTE')} → `ExecutiveIsFilled`, no safety property) and "
        f"`NoVP` ({V('M_SPEAKER_FIRST')} → `ActingOrder`): `acting' = Successor`, the Speaker, one person who "
        "never dies.",
        "`SomeoneActs` == `WF_vars(VPActs \\/ SuccessorActs)`: fairness on the two together. Under `FairSpec`, "
        "`ExecutiveIsFilled`: [[blue|proved]] (`ExecutiveIsFilledAlways`) and checked."], "teal", {})
    term_card = ("The term, and the people in it — Amend. XXV §1, XIV §3", [
        "`Die(x)`: a person in `Mortal` dies. A President's death makes the Vice President President "
        "(Amend. XXV §1); in the first half, that is service Amend. XXII counts (`servedLong`).",
        "`RemoveDisability(x)`: Congress removes an Amend. XIV §3 disability (`relieved`).",
        "`Midterm`: the second half of the term. `OpenElection`: election day again.",
        "Abstracted: death is the only way an office falls vacant in a term."], "grey", {})
    r1 = [states_card, electors_card, count_card]
    h_st = [c.card(0, 0, cw, t_, b_, draw=False, size=S) for t_, b_, _, _ in r1]
    h_h = c.card(0, 0, cw, house_card[0], house_card[1], draw=False, size=S)
    h_s = c.card(0, 0, cw, senate_card[0], senate_card[1], draw=False, size=S)
    cgap = 70
    h1 = max(max(h_st), h_h + cgap + h_s)
    r2 = [term_card, acting_card, office_card, noon_card]
    h2 = max(c.card(0, 0, cw, t_, b_, draw=False, size=S) for t_, b_, _, _ in r2)
    pad = 30
    y1 = y + 40
    y2 = y1 + h1 + 2 * pad + 170
    # regions
    c.region(cx[0] - pad, y1 - pad, 2 * cw + gap + 2 * pad, h1 + 2 * pad,
             "The college — Art. II §1, Amend. XII: the States and their electors", "brown")
    c.region(cx[2] - pad, y1 - pad, 2 * cw + gap + 2 * pad, h1 + 2 * pad,
             "Congress — the count and the contingent elections", "teal")
    c.region(cx[0] - pad, y2 - pad, cw + 2 * pad, h2 + 2 * pad, "The term (`TermSteps`)", "grey")
    c.region(cx[1] - pad, y2 - pad, 3 * cw + 2 * gap + 2 * pad, h2 + 2 * pad,
             "The executive power — `NoonSteps`: noon, the offices, acting", "teal")
    for i, s in enumerate(r1):
        c.card(cx[i], y1, cw, s[0], s[1], accent=s[2], h=h1, size=S)
    hs = h_s
    hh = h1 - cgap - hs
    c.card(cx[3], y1, cw, house_card[0], house_card[1], accent="teal", h=hh, size=S)
    c.card(cx[3], y1 + hh + cgap, cw, senate_card[0], senate_card[1], accent="teal", h=hs, size=S)
    for i, s in enumerate(r2):
        c.card(cx[i], y2, cw, s[0], s[1], accent=s[2], h=h2, size=S)
    # arrows, numbered
    L = lambda k: str(k)
    c.arrow([(cx[0] + cw + 6, y1 + h1 * 0.35), (cx[1] - 6, y1 + h1 * 0.35)], "brown", label=L(1))
    c.arrow([(cx[1] + cw + 6, y1 + h1 * 0.35), (cx[2] - 6, y1 + h1 * 0.35)], "brown", label=L(2))
    c.arrow([(cx[2] + cw + 6, y1 + hh / 2), (cx[3] - 6, y1 + hh / 2)], "teal", label=L(3))
    c.arrow([(cx[2] + cw + 6, y1 + hh + cgap + hs / 2), (cx[3] - 6, y1 + hh + cgap + hs / 2)], "teal",
            label=L(3))
    gy = y1 + h1 + pad + 85
    c.arrow([(cx[2] + cw / 2, y1 + h1 + 6), (cx[2] + cw / 2, gy), (cx[3] + cw * 0.3, gy),
             (cx[3] + cw * 0.3, y2 - 6)], "teal", label=L(4), lpos=0.25)
    bx = cx[3] + cw + bus / 2 + 6
    c.arrow([(cx[3] + cw + 6, y1 + hh / 2 + 40), (bx, y1 + hh / 2 + 40), (bx, y2 + 60),
             (cx[3] + cw + 6, y2 + 60)], "teal", label=L(5), lpos=0.5)
    c.line(cx[3] + cw + 6, y1 + hh + cgap + hs / 2 + 30, bx, y1 + hh + cgap + hs / 2 + 30, "teal", sw=2)
    c.arrow([(cx[3] - 6, y2 + h2 * 0.3), (cx[2] + cw + 6, y2 + h2 * 0.3)], "teal", label=L(6))
    c.arrow([(cx[1] + cw + 6, y2 + h2 * 0.3), (cx[2] - 6, y2 + h2 * 0.3)], "teal", label=L(7))
    c.arrow([(cx[2] - 6, y2 + h2 * 0.7), (cx[1] + cw + 6, y2 + h2 * 0.7)], "teal", label=L(8), dash="7 5")
    dy = y2 + h2 + pad + 45
    c.arrow([(cx[0] + cw * 0.5, y2 + h2 + 6), (cx[0] + cw * 0.5, dy), (cx[2] + cw * 0.5, dy),
             (cx[2] + cw * 0.5, y2 + h2 + 6)], "grey", dash="7 5", label=L(9), lpos=0.5)
    c.arrow([(cx[0] + cw * 0.5, y2 - 6), (cx[0] + cw * 0.5, y1 + h1 + 6)], "grey", label=L(10), lpos=0.5)
    y = dy + 50
    key = [
        ["1", "the States → the electors", "`Appoint(e, c)`; `ElectionDayEnds`",
         "a pledge per seat (`pledge`); `stage` `Appointing` → `Voting`"],
        ["2", "the electors → Congress", "`Vote(e, p, v)`; `ElectorsAdjourn`",
         "a ballot per elector (`ballot`); `stage` → `Voted`, the certificates on their way"],
        ["3", "the count → the House, the Senate", "`Announce(NoOne, …)`, `Announce(…, NoOne)`",
         "the choice and its list: `pList` = `PTop`, `vList` = `VTop`"],
        ["4", "the count → noon", "`Announce(p, v)`; or noon strikes while `stage = \"Counting\"`",
         "`pElect`, `vElect`; `TermEnds` needs only that the count is open"],
        ["5", "the House, the Senate → noon and the term", "`HouseChooses`, `SenateChooses`",
         "`pElect` or `vElect`, before noon or after it (then `Qualify`, `VPQualify`)"],
        ["6", "noon → the offices", "`NoonInaugurates`, `NoonSucceeds`, `NoonVacant`",
         "`president`, `vicePresident`; `acting = NoOne`; `clock` → `FirstHalf`"],
        ["7", "acting → the offices", "`VPActs`, `SuccessorActs`", "`acting`, while `president = NoOne`"],
        ["8", "the offices → acting (dashed: removes)", "`Qualify`, `VPQualify`; `Die`",
         "a qualifying President or Vice President elect, or a death, ends the acting (`acting' = NoOne`)"],
        ["9", "the term → the offices (dashed: removes)", "`Die(x)`",
         "empties a seat or moves the Vice President up (Amend. XXV §1); a dead President elect is `ElectGone`"],
        ["10", "the term → the States", "`OpenElection`",
         "`clock` `SecondHalf` → `BeforeNoon`, `stage` → `Appointing`, the college and the lists cleared"],
    ]
    y += c.table(X0, y, [("#", 60, {"bold": True}), ("From → to", 480), ("Action (`Elections.tla`)", 720),
                         ("What moves", WW - 1260)], key, size=13.5, accent="teal") + 50

    # ---- band 2: provisions table, abstracted, readings
    y = band(c, X0, y, "The provisions and where the module has them (README § `Elections.tla`, the table whole)")
    pw = 1500
    y_top = y
    hp = c.table(X0, y, [("Provision", 860), ("Where", pw - 860)], [[md(a), md(b)] for a, b in R["provisions"]],
                 size=13.5, accent="blue")
    rx = X0 + pw + 40
    rw = X1 - rx
    hdr = header_comment()
    s_ab = [i for i, x in enumerate(hdr) if x.startswith("ABSTRACTED:")]
    s_th = [i for i, x in enumerate(hdr) if x.startswith("Three readings are fixed")]
    need(len(s_ab) == 1 and len(s_th) == 1, "specs/Elections.tla", "header has no ABSTRACTED or Three readings")
    ab_text = " ".join(x.strip() for x in hdr[s_ab[0]:s_th[0]])[len("ABSTRACTED: "):]
    th_text = " ".join(x.strip() for x in hdr[s_th[0]:] if x.strip())
    th_text = re.sub(r"(\w)- (\w)", r"\1-\2", th_text)
    ab_text = re.sub(r"(\w)- (\w)", r"\1-\2", ab_text)
    yy = y
    yy += c.card(rx, yy, (rw - 30) / 2, "Abstracted (README § `Elections.tla`)", R["abstracted"], accent="grey",
                 status="abstracted", size=S) + 0
    hab = c.card(rx + (rw + 30) / 2, y, (rw - 30) / 2, "ABSTRACTED (`Elections.tla` header, in full)",
                 [ab_text], accent="grey", status="abstracted", size=13.5, bullets=False)
    yy = max(yy, y + hab) + 24
    yy += row_cards(c, rx, yy, rw, 30, [
        ("Three readings are fixed (README)", [R["readings_head"]] + R["readings"], "violet", {}),
        ("Where the header states them (`Elections.tla`, ABSTRACTED)", [th_text], "violet", {"bullets": False}),
    ], size=13.5)
    y = max(y_top + hp, yy) + 50

    # ---- band 3: the mutation table whole, with the reads beside it
    y = band(c, X0, y, "The mutations: the README's table whole, beside the module header's \"Breaks\" and the "
             "COUNTEREXAMPLE rows read from the results file")
    cols = [("Mutation", 230, {"mono": True, "bold": True}), ("Removes (README)", 440),
            ("Earlier text, doctrine or practice (README)", 520), ("Breaks (README)", 430),
            ("Module header names (`Elections.tla`, MUTATIONS)", 380),
            (f"COUNTEREXAMPLE rows read ({TF[8:]}): property, constants", 0),
            ("README = header = results (the diagram's check)", 300)]
    cols[5] = (cols[5][0], WW - sum(x[1] for x in cols))
    mrows = []
    disagree = []
    for m in muts:
        row = readme_mut[m]
        good, rb, hd, rs = ok_mut[m]
        def where(r):
            cons = [o for o in rrows[r["name"]]["opts"] if o.startswith("constraint=")]
            w = f" at `{' '.join(r['overrides'])}`" if r["overrides"] else (
                f" under `{r['spec']}`" if r["spec"] != "Spec" else "")
            if cons:
                w += f" (rows file: `{' '.join(cons)}`, not on the results line)"
            return w
        cer = "; ".join(f"`{r['prop']}`" + where(r) for r in ce.get(m, [])) or "none"
        chk = "[[teal|agree]]" if good else (f"[[red|differ]]: README {sorted(rb)}, header {sorted(hd)}, "
                                             f"results {sorted(rs)}")
        if not good:
            disagree.append(m)
        mrows.append({"cells": [m, md(row[1]), md(row[2]), md(row[3]),
                                ", ".join(f"`{x}`" for x in hb[m][1]) or "none", cer, chk],
                      "accent": "red" if not good else None})
    y += c.table(X0, y, cols, mrows, size=13.5, accent="violet", anchor="mutations") + 20
    y += c.para(X0, y, WW, R["safety"][:-1] + " (README). " + ("Every mutation's three lists agree." if not disagree else
                f"[[red|{len(disagree)} mutations' lists differ]]: " + ", ".join(disagree) + ".") +
                " The README's and the header's qualifications (\"with three candidates\", \"five States\") are "
                "the constants of the COUNTEREXAMPLE rows; the HOLDS rows at the other constants are in the "
                "matrix below.", 14, "muted") + 40

    # ---- band 4: the matrix
    y = band(c, X0, y, f"Every INVARIANT row on `Spec`, read from {TF[8:]}: one line per mutation and set of "
             "constants, so verdicts at different constants stay apart", status="checked")
    groups = []
    for r in inv_rows:
        k = (r["mut"], tuple(r["overrides"]))
        if not any(g[0] == k for g in groups):
            groups.append((k, {}))
        cell = dict(groups)[k]
        need(r["prop"] not in cell, TF, f"two rows for {k} {r['prop']}")
        cell[r["prop"]] = r
    order = [g for g in groups if g[0][0] == "none"]
    for m in muts:
        order += [g for g in groups if g[0][0] == m]
    need(len(order) == len(groups), TF, "a group of rows under a mutation not in the list")
    mcw = 190
    ccw = 300
    scw = 120
    pcw = (WW - mcw - ccw - scw) / len(mprops)
    need(pcw >= 130, "diagram", f"matrix column {pcw:.0f} px is too narrow")
    mcols = [("Mut", mcw, {"mono": True, "bold": True}), ("Constants the rows override", ccw),
             ("Distinct states (HOLDS rows)", scw)]
    mcols += [(camel(pp, pcw - 14), pcw) for pp in mprops]
    mx = []
    prev = None
    constraint_note = []
    for (mut, ov), cells in order:
        if mut != prev:
            if mut == "none":
                mx.append({"group": "Mut = \"none\": the text", "accent": "blue"})
            elif prev == "none":
                mx.append({"group": "Each mutation: one guard removed", "accent": "violet"})
            prev = mut
        names = [r["name"] for r in cells.values()]
        cons = sorted({o for nm in names for o in rrows[nm]["opts"] if o.startswith("constraint=")})
        ov_s = " ".join(ov)
        if cons:
            constraint_note.append((mut, cons))
        ctext = (f"`{ov_s}`" if ov_s else "defaults") + (
            f"; rows file: `{' '.join(cons)}` ([[red|not on the results lines]])" if cons else "")
        hold_states = sorted({r["states"] for r in cells.values() if r["verdict"] == "HOLDS" and r["states"]})
        ce_states = sorted({r["states"] for r in cells.values() if r["verdict"] != "HOLDS" and r["states"]})
        line = [mut, ctext, ", ".join(n(s) for s in hold_states) or
                ("— (the COUNTEREXAMPLE stopped at " + ", ".join(n(s) for s in ce_states) + ")")]
        good = ok_mut.get(mut, (True, set(), set(), set()))
        for pp in mprops:
            r = cells.get(pp)
            if r is None:
                line.append("")
            elif r["verdict"] == "COUNTEREXAMPLE":
                bad = mut == "none" or pp not in good[1]
                line.append("[[red|COUNTEREXAMPLE]]" + (" [[red|≠ README]]" if bad else ""))
            else:
                line.append("HOLDS")
        mx.append({"cells": line, "accent": "blue"} if mut == "none" else line)
    y += c.table(X0, y, mcols, mx, size=12.5, pad=7, hsize=12.5, accent="teal", anchor="matrix") + 20
    n_inv = len(inv_rows)
    y += c.para(X0, y, WW, "The unmutated lines are the text at the defaults (every property), then Safety at each set "
                "of constants a mutation's rows use (the c- rows), so a COUNTEREXAMPLE in a mutation's block is the "
                "mutation's and not the constants' (rows header). Each mutation's lines are its block at the "
                "constants where its check binds, then any further constants. "
                f"{n_inv} INVARIANT rows on `Spec`, all drawn; no row runs an INVARIANT on another spec. "
                f"A COUNTEREXAMPLE row's distinct-state count is where TLC stopped, so the column gives the HOLDS "
                f"rows' count. Not drawn here: the {len(dead_rows)} DEADLOCK rows (all HOLDS), the {W_N} witnesses "
                f"and `w-nostatute-successoracts`, and the PROPERTY rows (below). A COUNTEREXAMPLE not in the "
                f"README's \"Breaks\" cell would be marked ≠ README; none is.", 14, "muted") + 40

    # ---- band 5: witnesses
    y = band(c, X0, y, f"Witnesses: what the text allows, reached ({W_N}, each violated unmutated)", status="checked",
             extra="existential, never proved")
    lw = 940
    hw = c.card(X0, y, lw, "The README's list (README § `Elections.tla`, Witnesses)", R["witnesses"], accent="green",
                size=S)
    hdr_w = header_comment()
    s_rw = [i for i, x in enumerate(hdr_w) if x.startswith("REACHABILITY WITNESSES")]
    s_ab2 = [i for i, x in enumerate(hdr_w) if x.startswith("ABSTRACTED:")]
    need(len(s_rw) == 1 and len(s_ab2) == 1, "specs/Elections.tla", "header has no REACHABILITY WITNESSES")
    rw_text = " ".join(x.strip() for x in hdr_w[s_rw[0]:s_ab2[0]] if x.strip())
    hw += 24 + c.card(X0, y + hw + 24, lw, "The module header (`Elections.tla`, REACHABILITY WITNESSES)", [rw_text],
                      accent="green", size=13.5, bullets=False)
    hw += 24 + c.card(X0, y + hw + 24, lw, "`M_NO_STATUTE` and the witnesses (`Elections.tla` header, MUTATIONS)",
                      [hb["M_NO_STATUTE"][0]], accent="violet", size=13.5, bullets=False)
    extra_w = [r for r in t["rows"] if r["mut"] != "none" and r["prop"].startswith("Never")]
    wr = []
    for r in wit + extra_w:
        wr.append({"cells": [r["name"], r["prop"], r["kind"], " ".join(r["overrides"]) or "defaults",
                             ("[[red|COUNTEREXAMPLE]]" if r["verdict"] == "COUNTEREXAMPLE" else "HOLDS"),
                             n(r["states"]) if r["states"] is not None else "count not recorded",
                             "witness: reached" if r["mut"] == "none" else
                             f"`{r['mut']}` adds no state: it reaches no successor acting (rows file)"],
                   "accent": "green" if r["mut"] == "none" else "grey"})
    tw0 = X0 + lw + 40
    wcols = [("Row", 290, {"mono": True}), ("Property", 330, {"mono": True}), ("Kind", 130),
             ("Constants", 560, {"mono": True}), ("Verdict", 200), ("Distinct states", 190)]
    wcols.append(("What it shows", X1 - tw0 - sum(x[1] for x in wcols)))
    ht = c.table(tw0, y, wcols, wr, size=13, accent="green", anchor="witnesses")
    y += max(hw, ht) + 20
    y += c.para(X0, y, WW, "A state witness is an INVARIANT row, a step witness (`[][...]_vars`) a PROPERTY row "
                "(`Elections.tla`, Reachability witnesses). A step witness's count is not recorded. Without the "
                "witnesses a property could hold only because the state it forbids is unreachable (README § How "
                "the specs are written and checked).", 14, "muted") + 40

    # ---- band 6: liveness
    y = band(c, X0, y, "Liveness: the PROPERTY rows on `ExecutiveIsFilled` and `NoBehaviour`, read")
    lcols = [("Row", 280, {"mono": True}), ("Spec", 220, {"mono": True}), ("Mut", 170, {"mono": True}),
             ("Constants", 470, {"mono": True}), ("Property", 220, {"mono": True}), ("Verdict", 200),
             ("Distinct states", 180)]
    lcols.append(("Status", 0))
    lcols[-1] = ("Status", WW - sum(x[1] for x in lcols))
    lr = []
    for r in live:
        if r["prop"] == "ExecutiveIsFilled" and r["verdict"] == "HOLDS":
            st, acc = ("[[teal|checked]] at these constants, and [[blue|proved]] for all: `ExecutiveIsFilledAlways` "
                       f"[`{', '.join(eif['assume'])}`] `{eif['prove']}`"), "blue"
        elif r["prop"] == "NoBehaviour":
            st, acc = ("[[amber|checked, not proved]]: `FairSpec` has a behaviour (`NoBehaviour` == `<>FALSE` is "
                       "violated exactly when it does)"), "amber"
        elif r["mut"] != "none":
            st, acc = ("[[amber|checked, not proved]]: without the statute the vacancy can last (the theorem's one "
                       "hypothesis)"), "amber"
        else:
            st, acc = "[[amber|checked, not proved]]: this fairness does not suffice (existential, TLC's)", "amber"
        lr.append({"cells": [r["name"], r["spec"], r["mut"], " ".join(r["overrides"]) or "defaults", r["prop"],
                             "[[red|COUNTEREXAMPLE]]" if r["verdict"] == "COUNTEREXAMPLE" else "HOLDS",
                             n(r["states"]) if r["states"] is not None else "count not recorded", st],
                   "accent": acc})
    y += c.table(X0, y, lcols, lr, size=13.5, accent="amber") + 24
    y += row_cards(c, X0, y, WW, 30, [
        ("Liveness (README § `Elections.tla`)", [R["liveness_head"]] + R["liveness_fails"] + [R["liveness_tail"]],
         "amber", {}),
        ("The specs (`Elections.tla`, Liveness)", [
            "`Vacant` == `president = NoOne /\\ acting = NoOne`.",
            "`ExecutiveIsFilled` == `(clock # \"Founding\" /\\ Vacant) ~> ~Vacant`.",
            "`SomeoneActs` == `WF_vars(VPActs \\/ SuccessorActs)`; `FairSpec` == `Spec /\\ SomeoneActs`.",
            "`SpecVPOnly`, `SpecSuccessorOnly`: weak fairness on one officer only. `SpecEachAlone`: on each "
            "separately. `NoBehaviour` == `<>FALSE`."], "teal", {}),
        ("Proved: `ExecutiveIsFilledAlways` (`Elections_proof.tla`, Liveness)", [
            f"ASSUME `{', '.join(eif['assume'])}` PROVE `{eif['prove']}`.",
            "\"A leads-to with no quantifier, so one WF1 step: while the office is vacant the Vice President or the "
            "statute's officer can act, acting changes the state, and no step re-enters the founding.\"",
            "Lemmas `ClockLeavesFounding`, `SomeoneCanAct`, `ActingFills`; no measure.",
            "README § How …, What is not proved: \"the one leads-to with no quantifier, and it is proved, by one "
            "WF1 step\"."], "blue", {"status": "proved"}),
        ("Not proved, and TLC's (`Elections_proof.tla`, NOT PROVED)", [
            "\"That the weaker fairness conditions (SpecVPOnly, SpecSuccessorOnly, SpecEachAlone) do not suffice, "
            "and that FairSpec has a behaviour at all (NoBehaviour): existential, checked by TLC in the liveness "
            "rows.\"",
            "\"Reachability (the Never... witnesses) and the mutations' counterexamples: existential, so TLC's. "
            "ElectionsBound is a TLC device only.\"",
            f"No terminal state: the {len(dead_rows)} DEADLOCK rows, all HOLDS (module header, DEADLOCK)."],
         "amber", {"status": "notproved"}),
    ], size=13.5) + 50

    # ---- band 7: the proofs
    y = band(c, X0, y, f"The proofs: every theorem read from {PF[8:]}, with its hypotheses", status="proved",
             extra=f"{n(obl)} obligations")
    pcols = [("Theorem", 400, {"mono": True, "bold": True}), ("ASSUME (the mutations assumed absent)", 640),
             ("PROVE", 470, {"mono": True}),
             ("Mutations with a COUNTEREXAMPLE on the property (read; the diagram's join by name)", 640),
             ("Hypotheses = those mutations (the diagram's check)", 330)]
    pcols.append(("The property's kind (proof module, INDUCTIVE STRENGTHENING; the diagram's summary)",
                  WW - sum(x[1] for x in pcols)))
    flags = {"AppointedOnElectionDay", "SameDay", "NewCongressCounts", "CountIsCongress", "ElectorsChoose",
             "DevolvesOnlyWithoutMajority", "ChoiceFromTheList", "HouseVote", "SenateVote", "TwoTermLimit",
             "VPElectBecomesOnlyOnDeath"}
    kinds = {"ElectorsHoldNoOffice": "inductive alone over the college (`CollegeFrame`)",
             "OneNotAnInhabitant": "inductive alone over the college (`CollegeFrame`)",
             "PledgesBind": "needs `BallotNeedsPledge`, under every mutation",
             "CountCanClose": "valid, not inductive: `TwoNamesOnBallots`, `Pigeonhole`, `ClosesUnderInv`",
             "PresidentNotVP": "inductive alone over the offices (`OfficeFrame`)",
             "Qualifications": "inductive alone over the offices (`OfficeFrame`)",
             "Disability": "inductive alone over the offices (`OfficeFrame`)",
             "ActingOrder": "inductive alone over the offices (`OfficeFrame`)",
             "TypeOK": "under every mutation", "Safety": "the nineteen, under `Mut = \"none\"`",
             "ExecutiveIsFilled": "one WF1 step, no measure"}
    pr = []
    bad_thm = []
    for th in p["theorems"]:
        prop = th["name"][:-len("Always")] if th["name"] != "SafeAlways" else "Safety"
        if prop == "ExecutiveIsFilled":
            breaking = sorted({r["mut"] for r in live if r["prop"] == prop and r["mut"] != "none"
                               and r["verdict"] == "COUNTEREXAMPLE"})
        else:
            breaking = sorted({r["mut"] for r in inv_rows if r["prop"] == prop and r["mut"] != "none"
                               and r["verdict"] == "COUNTEREXAMPLE"})
        hy = sorted(a.split('"')[1] for a in th["assume"] if a.startswith("Mut #"))
        if prop == "Safety":
            check = "`Mut = \"none\"`: every mutation absent"
        else:
            check = "[[teal|equal]]" if hy == breaking else "[[red|differ]]"
            if hy != breaking:
                bad_thm.append(th["name"])
        kind = kinds.get(prop) or ("a flag (`FlagFrame`)" if prop in flags else "")
        if prop in ("ElectorsChoose", "DevolvesOnlyWithoutMajority"):
            kind += "; rests on `Sizes`, `VoteSizes`, `DisjointVotes`, `MajorityCarries`, `CarriesIsMajority`"
        pr.append({"cells": [th["name"], ", ".join(f"`{a}`" for a in th["assume"]) or "none",
                             th["prove"], ", ".join(f"`{x}`" for x in breaking) or "none", check, kind],
                   "accent": "blue" if prop in ("ExecutiveIsFilled", "Safety") else None})
    y += c.table(X0, y, pcols, pr, size=13.5, accent="blue", anchor="theorems") + 16
    flag_by = {}
    for pp in sorted(flags):
        k = [i for i, x in enumerate(hdr) if re.match(rf"^\s{{2}}{pp}\b", x)]
        need(len(k) == 1, "specs/Elections.tla", f"header PROPERTIES has no {pp}")
        txt = " ".join(x.strip() for x in hdr[k[0]:k[0] + 6])
        m = re.search(r"Flag set\s+by\s+([A-Za-z ,]+?)\.", txt)
        need(m, "specs/Elections.tla", f"{pp}: no 'Flag set by'")
        flag_by[pp] = m.group(1)
    two = {k: v for k, v in flag_by.items() if " and " in v}
    y += c.para(X0, y, WW, "The README (§ `Elections.tla`, Proof) says \"Eleven properties are flags and prove at the "
                "one action that sets each\"; the proof header says \"Eleven properties are flags set by one action "
                "each (FlagFrame)\". The module header (PROPERTIES) names the setting actions: "
                + "; ".join(f"`{k}` \"Flag set by {v}\"" for k, v in sorted(two.items()))
                + (" ([[red|two actions each]])." if two else ".")
                + " Every other flag is set by one.", 14, "muted") + 24
    base_lem = [x for x in p["lemmas"] if x not in after_end]
    y += row_cards(c, X0, y, WW, 30, [
        ("Proof (README § `Elections.tla`)", [R["proof"]], "blue", {}),
        ("Assumptions (`Elections_proof.tla` header)", [
            "\"the base module's named ASSUMEs PersonsWF, NoOneWF, SuccessorWF, FiniteWF and CollegeWF (MutKnown "
            "and InhabitantsWF are not used). So the theorems hold for every finite college, every set of "
            "candidates, States and Senators, every Inhabitants and every Binding within it\".",
            "\"the rows' three seats and two candidates, and the bound ElectionsBound, are TLC's business and are "
            "not assumed.\"",
            "\"M_NO_STATUTE breaks no safety property, so no safety theorem cites it; it is the one hypothesis of "
            "the liveness theorem.\""], "blue", {}),
        (f"The prover and the count ({PF[8:]})", [
            f"**{n(obl)} obligations, all proved**; {len(p['theorems'])} theorems; {len(p['lemmas'])} lemmas on "
            f"its LEMMAS line.",
            f"Prover: {p['prover'].split(' sha256')[0]}. Backends: {p['backends']}.",
            f"Command: `{p['command']}`.",
            f"Names the TLC results file `{p['tlc_file'][8:]}` by sha256 (equal to the file's digest now)."],
         "blue", {"status": "proved"}),
    ], size=13.5) + 24
    y += row_cards(c, X0, y, WW, 30, [
        (f"The lemmas, read ({len(base_lem)} before line {ends[0]})", [", ".join(f"`{x}`" for x in base_lem)],
         "blue", {"bullets": False}),
        (f"[[red|{len(after_end)} lemmas after line {ends[0]}]] (the diagram's reading of the text)", [
            f"Line {ends[0]} of `Elections_proof.tla` is a `====` line, which closes a TLA+ module; it follows "
            f"`ExecutiveIsFilledAlways`. The {len(after_end)} lemmas "
            + ", ".join(f"`{x}`" for x in after_end[:3]) + f" … `{after_end[-1]}` follow it (lines "
            f"{lem_line[after_end[0]]}–{lem_line[after_end[-1]]}), before a second `====` at line {ends[-1]}.",
            "`scripts/proof_results.py` reads LEMMA names from the whole text (`statements`), so the results file "
            f"lists them among its {len(p['lemmas'])}. No record says whether tlapm checked them, nor whether the "
            f"{n(obl)} obligations include them.",
            "README § How …, Proofs: each proof module has \"one lemma per mutation saying what that mutation "
            "admits\"."], "red", {}),
    ], size=13.5) + 50
    need(not thm_after, "specs/Elections_proof.tla", "a THEOREM after the first end-of-module line")

    # ---- band 8: README findings for the module
    y = band(c, X0, y, "What TLC and the prover found in `Elections.tla` (README § Findings, whole)", status="checked")
    y += c.para(X0, y, WW, find_head, 14.5, "ink") + 14
    per = 4
    for k in range(0, len(find_items), per):
        chunk = find_items[k:k + per]
        specs = [(it.split("**")[1] if it.startswith("**") else f"Finding {k + i + 1}",
                  ["**".join(it.split("**")[2:]).strip() if it.startswith("**") else it], "pink", {})
                 for i, it in enumerate(chunk)]
        while len(specs) < per:
            specs.append(None)
        real = [s for s in specs if s]
        cwf = (WW - (per - 1) * 30) / per
        h = max(c.card(0, 0, cwf, s[0], s[1], draw=False, size=S) for s in real)
        for i, s in enumerate(real):
            c.card(X0 + i * (cwf + 30), y, cwf, s[0], s[1], accent="pink", h=h, size=S)
        y += h + 24
    y += 26

    # ---- band 9: the rows, their constants, and Elections.cfg beside c-cfg-safety
    y = band(c, X0, y, f"The constants: the row list's defaults, where each mutation's check binds, and "
             f"`Elections.cfg` beside `c-cfg-safety` ({rows_rel})")
    cfg, cfg_spec, cfg_inv = cfg_constants()
    ccfg = [r for r in t["rows"] if r["name"] == "c-cfg-safety"]
    need(len(ccfg) == 1, TF, "no c-cfg-safety row")
    ccfg = ccfg[0]
    ov = dict(o.split("=", 1) for o in ccfg["overrides"])
    norm = lambda s: re.sub(r"\s+", "", s)
    crow = []
    differ = []
    for k in rconsts:
        eff = ov.get(k, rconsts[k])
        cv = cfg.get(k)
        need(cv is not None, "specs/Elections.cfg", f"no constant {k}")
        same = norm(eff) == norm(cv)
        if not same:
            differ.append(k)
        crow.append({"cells": [k, rconsts[k], ov.get(k, ""), eff, cv,
                               "[[teal|same]]" if same else "[[red|differs]]"],
                     "accent": None if same else "red"})
    need(norm(cfg.get("Mut", "")) == '"none"', "specs/Elections.cfg", "Mut is not \"none\"")
    ccols = [("Constant", 190, {"mono": True, "bold": True}), ("Row default (# const:)", 380, {"mono": True}),
             ("c-cfg-safety overrides", 330, {"mono": True}), ("c-cfg-safety runs", 380, {"mono": True}),
             ("Elections.cfg", 330, {"mono": True}), ("Same?", 110)]
    tw_c = sum(x[1] for x in ccols)
    hc = c.table(X0, y, ccols, crow, size=13, accent="teal")
    bx0 = X0 + tw_c + 40
    bw = X1 - bx0
    hb2 = c.card(bx0, y, bw, "Where each mutation's check binds (rows file header)",
                 [f"`{a}`: {b}" for a, b in rbinds] + [
                     "\"The other mutations bind at the defaults. Safety and the deadlock audit also run unmutated at "
                     "each of these sets of constants (the c- rows), so a COUNTEREXAMPLE in a mutation's block is "
                     "the mutation's and not the constants'.\""], accent="teal", size=13.5)
    y += max(hc, hb2) + 20
    big = sorted([r for r in t["rows"] if r["states"] and r["states"] > 1_000_000], key=lambda r: r["name"])
    y += row_cards(c, X0, y, WW, 30, [
        ("Rows (README § `Elections.tla`)", [R["rows"], R["cannot"]], "teal", {}),
        ("`Elections.cfg` and `c-cfg-safety` (the diagram's check)", [
            f"`Elections.cfg`: SPECIFICATION `{' '.join(cfg_spec)}`, INVARIANTS `{', '.join(cfg_inv)}`; "
            f"\"for ad hoc runs and simulation. The checked results come from {rows_rel}\".",
            f"`c-cfg-safety` checks `Safety` at the row defaults with {len(ov)} overrides: "
            f"{n(ccfg['states'])} distinct states, HOLDS.",
            ("The constants differ only in " + ", ".join(f"`{d}`" for d in differ) + ": the rows add the persons "
             "\"c, e4 and e5 … for the rows that add a candidate or a seat; unused, they add no state\" (rows "
             "header).") if differ else "Every constant is the same."], "teal", {}),
        ("Rows over a million states, read", [f"`{r['name']}`: {n(r['states'])} distinct states"
                                               + (f" at `{' '.join(r['overrides'])}`" if r["overrides"] else "")
                                               for r in big] + [
            f"The README says \"Two rows are larger\"; the rows header says \"Two further c- rows are larger\". "
            f"Read, {len(big)} rows exceed a million states, {len([r for r in big if r['name'].startswith('c-')])} "
            f"of them c- rows."], "teal", {}),
    ], size=13.5) + 50

    # ---- band 10: one band from the findings doc
    mrow_n = sum(1 for r in t["rows"] if r["name"].startswith("m-"))
    mhold = sum(1 for r in t["rows"] if r["name"].startswith("m-") and r["verdict"] == "HOLDS")
    y = band(c, X0, y, "From docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md (§ 2, § 7.6, § 8), beside what the "
             "records here give")
    y += row_cards(c, X0, y, WW, 30, [
        ("§ 2 The pattern: MutationMatrix", [
            "\"For Elections the grid is 25 mutations, 20 properties (TypeOK plus nineteen), and about a dozen "
            "constant sets, giving 490 `m-` rows out of 579.\"",
            f"Read: {len(muts)} mutations other than `none` ({len(muts) + 1} values of `Mut`), "
            f"{mrow_n} `m-` rows of {n(t['total'])}."], "pink", {}),
        ("§ 7.6 What happened when the proof was written", [
            "\"1,121 obligations, all proved by the pinned prover; 25 flip tests, one per mutation, each failing in "
            "the lemma that carries the hypothesis.\"",
            f"Read: {n(obl)} obligations; {len(muts)} mutations; {hyps} `Mut #` hypotheses across the "
            f"{len(p['theorems'])} theorems. No results file records a flip test (`flip_test.py` writes nothing "
            f"to the tree)."], "pink", {}),
        ("§ 8 What the proof means for the matrix", [
            "\"The proof says, for every finite college and any number of candidates, what 440 rows said at three "
            "electors and two candidates.\"",
            f"Read: {mhold} `m-` rows are HOLDS (the note's 440 is \"TypeOK plus 18 properties per block\"; "
            f"this count also takes the further constants). \"The rows are unchanged as of this note\"; its table, of what the "
            "rows could become, is below."], "pink", {}),
    ], size=13.5) + 20
    doc = C.read("docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md").splitlines()
    k = doc.index("**What the Elections rows could become.**")
    tl = []
    i = k + 1
    while not doc[i].startswith("|"):
        i += 1
    while i < len(doc) and doc[i].startswith("|"):
        tl.append([x.strip() for x in doc[i].strip().strip("|").split("|")])
        i += 1
    need(len(tl) > 3 and tl[0] == ["Row group", "Today", "With the proof"], "docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md",
         "§ 8 table header")
    y += c.table(X0, y, [(tl[0][0], 1100), (tl[0][1], 700), (tl[0][2], WW - 1800)], [[md(x) for x in r]
                 for r in tl[2:]], size=13.5, accent="pink") + 16
    y += c.para(X0, y, WW, "The note is dated 2026.11.17 and read against commit `4cc473b` (its opening); its "
                "§ 7 opens \"Elections has no proof module\", which § 7.6 then supersedes. It changes nothing in "
                "the tree, and none of its proposals is adopted at the state of record.", 13.5, "muted") + 10
    return c
