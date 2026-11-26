"""B4 — Government.tla: the authority graph, and which claims about it are proved, checked, sampled or refuted.

The picture is the grant layer of the graph as Government.tla draws it, read from the spec at build time (Founding,
Adds, Drops, AgencyEdges, CourtEdges): nodes left to right in the order of `Rank`, every grant edge that climbs the
rank above the nodes and every edge that runs back below them. The control layer is a holder-by-target table read
from the same sets. Then the README section's tables whole, the configurations, the mutation-by-property matrix per
configuration, witnesses, liveness, the theorems, the refuted claim, and one band from a findings doc.

Build-time reads and checks (each raises corpus.CorpusError, so the generator prints ERROR, like a gate):
  - the results files named by corpus.RESULTS["Government"] are the newest of their kind; every Modules: digest
    equals specs/ now; the rows file's digest equals the TLC file's Rows: line; the proof file names the TLC file
    by its digest; every row is as expected;
  - every results row's configuration, from its name prefix, matches its constants, and the rows file puts
    constraint=LawRowsBound on exactly the a- rows; every row falls in exactly one of the bands drawn;
  - Government.tla: the edge sets, Rank, Fixed, Challengeable, IsInert, the Fire(...) argument of every action
    in Next (and Next names exactly the actions drawn), the header's mutation list and paragraphs, the properties
    stated over Reach; Government.cfg; Government_proof.tla's mutation lemmas;
  - README § Government.tla: its blocks in order, both tables, and every local form has a theorem and no global
    form has one;
  - docs/SESSION-GATE-FINDINGS-2026.11.17.md § 5, and the two spec lines it cites.
"""
import re

from lib import Canvas, STATUS, text_width
import corpus as C

ID, SLUG = "B4", "government"

W = 3600
S = 14

SPEC, PROOF, CFG, ROWS = ("specs/Government.tla", "specs/Government_proof.tla", "specs/Government.cfg",
                          "rows/Government-rows.txt")
FIND = "docs/SESSION-GATE-FINDINGS-2026.11.17.md"
TF, PF = C.RESULTS["Government"]


def need(cond, rel, what):
    if not cond:
        raise C.CorpusError(f"{rel}: {what}")


# ---------------------------------------------------------------------------------------------- layout helpers
def row_cards(c, x, y, w, gap, specs, size=S):
    n = len(specs)
    cw = (w - (n - 1) * gap) / n
    h = max(c.card(0, 0, cw, t, b, draw=False, size=size, status=k.get("status"),
                   bullets=k.get("bullets", True)) for t, b, _, k in specs)
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
        need_w = lw + sum(pws) + 10 * (len(pws) - 1)
        if px + need_w > x1:
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


def md(s):
    """README markdown to the library's rich text: single-star italics have no style, so drop the stars."""
    return re.sub(r"(?<![*\w])\*(?!\*)([^*]+?)\*(?![*\w])", r"\1", s)


def codes(names):
    return ", ".join(f"`{x}`" for x in names)


# ---------------------------------------------------------------------------------------------- the README section
README_HEAD = "### `Government.tla` — the authority graph"
README_SHAPE = [  # (kind, text the block starts with): the section's blocks in order
    ("p", "The other three modules model"), ("ul", "**Grant**"), ("p", "Every exercise of authority"),
    ("ul", "statutes add"), ("p", "The graph claims are about reachability"), ("ul", "a **local form**"),
    ("table", "Claim"), ("p", "The act and doctrine properties"), ("table", "Mutation"),
    ("p", "Witnesses (each violated):"), ("ul", "an agency created"), ("p", "**Liveness.**"),
    ("ul", "`LitigantsSue`"), ("p", "`SpecNoSuit` and `SpecNoRuling`"), ("p", "**Rows.** Four configurations:"),
    ("ul", "no agency or court"), ("p", "Every row uses `VIEW Unrecorded`"), ("h", "A claim TLC refuted"),
    ("p", "`Government.tla` first folded"), ("code", "State 1:"), ("p", "Section 2 of the Twenty-fifth"),
    ("p", "The original properties are kept"),
]


def readme_blocks():
    lines = C.read("README.md").splitlines()
    need(lines.count(README_HEAD) == 1, "README.md", "the Government.tla section heading is not there once")
    i = lines.index(README_HEAD) + 1
    end = next((j for j in range(i, len(lines)) if lines[j].startswith("## ")), None)
    need(end, "README.md", "no heading after the Government.tla section")
    blocks = []
    while i < end:
        ln = lines[i]
        if not ln.strip():
            i += 1
        elif ln.startswith("```"):
            j = i + 1
            while j < end and not lines[j].startswith("```"):
                j += 1
            need(j < end, "README.md", "unclosed code block in § Government.tla")
            blocks.append(("code", lines[i + 1:j]))
            i = j + 1
        elif ln.startswith("#### "):
            blocks.append(("h", ln[5:]))
            i += 1
        elif ln.startswith("|"):
            rows = []
            while i < end and lines[i].startswith("|"):
                rows.append([x.strip() for x in lines[i].strip().strip("|").split("|")])
                i += 1
            need(len(rows) > 2 and set("".join(rows[1])) <= set("-: "), "README.md", "a table without a separator")
            need(all(len(r) == len(rows[0]) for r in rows[2:]), "README.md",
                 f"a row of the table headed {rows[0][0]!r} has the wrong number of cells")
            blocks.append(("table", rows[0], rows[2:]))
        elif ln.startswith("- "):
            items = []
            while i < end and (lines[i].startswith("- ") or lines[i].startswith("  ")):
                if lines[i].startswith("- "):
                    items.append(lines[i][2:].strip())
                else:
                    items[-1] += " " + lines[i].strip()
                i += 1
            blocks.append(("ul", items))
        else:
            p = []
            while i < end and lines[i].strip() and not lines[i].startswith(("|", "- ", "```", "#")):
                p.append(lines[i].strip())
                i += 1
            blocks.append(("p", " ".join(p)))
    need(len(blocks) == len(README_SHAPE), "README.md",
         f"§ Government.tla has {len(blocks)} blocks, the diagram draws {len(README_SHAPE)}")
    for b, (kind, start) in zip(blocks, README_SHAPE):
        first = {"p": lambda: b[1], "h": lambda: b[1], "ul": lambda: b[1][0], "code": lambda: b[1][0],
                 "table": lambda: b[1][0]}[b[0]]()
        need(b[0] == kind and first.startswith(start), "README.md",
             f"§ Government.tla: expected a {kind} starting {start!r}, found a {b[0]} starting {first[:40]!r}")
    return blocks


# ---------------------------------------------------------------------------------------------- Government.tla
EDGE = re.compile(r'\b(Txt|Law)\("(\w+)",\s*(?:"(\w+)"|(\w+)),\s*"(\w+)",\s*"(\w+)"\)')


def seg(lines, start, stop):
    """Lines from the one starting with `start` up to (not including) the next one starting with `stop`."""
    i = next((k for k, ln in enumerate(lines) if ln.startswith(start)), None)
    need(i is not None, SPEC, f"no line starting {start!r}")
    j = next((k for k in range(i + 1, len(lines)) if lines[k].startswith(stop)), None)
    need(j is not None, SPEC, f"no line starting {stop!r} after {start!r}")
    return lines[i:j]


def edge_lines(lines, part_of=lambda ln, cur: cur, stop_at_close=False):
    """Edges written one per line, with the spec's trailing comment, continuation comments and `\\* --` group
    headings. part_of(line, current) names the set or condition an edge belongs to."""
    out, part, group, prev_head = [], None, None, False
    for ln in lines:
        part = part_of(ln, part)
        s = ln.strip().lstrip("{(").strip()
        ms = list(EDGE.finditer(ln))
        if ms:
            tail = ln[ms[-1].end():]
            note = tail.split("\\*", 1)[1].strip() if "\\*" in tail else ""
            for m in ms:
                out.append({"basis": "Text" if m.group(1) == "Txt" else "Statute", "frm": m.group(2),
                            "to": m.group(3) or m.group(4), "kind": m.group(5), "label": m.group(6),
                            "part": part, "group": group, "note": note})
            prev_head = False
            if stop_at_close and re.search(r"\)\s*\}", ln):
                break
        elif s.startswith("\\* --"):
            g = s[5:].strip()
            group = f"{group} {g}" if prev_head else g
            prev_head = True
        elif s.startswith("\\*") and out:
            out[-1]["note"] = (out[-1]["note"] + " " + s[2:].strip()).strip()
            prev_head = False
        else:
            prev_head = False
    return out


def defs(lines):
    """Top-level definitions: name -> (params, body text)."""
    out = {}
    for i, ln in enumerate(lines):
        m = re.match(r"^([A-Za-z]\w*)(\(([^)]*)\))?\s+==(.*)$", ln)
        if not m:
            continue
        body = [m.group(4)]
        for nxt in lines[i + 1:]:
            if nxt and not nxt[0].isspace():
                break
            body.append(nxt)
        out[m.group(1)] = (m.group(3) or "", "\n".join(body))
    return out


FIRE = re.compile(r"Fire\(((?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)")

# The actions of Next, by the spec's section headings, with what each changes (the diagram's gloss of the
# operator's body; the edge it fires is read from the body at build time).
ACTIONS = [
    ("The flow of law: Art. I sec. 7", [
        ("Pass", "Both Houses pass a bill in scope (`InScope`), while sitting, with no bill in flight and "
                 "`Applicable(op)`; it is presented."),
        ("Sign", "The President signs; `Rechecked(op)`, then `Enact(op)` changes the statutory edges and bodies."),
        ("Lapse", "Law without signature, only if `CanReturn` (Congress sitting); `Enact(op)`. A lapse in recess "
                  "(only under `M_NOPOCKET`) records the `PocketVeto` breach."),
        ("Veto", "Returned with objections, only while Congress sits: the bill is `Vetoed`."),
        ("PocketVeto", "Congress has adjourned and prevented the return: the bill dies."),
        ("Override", "Two-thirds of each House, while sitting; `Rechecked(op)`, then `Enact(op)`."),
        ("BillFails", "A chamber votes it down or an override fails. Fires no edge: `last' = NoEdge`."),
    ]),
    ("Sessions", [
        ("Adjourn", "Congress adjourns under its own Article I power."),
        ("Convene", "Congress convenes."),
        ("ConveneByPresident", "Art. II sec. 3, \"on extraordinary Occasions\"."),
    ]),
    ("Offices", [
        ("ElectPresident", "The electors seat the President."),
        ("ContingentElection", "The House seats the President."),
        ("PresidentLeaves", "Death, resignation, end of term. Fires no edge."),
        ("ElectVicePresident", "The electors seat the Vice President."),
        ("ContingentElectionVP", "The Senate seats the Vice President (Amend. XII)."),
        ("VicePresidentLeaves", "The Vice Presidency falls vacant. Fires no edge."),
        ("Succeed", "The Vice President becomes President; the Vice Presidency falls vacant."),
        ("NominateVP", "XXV sec. 2: possible only while that edge is in the graph, that is once XXV is ratified."),
        ("ConfirmVP", "Both Houses confirm; the office is re-checked vacant at confirmation."),
        ("RejectVP", "The nomination ends."),
        ("Nominate", "A head or a judge, only for a live body: its Select edges exist only while its act does."),
        ("Consent", "Seats the nominee; re-checked at confirmation."),
        ("Reject", "The nomination ends."),
        ("Remove", "By whichever removal edge the act drew and the courts left. A court has none, so removing a "
                   "judge (reachable only under `M_OFFEDGE`) records the `GoodBehaviour` breach."),
        ("Resign", "Any office but the presidency. Fires no edge."),
    ]),
    ("Impeachment: the House impeaches, the Senate tries", [
        ("Impeach", "Opens a trial of a seated officer, or of the Judiciary."),
        ("Convict", "Unseats the one tried."),
        ("Acquit", "Ends the trial."),
    ]),
    ("Courts: Art. III acts only on a case", [
        ("Sue", "Someone affected challenges a statutory edge whose label is in `Standing`."),
        ("Review", "Strikes the edge if `Forbidden` (and not `M_UPHOLD`), leaving what `Sever` leaves; an upheld "
                   "edge a doctrine forbids records that doctrine's breach."),
    ]),
    ("Article V", [
        ("Propose", "Two-thirds of each House, or a convention on the States' application."),
        ("Ratify", "Three-fourths of the States: `SetEdges((edges \\ Drops(x)) \\cup Adds(x))` rewrites the text."),
    ]),
    ("Exercises of power whose effects other modules model", [
        ("Exercise", "An edge with an `IsInert` label fires under its `Guard`; only `last` and `stray` change."),
    ]),
]


def read_spec():
    text = C.read(SPEC)
    L = text.splitlines()
    D = defs(L)
    out = {"text": text, "lines": L, "defs": D}

    m = re.search(r"^Fixed\s*==\s*\{([^}]*)\}", text, re.M)
    need(m, SPEC, "no Fixed == {...}")
    out["fixed"] = re.findall(r'"(\w+)"', m.group(1))

    rank = {}
    for ln in seg(L, "Rank(n) ==", "\\* An office acts"):
        r = re.search(r'n = "(\w+)"\s*-> (\d)', ln)
        if r:
            rank[r.group(1)] = int(r.group(2))
        r = re.search(r"OTHER\s*-> (\d)", ln)
        if r:
            rank["OTHER"] = int(r.group(1))
    need(len(rank) == 6 and "OTHER" in rank, SPEC, f"Rank does not parse: {rank}")
    out["rank"] = rank

    fl = seg(L, "Founding ==", "ArticleV ==")
    found = edge_lines(fl, lambda ln, cur: "Founding", stop_at_close=True)
    need(len(found) == "".join(fl).count("Txt(") and len(found) > 30, SPEC,
         f"Founding: parsed {len(found)} edges")
    out["founding"] = found

    av = edge_lines(seg(L, "ArticleV ==", "-----"), lambda ln, cur: "ArticleV")
    need(len(av) == 3, SPEC, "ArticleV is not three edges")
    out["artv"] = av

    def adds_part(ln, cur):
        if 'CASE x = "XVII"' in ln:
            return "Adds(\"XVII\")"
        if '[] x = "XXV"' in ln:
            return "Adds(\"XXV\")"
        if 'IF Mut = "M_CONGRESS_AMENDS"' in ln:
            return "M_CONGRESS_AMENDS"
        return cur
    adds_l = seg(L, "Adds(x) ==", "Drops(x) ==")
    adds = edge_lines(adds_l, adds_part)
    need(len(adds) == "".join(adds_l).count("Txt(") and {e["part"] for e in adds} ==
         {"Adds(\"XVII\")", "Adds(\"XXV\")", "M_CONGRESS_AMENDS"}, SPEC, "Adds does not parse")
    out["adds"] = adds

    drops_l = seg(L, "Drops(x) ==", "\\* Every amendment rewrites")
    drops = edge_lines(drops_l, lambda ln, cur: "Drops(\"XVII\")")
    need(len(drops) == 1, SPEC, "Drops(\"XVII\") is not one edge")
    need(any('x = "XXV"  -> IF Mut = "M_NO_ARTV" THEN ArticleV ELSE {}' in ln for ln in drops_l), SPEC,
         "Drops(\"XXV\") is not 'IF Mut = \"M_NO_ARTV\" THEN ArticleV ELSE {}'")
    out["drops"] = drops

    ag_l = seg(L, "AgencyEdges(a, x, r, v) ==", "\\* Art. III sec. 1")
    state = {"exec": False}

    def ag_part(ln, cur):
        if "IF x THEN" in ln:
            state["exec"] = True
        r = re.search(r'\b([rv]) = "(\w+)"', ln)
        if r:
            return ("remover" if r.group(1) == "r" else "vesting") + f" = {r.group(2)}"
        if state["exec"]:
            if "ELSE {})" in ln and not EDGE.search(ln):
                state["exec"] = False
                return cur
            return "exec = TRUE"
        return "always"
    agency = edge_lines(ag_l, ag_part)
    need(len(agency) == "".join(ag_l).count("Law(") == 14, SPEC, f"AgencyEdges: {len(agency)} edges, not 14")
    need(any('v = "Head"      -> {})' in ln for ln in ag_l), SPEC, "AgencyEdges: no 'v = \"Head\" -> {}' line")
    out["agency"] = agency

    ct_l = seg(L, "CourtEdges(c) ==", "\\* The edges by which")
    court = edge_lines(ct_l, lambda ln, cur: "always")
    need(len(court) == 7, SPEC, "CourtEdges is not seven edges")
    out["court"] = court

    ea = D.get("EdgesAfter", ("", ""))[1]
    for s in ('edges \\cup {Law("Congress", t, "Control", "LegislativeVeto")}',
              'edges \\cup {Law("Congress", t, "Control", "DiminishPay")}',
              'edges \\ {Law("Judiciary", t, "Control", "Appeal")}   \\* McCardle'):
        need(s in ea, SPEC, f"EdgesAfter has no {s!r}")
    sv = D.get("Sever", ("", ""))[1]
    for s in ('(edges \\ {e}) \\cup {Law("Executive", a, "Control", "Remove")}',
              'edges \\ {Law("Executive", a, "Power", "ExecutivePower"),',
              'IF Mut = "M_SEVER_PLAIN" THEN edges \\ {e} ELSE'):
        need(s in sv, SPEC, f"Sever has no {s!r}")
    ch = D.get("Challengeable", ("", ""))[1]
    out["challengeable"] = {(m.group(2), m.group(5), m.group(6)) for m in EDGE.finditer(ch)}
    need(len(out["challengeable"]) == 5, SPEC, "Challengeable is not five edges")
    ii = D.get("IsInert", ("", ""))[1]
    out["inert"] = re.findall(r'"(\w+)"', ii.split("\\/ e.label = \"Review\"")[0])
    need(len(out["inert"]) == 14, SPEC, f"IsInert's first list has {len(out['inert'])} labels, not 14")

    # the actions of Next, and the edge each fires
    nb = re.sub(r'"[^"]*"', "", D["Next"][1])
    named = set(re.findall(r"\b([A-Z][A-Za-z]+)\b", nb)) - {"Ops", "Agencies", "Courts", "Offices", "AmendIds"}
    drawn = [a for _, acts in ACTIONS for a, _ in acts]
    need(named == set(drawn) and len(drawn) == len(set(drawn)), SPEC,
         f"Next names {sorted(named ^ set(drawn))} differently from the diagram's action list")
    fires = {}
    for a in drawn:
        need(a in D, SPEC, f"no definition of {a}")
        f = FIRE.findall(D[a][1])
        if not f:
            need("last' = NoEdge" in D[a][1], SPEC, f"{a} fires no edge and does not set last' = NoEdge")
        fires[a] = (D[a][0], [re.sub(r"\s+", " ", x) for x in f])
    for g, _ in ACTIONS:
        need(f"(* {g}" in text, SPEC, f"no section heading {g!r}")
    out["fires"] = fires

    # properties stated over Reach (directly, or through Acyclic)
    out["reach"] = sorted(k for k, (p, b) in D.items() if not p and re.search(r"\b(Reach|Acyclic)\(", b)
                          and k not in ("Reach", "Acyclic"))

    # the header: its paragraphs, and the mutation list
    hdr = []
    for ln in L:
        if ln.startswith("(*") and ln.rstrip().endswith("*)") and not ln.startswith("(* Nodes and edges"):
            body = ln.rstrip()[2:-2].rstrip()
            hdr.append("" if set(body.strip()) <= {"*"} else body)
        elif hdr and ln.startswith("EXTENDS"):
            break
    paras, cur = [], []
    for h in hdr:
        if h.strip():
            cur.append(h.strip())
        elif cur:
            paras.append(" ".join(cur))
            cur = []
    if cur:
        paras.append(" ".join(cur))
    out["hpara"] = paras
    muts, curm, inside = {}, None, False
    for h in hdr:
        if h.strip().startswith("MUTATIONS."):
            inside = True
            continue
        if not inside:
            continue
        if h.strip().startswith("The two constant mutations") or h.strip().startswith("WITNESSES."):
            break
        m = re.match(r"^\s{3}(M_[A-Z_]+)\s+(.*)$", h)
        if m:
            curm = m.group(1)
            muts[curm] = m.group(2).strip()
        elif curm:
            muts[curm] += " " + h.strip()
    need(len(muts) == 14, SPEC, f"the header's MUTATIONS list has {len(muts)} entries, not 14")
    out["hmuts"] = muts
    return out


def hpara(spec, start):
    p = [x for x in spec["hpara"] if x.startswith(start)]
    need(len(p) == 1, SPEC, f"no single header paragraph starting {start!r}")
    return p[0]


# ---------------------------------------------------------------------------------------------- results
CONFS = {  # configuration -> (constants on the results row, constraint=LawRowsBound in the rows file)
    "o": (['Agencies={}', 'Proposable={"XVII","XXV"}'], False),
    "c": (['Agencies={}', 'Courts={ct1}'], False),
    "a": ([], True),
    "af": ([], False),
    "l-a": (['RemoverOptions={"PresidentForCause"}'], False),
    "l-c": (['Agencies={}', 'Courts={ct1}'], False),
}


def conf_of(name):
    if name.startswith("s-"):
        return "s"
    m = re.match(r"^l-(a|c)-", name)
    if m:
        return "l-" + m.group(1)
    m = re.match(r"^(?:[dwr]-)?(af|a|o|c)-", name)
    need(m, ROWS, f"row {name}: no configuration prefix")
    return m.group(1)


def read_results():
    for kind, rel in (("tlc", TF), ("proof", PF)):
        need(C.newest(kind, "Government") == rel, rel, f"not the newest committed {kind} results file")
    t, p = C.tlc_results(TF), C.proof_results(PF)
    for res, rel in ((t, TF), (p, PF)):
        for f, d in res["modules"].items():
            need(C.sha256(f"specs/{f}") == d, rel, f"{f} has moved since it was checked")
    need(t["rows_file"] == ROWS and C.sha256(ROWS) == t["rows_sha"], TF, "the rows file has moved since the run")
    need(p["tlc_file"] == TF and C.sha256(TF) == p["tlc_sha"], PF, "does not name the TLC file by its digest")
    need(t["as_expected"] == t["total"] and not t["not"] and not t["error"], TF, "not every row is as expected")

    rows_file = []
    for ln in C.read(ROWS).splitlines():
        if not ln.strip() or ln.startswith("#"):
            continue
        tok = ln.split()
        need(len(tok) >= 6, ROWS, f"row does not parse: {ln[:60]!r}")
        rows_file.append({"name": tok[0], "kv": tok[6:]})
    need([r["name"] for r in rows_file] == [r["name"] for r in t["rows"]], ROWS,
         "rows file and results file list different rows")
    kv = {r["name"]: r["kv"] for r in rows_file}
    for r in t["rows"]:
        r["conf"] = cf = conf_of(r["name"])
        if cf == "s":
            need(r["kind"] == "SIMULATE", TF, f"{r['name']} is not a SIMULATE row")
            continue
        over, bound = CONFS[cf]
        need(r["overrides"] == over, TF, f"{r['name']}: constants {r['overrides']} are not configuration {cf}'s")
        need(("constraint=LawRowsBound" in kv[r["name"]]) == bound, ROWS,
             f"{r['name']}: constraint=LawRowsBound {'missing' if bound else 'present'}")
        r["asserted"] = [x for x in kv[r["name"]] if x.startswith("states=")]
    hdr = [ln[len("# expected: "):] for ln in C.read(ROWS).splitlines() if ln.startswith("# expected: ")]
    need(len(hdr) == 4, ROWS, "not four '# expected:' lines")
    return t, p, hdr


# ---------------------------------------------------------------------------------------------- the picture
NODE_ORDER = ["People", "States", "Constitution", "Congress", "VicePresident", "Executive", "Judiciary", "a", "c"]


def picture(c, y, spec):
    """The grant layer: nodes in Rank order, climbing edges above, edges that run back below."""
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    need(set(spec["fixed"]) == set(NODE_ORDER[:7]), SPEC, f"Fixed is {spec['fixed']}, not the diagram's nodes")
    rk = spec["rank"]
    order = sorted(NODE_ORDER[2:7], key=lambda k: rk[k])
    need(order == NODE_ORDER[2:7], SPEC, f"Rank orders the nodes {order}")

    # every grant edge, from every set the spec draws, grouped by (from, to)
    E = []
    for e in spec["founding"]:
        dropped = any(d["frm"] == e["frm"] and d["to"] == e["to"] and d["label"] == e["label"]
                      for d in spec["drops"])
        E.append(dict(e, ann="until XVII" if dropped else ""))
    for e in spec["adds"]:
        E.append(dict(e, ann={"Adds(\"XVII\")": "from XVII", "Adds(\"XXV\")": "from XXV",
                              "M_CONGRESS_AMENDS": "only under M_CONGRESS_AMENDS"}[e["part"]]))
    for e in spec["agency"]:
        E.append(dict(e, ann="" if e["part"] == "always" else "if " + e["part"]))
    for e in spec["court"]:
        E.append(dict(e, ann=""))
    pairs = {}
    for e in E:
        if e["kind"] not in ("Power", "Select", "Amend"):
            continue
        pairs.setdefault((e["frm"], e["to"]), []).append(e)

    nw = 272
    gap = (WW - 9 * nw) / 8
    cx = {k: X0 + i * (nw + gap) + nw / 2 for i, k in enumerate(NODE_ORDER)}
    idx = {k: i for i, k in enumerate(NODE_ORDER)}

    arcs = []
    for (f, t), es in pairs.items():
        need(f in idx and t in idx, SPEC, f"grant edge {f} -> {t} outside the drawn nodes")
        kinds = []
        for e in es:
            if e["kind"] not in kinds:
                kinds.append(e["kind"])
        lab = " · ".join(k + " " + ", ".join(e["label"] + (f" ({e['ann']})" if e["ann"] else "")
                                             for e in es if e["kind"] == k) for k in kinds)
        if any(e["part"] == "M_CONGRESS_AMENDS" for e in es):
            acc, dash = "violet", "7 5"
        elif any(e["label"] == "NominateVP" for e in es):
            acc, dash = "red", None
        elif es[0]["basis"] == "Statute":
            acc, dash = "teal", None
        else:
            acc, dash = "blue", None
        side = "up" if idx[t] > idx[f] else "down"
        lo, hi = sorted((cx[f], cx[t]))
        arcs.append(dict(f=f, t=t, lab=lab, acc=acc, dash=dash, side=side, lo=lo, hi=hi))

    for sd in ("up", "down"):
        placed = []
        for a in sorted([a for a in arcs if a["side"] == sd], key=lambda a: (a["hi"] - a["lo"], a["lo"])):
            L = 1 + max([b["lane"] for b in placed if b["lo"] >= a["lo"] and b["hi"] <= a["hi"]] or [0])
            while any(b["lane"] == L and b["lo"] < a["hi"] and a["lo"] < b["hi"] for b in placed):
                L += 1
            a["lane"] = L
            placed.append(a)
    # attach points: at each node, arcs coming from the left, then arcs leaving to the right, ordered so that
    # nested arcs do not cross (above: incoming by lane ascending, outgoing by lane descending; mirrored below)
    for sd in ("up", "down"):
        for k in NODE_ORDER:
            inc = [a for a in arcs if a["side"] == sd and ((a["t"] == k and a["lo"] < cx[k]) or
                                                          (a["f"] == k and a["lo"] < cx[k]))]
            out = [a for a in arcs if a["side"] == sd and ((a["f"] == k and a["hi"] > cx[k]) or
                                                          (a["t"] == k and a["hi"] > cx[k]))]
            seq = sorted(inc, key=lambda a: a["lane"]) + sorted(out, key=lambda a: -a["lane"])
            m = len(seq)
            step = min(30, (nw - 60) / max(m - 1, 1))
            for i, a in enumerate(seq):
                x = cx[k] + (i - (m - 1) / 2) * step
                a["x_" + ("f" if a["f"] == k else "t")] = x

    LS = 40
    up_n = max(a["lane"] for a in arcs if a["side"] == "up")
    dn_n = max([a["lane"] for a in arcs if a["side"] == "down"] or [0])

    # the legend
    y += c.legend(X0, y, [
        ("arrow", "blue", "grant edge of the text (Txt)"), ("arrow", "teal", "grant edge of a statute (Law)"),
        ("arrow", "red", "XXV sec. 2's NominateVP: the one grant edge among government bodies that runs back"),
        ("arrow", "violet", "drawn only under M_CONGRESS_AMENDS (a mutation)", "7 5"),
        ("box", "brown", "the People and the States, set aside by InnerGrant"),
    ]) + 18

    top = y + 26
    yN = top + 30 + (up_n - 1) * LS + 34
    nodes = {
        "People": ("`People`", "brown", ["Fixed node. Ordains the Constitution; elects the House; sues.",
                                          "Set aside by `InnerGrant`."]),
        "States": ("`States`", "brown", ["Fixed node. Ratify amendments, appoint electors, chose the Senate "
                                          "until XVII.", "Set aside by `InnerGrant`."]),
        "Constitution": ("`Constitution`", "blue", [f"Rank {rk['Constitution']}. The text: only the People and "
                                                     "the States write into it."]),
        "Congress": ("`Congress`", "teal", [f"Rank {rk['Congress']}. Both Houses, the Senate's consent and "
                                             "trial; creates and abolishes bodies."]),
        "VicePresident": ("`VicePresident`", "teal", [f"Rank {rk['VicePresident']}. An office: acts only while "
                                                       "seated (`Active`)."]),
        "Executive": ("`Executive`", "teal", [f"Rank {rk['Executive']}. The President; an office, acts only "
                                               "while seated."]),
        "Judiciary": ("`Judiciary`", "teal", [f"Rank {rk['Judiciary']}. The Supreme Court, \"an institution that "
                                               "never lapses\" (`Offices`)."]),
        "a": ("agency `a` ∈ `Agencies`", "teal", [f"Rank {rk['OTHER']}. Exists only while its enabling act "
                                                   "stands (`live`); its head is an office."]),
        "c": ("court `c` ∈ `Courts`", "teal", [f"Rank {rk['OTHER']}. An inferior court Congress ordains; its "
                                               "judge holds office in good behaviour."]),
    }
    hN = max(c.card(0, 0, nw, t, b, draw=False, size=13.5, bullets=False) for t, _, b in nodes.values())
    yB = yN + hN
    for k in NODE_ORDER:
        t, acc, b = nodes[k]
        c.card(cx[k] - nw / 2, yN, nw, t, b, accent=acc, h=hN, size=13.5, bullets=False,
               dash="7 5" if k in ("a", "c") else None)

    def lane_y(a):
        return (yN - 34 - (a["lane"] - 1) * LS) if a["side"] == "up" else (yB + 34 + (a["lane"] - 1) * LS)

    for a in arcs:
        ly = lane_y(a)
        y0, y1 = (yN - 1, yN - 3) if a["side"] == "up" else (yB + 1, yB + 3)
        c.arrow([(a["x_f"], y0), (a["x_f"], ly), (a["x_t"], ly), (a["x_t"], y1)], a["acc"], dash=a["dash"],
                sw=2)
    for a in arcs:
        ly = lane_y(a)
        lo, hi = sorted((a["x_f"], a["x_t"]))
        cross = sorted(x for b in arcs if b is not a and b["side"] == a["side"] and b["lane"] > a["lane"]
                       for x in (b["x_f"], b["x_t"]) if lo + 1 < x < hi - 1)
        pts = [lo] + cross + [hi]
        g0, g1 = max(zip(pts, pts[1:]), key=lambda p: p[1] - p[0])
        c.label((g0 + g1) / 2, ly, a["lab"], a["acc"], 12.5, maxw=max(g1 - g0 - 30, 120))

    y = yB + (34 + (dn_n - 1) * LS + 24 if dn_n else 20)
    # what sits under the nodes: the set InnerGrant keeps
    xa, xb = cx["People"] - nw / 2, cx["States"] + nw / 2
    c.line(xa, y, xb, y, "brown", sw=2.2)
    c.text((xa + xb) / 2, y + 22, "set aside by `InnerGrant` (`LiveNodes \\ {\"People\", \"States\"}`)", 13.5,
           "brown", anchor="middle")
    xa2, xb2 = cx["Constitution"] - nw / 2, cx["c"] + nw / 2
    c.line(xa2, y, xb2, y, "teal", sw=2.2)
    c.text((xa2 + xb2) / 2, y + 22, "the inner grant layer: `Rank` climbs left to right, 1 to 6 "
           "(`GrantFollowsChainExceptXXV`: every grant edge here but `NominateVP` climbs)", 13.5, "teal",
           anchor="middle")
    return y + 40, arcs


# ---------------------------------------------------------------------------------------------- the diagram
def build():
    spec = read_spec()
    blocks = readme_blocks()
    t, p, rows_hdr = read_results()
    R = t["rows"]
    byname = {r["name"]: r for r in R}

    # README's two tables
    _, ch_hdr, ch_rows = blocks[6]
    _, mu_hdr, mu_rows = blocks[8]
    need(ch_hdr == ["Claim", "Local form (proved)", "Global form (checked)"], "README.md", "claims table header")
    need(mu_hdr == ["Mutation", "Removes", "Reverts to", "Breaks"], "README.md", "mutation table header")

    thm_of = {}
    for th in p["theorems"]:
        m = re.fullmatch(r"Spec => (?:\[\])?(\w+)", th["prove"])
        need(m, PF, f"theorem {th['name']} does not prove Spec => []P or Spec => P")
        th["prop"] = m.group(1)
        thm_of.setdefault(m.group(1), []).append(th)
    local_names, global_names = [], []
    run_props = {r["prop"] for r in R}
    for row in ch_rows:
        for col, acc in ((1, local_names), (2, global_names)):
            for x in re.findall(r"`(\w+)`", row[col]):
                need(x in run_props or x == "FairSpec", "README.md", f"claims table names {x}, which no row runs")
                if x in run_props:
                    acc.append(x)
    for x in local_names:
        need(x in thm_of, PF, f"README's local form {x} has no theorem")
    for x in global_names:
        need(x not in thm_of, PF, f"README's global form {x} has a theorem")
    reach_claims = [x for x in global_names if x != "UnconstitutionalEdgesAreStruck"]
    refuted = ["GrantCyclesPassThroughPeopleOrStates", "GrantFollowsChain"]
    need(sorted(reach_claims) == sorted(set(spec["reach"]) - set(refuted)), SPEC,
         f"the properties over Reach {spec['reach']} are not README's global forms {reach_claims} plus the refuted")
    live_prop = "UnconstitutionalEdgesAreStruck"

    # every row, in exactly one band
    cat = {}
    for r in R:
        nm = r["name"]
        if r["kind"] == "SIMULATE":
            cat[nm] = "sample"
        elif r["kind"] == "DEADLOCK":
            cat[nm] = "deadlock"
        elif nm.startswith("r-"):
            cat[nm] = "refuted"
        elif r["mut"] == "none" and r["prop"].startswith("Never"):
            cat[nm] = "witness"
        elif r["spec"] != "Spec":
            cat[nm] = "liveness"
        else:
            cat[nm] = "matrix"
    wit = [r for r in R if cat[r["name"]] == "witness"]
    need(wit == C.witnesses(t), TF, "witness rows differ from corpus.witnesses")
    need(all(r["prop"] in refuted and r["verdict"] == "COUNTEREXAMPLE" and r["mut"] == "none" and
             r["conf"] == "o" for r in R if cat[r["name"]] == "refuted") and
         sorted(r["prop"] for r in R if cat[r["name"]] == "refuted") == sorted(refuted), TF,
         "the r- rows are not the two refuted claims, COUNTEREXAMPLE under none")
    obl = p["obligations"]
    readme_sum = C.readme_summary()["Government"]
    need(readme_sum == dict(rows=t["total"], mutations=len(C.mutations(t)), witnesses=len(wit),
                            obligations=obl), "README.md", f"summary table Government row {readme_sum} differs")

    W_ = W
    c = Canvas(ID, "`Government.tla`: the authority graph — who creates, fills, directs and removes whom, and "
               "which claims about it are proved, checked, sampled or refuted",
               "A directed, labelled multigraph over the People, the States, the Constitution, the three "
               "branches, the Vice President, and the agencies and inferior courts Congress creates. Every act "
               "fires one edge, by its holder; statutes, amendments and courts reshape the graph. Each "
               "reachability claim is stated twice: **a local form, proved, and a global form over `Reach`, "
               f"checked by TLC and not proved**. The liveness property `{live_prop}` is **checked, not "
               "proved**, and two claims of the module's first version are **refuted by TLC**. This models the "
               "text's procedure; it is an exercise, not law (README, opening).",
               W_, "README.md § Government.tla — the authority graph (every paragraph, both tables, Witnesses, "
               "Liveness, Rows, A claim TLC refuted), § How the specs are written and checked (the summary table "
               "row, the vocabulary, What is not proved), § Findings (One mutation that changes nothing), the "
               "opening; specs/Government.tla (header: PROPERTIES, REFUTED CLAIMS, MUTATIONS, WITNESSES, "
               "ABSTRACTED, CONSTANTS; Fixed, Offices, Founding, ArticleV, Adds, Drops, AgencyEdges, CourtEdges, "
               "EdgesAfter, Sever, Challengeable, Rank, InnerGrant, IsInert, every action of Next, the properties, "
               "Unrecorded, LawRowsBound); specs/Government.cfg; specs/Government_proof.tla (header, LocalSafety, "
               "the mutation lemmas); rows/Government-rows.txt (header); " + TF + "; " + PF + "; " + FIND +
               " § 1 and § 5")
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    items = [("Government.tla", [("checked", f"{t['total']} rows, all as expected"),
                                 ("proved", f"{n(obl)} obligations, all proved")]),
             ("Global claims over Reach", [("notproved", x) for x in reach_claims]),
             ("Liveness", [("notproved", live_prop)]),
             ("Witnesses", [("checked", f"{len(wit)}, each violated")]),
             ("First version's claims", [("refuted", x) for x in refuted]),
             ("At Government.cfg's constants", [("sampled", "1 row, never a check")]),
             ("Header's ABSTRACTED list", [("abstracted", "")])]
    y = status_strip(c, X0, X1, y, items)
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row "
                "list. **Proved** means TLAPS discharged every obligation for every value of the constants the "
                "module's named assumptions admit. **Sampled** means random simulation found no error, and is "
                "never cited as a check. **Refuted** means TLC found a counterexample to a claim the model was "
                "expected to satisfy. \"None of these is a claim about law or practice\" (README § How the specs "
                "are written and checked).", 14.5, "muted") + 30

    # ---- band 1: the picture
    y = band(c, X0, y, "The grant layer: where authority comes from, read from `Government.tla`'s edge sets "
             "(`Founding`, `Adds`, `Drops`, `AgencyEdges`, `CourtEdges`)", "teal")
    y += c.para(X0, y, WW, md(blocks[0][1]) + " " + md(blocks[1][1][0]) + " " + md(blocks[1][1][1]) +
                " (README § Government.tla.) One arrow per pair of nodes, labelled with each kind and label; "
                "the agency's conditional edges carry the enabling act's option (`x`, `r`, `v`).", 14, "ink") + 18
    y, arcs = picture(c, y, spec)
    y += 10
    up = [a for a in arcs if a["side"] == "up"]
    y += row_cards(c, X0, y, WW, 26, [
        ("Above the nodes: every grant edge climbs", [
            f"{len(up)} arrows, each from a lower `Rank` to a higher one, or from the People or the States.",
            "`GrantFollowsChainExceptXXV`: every inner grant edge but `NominateVP` has "
            "`Rank(e.from) < Rank(e.to)`. Proved under `Mut # \"M_CONGRESS_AMENDS\"`."], "blue",
         {"status": "proved"}),
        ("Below: the edges that run back", [
            "`Congress -> States` (`Propose`): into a node `InnerGrant` sets aside.",
            "`Executive -> VicePresident` (`NominateVP`, XXV sec. 2), with `Succession` back up: the one inner "
            "grant cycle (`NominationLoopIffXXV`, proved; `OnlyGrantCycleIsXXV`, checked).",
            "`Congress -> Constitution` (`Ratify`) exists only under `M_CONGRESS_AMENDS`."], "red", {}),
        ("Every body traces to the People", [
            "`NamedPathsFromPeople` (proved): `People -ElectHouse-> Congress`, then one named edge from Congress "
            "to every branch, the Vice President and every live body (`FromCongress`).",
            "`PowerTracesToPeople`: the same over `Reach`; checked, not proved."], "brown", {}),
        ("Power comes only through the text", [
            "`PeoplePowerGoesThroughConstitution` (proved): every Power or Amend edge out of the People goes "
            "into the text.",
            "`ConstitutionIsTheOnlyDoor`: remove the Constitution and no Power or Amend path from the People "
            "reaches the government; over `Reach`, checked, not proved."], "amber", {"status": "notproved"}),
    ]) + 36

    # ---- the control layer, holder by target, read
    y = band(c, X0, y, "The control layer: one holder acting on another's exercise of power, read from the same "
             "edge sets", "teal")
    allE = ([dict(e, src="") for e in spec["founding"]] +
            [dict(e, src={"Adds(\"XVII\")": "XVII", "Adds(\"XXV\")": "XXV",
                          "M_CONGRESS_AMENDS": "M_CONGRESS_AMENDS"}[e["part"]]) for e in spec["adds"]] +
            [dict(e, src="" if e["part"] == "always" else e["part"]) for e in spec["agency"]] +
            [dict(e, src="") for e in spec["court"]])
    allE += [dict(basis="Statute", frm="Congress", to="a", kind="Control", label="LegislativeVeto",
                  src="bill LegislativeVeto"),
             dict(basis="Statute", frm="Congress", to="c", kind="Control", label="DiminishPay", src="bill CutPay")]
    ctrl = [e for e in allE if e["kind"] == "Control"]
    holders = [k for k in NODE_ORDER if any(e["frm"] == k for e in ctrl)]
    targets = [k for k in NODE_ORDER if any(e["to"] == k for e in ctrl)]
    chal = spec["challengeable"]
    tname = {"a": "agency `a`", "c": "court `c`"}
    cols = [("Holder", 210, {"bold": True})]
    tw = (WW - 210) / len(targets)
    cols += [(f"onto {tname.get(k, k)}", tw) for k in targets]
    rows = []
    for h in holders:
        cells = [f"`{h}`"]
        for k in targets:
            es = [e for e in ctrl if e["frm"] == h and e["to"] == k]
            parts = []
            for e in es:
                s = e["label"]
                if e["src"]:
                    s += (f" (by a later {e['src']})" if e["src"].startswith("bill") else
                          f" ({'from ' if e['src'] in ('XVII', 'XXV') else 'if '}{e['src']})")
                if (e["frm"], e["kind"], e["label"]) in chal:
                    s = f"[[red|{s}]]"
                parts.append(s)
            cnt = f"**{len(es)}**: " if h in ("Congress", "Executive", "Judiciary") and \
                k in ("Congress", "Executive", "Judiciary") and es else ""
            cells.append(cnt + ", ".join(parts) if parts else "—")
        rows.append(cells)
    y += c.table(X0, y, cols, rows, size=13.5) + 16

    def cnt(f, to, with_xxv):
        return sum(1 for e in ctrl if e["frm"] == f and e["to"] == to and (e["src"] == "" or
                                                                            (with_xxv and e["src"] == "XXV")))
    prim = [(x, cnt("Congress", x, False), cnt(x, "Congress", False), cnt("Congress", x, True),
             cnt(x, "Congress", True)) for x in ("Executive", "Judiciary")]
    for x, a0, b0, a1, b1 in prim:
        need(a0 > b0 and a1 > b1, SPEC, f"LegislativePrimacy fails on the text for {x}")
    y += row_cards(c, X0, y, WW, 26, [
        ("How to read it", ["Each cell lists the labels of the edges from the holder onto the target. **Bold** "
                            "numbers count the edges between two branches. [[red|Red]]: the five `Challengeable` "
                            "edges, those a doctrine can forbid (`Violates`).",
                            "An agency's edges are drawn by its enabling act (`AgencyEdges(a, x, r, v)`); "
                            "`Direct` only if it has executive power (`x`), one removal edge by `r`. A later bill "
                            "(`EdgesAfter`) adds `LegislativeVeto` or `DiminishPay`."], "grey", {}),
        ("`MutualChecks` (proved) and `ControlLayerIsCyclic` (checked)",
         ["Every branch has a control edge onto each other branch: every off-diagonal cell among the three "
          "branches is filled, and no statute joins two branches.",
          "So the control layer among the branches is cyclic. That global form is over `Reach`: checked, not "
          "proved."], "teal", {}),
        ("`LegislativePrimacy` (proved), counted by the diagram",
         [f"Congress onto `{x}`: {a0} edges in the 1789 text ({a1} with XXV); `{x}` onto Congress: {b0} ({b1})."
          for x, a0, b0, a1, b1 in prim] +
         ["The property counts the edges in the graph at each state; these are the diagram's counts over "
          "`Founding` and `Adds(\"XXV\")`."], "blue", {"status": "proved"}),
    ]) + 36

    # ---- the edge sets, whole
    y = band(c, X0, y, "Every edge the module draws, as `Government.tla` writes it (read at build time)")
    lw_ = (WW - 30) * 0.53
    rw_ = WW - 30 - lw_
    lcols = [("Set", 210), ("From", 140, {"mono": True}), ("To", 140, {"mono": True}),
             ("Kind", 90), ("Label", 200, {"mono": True})]
    lcols.append(("The spec's comment", lw_ - sum(x[1] for x in lcols)))
    lrows = []
    grp = None
    for e in spec["founding"]:
        if e["group"] != grp:
            grp = e["group"]
            lrows.append({"group": f"Founding — {grp}", "accent": "blue"})
        dropped = any(d["frm"] == e["frm"] and d["to"] == e["to"] and d["label"] == e["label"]
                      for d in spec["drops"])
        av = any(d["frm"] == e["frm"] and d["to"] == e["to"] and d["label"] == e["label"] for d in spec["artv"])
        tags = (" [[grey|dropped by XVII]]" if dropped else "") + (" [[blue|ArticleV]]" if av else "")
        lrows.append(["`Founding`", e["frm"], e["to"], e["kind"], e["label"], (e["note"] or "—") + tags])
    lrows.append({"group": "What ratifying an amendment adds (Adds) and drops (Drops); the constant mutations",
                  "accent": "violet"})
    for e in spec["adds"]:
        st = f"`{e['part']}`" if e["part"] != "M_CONGRESS_AMENDS" else "[[violet|M_CONGRESS_AMENDS]]"
        lrows.append([st, e["frm"], e["to"], e["kind"], e["label"], e["note"] or "—"])
    for e in spec["drops"]:
        lrows.append(["`Drops(\"XVII\")`", e["frm"], e["to"], e["kind"], e["label"], "removed at ratification"])
    lrows.append(["[[violet|M_NO_ARTV]]", "—", "—", "—", "ArticleV",
                  "`Drops(\"XXV\")` is `IF Mut = \"M_NO_ARTV\" THEN ArticleV ELSE {}`: XXV would repeal "
                  "Article V's three edges"])
    rcols = [("Condition", 190), ("From", 120, {"mono": True}), ("To", 50, {"mono": True}),
             ("Kind", 82), ("Label", 170, {"mono": True})]
    rcols.append(("Note", rw_ - sum(x[1] for x in rcols)))
    doct = {("Congress", "AppointInferior"): "Buckley", ("Executive", "RemoveForCause"): "Seila Law",
            ("Congress", "Remove"): "Bowsher", ("Congress", "LegislativeVeto"): "Chadha",
            ("Congress", "DiminishPay"): "Will"}
    rrows = [{"group": "AgencyEdges(a, x, r, v): the enabling act", "accent": "teal"}]
    for e in spec["agency"]:
        ch_ = (e["frm"], e["kind"], e["label"]) in chal
        note = (f"[[red|Challengeable]]; `Violates` under {doct[(e['frm'], e['label'])]}"
                + (" with executive power" if e["label"] in ("RemoveForCause", "Remove") else "")) if ch_ else "—"
        rrows.append([e["part"], e["frm"], e["to"], e["kind"], e["label"], note])
    rrows.append(["vesting = Head", "—", "a", "—", "—", "no edge: the head appoints inside the agency, which "
                  "does not cross between bodies (header, ABSTRACTED)"])
    rrows.append({"group": "CourtEdges(c): an inferior court, ordained by Congress", "accent": "teal"})
    for e in spec["court"]:
        rrows.append(["always", e["frm"], e["to"], e["kind"], e["label"], e["note"] or "—"])
    rrows.append({"group": "Later statutes (EdgesAfter) and courts' remedies (Sever)", "accent": "teal"})
    rrows += [["bill `LegislativeVeto`", "Congress", "a", "Control", "LegislativeVeto",
               "[[red|Challengeable]]; Chadha"],
              ["bill `CutPay`", "Congress", "c", "Control", "DiminishPay", "[[red|Challengeable]]; Will"],
              ["bill `StripJurisdiction`", "Judiciary", "c", "Control", "Appeal", "removed (\"McCardle\")"],
              ["`Sever`, Seila Law", "Executive", "a", "Control", "Remove", "replaces the struck `RemoveForCause`: "
               "the head serves at will"],
              ["`Sever`, Bowsher", "Executive", "a", "Power", "ExecutivePower",
               "removed with `Direct`; Congress keeps its removal power"],
              ["[[violet|M_SEVER_PLAIN]]", "—", "—", "—", "—", "`Sever(e)` is `edges \\ {e}`: no remedy"]]
    hl = c.table(X0, y, lcols, lrows, size=13)
    hr = c.table(X0 + lw_ + 30, y, rcols, rrows, size=13)
    y += max(hl, hr) + 16
    y += c.para(X0, y, WW, f"{len(spec['founding'])} founding edges; `ArticleV` is "
                f"{len(spec['artv'])} of them. `AgencyEdges` has {len(spec['agency'])} edges over its options and "
                f"`CourtEdges` {len(spec['court'])}. The Note column's doctrine names are the diagram's reading "
                "of `Violates`; red marks the edges `Challengeable` lists.", 13.5, "muted") + 36

    # ---- the actions
    y = band(c, X0, y, "Every act is the firing of an edge: the actions of `Next` and the edge each fires (read "
             "from each body)", "teal")
    acols = [("Section of the spec", 330), ("Action", 260, {"mono": True}),
             ("Fires (the spec's Fire argument)", 900, {"mono": True})]
    acols.append(("What it changes (the diagram's gloss of the body)", WW - sum(x[1] for x in acols)))
    arows = []
    for g, acts in ACTIONS:
        first = True
        for a, gloss in acts:
            prm, fs_ = spec["fires"][a]
            arows.append([f"**{g}**" if first else "", a + (f"({prm})" if prm else ""),
                          " or ".join(fs_) if fs_ else "none: last' = NoEdge", gloss])
            first = False
    y += c.table(X0, y, acols, arows, size=13) + 14
    y += c.para(X0, y, WW, "`Fire(e)` is `OnGraph(e) /\\ Held(e)`: the edge is in the graph and its holder is "
                "seated (`Active`), unless `M_OFFEDGE` or `M_INACTIVE` removes the check; an act that strayed "
                "is recorded in `stray`. `IsInert` labels: " + codes(spec["inert"]) + ", and `Review` onto "
                "anything but Congress, `Nominate` and `Consent` onto the Judiciary.", 13.5, "muted") + 20
    y += row_cards(c, X0, y, WW, 26, [
        ("Statutes add and remove edges and nodes", [
            "`Enact(op)` (from `Sign`, `Lapse`, `Override`): `CreateAgency` adds `AgencyEdges`, `EstablishCourt` "
            "adds `CourtEdges`, abolition removes every edge `Touching` the body and unseats its holder (Stuart "
            "v. Laird, `Unseat`), `LegislativeVeto` and `CutPay` add one edge, `StripJurisdiction` removes "
            "`Appeal`.",
            "`Precondition(op)`: the body exists, or not yet; the edge is new. Checked at passage and re-checked "
            "at enactment."], "teal", {}),
        ("Amendments rewrite text edges", [md(blocks[3][1][1]) + " (README.)",
                                           "`Ratify(x)` is the only action that changes the text "
                                           "(`TextChangesOnlyByArticleV`, an action property, proved)."], "blue", {}),
        ("Courts sever statutory edges", [
            "`Review(e)`: a forbidden edge is struck and `Sever` keeps the rest of the Act; an upheld edge a "
            "doctrine forbids is recorded in `breaches`.",
            "Statutory edges change only by presentment, override or review (`StatutesChangeOnlyByLawOrCourt`, "
            "proved)."], "teal", {}),
        ("Two flags", [md(blocks[7][1]) + " (README.)"], "grey", {}),
    ]) + 36

    # ---- band: the README's claims table, whole
    y = band(c, X0, y, "The README's claims table, every row and column, with the theorem and the TLC rows behind "
             "each name")
    y += c.para(X0, y, WW, md(blocks[4][1]) + " " + " ".join(md(x) for x in blocks[5][1]) + " (README § "
                "Government.tla.)", 14, "ink") + 12

    def tlc_none(name):
        rs = [r for r in R if r["prop"] == name and r["mut"] == "none" and r["spec"] in ("Spec", "FairSpec")
              and cat[r["name"]] in ("matrix", "liveness")]
        need(rs, TF, f"no Mut = none row for {name}")
        out = []
        for r in rs:
            v = "[[teal|HOLDS]]" if r["verdict"] == "HOLDS" else "[[red|COUNTEREXAMPLE]]"
            out.append(f"{r['conf']} {v}" + (f" ({r['spec']})" if r["spec"] != "Spec" else ""))
        return " · ".join(out)

    ccols = [("Claim", 780), ("Local form (proved)", 520), ("Global form (checked)", 430),
             ("Theorem for each local form (proof results; the diagram's join)", 640)]
    ccols.append(("TLC rows under Mut = none on Spec or FairSpec, by configuration (read; the diagram's join)",
                  WW - sum(x[1] for x in ccols)))
    crows = []
    for row in ch_rows:
        ln_ = [x for x in re.findall(r"`(\w+)`", row[1]) if x in run_props]
        gn_ = [x for x in re.findall(r"`(\w+)`", row[2]) if x in run_props]
        thms = "; ".join(f"`{th['name']}`" + (" [" + ", ".join(th["assume"]) + "]" if th["assume"] else "")
                         for x in ln_ for th in thm_of[x]) or "—"
        tl = "\n".join(f"`{x}`: " + tlc_none(x) for x in ln_ + gn_)
        crows.append([md(row[0]), md(row[1]), md(row[2]) + (" [[amber|checked, not proved]]" if gn_ else ""),
                      thms, tl])
    y += c.table(X0, y, ccols, crows, size=13) + 14
    y += c.para(X0, y, WW, "Configurations: o no agency or court, every amendment; c one inferior court; a one "
                "agency under `LawRowsBound`; af the agency without it; l-a, l-c the liveness rows (below). "
                "Under `Mut = \"none\"` every property is run in o, c and a; `Safety` and `TypeOK` also in af.",
                13.5, "muted") + 20
    y += row_cards(c, X0, y, WW, 26, [
        ("What is not proved: the global forms (README § How the specs are written and checked)",
         ["\"`Government.tla`'s global reachability claims are checked, not proved. They are stated over "
          "`Reach`, a recursive function the prover has no fixpoint theory for. Each one's local form is "
          "proved.\"",
          "The diagram's check: the properties whose definitions use `Reach` or `Acyclic` are exactly these "
          f"{len(reach_claims)} and the two refuted claims: " + codes(reach_claims) + "."], "amber",
         {"status": "notproved"}),
        ("Why each global form still holds (`Government_proof.tla`, header, NOT PROVED)",
         ["\"Each follows from proved local forms: no inner grant edge but NominateVP descends the rank "
          "(GrantFollowsChainExceptXXV), so none outside the VP lies on a cycle; NominateVP is present exactly "
          "under XXV and Succession always (NominationLoopIffXXV), which closes the one loop; People -> "
          "Congress -> each body by named edges (NamedPathsFromPeople); every Power or Amend edge out of the "
          "People enters the text (PeoplePowerGoesThroughConstitution); every pair of branches has a control "
          "edge each way (MutualChecks).\"", "That argument is prose, not a proof the prover checked."],
         "amber", {}),
        ("Abstracted (`Government.tla` header)", [hpara(spec, "ABSTRACTED:"), hpara(spec, "CONSTANTS beyond")],
         "grey", {"status": "abstracted"}),
    ]) + 36

    # ---- band: the configurations
    y = band(c, X0, y, "The configurations: rows run under different constants (rows file header; results read)")
    cnf = {}
    for cf in ("o", "c", "a", "af", "l-a", "l-c", "s"):
        rs = [r for r in R if r["conf"] == cf]
        st = sorted({r["states"] for r in rs if r["verdict"] == "HOLDS" and r["mut"] == "none" and
                     r["states"] is not None})
        cnf[cf] = (rs, st)
    y += c.para(X0, y, WW, "Rows file header: \"" + rows_hdr[0] + "\"", 14, "ink") + 10
    y += c.para(X0, y, WW, "Default constants (results file, Constants:): `" + t["constants"].split(" (Mut")[0] +
                "`; Config: `" + "`, `".join(t["config"]) + "`.", 13.5, "muted") + 14
    cfg_text = C.read(CFG)
    need("SPECIFICATION FairSpec" in cfg_text and "Agencies = {ag1, ag2}" in cfg_text and "VIEW" not in cfg_text,
         CFG, "not the configuration drawn (FairSpec, two agencies, no VIEW)")
    cfg_consts = [ln.strip() for ln in cfg_text.split("CONSTANTS", 1)[1].split("INVARIANTS")[0].splitlines()
                  if ln.strip()]
    cfg_inv = [ln.strip() for ln in cfg_text.split("INVARIANTS", 1)[1].split("PROPERTIES")[0].splitlines()
               if ln.strip()]
    cfg_prop = [ln.strip() for ln in cfg_text.split("PROPERTIES", 1)[1].splitlines() if ln.strip()]
    sim = [r for r in R if r["conf"] == "s"]
    need(len(sim) == 1 and sim[0]["verdict"] == "NO-ERROR-SAMPLED" and sim[0]["sampled"], TF,
         "not one NO-ERROR-SAMPLED row")
    sim = sim[0]

    def cbody(cf, txt):
        rs, st = cnf[cf]
        return [txt, f"Constants on its rows: `{' '.join(CONFS[cf][0]) or 'the defaults'}`" +
                ("; `CONSTRAINT LawRowsBound`" if CONFS[cf][1] else ""),
                f"**{len(rs)} rows**; distinct states under `none` when a row holds: "
                + (", ".join(n(s) for s in st) or "—")]
    y += row_cards(c, X0, y, WW, 22, [
        ("o: no agency or court", cbody("o", "Every amendment proposable: XVII, XXV and the Vice Presidency's "
                                        "machinery."), "teal", {}),
        ("c: one inferior court", cbody("c", "No agency; `ct1` may be established, staffed, abolished."), "teal",
         {}),
        ("a: one agency, bounded", cbody("a", "Executive power, removal by the President for cause or by "
                                         "Congress, Congress appoints inferior officers; no trial, no Vice "
                                         "President, no nomination (`LawRowsBound`)."), "teal", {}),
        ("af: the agency, unbounded", cbody("af", "The same agency without `LawRowsBound`."), "teal", {}),
        ("l-a, l-c: liveness", [f"l-a: `{' '.join(CONFS['l-a'][0])}`, no bound; **{len(cnf['l-a'][0])} rows**.",
                                f"l-c: the court; **{len(cnf['l-c'][0])} rows**.",
                                "Distinct states when `UnconstitutionalEdgesAreStruck` holds: " +
                                ", ".join(n(s) for s in cnf["l-a"][1] + cnf["l-c"][1]) + "."], "amber", {}),
        ("s: a sample at `Government.cfg`'s constants", [
            f"`{sim['name']}`: `{sim['prop']}` ({sim['extra']}), **{sim['verdict']}**, {n(sim['states'])} states "
            "checked.", "\"The s- row is a sample at Government.cfg's constants, never a check\" (rows file "
            "header)."], "grey", {"status": "sampled"}),
        ("`Government.cfg`, the full constants", [
            "`SPECIFICATION FairSpec`; `" + "`, `".join(cfg_consts) + "`",
            "INVARIANTS `" + "`, `".join(cfg_inv) + "`; PROPERTIES `" + "`, `".join(cfg_prop) + "`.",
            "No `VIEW` there: the rows add `VIEW Unrecorded` (rows file `# cfg:`). \"The exhaustive state space "
            "at these constants is very large\" (its comment)."], "grey", {}),
    ], size=13.5) + 16
    y += row_cards(c, X0, y, WW, 26, [
        ("README § Government.tla, Rows", [md(blocks[14][1])] + [md(x) for x in blocks[15][1]] +
         [md(blocks[16][1])], "grey", {}),
        ("`Unrecorded` and `LawRowsBound` (`Government.tla`, Bounds for TLC)",
         ["`Unrecorded` is every variable but `last`: \"no action reads it, so states that differ only in "
          "`last` have the same successors.\"",
          "`LawRowsBound == trial = \"None\" /\\ \"VicePresident\" \\notin seated /\\ nominated = {}`: \"the "
          "mutations they check act on statutes and courts' rulings\"."], "grey", {}),
    ]) + 36

    # ---- band: the mutation table, whole, with the header's list and the results
    y = band(c, X0, y, "The README's mutation table, every row and column, beside the module header and the "
             "results", "violet")
    hm = spec["hmuts"]
    props_known = sorted({r["prop"] for r in R if cat[r["name"]] in ("matrix", "liveness")}, key=len,
                         reverse=True)
    five = ["BuckleyHonoured", "SeilaLawHonoured", "BowsherHonoured", "ChadhaHonoured", "WillHonoured"]

    def parse_breaks(cell):
        names = [x for x in re.findall(r"`(\w+)`", cell) if x != "none"]
        for x in names:
            need(x in props_known, "README.md", f"mutation table names {x}, which no row checks")
        rest = re.sub(r"`\w+`|\(see Findings\)", "", cell)
        out = list(names)
        if "the five doctrine properties" in rest:
            out += five
            rest = rest.replace("the five doctrine properties", "")
        if "liveness" in rest:
            out.append(live_prop)
            rest = rest.replace("liveness", "")
        if rest.strip().startswith("nothing"):
            need(not names, "README.md", "a Breaks cell says nothing and names a property")
            rest = rest.replace("nothing: the same reachable states as", "")
        need(not re.sub(r"[\s,;:]", "", rest), "README.md", f"Breaks cell not understood: {cell!r}")
        return out

    def parse_header(txt):
        out = [x for x in props_known if re.search(r"\b" + x + r"\b", txt)]
        if "All five doctrine properties must fail" in txt:
            out += five
        need("must fail" in txt or "no property may fail" in txt, SPEC, f"header entry not understood: {txt!r}")
        return out

    lemmas = {}
    for m in re.finditer(r"^LEMMA (\w+) ==\n\s+ASSUME Mut = \"(M_\w+)\"(.*?)\n(?:BY|PROOF)", C.read(PROOF),
                         re.M | re.S):
        lemmas[m.group(2)] = (m.group(1), re.sub(r"\s+", " ", m.group(3).split("PROVE", 1)[1]).strip())
    need(len(lemmas) == 14 and all(x in p["lemmas"] for x, _ in lemmas.values()), PROOF,
         "not one listed mutation lemma per mutation")

    muts = C.mutations(t)
    need([r[0].strip("`") for r in mu_rows] == muts and list(hm) == muts, "README.md",
         "README's mutation table, the module header and the results run the mutations in different orders")
    ce = {m: [] for m in muts}
    mconf = {m: [] for m in muts}
    for r in R:
        if r["mut"] != "none" and cat[r["name"]] in ("matrix", "liveness"):
            if r["conf"] not in mconf[r["mut"]]:
                mconf[r["mut"]].append(r["conf"])
            if r["verdict"] == "COUNTEREXAMPLE":
                ce[r["mut"]].append((r["prop"], r["conf"]))
    disagree = []
    mcols = [("Mutation", 210, {"mono": True, "bold": True}), ("Removes", 400), ("Reverts to", 330),
             ("Breaks", 470), ("Module header: must fail", 470), ("Configurations run (read)", 170),
             ("COUNTEREXAMPLE in the results (read)", 520)]
    mcols.append(("Lemma: what it admits (proof module)", WW - sum(x[1] for x in mcols)))
    mrows = []
    for row in mu_rows:
        m = row[0].strip("`")
        rb, hb = parse_breaks(row[3]), parse_header(hm[m])
        got = sorted({x for x, _ in ce[m]})
        ok_r, ok_h = sorted(set(rb)) == got, sorted(set(hb)) == got
        if not ok_r:
            disagree.append(f"README's Breaks for `{m}` names {codes(sorted(set(rb)))}, its COUNTEREXAMPLE rows are on "
                            f"{codes(got)}")
        if not ok_h:
            disagree.append(f"the module header's entry for `{m}` names {codes(sorted(set(hb)))}, its COUNTEREXAMPLE "
                            f"rows are on {codes(got)}")
        hb_txt = codes(hb) if hb else "no property may fail"
        cetxt = ", ".join(f"`{x}` ({cf}" + (", liveness" if x == live_prop else "") + ")" for x, cf in ce[m]) \
            or "none: every row HOLDS"
        lm = lemmas[m]
        cells = [m, md(row[1]), md(row[2]), md(row[3]) + ("" if ok_r else " [[red|≠ results]]"),
                 hb_txt + ("" if ok_h else " [[red|≠ results]]"), ", ".join(mconf[m]), cetxt,
                 f"`{lm[0]}`: `{lm[1]}`"]
        mrows.append(cells if ok_r and ok_h else {"cells": cells, "accent": "red"})
    y += c.table(X0, y, mcols, mrows, size=13) + 14
    rech = [r for r in R if r["mut"] == "M_RECHECK"]
    a_none = byname["a-none-type"]["states"]
    need(all(r["states"] == a_none and r["asserted"] == [f"states={a_none}"] for r in rech), TF,
         "M_RECHECK's rows do not all assert and reach the states of none (a)")
    y += c.para(X0, y, WW, "The diagram's comparison: a mutation's Breaks cell, and its header entry, agree when "
                "the properties named are exactly those with a COUNTEREXAMPLE row under it, in any "
                "configuration (liveness included). "
                + ("**Every row agrees.**" if not disagree else "[[red|Disagreements are marked in red:]] "
                                                     + "; ".join(disagree) + ".") +
                f" `M_UPHOLD` breaks four doctrine properties in a and `WillHonoured` only in c (the cut-pay bill "
                f"needs a court). All {len(rech)} `M_RECHECK` rows assert, and reach, {n(a_none)} distinct "
                f"states, the count of `none` in a (README § Findings, One mutation that changes nothing).",
                13.5, "muted") + 36

    # ---- band: the matrix
    y = band(c, X0, y, "Mutation × property, every `Spec` row read from the results file, one column per "
             "mutation and configuration", "violet")
    GROUPS = [
        ("Type", ["TypeOK"]),
        ("Shape of the graph", ["EdgesConnectLiveNodes", "OfficesAreLive", "TextFollowsArticleV", "ArticleVStands",
                                "ConstitutionWrittenByPeopleAndStates", "OnlyStatutesOverstep"]),
        ("Grant layer", ["GrantFollowsChainExceptXXV", "GrantCyclesPassThroughPeopleStatesOrVP",
                         "NominationLoopIffXXV", "OnlyGrantCycleIsXXV", "NamedPathsFromPeople",
                         "EveryBodyIsCreatedByLaw", "PowerTracesToPeople", "PeoplePowerGoesThroughConstitution",
                         "ConstitutionIsTheOnlyDoor"]),
        ("Control layer", ["MutualChecks", "ControlLayerIsCyclic", "LegislativePrimacy"]),
        ("Doctrine", ["BuckleyHonoured", "SeilaLawHonoured", "BowsherHonoured", "ChadhaHonoured", "WillHonoured",
                      "ExecutorsAreRemovable"]),
        ("Acts", ["ActsFollowEdges", "ActsByHolders", "GoodBehaviour", "PocketVetoHonoured"]),
        ("Action properties (PROPERTY rows)", ["TextChangesOnlyByArticleV", "StatutesChangeOnlyByLawOrCourt"]),
        ("Conjunctions, run under none only", ["Safety", "EveryActIsAnEdge"]),
        ("The refuted claims (r- rows), kept unchanged", refuted),
    ]
    mx = [r for r in R if cat[r["name"]] in ("matrix", "refuted")]
    mprops = [x for _, g in GROUPS for x in g]
    need(sorted(set(r["prop"] for r in mx)) == sorted(mprops), TF,
         f"matrix properties {sorted(set(r['prop'] for r in mx) ^ set(mprops))} not grouped")
    mcol = []
    cell = {}
    for r in mx:
        k = (r["mut"], r["conf"])
        if k not in mcol:
            mcol.append(k)
        need((k, r["prop"]) not in cell, TF, f"two rows for {k} {r['prop']}")
        cell[(k, r["prop"])] = r
    need(len(mcol) <= 20, TF, f"{len(mcol)} matrix columns")
    rb_all = {row[0].strip("`"): set(parse_breaks(row[3])) for row in mu_rows}
    hb_all = {m: set(parse_header(hm[m])) for m in muts}
    pw, sw_ = 360, 190
    cw = (WW - pw - sw_) / len(mcol)
    xcols = [("Property", pw, {"mono": True}), ("Status", sw_)]
    xcols += [(f"{m}\n({cf})", cw) for m, cf in mcol]
    xrows = []
    for gname, g in GROUPS:
        xrows.append({"group": gname, "accent": "red" if gname.startswith("The refuted") else "violet"})
        for prop in g:
            if prop in refuted:
                stt = "[[red|refuted]]"
            elif prop in reach_claims:
                stt = "[[amber|checked, not proved]]"
            elif prop == "Safety":
                stt = "[[amber|checked; its five Reach conjuncts are not proved]]"
            elif prop in thm_of or prop == "EveryActIsAnEdge":
                stt = "[[blue|proved]]" if prop in thm_of else "[[blue|proved as its two conjuncts]]"
            else:
                stt = "—"
            cells = [prop, stt]
            for m, cf in mcol:
                r = cell.get(((m, cf), prop))
                if r is None:
                    cells.append("")
                    continue
                if r["verdict"] == "HOLDS":
                    s = "[[teal|HOLDS]]"
                    if m != "none" and prop in (rb_all[m] | hb_all[m]) and \
                            not any(x == prop for x, _ in ce[m]):
                        s += " [[red|≠ README/header]]"
                else:
                    s = "[[red|COUNTEREXAMPLE]]"
                    if m != "none" and (prop not in rb_all[m] or prop not in hb_all[m]):
                        s += " [[red|≠ " + ("README" if prop not in rb_all[m] else "header") + "]]"
                cells.append(s)
            xrows.append(cells)
    st_row = ["distinct states", "when the row HOLDS"]
    for m, cf in mcol:
        st = sorted({r["states"] for (k, _), r in cell.items() if k == (m, cf) and r["verdict"] == "HOLDS"})
        st_row.append("**" + ", ".join(n(s) for s in st) + "**" if st else "—")
    xrows.append({"cells": st_row, "accent": "grey"})
    y += c.table(X0, y, xcols, xrows, size=12.5, hsize=11.5) + 14
    nmx = sum(1 for r in R if cat[r["name"]] == "matrix")
    y += c.para(X0, y, WW, f"{nmx} rows on `Spec` and {len(refuted)} r- rows, every one as expected. An empty cell "
                "is a property no row runs under that mutation in that configuration. `Safety` is every safety "
                "property at once and `EveryActIsAnEdge` is `ActsFollowEdges /\\ ActsByHolders`; neither has a "
                "theorem of its own: `SafeAlways` proves `LocalSafety`, which is `Safety` without the five global forms "
                "over `Reach`. The status column "
                "is the diagram's reading of the proof results. A COUNTEREXAMPLE row's count is the states "
                "explored until the violation; the bottom row is the full count of a HOLDS row.", 13.5, "muted") \
        + 16
    dl = [r for r in R if cat[r["name"]] == "deadlock"]
    need(all(r["verdict"] == "HOLDS" for r in dl), TF, "a deadlock row did not hold")
    y += c.para(X0, y, WW, "**Deadlock rows** (`-deadlock` on; rows file: \"no reachable state is terminal "
                "(Adjourn and Convene are always possible)\"): " + "; ".join(
                    f"`{r['name']}` [[teal|{r['verdict']}]], {n(r['states'])} distinct states" for r in dl) + ".",
                13.5, "ink") + 36

    # ---- band: witnesses
    y = band(c, X0, y, "Witnesses: each `Never…` property must be violated under `Mut = \"none\"`", "green",
             status="checked", extra="never proved")
    WMAP = [["NeverAgencyCreated", "NeverAgencyAbolished", "NeverCourtEstablished"],
            ["NeverForbiddenEnacted", "NeverStruckBuckley", "NeverStruckSeilaLaw", "NeverStruckBowsher",
             "NeverStruckChadha", "NeverStruckWill"],
            ["NeverXVII", "NeverXXV", "NeverVPByNomination", "NeverInabilityContested"],
            ["NeverCourtAbolishedUnderAJudge", "NeverBillOnDeskInRecess"]]
    wb = blocks[10][1]
    need(len(wb) == len(WMAP) and sorted(x for g in WMAP for x in g) == sorted(r["prop"] for r in wit),
         "README.md", "the witness bullets and the witness rows do not pair as drawn")
    wcols = [("Row (results)", 330, {"mono": True}), ("Property", 380, {"mono": True}), ("Kind", 130),
             ("Configuration", 160), ("Verdict", 200), ("Distinct states", 190)]
    wcols.append(("Definition (Government.tla)", WW - sum(x[1] for x in wcols)))
    wrows = []
    wp = {r["prop"]: r for r in wit}
    for b, g in zip(wb, WMAP):
        wrows.append({"group": "README: " + md(b), "accent": "green"})
        for x in g:
            r = wp[x]
            need(r["verdict"] == "COUNTEREXAMPLE", TF, f"witness {x} not violated")
            body = re.sub(r"\s+", " ", spec["defs"][x][1]).strip()
            wrows.append([r["name"], x, r["kind"], r["conf"], "[[green|COUNTEREXAMPLE]]",
                          n(r["states"]) if r["states"] is not None else "count not recorded", f"`{body}`"])
    y += c.table(X0, y, wcols, wrows, size=13) + 14
    y += c.para(X0, y, WW, "A witness is existential: a run that reaches the state is evidence that it is "
                "reachable at those constants, and no proof is attempted (README § What is not proved). TLC "
                "records no distinct-state count for a violated temporal property. The pairing of rows with the "
                "README's bullets is the diagram's.", 13.5, "muted") + 36

    # ---- band: liveness
    y = band(c, X0, y, f"Liveness: `{live_prop}` under `FairSpec`, and the specs that drop one fairness "
             "condition", "amber", status="notproved")
    lv = [r for r in R if cat[r["name"]] == "liveness"]
    lcols2 = [("Row (results)", 300, {"mono": True}), ("Spec", 170, {"mono": True}), ("Mut", 170, {"mono": True}),
              ("Configuration", 150), ("Property", 360, {"mono": True}), ("Verdict", 200), ("Distinct states", 190)]
    lcols2.append(("What the row shows (the diagram's reading of the rows header)", WW - sum(x[1] for x in lcols2)))
    lrows2 = []
    for r in lv:
        if r["prop"] == "NoBehaviour":
            what = "`NoBehaviour == <>FALSE` is violated by every behaviour: the fair spec has one"
        elif r["verdict"] == "HOLDS":
            what = "[[amber|checked, not proved]]: a forbidden statutory edge does not last"
        elif r["spec"] != "FairSpec":
            what = "without the dropped fairness condition, a forbidden edge can last forever"
        else:
            what = f"under `{r['mut']}` the courts do not strike it, so it lasts"
        v = "[[teal|HOLDS]]" if r["verdict"] == "HOLDS" else "[[red|COUNTEREXAMPLE]]"
        lrows2.append([r["name"], r["spec"], r["mut"], r["conf"], r["prop"], v,
                       n(r["states"]) if r["states"] is not None else "count not recorded", what])
    y += c.table(X0, y, lcols2, lrows2, size=13) + 16
    y += row_cards(c, X0, y, WW, 26, [
        ("README § Government.tla, Liveness", [md(blocks[11][1])] + [md(x) for x in blocks[12][1]] +
         [md(blocks[13][1])], "amber", {}),
        ("The definitions (Government.tla)", [
            "`" + re.sub(r"\s+", " ", spec["defs"][live_prop][1]).strip() + "`",
            "`LitigantsSue == \\A e \\in Challengeable : WF_vars(Sue(e))`; `CourtsDecide`, the same on "
            "`Review(e)`. `FairSpec == Spec /\\ LitigantsSue /\\ CourtsDecide`; `SpecNoSuit` drops the first, "
            "`SpecNoRuling` the second."], "teal", {}),
        ("Why it is not proved", [
            "README § What is not proved: \"Each is a leads-to quantified over bills, agencies or edges, and the "
            "pinned prover has no sound route for a quantified leads-to.\"",
            "`Government_proof.tla` header: \"it is quantified over the challengeable edges with an ENABLED "
            "premise per edge, the shape the prover's temporal backend cannot combine from instances.\""],
         "amber", {"status": "notproved"}),
    ]) + 36

    # ---- band: the proofs
    y = band(c, X0, y, f"The proofs: {len(p['theorems'])} theorems in `Government_proof.tla`, read from the proof "
             "results file", "blue", status="proved", extra=f"{n(obl)} obligations")
    tcols = [("Theorem", 470, {"mono": True}), ("Hypotheses (ASSUME)", 560, {"mono": True}),
             ("Proves", 560, {"mono": True}),
             ("Mutations with a COUNTEREXAMPLE on that property (TLC results; the diagram's join)", 760)]
    tcols.append(("Hypotheses = those mutations? (the diagram's check)", WW - sum(x[1] for x in tcols)))
    trows = []
    bad_thm = []
    for th in p["theorems"]:
        hyp = [re.fullmatch(r'Mut # "(M_\w+)"', a) for a in th["assume"]]
        if th["name"] == "SafeAlways":
            need(th["assume"] == ['Mut = "none"'], PF, "SafeAlways's hypothesis is not Mut = \"none\"")
            trows.append([th["name"], ", ".join(th["assume"]), th["prove"],
                          "`LocalSafety`: every property above at once (proof module), under the text itself",
                          "—"])
            continue
        need(all(hyp), PF, f"{th['name']}: a hypothesis is not Mut # \"M_X\"")
        hs = sorted(h.group(1) for h in hyp)
        br = sorted({m for m in muts for x, _ in ce[m] if x == th["prop"]})
        ok = hs == br
        if not ok:
            bad_thm.append(f"{th['name']}: hypotheses {hs}, TLC breaks {br}")
        trows.append([th["name"], ", ".join(th["assume"]) or "none", th["prove"],
                      codes(br) if br else "none", "[[blue|yes]]" if ok else "[[red|no]]"])
    y += c.table(X0, y, tcols, trows, size=13) + 14
    need(not bad_thm, PF, f"theorem hypotheses differ from the TLC breaks: {bad_thm}")
    y += row_cards(c, X0, y, WW, 26, [
        ("The prover and the obligations", [
            f"**{n(obl)} obligations, all proved** (\"Result: All {obl} obligations proved.\").",
            f"Prover: {p['prover']}.", f"Backends: {p['backends']}.", f"Command: `{p['command']}`.",
            f"Cites the TLC file `{p['tlc_file'][8:]}` by sha256 \"(the mutations' counterexamples and the "
            "witnesses)\"."], "blue", {"status": "proved"}),
        ("What proved means here (the proof results file, Words:)", [p["words"] + ".",
                                                                      "The named assumptions: `PoolsDisjoint`, "
                                                                      "`PoolsAreNew`, `MutIsKnown`, "
                                                                      "`BoundsWellFormed`, "
                                                                      "`AmendmentsRewriteText` (proof module "
                                                                      "header)."], "blue", {}),
        ("No theorem assumes `Mut # \"M_RECHECK\"`", [
            "\"every property holds without the re-check at enactment, which TLC confirms reaches no new state\" "
            "(proof module header). Its lemma `MutRecheckSkipsTheRecheck` says what the mutation admits.",
            "One inductive strengthening, `Shape`, holds under every mutation (proof module header)."], "blue",
         {}),
    ]) + 16
    y += c.para(X0, y, WW, f"**Lemmas ({len(p['lemmas'])})**: " + codes(p["lemmas"]) + ".", 13, "ink") + 36

    # ---- band: the refuted claim
    y = band(c, X0, y, "A claim TLC refuted: the grant layer of 1789 is not acyclic once XXV gives the President "
             "a nomination", "red", status="refuted")
    rr = [r for r in R if cat[r["name"]] == "refuted"]
    code = blocks[19][1]
    lw3 = WW * 0.36
    gap3 = 30
    mw = WW * 0.26
    rw3 = WW - lw3 - mw - 2 * gap3
    hL = c.card(0, 0, lw3, "README § A claim TLC refuted", [md(blocks[18][1])], draw=False, size=S,
                bullets=False)
    hC = c.card(0, 0, lw3, "The trace (README)", [f"`{ln}`" for ln in code], draw=False, size=13.5,
                bullets=False)
    yy = y
    c.card(X0, yy, lw3, "README § A claim TLC refuted", [md(blocks[18][1])], accent="red", size=S,
           bullets=False, h=hL)
    c.card(X0, yy + hL + 16, lw3, "The trace (README)", [f"`{ln}`" for ln in code], accent="red", size=13.5,
           bullets=False, h=hC)
    left_bottom = yy + hL + 16 + hC
    # the loop
    mx0 = X0 + lw3 + gap3
    bw, bh = 230, 74
    ex_x, vp_x = mx0 + 20, mx0 + mw - bw - 20
    by = yy + 70
    c.card(ex_x, by, bw, "`Executive`", ["Rank 4"], accent="teal", h=bh, bullets=False, size=13.5)
    c.card(vp_x, by, bw, "`VicePresident`", ["Rank 3"], accent="teal", h=bh, bullets=False, size=13.5)
    c.arrow([(ex_x + bw / 2, by - 2), (ex_x + bw / 2, by - 40), (vp_x + bw / 2, by - 40), (vp_x + bw / 2, by - 4)],
            "red", label="NominateVP (from XXV, sec. 2)", lpos=0.5)
    c.arrow([(vp_x + bw / 2, by + bh + 2), (vp_x + bw / 2, by + bh + 40), (ex_x + bw / 2, by + bh + 40),
             (ex_x + bw / 2, by + bh + 4)], "blue", label="Succession (Art. II sec. 1 cl. 6)", lpos=0.5)
    ry = by + bh + 80
    for r in rr:
        body = re.sub(r"\s+", " ", spec["defs"][r["prop"]][1]).strip()
        ry += c.card(mx0, ry, mw, f"`{r['prop']}`", [f"`{body}`", f"`{r['name']}`, `Mut = \"none\"`, {r['conf']}: "
                                                    f"[[red|{r['verdict']}]], {n(r['states'])} distinct states, "
                                                    "as expected."],
                     accent="red", status="refuted", size=13.5) + 14
    mid_bottom = ry - 14
    rx0 = mx0 + mw + gap3
    hR = [md(blocks[20][1]), md(blocks[21][1]), hpara(spec, "REFUTED CLAIMS")]
    rh = c.card(rx0, yy, rw3, "What it is, and what was kept", [hR[0], hR[1], "Module header: " + hR[2]],
                accent="red", size=S)
    y = max(left_bottom, mid_bottom, yy + rh) + 16
    y += c.para(X0, y, WW, "What holds instead is drawn above: `GrantFollowsChainExceptXXV` (proved) and "
                "`GrantCyclesPassThroughPeopleStatesOrVP` (checked), which set the Vice Presidency aside too, and "
                "`OnlyGrantCycleIsXXV` (checked): the loop is the only inner grant cycle, present exactly under "
                "XXV.", 13.5, "muted") + 36

    # ---- band: the findings doc
    y = band(c, X0, y, f"A finding about the session (`{FIND}` § 5)", "pink")
    ftxt = C.read(FIND)
    sec = ftxt.split("## 5. Government.tla gates what Constitution.tla does not", 1)
    need(len(sec) == 2, FIND, "no § 5 heading")
    sec = sec[1].split("\n---", 1)[0]
    paras = [re.sub(r"\s+", " ", x).strip() for x in sec.strip().split("\n\n") if x.strip()]
    need(len(paras) == 3 and paras[2].startswith("1. "), FIND, "§ 5 is not two paragraphs and a numbered list")
    items_ = [re.sub(r"^\d\. ", "", x).strip() for x in re.split(r"(?=\b\d\. \*\*)", paras[2]) if x.strip()]
    need(len(items_) == 2, FIND, "§ 5's list is not two items")
    for ln_no, op in ((646, "Pass"), (698, "Override")):
        need(spec["lines"][ln_no - 1].strip() == "/\\ inSession", SPEC,
             f"line {ln_no} is not the `inSession` guard of {op} that {FIND} § 5 cites")
    y += row_cards(c, X0, y, WW, 26, [
        ("What § 5 says", [md(paras[0]), md(paras[1])], "pink", {}),
        ("The two discrepancies (§ 5)", [md(x) for x in items_], "pink", {}),
        ("Checked by the diagram, and its reading", [
            "Checked at build time: `Government.tla` line 646 (in `Pass`) and line 698 (in `Override`) are "
            "`/\\ inSession`, as § 5 says.",
            "The diagram's reading: no mutation in the header's list removes either guard, so no column of the "
            "matrix above tests them."], "pink", {}),
    ]) + 10
    return c
