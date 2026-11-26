"""B1 — Constitution.tla: legislation, the Executive and Article V as three machines.

The module's picture (its three machines, their actions and the check each action carries), the README's
provisions and mutation tables whole, the mutation x property matrix and the witness, liveness and deadlock rows
read from the named TLC results file, and every theorem with its hypotheses read from the named proof results file.

Build-time reads and checks (each raises corpus.CorpusError, so the generator prints ERROR, like a gate):
  - the README section is parsed strictly: its two tables, the Abstracted paragraph, the Safety paragraph, the
    witness list, the Liveness and Rows paragraphs;
  - the module header's MUTATIONS list is parsed for each mutation's "Breaks" clause, and the thirteen properties
    are read from the module's Safety definition;
  - for each mutation, five records are compared: the README's Breaks cell, the module header, the results file's
    Expected: line, the COUNTEREXAMPLE rows, and the theorems that assume the mutation absent. They are drawn side
    by side; a disagreement is drawn red, never reconciled;
  - the rows header's inert-cell sentence is checked verbatim, and each cell it names is compared, by distinct
    states, with the unmutated row of the same property (the diagram's check).
"""
import re

from lib import Canvas, STATUS, text_width
import corpus as C

ID, SLUG = "B1", "constitution"

W = 3400
S = 14

MOD = "Constitution"
TF, PF = C.RESULTS[MOD]
README_HEAD = "### `Constitution.tla` — Articles I, II and V, Amendments XXII and XXV"


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


def md(s):
    """README markdown to the library's rich text: `code` and **bold** kept, *italic* dropped to plain."""
    return re.sub(r"(?<!\*)\*(?!\*)([^*]+?)\*(?!\*)", r"\1", s)


def need(cond, rel, what):
    if not cond:
        raise C.CorpusError(f"{rel}: {what}")


# ---------------------------------------------------------------------------------------------- build-time reads
def readme_section():
    lines = C.read("README.md").splitlines()
    need(README_HEAD in lines, "README.md", "the Constitution.tla section heading is not found")
    i = lines.index(README_HEAD) + 1
    j = i
    while j < len(lines) and not lines[j].startswith("### "):
        j += 1
    sec = lines[i:j]
    out = {}

    def table(head):
        need(head in sec, "README.md", f"table {head[:40]!r} not found in § Constitution.tla")
        k = sec.index(head)
        ncol = head.count("|") - 1
        need(re.fullmatch(r"\|(---\|)+", sec[k + 1]), "README.md", f"table {head[:30]!r} has no rule line")
        rows = []
        k += 2
        while k < len(sec) and sec[k].startswith("|"):
            cells = [x.strip() for x in sec[k].strip().strip("|").split("|")]
            need(len(cells) == ncol, "README.md", f"row of {ncol} cells expected: {sec[k][:60]!r}")
            rows.append(cells)
            k += 1
        need(rows, "README.md", f"table {head[:30]!r} is empty")
        return rows

    def para(start):
        ks = [k for k, ln in enumerate(sec) if ln.startswith(start)]
        need(len(ks) == 1, "README.md", f"one paragraph starting {start!r} expected in § Constitution.tla")
        k = ks[0]
        buf = []
        while k < len(sec) and sec[k].strip():
            buf.append(sec[k].strip())
            k += 1
        return " ".join(buf), k

    def bullets(k):
        items = []
        while k < len(sec) and (sec[k].startswith("- ") or sec[k].startswith("  ")):
            if sec[k].startswith("- "):
                items.append(sec[k][2:].strip())
            else:
                need(items, "README.md", "a continuation line before any bullet")
                items[-1] += " " + sec[k].strip()
            k += 1
        need(items, "README.md", "a bullet list expected")
        return items

    out["intro"], _ = para("The module is three machines")
    out["provisions"] = table("| Provision | Where |")
    out["abstracted"], _ = para("Abstracted:")
    out["mutations"] = table("| Mutation | Removes | Earlier text, doctrine or practice | Breaks |")
    out["safety"], k = para("`Safety` is the conjunction")
    need(out["safety"].endswith("changed meaning:"), "README.md", "the Safety paragraph does not end 'changed meaning:'")
    out["safety_bullets"] = bullets(k + 1)
    _, k = para("Witnesses (each violated):")
    out["witnesses"] = bullets(k + 1)
    out["liveness"], _ = para("**Liveness.**")
    out["rows"], _ = para("**Rows.**")
    return out


def module_reads():
    rel = "specs/Constitution.tla"
    text = C.read(rel)
    m = re.search(r"^Safety ==\n((?:  .*\n)+)", text, re.M)
    need(m, rel, "no Safety definition")
    props = re.findall(r"\b([A-Z]\w+)\b", m.group(1))
    need(len(props) == 13, rel, f"Safety has {len(props)} conjuncts, the README says thirteen")
    # the header's MUTATIONS list: each entry's "Breaks ..." clause
    lines = text.splitlines()
    s = [k for k, ln in enumerate(lines) if ln.startswith("(* MUTATIONS.")]
    e = [k for k, ln in enumerate(lines) if ln.startswith("(* No mutation breaks")]
    need(len(s) == 1 and len(e) == 1 and s[0] < e[0], rel, "header MUTATIONS paragraph not found")
    entries, cur = {}, None
    for ln in lines[s[0] + 2:e[0]]:
        inner = ln[2:-2] if ln.startswith("(*") and ln.endswith("*)") else None
        need(inner is not None, rel, f"header line is not a comment line: {ln[:50]!r}")
        mm = re.match(r"^ {3}(M_[A-Z_]+) +(.*)$", inner)
        if mm:
            cur = mm.group(1)
            need(cur not in entries, rel, f"{cur} twice in the header")
            entries[cur] = mm.group(2).strip()
        else:
            need(cur is not None, rel, "a header line before the first mutation")
            entries[cur] += " " + inner.strip()
    s2 = [k for k, ln in enumerate(lines) if ln.startswith("(* PROPERTIES")]
    need(len(s2) == 1 and s2[0] < s[0], rel, "header PROPERTIES paragraph not found")
    pent, cur = {}, None
    for ln in lines[s2[0] + 2:s[0]]:
        inner = ln[2:-2]
        if not inner.strip():
            continue
        mm = re.match(r"^ {3}([A-Z]\w+) +(.*)$", inner)
        if mm:
            cur = mm.group(1)
            pent[cur] = mm.group(2).strip()
        else:
            need(cur is not None, rel, "a PROPERTIES line before the first property")
            pent[cur] += " " + inner.strip()
    pent = {k: " ".join(v.split()) for k, v in pent.items()}
    need(set(props) <= set(pent), rel, "a Safety conjunct has no entry in the header's PROPERTIES")
    breaks = {}
    for mu, body in entries.items():
        b = re.findall(r"Breaks\s+(.+?)\.", " ".join(body.split()))
        need(len(b) == 1, rel, f"{mu}: one 'Breaks ...' clause expected in the header")
        breaks[mu] = [p for p in props if re.search(rf"\b{p}\b", b[0])]
        need(breaks[mu], rel, f"{mu}: its header Breaks clause names no property")
    return props, breaks, pent


def expected_breaks(t, props):
    """The results file's Expected: line (the rows file's # expected: lines), clause by clause."""
    ex = t["expected"]
    a = "HOLDS on every other: "
    need(a in ex and "TypeOK HOLDS under every mutation" in ex, TF, "Expected: line does not have its usual shape")
    body = ex.split(a, 1)[1].split(" TypeOK HOLDS under every mutation", 1)[0].rstrip(".")
    out = {}
    for clause in body.split(";"):
        ms = re.findall(r"M_[A-Z_]+", clause)
        ps = [p for p in props if re.search(rf"\b{p}\b", clause)]
        need(ms and ps, TF, f"Expected: clause does not parse: {clause.strip()!r}")
        for mu in ms:
            out.setdefault(mu, []).extend(ps)
    return out


INERT_SENTENCE = ("Those cells are M_UNICAMERAL..M_POCKET_SITTING against the Executive, appointment and Article V "
                  "properties; M_INCOMPAT, M_VP_RECHECK, M_CONSENT_RECHECK and M_PRO_FORMA against the legislative "
                  "and Article V properties; M_RATIFY_VOTE and M_SUFFRAGE against all but ArticleV.")
ASSESS_SENTENCE = ("There, 133 of the rows that check a mutation does *not* break a property switch on only the part "
                   "of the model the property reads.")


def rows_header():
    rel = "rows/Constitution-rows.txt"
    hdr = " ".join(ln[1:].strip() for ln in C.read(rel).splitlines() if ln.startswith("#"))
    hdr = " ".join(hdr.split())
    need(INERT_SENTENCE in hdr, rel, "the inert-cell sentence has changed; redraw the inert cells")
    need("Run with both machines on, M_INCOMPAT against Bicameralism alone is 2,756,172 states." in hdr, rel,
         "the all-on M_INCOMPAT sentence has changed")
    a = " ".join(C.read("docs/ASSESSMENT.md").split())
    need(ASSESS_SENTENCE in a, "docs/ASSESSMENT.md", "the 133-rows sentence (§ Strengths, point 1) has changed")
    return hdr


def read_all():
    t, p = C.tlc_results(TF), C.proof_results(PF)
    for rel in (TF, PF):
        need(C.newest("tlc" if rel == TF else "proof", MOD) == rel, rel, "is not the newest committed file")
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
    props, hdr_breaks, pent = module_reads()
    rh = rows_header()
    muts = C.mutations(t)
    wit = C.witnesses(t)
    mx_muts, mx_props, cells = C.matrix(t)
    rows_by = {r["name"]: r for r in t["rows"]}
    need(set(hdr_breaks) == set(muts), "specs/Constitution.tla", "header mutations differ from the results file's")
    sampled = [r for r in t["rows"] if r["kind"] == "SIMULATE"]
    need(not sampled, TF, "a SIMULATE row: draw it as sampled")

    # which machine each property's rows switch on (read from the unmutated row's overrides)
    base = {}
    for r in t["rows"]:
        if r["mut"] == "none" and r["kind"] == "INVARIANT" and r["prop"] in props:
            base[r["prop"]] = r
    need(set(base) == set(props), TF, "an unmutated row is missing for a property")

    def machine(r):
        o = set(r["overrides"])
        if {"Offices={}", "Amendments={}"} <= o and "Bills={}" not in o:
            return "leg"
        if {"Bills={}", "Amendments={}"} <= o and "Offices={}" not in o:
            return "exec"
        if {"Bills={}", "Offices={}"} <= o and "Amendments={}" not in o:
            return "artv"
        if not o:
            return "all"
        return "exec-only"
    mach = {q: machine(base[q]) for q in props}
    leg = [q for q in props if mach[q] == "leg"]
    exe = [q for q in props if mach[q] == "exec"]
    artv = [q for q in props if mach[q] == "artv"]
    need(len(leg) + len(exe) + len(artv) == 13, TF, "a property's row switches on no single machine")

    # five records per mutation
    rd_breaks = {}
    for row in R["mutations"]:
        mu = row[0].strip("`")
        rd_breaks[mu] = [q for q in props if re.search(rf"`{q}`", row[3])]
    need(list(rd_breaks) == muts, "README.md", "the mutation table's mutations are not the results file's, in order")
    ex_breaks = expected_breaks(t, props)
    ce = {mu: [q for q in props if "COUNTEREXAMPLE" in cells.get((mu, q), set())] for mu in muts}
    thm = {}
    for th in p["theorems"]:
        prop = th["prove"].split("[]", 1)[1]
        for a in th["assume"]:
            mm = re.fullmatch(r'Mut # "(M_[A-Z_]+)"', a)
            if mm:
                thm.setdefault(mm.group(1), []).append(th["name"])
    mlem = {}
    for mu in muts:
        key = mu[2:].replace("_", "")
        hits = [lm for lm in p["lemmas"] if lm.startswith("Mut") and lm[3:].upper().startswith(key)]
        need(len(hits) == 1, PF, f"{mu}: one mutation lemma expected, found {hits}")
        mlem[mu] = hits[0]
    agree = {}
    for mu in muts:
        sets = [set(rd_breaks[mu]), set(hdr_breaks[mu]), set(ex_breaks.get(mu, [])), set(ce[mu]),
                {th[:-len("Always")] for th in thm.get(mu, [])}]
        agree[mu] = all(s == sets[0] for s in sets)

    # the rows header's inert cells, and the diagram's state-count check
    i0, i1 = muts.index("M_UNICAMERAL"), muts.index("M_POCKET_SITTING")
    inert = set()
    for mu in muts[i0:i1 + 1]:
        inert |= {(mu, q) for q in exe + artv}
    for mu in ("M_INCOMPAT", "M_VP_RECHECK", "M_CONSENT_RECHECK", "M_PRO_FORMA"):
        inert |= {(mu, q) for q in leg + artv}
    for mu in ("M_RATIFY_VOTE", "M_SUFFRAGE"):
        inert |= {(mu, q) for q in props if q != "ArticleV"}
    mrow = {}
    for r in t["rows"]:
        if r["kind"] == "INVARIANT" and r["mut"] != "none" and r["prop"] in props:
            mrow[(r["mut"], r["prop"])] = r
    inert_eq = {k for k in inert if mrow[k]["states"] == base[k[1]]["states"]
                and mrow[k]["overrides"] == base[k[1]]["overrides"]}
    inert_ne = sorted(inert - inert_eq, key=lambda k: (muts.index(k[0]), props.index(k[1])))
    ne_muts = sorted({k[0] for k in inert_ne}, key=muts.index)
    nonbreak = sum(1 for mu in muts for q in props if "COUNTEREXAMPLE" not in cells.get((mu, q), set()))

    allon = rows_by["t-none-typeok"]["states"]
    st_leg, st_exe, st_artv = (base[leg[0]]["states"], base[exe[0]]["states"], base[artv[0]]["states"])

    c = Canvas(ID, "`Constitution.tla`: legislation, the Executive and Article V as three machines, each rule a "
               "check that TLC shows a property depends on and TLAPS proves",
               f"The module models the procedure of Articles I, II and V and Amendments XXII and XXV as three machines "
               f"over one Executive and one sitting of Congress. Each of its {len(muts)} mutations removes one check, "
               f"and TLC finds a counterexample exactly where the README, the module header and the row list say it "
               f"should; TLAPS proves each of the thirteen safety properties as `Spec => []P` under exactly those "
               f"hypotheses ({n(p['obligations'])} obligations). **The ten-day rule's liveness, "
               f"`PresentedBillsResolve`, is checked, not proved, and the {len(wit)} witnesses are checked, never "
               f"proved.** This models the text's procedure: an exercise, not law (README, opening).",
               W, "README.md (opening; § How the specs are written and checked; § `Constitution.tla`: the opening "
               "sentence, provisions table, Abstracted paragraph, mutation table, the Safety paragraph, Witnesses, "
               "Liveness, Rows; § Findings; § Ideas for next steps); specs/Constitution.tla (header: PROPERTIES, "
               "MUTATIONS, WITNESSES, LIVENESS, DEADLOCK, ABSTRACTED, Sessions, CONSTANTS; the actions, the checks, "
               "Next, Safety, the witnesses, TimeRuns, PresidentActs, FairSpec, SpecPresidentActs); "
               "specs/Constitution.cfg; specs/Constitution_proof.tla (header; the strengthenings; SafeAlways; the "
               "mutation lemmas); rows/Constitution-rows.txt (header); " + TF + "; " + PF + "; docs/ASSESSMENT.md "
               "§ Strengths, points 1 and 3; docs/SESSION-GATE-FINDINGS-2026.11.17.md §§ 1–2")
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    items = [("Constitution.tla", [("checked", f"{t['total']} rows, all as expected"),
                                   ("proved", f"{n(p['obligations'])} obligations")]),
             ("13 safety properties and Safety", [("proved", f"{len(p['theorems'])} theorems")]),
             ("TypeOK", [("checked", "every mutation"), ("proved", "every mutation")]),
             ("PresentedBillsResolve (liveness)", [("notproved", "")]),
             (f"Witnesses ({len(wit)})", [("checked", "existential, never proved")]),
             (f"Inert mutation cells ({len(inert)})", [("proved", "the theorems cover them"),
                                                      (("Not exercised by TLC", "grey", "4 3"), "")]),
             ("Sampled rows", [(("None", "grey", "4 3"), "")]),
             ("README's Abstracted list", [("abstracted", "")])]
    y = status_strip(c, X0, X1, y, items)
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row list. "
                "**Proved** means TLAPS discharged every obligation for every value of the constants the module's "
                "named assumptions admit. A witness is checked, never proved. \"None of these is a claim about law "
                "or practice\" (README § How the specs are written and checked). This is an exercise, not law "
                "(README, opening).", 14.5, "muted") + 34

    # ---- band 1: the picture
    y = band(c, X0, y, "The three machines over one Executive and one sitting of Congress (README § `Constitution.tla`; "
             "`Constitution.tla` `Next`)")
    y += c.para(X0, y, WW, md(R["intro"]) + " Each arrow is an action, numbered within its machine; the key under "
                "each machine gives its guards, the [[violet|mutation]] that removes each check, and the flag a "
                "violating step would raise.", 14.5, "muted") + 20
    y += row_cards(c, X0, y, WW, 30, [
        ("One sitting of Congress: `inSession`, `Convene`, `Adjourn` (Art. I §5, Art. II §2 cl. 3)",
         ["Congress sits and adjourns as one body; `Init` has it sitting. `Adjourn` ends every recess commission "
          "(`Constitution.tla` `Adjourn`).",
          "Read only where the text turns on a sitting: whether a bill can be returned (`Veto`, `BecomeLawUnsigned`, "
          "`PocketVeto`) and whether the Senate is in Recess (`RecessAppoint`). Every other act of Congress may "
          "happen while it is adjourned (header, Sessions)."], "teal", {}),
        ("One Executive: `president`, `vicePresident`, `terms`, `vpNominee`",
         ["Always on: no row empties it. \"Legislation reads only the President's presence and the session, and "
          "Article V reads nothing\" (rows header).",
          "`NoOne` marks a vacancy; `Sign`, `Veto`, `Nominate`, `NominateVP` and `RecessAppoint` need "
          "`president # NoOne`."], "teal", {}),
        ("`Next` and the specs",
         ["`Spec == Init /\\ [][Next]_vars`; `Next` is the disjunction of every action below, with `Convene` and "
          "`Adjourn`.",
          "`FairSpec == Spec /\\ TimeRuns` (weak fairness on `Lapse(b)`); `SpecPresidentActs == Spec /\\ "
          "PresidentActs` (on `Sign(b) \\/ Veto(b)`). The checked safety rows run `Spec`."], "teal", {}),
    ]) + 50

    top = y
    LX, LW = X0, 1250
    EX, EW = X0 + 1290, 1250
    AX, AW = X0 + 2580, WW - 2580
    LS = 13.5

    def hgt(w, title, body, size=LS):
        return c.card(0, 0, w, title, body, draw=False, size=size, bullets=False)

    def box(x, yy, w, h, title, body, acc="teal", **k):
        c.card(x, yy, w, title, body, accent=acc, h=h, size=LS, bullets=False, **k)

    # -- legislation geometry
    lU, lP, lPr, lV = (LX + 30, 160), (LX + 310, 160), (LX + 610, 240), (LX + 980, 240)
    lLaw = (LX + 610, 610)
    leg_cards = {
        "U": ("`\"Unintroduced\"`", ["`Init`: every bill"]),
        "P": ("`\"Pending\"`", ["`origin` set; `passed` grows"]),
        "Pr": ("`\"Presented\"`", ["on the President's desk; the ten days run"]),
        "V": ("`\"Vetoed\"`", ["returned; `overridden` grows, origin first"]),
        "Law": ("`\"Law\"`", ["`how`: `\"Signed\"`, `\"Unsigned\"` or `\"Override\"`"]),
        "Dead": ("`\"Dead\"`", ["`how = \"Pocket\"`, or a veto not overridden"]),
    }
    hM = max(hgt(w, *leg_cards[k]) for k, (_, w) in (("U", lU), ("P", lP), ("Pr", lPr), ("V", lV)))
    hL = hgt(lLaw[1], *leg_cards["Law"])
    hD = hgt(lLaw[1], *leg_cards["Dead"])
    lyT = top + 46
    lyM = lyT + hL + 120
    lyB = lyM + hM + 120

    # -- executive geometry
    eA, eB, eC = (EX + 30, 320), (EX + 500, 270), (EX + 960, 260)
    ex_cards = {
        "El": ("Elections themselves (one `Elect` step)", ["abstracted: \"the whole electoral process in one step\""]),
        "Pres": ("`president`", ["`terms[p]` counts elections"]),
        "VP": ("`vicePresident`", ["Amend. XII, XXV"]),
        "vpN": ("`vpNominee`", ["a XXV §2 nominee, pending"]),
        "nom": ("`nominee[o]`", ["pending; `Offices` switched on"]),
        "off": ("`officer[o]`, `recess[o]`", ["`recess[o]`: a recess appointee"]),
        "imp": ("`impeached`", ["awaiting trial in the Senate"]),
        "dq": ("`disqualified`", ["convicted and barred: never `Qualified`"]),
    }
    eh0 = c.card(0, 0, eC[0] + eC[1] - eB[0], *ex_cards["El"], draw=False, size=LS, bullets=False,
                 status="abstracted")
    eh1 = max(hgt(eB[1], *ex_cards["Pres"]), hgt(eC[1], *ex_cards["VP"]))
    eh2 = max(hgt(eA[1], *ex_cards["nom"]), hgt(eC[1], *ex_cards["vpN"]))
    eh3 = hgt(eA[1], *ex_cards["off"])
    eh4 = max(hgt(eB[1], *ex_cards["imp"]), hgt(eC[1], *ex_cards["dq"]))
    ey0 = top + 46
    ey1 = ey0 + eh0 + 80
    ey2 = ey1 + eh1 + 110
    ey3 = ey2 + eh2 + 80
    ey4 = ey3 + eh3 + 100

    # -- Article V geometry
    aw = 230
    ax = AX + (AW - aw) / 2
    av_cards = {
        "None": ("`\"None\"`", ["`Init`: every amendment"]),
        "Prop": ("`\"Proposed\"`", ["`route`: `\"Congress\"` or `\"Convention\"`"]),
        "Rat": ("`\"Ratified\"`", ["`ratifications` = the count `n`"]),
    }
    ah = max(hgt(aw, *v) for v in av_cards.values())
    ay0 = top + 46
    ay1 = ay0 + ah + 150
    ay2 = ay1 + ah + 110
    st_card = ("The States: `States`, counted", ["Apply (2) and ratify (3) as a count, `n \\in StateVotes`; which "
                                                "States is abstracted to how many (header, ABSTRACTED)."])
    sh = c.card(0, 0, AW - 40, st_card[0], st_card[1], draw=False, size=LS, bullets=False)

    # -- keys (numbered actions), measured first so all three regions share one height
    V = "violet"
    leg_key = [
        "**1** `Introduce(b, c)`: `MayOriginate`, revenue bills start in the House, [[violet|M_ORIGIN]] "
        "(Art. I §7 cl. 1).",
        "**2** `PassChamber(b, c, ayes)` ×2: a majority of House `c`, the House of origin first; presented only "
        "when `BothHouses` have passed it, [[violet|M_UNICAMERAL]] (cl. 2).",
        "**3** `Sign(b)`: a President sits.",
        "**4** `BecomeLawUnsigned(b)`: the ten days run out (`Lapse`) while Congress sits, "
        "[[violet|M_NO_POCKET]]; flag `tenDayBreach`.",
        "**5** `Veto(b)`: a President sits and Congress can receive the return (`inSession`).",
        "**6** `PocketVeto(b)`: the ten days run out while Congress is adjourned (`Lapse`), "
        "[[violet|M_POCKET_SITTING]]; flag `tenDayBreach`.",
        "**7** `Override(b, c, ayes)` ×2: origin first; `OverrideCarries`, two-thirds of House `c`, "
        "[[violet|M_OVR_VOTE]] (flag `shortOverride`); law when `OverrideComplete`, both Houses, "
        "[[violet|M_OVR_ONE_HOUSE]].",
        "**8** `FailOverride(b)`: a veto not overridden dies.",
        "Properties its rows read: " + ", ".join(f"`{q}`" for q in leg) + ".",
    ]
    exe_key = [
        "**1** `Elect(p, v)`: `p, v \\in Eligible`; `Qualified` [[violet|M_DQ]], `Compatible` "
        "[[violet|M_INCOMPAT]], `TwoPersons` [[violet|M_ONE_PERSON]], `TermAllowed` [[violet|M_XXII]] "
        "(Art. II §1, Amend. XII, XXII).",
        "**2** `PresidentVacates`: death or resignation; the Vice President becomes President (XXV §1). "
        "`VicePresidentVacates` empties the second seat.",
        "**3** `NominateVP(p)`: the Vice Presidency vacant, a President sitting; `Qualified`, `Compatible`, "
        "`TwoPersons(p, president)` (XXV §2).",
        "**4** `ConfirmVP(hAyes, sAyes)`: re-checks disqualification, [[violet|M_VP_RECHECK]]; `HouseConfirms`, "
        "a House majority, [[violet|M_XXV_SENATE]] (flag `vpWithoutHouse`); a Senate majority. `RejectVP` "
        "clears the nominee.",
        "**5** `Nominate(o, p)`: the office vacant or held by a recess appointee; `Qualified`, `Compatible` "
        "(Art. II §2 cl. 2).",
        "**6** `Consent(o, ayes)`: re-checks disqualification, [[violet|M_CONSENT_RECHECK]]; a Senate majority. "
        "`Reject(o)` clears; `OfficerResigns(o)` vacates.",
        "**7** `RecessAppoint(o, p)`: `SenateInRecess`, [[violet|M_PRO_FORMA]] (flag `recessWhileSitting`); "
        "the commission ends at the next `Adjourn` (cl. 3).",
        "**8** `Impeach(p, ayes)`: `Impeachable`, officeholders only, [[violet|M_BLOUNT]]; a House majority "
        "(Art. I §2 cl. 5).",
        "**9** `Convict(p, ayes, dq)`: `ConvictionCarries`, two-thirds of the Senate, [[violet|M_CONVICT_VOTE]] "
        "(flag `shortConviction`); disqualified if `dq`. `Acquit(p)` clears (Art. I §3 cl. 6–7).",
        "**10** removal: `RemovedBy` removes the convicted from every office, the Vice President succeeding a "
        "removed President, [[violet|M_NO_REMOVAL]] (Art. II §4).",
        "Properties its rows read: " + ", ".join(f"`{q}`" for q in exe) + ".",
    ]
    av_key = [
        "**1** `ProposeByCongress(a, hAyes, sAyes)`: two-thirds of both Houses.",
        "**2** `ProposeByConvention(a, n)`: on the application of two-thirds of the States.",
        "**3** `Ratify(a, n)`: `Ratifies`, three-fourths of the States, [[violet|M_RATIFY_VOTE]], and every State "
        "for an amendment in `SuffrageAmendments`, [[violet|M_SUFFRAGE]].",
        "No mutation removes a proposal threshold (`Mutations`).",
        "Properties its rows read: " + ", ".join(f"`{q}`" for q in artv) + ".",
    ]
    kt = "Key: the actions and the checks they carry"
    lk_y = lyB + hD + 40
    ek_y = ey4 + eh4 + 40
    ak_y = ay2 + ah + 30 + sh + 30
    lk_h = c.card(0, 0, LW - 40, kt, leg_key, draw=False, size=LS, bullets=False)
    ek_h = c.card(0, 0, EW - 40, kt, exe_key, draw=False, size=LS, bullets=False)
    ak_h = c.card(0, 0, AW - 40, kt, av_key, draw=False, size=LS, bullets=False)
    bottom = max(lk_y + lk_h, ek_y + ek_h, ak_y + ak_h) + 24
    RH = bottom - top

    c.region(LX, top, LW, RH, "Legislation, Art. I §7 · `bill`, switched on by `Bills`", "teal")
    c.region(EX, top, EW, RH, "The Executive, appointments and impeachment, Art. I–II · `Offices` switches on "
             "appointments", "teal")
    c.region(AX, top, AW, RH, "Article V · `amend`, switched on by `Amendments`", "teal")

    # legislation cards and arrows
    box(lU[0], lyM, lU[1], hM, *leg_cards["U"])
    box(lP[0], lyM, lP[1], hM, *leg_cards["P"])
    box(lPr[0], lyM, lPr[1], hM, *leg_cards["Pr"])
    box(lV[0], lyM, lV[1], hM, *leg_cards["V"])
    box(lLaw[0], lyT, lLaw[1], hL, *leg_cards["Law"], acc="green")
    box(lLaw[0], lyB, lLaw[1], hD, *leg_cards["Dead"], acc="grey")
    mid = lyM + hM / 2
    c.arrow([(lU[0] + lU[1] + 6, mid), (lP[0] - 6, mid)], "teal", label="1 · `Introduce`", lsize=12)
    c.arrow([(lP[0] + lP[1] + 6, mid), (lPr[0] - 6, mid)], "teal", label="2 · `PassChamber`", lsize=12,
            loff=(0, -26))
    c.arrow([(lPr[0] + 40, lyM - 6), (lPr[0] + 40, lyT + hL + 6)], "teal", label="3 · `Sign`", lsize=12)
    c.arrow([(lPr[0] + 195, lyM - 6), (lPr[0] + 195, lyT + hL + 6)], "teal", label="4 · `BecomeLawUnsigned`",
            lsize=12)
    c.arrow([(lPr[0] + lPr[1] + 6, mid), (lV[0] - 6, mid)], "teal", label="5 · `Veto`", lsize=12)
    c.arrow([(lPr[0] + 120, lyM + hM + 6), (lPr[0] + 120, lyB - 6)], "teal", label="6 · `PocketVeto`", lsize=12)
    c.arrow([(lV[0] + 120, lyM - 6), (lV[0] + 120, lyT + hL + 6)], "teal", label="7 · `Override` ×2", lsize=12)
    c.arrow([(lV[0] + 120, lyM + hM + 6), (lV[0] + 120, lyB - 6)], "teal", dash="7 5", label="8 · `FailOverride`",
            lsize=12)
    c.card(LX + 20, lk_y, LW - 40, kt, leg_key, accent="teal", size=LS, bullets=False, tint=False)

    # executive cards and arrows
    box(eB[0], ey0, eC[0] + eC[1] - eB[0], eh0, *ex_cards["El"], acc="grey", status="abstracted")
    box(eB[0], ey1, eB[1], eh1, *ex_cards["Pres"])
    box(eC[0], ey1, eC[1], eh1, *ex_cards["VP"])
    box(eC[0], ey2, eC[1], eh2, *ex_cards["vpN"])
    box(eA[0], ey2, eA[1], eh2, *ex_cards["nom"])
    box(eA[0], ey3, eA[1], eh3, *ex_cards["off"])
    box(eB[0], ey4, eB[1], eh4, *ex_cards["imp"], acc="red")
    box(eC[0], ey4, eC[1], eh4, *ex_cards["dq"], acc="red")
    pB = eB[0] + eB[1] / 2
    pC = eC[0] + eC[1] / 2
    pA = eA[0] + eA[1] / 2
    c.arrow([(pB, ey0 + eh0 + 6), (pB, ey1 - 6)], "teal", label="1 · `Elect`", lsize=12)
    c.arrow([(pC, ey0 + eh0 + 6), (pC, ey1 - 6)], "teal", label="1 · `Elect`", lsize=12)
    m1 = ey1 + eh1 / 2
    c.arrow([(eC[0] - 6, m1), (eB[0] + eB[1] + 6, m1)], "teal", label="2 · `PresidentVacates`", lsize=12)
    m2 = ey2 + eh2 / 2
    x3 = eB[0] + 175
    v3 = m2 - (ey1 + eh1 + 6)
    h3 = eC[0] - 6 - x3
    c.arrow([(x3, ey1 + eh1 + 6), (x3, m2), (eC[0] - 6, m2)], "teal", label="3 · `NominateVP`", lsize=12,
            lpos=(v3 + h3 / 2) / (v3 + h3))
    c.arrow([(pC + 40, ey2 - 6), (pC + 40, ey1 + eh1 + 6)], "teal", label="4 · `ConfirmVP`", lsize=12)
    h5 = eB[0] - 6 - pA
    v5 = ey2 - 6 - m1
    c.arrow([(eB[0] - 6, m1), (pA, m1), (pA, ey2 - 6)], "teal", label="5 · `Nominate`", lsize=12,
            lpos=(h5 / 2) / (h5 + v5))
    c.arrow([(pA, ey2 + eh2 + 6), (pA, ey3 - 6)], "teal", label="6 · `Consent`", lsize=12)
    x7 = eB[0] + 45
    m3 = ey3 + eh3 / 2
    v7 = m3 - (ey1 + eh1 + 6)
    h7 = x7 - (eA[0] + eA[1] + 6)
    c.arrow([(x7, ey1 + eh1 + 6), (x7, m3), (eA[0] + eA[1] + 6, m3)], "teal", label="7 · `RecessAppoint`",
            lsize=12, lpos=(v7 + h7 / 2) / (v7 + h7))
    m4 = ey4 + eh4 / 2
    v8 = m4 - (ey3 + eh3 + 6)
    h8 = eB[0] - 6 - pA
    c.arrow([(pA, ey3 + eh3 + 6), (pA, m4), (eB[0] - 6, m4)], "red", label="8 · `Impeach` an officeholder",
            lsize=12, lpos=(v8 + h8 / 2) / (v8 + h8))
    c.arrow([(eB[0] + eB[1] + 6, m4), (eC[0] - 6, m4)], "red", label="9 · `Convict`", lsize=12)
    xr = eB[0] + 110
    vr = (ey4 - 6) - (ey1 + eh1 + 6)
    c.arrow([(xr, ey4 - 6), (xr, ey1 + eh1 + 6)], "red", dash="7 5", label="10 · removal from every office",
            lsize=12, lpos=(ey4 - 6 - (m3 + ey4) / 2 - 8) / vr)
    c.card(EX + 20, ek_y, EW - 40, kt, exe_key, accent="teal", size=LS, bullets=False, tint=False)

    # Article V cards and arrows
    box(ax, ay0, aw, ah, *av_cards["None"])
    box(ax, ay1, aw, ah, *av_cards["Prop"])
    box(ax, ay2, aw, ah, *av_cards["Rat"], acc="green")
    a0m, a1m = ay0 + ah / 2, ay1 + ah / 2
    xl, xr2 = AX + 105, AX + AW - 105
    c.arrow([(ax - 6, a0m), (xl, a0m), (xl, a1m), (ax - 6, a1m)], "teal", label="1 · `ProposeByCongress`",
            lsize=12, lw=150)
    c.arrow([(ax + aw + 6, a0m), (xr2, a0m), (xr2, a1m), (ax + aw + 6, a1m)], "teal",
            label="2 · `ProposeByConvention`", lsize=12, lw=150)
    c.arrow([(ax + aw / 2, ay1 + ah + 6), (ax + aw / 2, ay2 - 6)], "teal", label="3 · `Ratify`", lsize=12)
    c.card(AX + 20, ay2 + ah + 30, AW - 40, st_card[0], st_card[1], accent="brown", size=LS, bullets=False)
    c.card(AX + 20, ak_y, AW - 40, kt, av_key, accent="teal", size=LS, bullets=False, tint=False)
    y = bottom + 50

    strength = {
        "Incompatibility": "`IncompatPW`: the property pointwise, and no pending nominee (VP or officer) is a "
                           "member of Congress",
        "CongressNotImpeachable": "rests on `IncompatPW`: `Impeach` reaches only officeholders, who are not "
                                  "members; hence `M_INCOMPAT` among its hypotheses",
        "Disqualification": "`DisqPW`: the property pointwise; `Convict` removes the person it disqualifies from "
                            "every office",
        "PresidentNotVP": "`PresidentNotVPInv`: while a XXV §2 nomination is pending the Vice Presidency is "
                          "vacant and the nominee is not the President",
    }
    flags = {"TenDayRule", "ConvictionTwoThirds", "XXVBothHouses", "RecessAppointmentsInRecess"}
    kind_of = lambda q: strength.get(q, "a flag, false initially and raised only by one action, whose guard "
                                     "makes the raised value false" if q in flags else
                                     "inductive as stated, with `TypeOK`")
    mname = {"leg": "legislation (`Offices={}`, `Amendments={}`)", "exec": "the Executive with appointments "
             "(`Bills={}`, `Amendments={}`)", "artv": "Article V (`Bills={}`, `Offices={}`)"}
    y = band(c, X0, y, "The thirteen properties of `Safety`, as the module header states them (`Constitution.tla`, "
             "PROPERTIES)")
    pc = [("Property", 330, {"mono": True, "bold": True}), ("The header's entry, whole (read)", 1500),
          ("Inductive form (`Constitution_proof.tla` header)", 700), ("Machine its rows switch on (read)", 480)]
    pc.append(("Unmutated row (read)", WW - sum(x[1] for x in pc)))
    prows_ = []
    for q in props:
        r = base[q]
        kq = kind_of(q)
        if q == "TenDayRule":
            kq += (" [[red|(the proof header's words; `tenDayBreach` is written by two actions, "
                   "`BecomeLawUnsigned` and `PocketVeto`)]]")
        prows_.append([q, pent[q], kq, mname[mach[q]],
                       f"`{r['name']}`: [[teal|{r['verdict']}]], {n(r['states'])} states"])
    y += c.table(X0, y, pc, prows_, size=13.5) + 20
    y += c.para(X0, y, WW, "`Safety` is \"the conjunction of the thirteen\". The header also lists "
                "`PresentedBillsResolve`, the liveness property: \"" + pent["PresentedBillsResolve"].split(") ", 1)[1]
                + "\"", 13.5, "muted") + 50

    # ---- band 2: rows and machines
    y = band(c, X0, y, "Each row switches on only the machine its property reads (README § `Constitution.tla`, "
             "Rows; rows header)", status="checked")
    y += row_cards(c, X0, y, WW, 26, [
        ("The switch (rows header)", [
            "Each row \"switches on the machine its property reads and sets the other two empty (`Bills={}`, "
            "`Offices={}`, `Amendments={}`)\".",
            f"Read from the unmutated rows: all three on, [[teal|{n(allon)}]] states (`t-none-typeok`); "
            f"legislation [[teal|{n(st_leg)}]]; the Executive with appointments [[teal|{n(st_exe)}]]; Article V "
            f"[[teal|{n(st_artv)}]]. `TypeOK`, `Safety` and the deadlock audit run with all three on."],
         "teal", {}),
        (f"The inert cells: {len(inert)}, by the rows header's list (the diagram's count)", [
            "\"A mutation whose check lies in a machine switched off is inert in that row, which then records only "
            "that the property holds with Mut set to it.\"",
            "The list: `M_UNICAMERAL`..`M_POCKET_SITTING` against the Executive, appointment and Article V "
            "properties; `M_INCOMPAT`, `M_VP_RECHECK`, `M_CONSENT_RECHECK`, `M_PRO_FORMA` against the legislative "
            "and Article V ones; `M_RATIFY_VOTE`, `M_SUFFRAGE` against all but `ArticleV`.",
            "\"The theorems in Constitution_proof.tla, whose hypotheses omit these mutations, cover every such cell "
            "at every constant.\""], "grey", {"status": "proved", "status_extra": "covers them"}),
        ("The diagram's check: distinct states", [
            f"An inert mutation leaves a row with exactly the unmutated row's distinct states at the same "
            f"constants. [[teal|{len(inert_eq)}]] of the {len(inert)} listed cells match, as inertness requires.",
            (f"[[red|{len(inert_ne)} do not]]: " + ", ".join(f"`{m}`" for m in ne_muts) + " reaches "
             + "; ".join(f"{n(mrow[k]['states'])} states, not {n(base[k[1]]['states'])}, against `{k[1]}`"
                         for k in inert_ne) + ". Its check is a weakened guard of `ConfirmVP` (`Mut = "
             "\"M_VP_RECHECK\" \\/ vpNominee \\notin disqualified`), in the Executive, which no row switches "
             "off, so the extra states are ones the text does not reach. The rows header lists it as inert; the "
             "results show it acts. Every verdict is still HOLDS, as expected.") if inert_ne else
            "Every listed cell does."], "red" if inert_ne else "teal", {}),
        ("Two counts of the inert rows, side by side", [
            "docs/ASSESSMENT.md § Strengths, point 1: \"133 of the rows that check a mutation does not break a "
            "property switch on only the part of the model the property reads.\" The assessment is as of commit "
            "`e86e3c9` (its opening).",
            f"The rows header's list gives [[red|{len(inert)}]] (the diagram's count), of the {nonbreak} "
            f"mutation-against-property rows that do not break."], "red", {}),
        ("With every machine on", [
            "README § Rows: \"With all three machines on, `M_INCOMPAT` against `Bicameralism` alone is 2.8 million "
            "states.\"",
            "Rows header: \"(Run with both machines on, M_INCOMPAT against Bicameralism alone is 2,756,172 "
            "states.)\"",
            "README § Ideas for next steps: such rows \"so that every mutation-against-property cell is checked "
            "as well as proved. This needs a bigger machine.\""], "amber", {}),
    ]) + 26
    y += row_cards(c, X0, y, WW, 26, [
        ("Constants and why (rows header)", [
            "One member per House: \"enough for every vote check, since each mutation removes its threshold and a "
            "vote of none then carries\".",
            "Two persons eligible to be President, \"so two can alternate and three terms are reachable under "
            "M_XXII\"; four States, \"the fewest at which three-fourths is not every State\".",
            "`a1` touches equal suffrage, so `m-ratifyvote-artv` and `w-none-ratfewer` set `SuffrageAmendments={}`."],
         "teal", {}),
        ("`Constitution.cfg`", [
            "`SPECIFICATION FairSpec`; `INVARIANTS TypeOK Safety`; `PROPERTIES PresentedBillsResolve`; "
            "`CONSTRAINT ElectionsBound`.",
            "\"For ad hoc runs\" and the visual tools: \"The checked results come from "
            "rows/Constitution-rows.txt via scripts/tlc_rows.py, which writes its own configs\"; the constants "
            "are the row list's defaults."], "grey", {}),
        ("`ElectionsBound` (header, CONSTANTS)", [
            "`terms[p] <= 3`: \"a state constraint for TLC only: it binds only under M_XXII, whose state space is "
            "otherwise infinite; no property or proof uses it.\""], "grey", {}),
        ("Thresholds at one member (ASSESSMENT.md § Strengths, point 3)", [
            "At `House = {h1}`, `Senate = {s1}` \"two-thirds and a majority are the same vote\". The threshold "
            "mutations still show, \"because they drop the threshold altogether and a vote of none then carries\".",
            "\"But only the TLAPS theorems hold for every size the named ASSUMEs allow, which is what the "
            "threshold properties need.\""], "blue", {"status": "proved"}),
    ]) + 50

    # ---- band 3: the provisions table, whole
    y = band(c, X0, y, "The README's provisions table, every row and column (README § `Constitution.tla`)")
    y += c.table(X0, y, [("Provision", 1250, {"bold": True}), ("Where", WW - 1250)],
                 [[md(a), md(b)] for a, b in R["provisions"]], size=13.5) + 26
    absx = R["abstracted"]
    need(absx.startswith("Abstracted: "), "README.md", "the Abstracted paragraph")
    y += row_cards(c, X0, y, WW, 26, [
        ("Abstracted (README § `Constitution.tla`, the paragraph whole)", [md(absx[len("Abstracted: "):])], "grey",
         {"status": "abstracted", "bullets": False}),
        ("Abstracted as well, in the module header (ABSTRACTED) but not in the README's paragraph", [
            "the \"more than two years of another's term\" nuance of XXII;",
            "presidential succession beyond the Vice President;",
            "votes are counts of ayes, of members or of States; which States ratify or apply is abstracted to how "
            "many; ratification and a convention's call are each one step at the moment the count suffices;",
            "a bill that never passes the other House stays pending (no step kills it); one House adjourning "
            "without the other (Art. I §5 cl. 4) is not expressed."], "grey", {"status": "abstracted"}),
    ]) + 50

    # ---- band 4: the mutation table, whole, with the four other records beside it
    y = band(c, X0, y, "The README's mutation table, every row and column, beside the four other records that name "
             "what each mutation breaks")
    cols = [("Mutation", 230, {"mono": True, "bold": True}), ("Removes", 400),
            ("Earlier text, doctrine or practice", 520), ("Breaks (README)", 330),
            ("Breaks (module header)", 330), ("Expected: line (rows header, results file)", 330),
            ("COUNTEREXAMPLE rows (results, read)", 330), ("Theorems assuming it absent (proof results)", 400)]
    cols.append(("Mutation lemma (proof results)", WW - sum(x[1] for x in cols)))
    trows = []
    for row in R["mutations"]:
        mu = row[0].strip("`")
        cell = lambda xs: ", ".join(f"`{q}`" for q in xs) if xs else "[[red|none]]"
        cells_ = [mu, md(row[1]), md(row[2]), md(row[3]), cell(hdr_breaks[mu]), cell(ex_breaks.get(mu, [])),
                  "[[red|" + ", ".join(ce[mu]) + "]]" if ce[mu] else "[[red|none]]",
                  ", ".join(f"`{x}`" for x in thm.get(mu, [])) or "[[red|none]]", f"`{mlem[mu]}`"]
        trows.append({"cells": cells_, "accent": "red"} if not agree[mu] else cells_)
    y += c.table(X0, y, cols, trows, size=13.5) + 20
    nd = [mu for mu in muts if not agree[mu]]
    y += c.para(X0, y, WW, (f"**All five records agree for every one of the {len(muts)} mutations** (read when this "
                            "diagram is built; a disagreement would be drawn as a red row and reported, not "
                            "reconciled). " if not nd else
                            f"[[red|{len(nd)} mutations disagree between records]]: " + ", ".join(nd) + ". ")
                + "The theorem column is each `…Always` theorem whose `ASSUME` names `Mut # \"M_X\"`; the proof "
                "module's header says its hypotheses are \"exactly the mutations whose rows against P read "
                "COUNTEREXAMPLE\". A mutation lemma states what the mutation admits; the counterexamples are TLC's "
                "(`Constitution_proof.tla`, MUTATION LEMMAS).", 13.5, "muted") + 20
    sb = R["safety_bullets"]
    y += row_cards(c, X0, y, WW, 26, [
        ("`Safety` (README § `Constitution.tla`)", [md(R["safety"])], "blue", {"bullets": False}),
        ("Three existing properties changed meaning (README)", [md(x) for x in sb], "blue", {}),
        ("What `Mut` is (README § How the specs are written and checked)", [
            "\"`Mut = \"none\"` is the text. Each other value removes exactly one check, and the module header names "
            "the property that removal must break.\"",
            "\"TLC must find a counterexample for every mutation against every property it breaks, and none "
            "against any other.\""], "violet", {}),
    ]) + 50

    # ---- band 5: the matrix
    y = band(c, X0, y, f"Every mutation against every property: the {sum(len(v) for v in cells.values())} "
             f"`Spec` INVARIANT rows of {TF[8:]}, read when this diagram is built", status="checked")
    mcols = [("Mut", 200, {"mono": True, "bold": True})]
    hs = 12.5
    mins = [max(text_width(q, hs, True) + 22, 120) for q in mx_props]
    extra = (WW - 200 - sum(mins)) / len(mins)
    need(extra >= 0, TF, "the matrix does not fit the width")
    for q, w in zip(mx_props, mins):
        mcols.append((q, w + extra))
    # the last column absorbs rounding
    mcols[-1] = (mcols[-1][0], WW - sum(x[1] for x in mcols[:-1]))
    mrows = []
    for mu in mx_muts:
        rowc = [mu if mu != "none" else "none (the text)"]
        for q in mx_props:
            vs = cells.get((mu, q))
            if not vs:
                rowc.append("")
                continue
            rr = [r for r in t["rows"] if r["mut"] == mu and r["prop"] == q and r["kind"] == "INVARIANT"
                  and r["spec"] == "Spec"]
            sts = "; ".join(n(r["states"]) for r in rr)
            if "COUNTEREXAMPLE" in vs:
                s = f"[[red|COUNTEREXAMPLE]]\n{sts} states"
                if not (q in rd_breaks.get(mu, []) and q in hdr_breaks.get(mu, [])):
                    s += "\n[[red|not in README / header Breaks]]"
            else:
                s = "[[teal|HOLDS]]\n" + sts
                if mu != "none" and q in rd_breaks.get(mu, []):
                    s += "\n[[red|README says it breaks]]"
                if (mu, q) in inert_eq:
                    s = "[[grey|HOLDS · inert]]\n" + sts + " = none's"
                elif (mu, q) in inert:
                    s = "[[teal|HOLDS]] · [[red|listed inert]]\n" + sts + " ≠ " + n(base[q]["states"])
            rowc.append(s)
        mrows.append({"cells": rowc, "accent": "blue"} if mu == "none" else rowc)
    y += c.legend(X0, y, [("box", "red", "COUNTEREXAMPLE: the mutation breaks the property, as expected"),
                          ("box", "teal", "HOLDS at these constants, with distinct states"),
                          ("box", "grey", "HOLDS · inert: a cell the rows header lists, at the unmutated row's states",
                           "2 3"),
                          ("box", "red", "listed inert by the rows header, but the states differ (the diagram's "
                           "check)", "6 4")],
                  title="Cells", size=13) + 16
    y += c.table(X0, y, mcols, mrows, size=12.5, hsize=hs) + 20
    y += c.para(X0, y, WW, "An empty cell is a pair no row runs: `Safety` runs unmutated only. `TypeOK` runs under "
                "each mutation with the machine that mutation changes (rows header). "
                + ("Every COUNTEREXAMPLE cell is one the README's Breaks column and the module header both name, "
                   "and no HOLDS cell is one they name (read). " if all(agree.values()) else
                   "[[red|Some cells disagree with the README or the header; they are marked.]] ")
                + "At one member per House the vote checks are checked only at that size; the theorems cover "
                "every size.", 13.5, "muted") + 50

    # ---- band 6: witnesses
    y = band(c, X0, y, f"Witnesses: the {len(wit)} `Never…` rows, each violated unmutated (README § "
             "`Constitution.tla`, Witnesses)", status="checked", extra="existential, never proved")
    groups = [
        ["NeverLawBySignature", "NeverLawByLapse", "NeverLawByOverride", "NeverPocketVeto"],
        ["NeverDisqualified"],
        ["NeverVPNomineeDisqualified", "NeverNomineeDisqualified"],
        ["NeverRecessAppointment", "NeverReelected"],
        ["NeverSuccession", "NeverXXVConfirmation"],
        ["NeverRatifiedFromCongress", "NeverRatifiedFromConvention", "NeverRatifiedByFewerThanAll"],
    ]
    need(len(R["witnesses"]) == len(groups), "README.md", f"{len(R['witnesses'])} witness bullets, the diagram "
         f"joins {len(groups)}")
    wprops = [r["prop"] for r in wit]
    need(sorted(wprops) == sorted(q for g in groups for q in g), TF, "the witness rows are not the ones joined")
    wcols = [("README's witness bullet (the diagram's join of bullet to row)", 760),
             ("Witness property", 380, {"mono": True}), ("Row", 300, {"mono": True}), ("Kind", 160),
             ("Constants set empty (the machine switched off)", 820), ("Verdict", 240), ("Distinct states", 220)]
    wcols.append(("Status", WW - sum(x[1] for x in wcols)))
    wrows = []
    for b, g in zip(R["witnesses"], groups):
        for k, q in enumerate(g):
            r = [x for x in wit if x["prop"] == q][0]
            wrows.append([md(b) if k == 0 else "", q, r["name"], r["kind"],
                          ", ".join(f"`{o}`" for o in r["overrides"]) or "none",
                          "[[green|COUNTEREXAMPLE]]" if r["verdict"] == "COUNTEREXAMPLE" else f"[[red|{r['verdict']}]]",
                          n(r["states"]) if r["states"] is not None else "count not recorded",
                          "checked, as expected" if r["ok"] else "[[red|not as expected]]"])
    y += c.table(X0, y, wcols, wrows, size=13.5) + 20
    y += c.para(X0, y, WW, "A witness's COUNTEREXAMPLE is the expected result: it shows TLC reaches the state the "
                "property forbids, so a property that holds is not holding only because that state is unreachable "
                "(README § How the specs are written and checked, Witnesses). `NeverSuccession` and "
                "`NeverXXVConfirmation` are action properties, run as PROPERTY rows (`Constitution.tla`). TLC does "
                "not record a distinct-state count for PROPERTY rows here.", 13.5, "muted") + 50

    # ---- band 7: liveness and deadlock rows
    y = band(c, X0, y, "Liveness and deadlock: the PROPERTY and DEADLOCK rows (README § `Constitution.tla`, "
             "Liveness; header, LIVENESS, DEADLOCK)", status="notproved", extra="PresentedBillsResolve")
    lrows_ = [r for r in t["rows"] if (r["kind"] == "PROPERTY" and r not in wit) or r["kind"] == "DEADLOCK"]
    say = {
        ("FairSpec", "PresentedBillsResolve"): "holds under `FairSpec`: the ten days run out (`TimeRuns`)",
        ("Spec", "PresentedBillsResolve"): "fails with `TimeRuns` dropped",
        ("SpecPresidentActs", "PresentedBillsResolve"): "fails with fairness on the President instead, \"because "
                                                        "the Presidency can be vacant\"",
        ("FairSpec", "NoBehaviour"): "violated: `FairSpec` has a behaviour, so the leads-to is not vacuous",
        ("Spec", "Safety"): "no state is terminal: \"Convene or Adjourn is always enabled\"",
    }
    lcols = [("Row", 300, {"mono": True}), ("Spec", 240, {"mono": True}), ("Kind", 150),
             ("Property", 300, {"mono": True}), ("Constants overridden", 820), ("Verdict", 240),
             ("Distinct states", 220)]
    lcols.append(("What it shows (README § Liveness; header)", WW - sum(x[1] for x in lcols)))
    lr = []
    for r in lrows_:
        k = (r["spec"], r["prop"])
        need(k in say, TF, f"a liveness or deadlock row the diagram does not explain: {r['name']}")
        verdict = (f"[[teal|{r['verdict']}]]" if r["verdict"] == "HOLDS" else f"[[red|{r['verdict']}]]")
        lr.append([r["name"], r["spec"], r["kind"], r["prop"], ", ".join(f"`{o}`" for o in r["overrides"]) or "none",
                   verdict, n(r["states"]) if r["states"] is not None else "count not recorded",
                   say[k] + (", with two bills" if "Bills={b1,b2}" in r["overrides"] else "") + "; as expected"])
    y += c.table(X0, y, lcols, lr, size=13.5) + 20
    y += row_cards(c, X0, y, WW, 26, [
        ("README § `Constitution.tla`, Liveness (whole)", [md(R["liveness"])], "amber", {"bullets": False}),
        ("`TimeRuns` and `PresidentActs` (`Constitution.tla`)", [
            "`TimeRuns == \\A b \\in Bills : WF_vars(Lapse(b))`, where `Lapse(b) == BecomeLawUnsigned(b) \\/ "
            "PocketVeto(b)`: \"no one's obligation; the clause executes itself\".",
            "`PresidentActs == \\A b \\in Bills : WF_vars(Sign(b) \\/ Veto(b))`: \"an obligation the text does not "
            "impose, stated to show it would not suffice in the clock's place\"."], "teal", {}),
        ("Why it is not proved (`Constitution_proof.tla`, NOT PROVED)", [
            "\"PresentedBillsResolve, the ten-day rule's leads-to: it is quantified over bills inside the temporal "
            "body (\\A b : P(b) ~> Q(b)) with an ENABLED premise over b for WF1, the case for which the pinned "
            "prover has no sound route under the writing rules; it is checked by TLC only, in the liveness rows.\""],
         "amber", {"status": "notproved"}),
    ]) + 50

    # ---- band 8: the proofs
    y = band(c, X0, y, f"The proofs: every theorem in {PF[8:]}, with its hypotheses, read when this diagram is built",
             status="proved", extra=f"{n(p['obligations'])} obligations")
    pcols = [("Theorem", 400, {"mono": True, "bold": True}), ("ASSUME (read)", 560), ("PROVE (read)", 380),
             ("Inductive strengthening (proof module header)", 860), ("Init and Next lemmas (read)", 520)]
    pcols.append(("Hypotheses = the mutations whose rows break it (the diagram's check)",
                  WW - sum(x[1] for x in pcols)))
    prow = []
    for th in p["theorems"]:
        prop = th["prove"].split("[]", 1)[1]
        assumes = ", ".join(f"`{a}`" for a in th["assume"])
        if prop == "Safety":
            st, lem, chk = "the conjunction: each of the thirteen theorems, by PTL", "—", (
                "`Mut = \"none\"`: every property at once")
        else:
            st = strength.get(prop, "a flag, false initially and raised only by one action, whose guard makes the "
                              "raised value false" if prop in flags else "inductive as stated, with `TypeOK`")
            keyn = {"Incompatibility": "IncompatPW", "Disqualification": "DisqPW",
                    "PresidentNotVP": "PresidentNotVPInv"}.get(prop, prop)
            lms = [lm for lm in p["lemmas"] if lm in (f"Init{keyn}", f"Next{keyn}", f"{keyn}Implies")]
            need(len(lms) >= 2, PF, f"{th['name']}: its Init and Next lemmas are not in the lemma list")
            lem = ", ".join(f"`{x}`" for x in lms)
            hyp = {re.fullmatch(r'Mut # "(M_[A-Z_]+)"', a).group(1) for a in th["assume"]}
            brk = {mu for mu in muts if prop in ce[mu]}
            chk = ("[[teal|equal]]: " + ", ".join(f"`{m}`" for m in sorted(hyp, key=muts.index))) if hyp == brk \
                else "[[red|differ]]: hypotheses " + ", ".join(sorted(hyp)) + "; breaks " + ", ".join(sorted(brk))
        prow.append([th["name"], assumes, f"`{th['prove']}`", st, lem, chk])
    y += c.table(X0, y, pcols, prow, size=13.5) + 20
    other = [lm for lm in p["lemmas"] if not lm.startswith("Mut") and not any(
        lm in (r[4] or "") for r in prow)]
    y += row_cards(c, X0, y, WW, 26, [
        ("The prover (proof results header, read)", [
            f"`{p['prover'].split(' sha256')[0]}`, by sha256; backends {p['backends']}.",
            f"Result: all {n(p['obligations'])} obligations proved; {len(p['theorems'])} theorems, "
            f"{len(p['lemmas'])} lemmas.", "Command: `" + p["command"] + "`."], "blue", {"status": "proved"}),
        ("The other lemmas (read)", [
            ", ".join(f"`{x}`" for x in other) + ".",
            "\"Next is split once (NextDef) into the session, legislation, the Executive, appointments, "
            "impeachment and Article V; three frame lemmas say which variables each part leaves alone\" (header). "
            "`TypeOK` is proved under every mutation (`InitTypeOK`, `NextTypeOK`)."], "blue", {}),
        ("Named assumptions used (proof module header)", [
            "`NoOneIsNoPerson`, `CongressPersons`, `EligiblePersons`, `RevenueAreBills`, `SuffrageAreAmendments`, "
            "`FiniteBodies` (for `StateVotesNat`).",
            "\"Nothing else is assumed: no bound on any constant, no chamber or State count.\""], "blue", {}),
        ("Not proved (proof module header, NOT PROVED)", [
            "\"The witnesses (Never...), which are existential and stay with TLC.\"",
            "`PresentedBillsResolve`, checked by TLC only. `ElectionsBound` \"is a TLC device only\"."],
         "amber", {"status": "notproved"}),
        ("The words (proof results file, Words:)", [
            "\"proved means every obligation below was discharged by the prover under the named assumptions and "
            "each theorem's hypotheses; it is not a claim about any constant the assumptions exclude, nor about "
            "law or practice\""], "blue", {}),
    ]) + 50

    # ---- band 9: findings
    y = band(c, X0, y, "Findings about this module (README § Findings; docs/SESSION-GATE-FINDINGS-2026.11.17.md)")
    y += row_cards(c, X0, y, WW, 26, [
        ("A check made at nomination but not at confirmation (README § Findings)", [
            "\"`Constitution.tla` — a Vice-Presidential nominee could be impeached, convicted and disqualified while "
            "pending, then confirmed anyway (`M_VP_RECHECK`).\" TLC found it while the module was first written; "
            "it is now a mutation that restores the bug.",
            "The module header: `M_VP_RECHECK` is \"this module's own text before commit fe3ce28, which TLC "
            "refuted\". Its witness is `NeverVPNomineeDisqualified`."], "pink", {}),
        ("What `inSession` gates (SESSION-GATE-FINDINGS § 1, Summary)", [
            "\"Four actions read `inSession`, apart from `Convene` and `Adjourn`: `Veto`, `BecomeLawUnsigned`, "
            "`PocketVeto` and `RecessAppoint`. Twelve actions of Congress ignore it.\"",
            "\"Nothing checked or proved is wrong\": only `TenDayRule` and `RecessAppointmentsInRecess` mention "
            "the session, and the actions they depend on read it. `Government.tla` gates `Pass` and `Override` on "
            "its own `inSession`; \"the two modules disagree\".",
            "Recommendation: document the abstraction; \"Done in PR #11 (commit `84bd8a1`), with the Constitution "
            "results regenerated as the 2026.11.18 files\", the files drawn here."], "pink", {}),
    ]) + 20
    return c
