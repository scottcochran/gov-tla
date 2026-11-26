"""B2 — Judiciary.tla: Article III and every federal court.

The module's picture (Congress, the courts, the judges and the cases, with the guards each mutation removes), the
README section's tables whole, the two row profiles, the mutation x property matrix read from the named TLC
results file, the witnesses, and every theorem with its hypotheses read from the named proof results file.

Build-time reads (each parses strictly and raises corpus.CorpusError, so the generator prints ERROR):
  - results/Judiciary-results-2026.11.09.txt and results/Judiciary-proof-results-2026.11.17.txt (corpus.RESULTS);
  - README.md § `Judiciary.tla`: the provisions table, the mutation table, Abstracted, the witness list, Rows;
  - specs/Judiciary.tla's header: PROPERTIES, MUTATIONS (each "Breaks"), WITNESSES, ABSTRACTED, LIVENESS;
  - rows/Judiciary-rows.txt's section comments ("# M_X: breaks ...");
  - specs/Judiciary_proof.tla: the Inv... definitions, the Mut... lemmas and the header's prose.
The mutation table and the matrix compare each source's "breaks" with the results file's COUNTEREXAMPLE rows and
draw every disagreement; nothing is reconciled.
"""
import re

from lib import Canvas, STATUS, text_width
import corpus as C

ID, SLUG = "B2", "judiciary"

W = 3600
S = 14
MOD = "Judiciary"


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


def camel(name, maxw, size=13.5):
    """Break a TLA+ name at its capitals so a narrow header column can hold it."""
    toks = re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z]*|[a-z]+|\d+", name)
    if "".join(toks) != name:
        raise C.CorpusError(f"cannot split {name!r}")
    lines, cur = [], ""
    for t in toks:
        if cur and text_width(cur + t, size, True) > maxw:
            lines.append(cur)
            cur = t
        else:
            cur += t
    lines.append(cur)
    return "\n".join(lines)


def md(s):
    """README markdown to the library's rich text: single-asterisk italics are dropped (the library has none)."""
    return re.sub(r"(?<![*\w])\*(?!\*)([^*\n]+?)\*(?![*\w])", r"\1", s)


def need(cond, rel, what):
    if not cond:
        raise C.CorpusError(f"{rel}: {what}")


# ---------------------------------------------------------------------------------------------- build-time reads
README_HEAD = "### `Judiciary.tla` — Article III and every federal court"


def readme_section():
    rel = "README.md"
    lines = C.read(rel).splitlines()
    need(README_HEAD in lines, rel, "the Judiciary.tla section heading is not found")
    i = lines.index(README_HEAD)
    j = next(k for k in range(i + 1, len(lines)) if lines[k].startswith("### ") or lines[k].startswith("## "))
    sec = lines[i + 1:j]

    def table(header, ncol):
        need(header in sec, rel, f"table {header!r} not found in § Judiciary.tla")
        k = sec.index(header) + 1
        need(re.fullmatch(r"\|(---\|)+", sec[k]), rel, f"no separator under {header!r}")
        rows = []
        k += 1
        while k < len(sec) and sec[k].startswith("|"):
            cells = [x.strip() for x in sec[k].strip().strip("|").split("|")]
            need(len(cells) == ncol, rel, f"row of {ncol} cells expected: {sec[k]!r}")
            rows.append(cells)
            k += 1
        need(rows, rel, f"table {header!r} is empty")
        return rows

    out = {"provisions": table("| Provision | Where |", 2),
           "mutations": table("| Mutation | Removes (reverts to) | Breaks |", 3)}
    paras, cur = [], []
    for ln in sec:
        if ln.strip():
            cur.append(ln)
        elif cur:
            paras.append(cur)
            cur = []
    if cur:
        paras.append(cur)
    out["intro"] = " ".join(paras[0])
    ab = [p for p in paras if p[0].startswith("Abstracted:")]
    need(len(ab) == 1, rel, "one 'Abstracted:' paragraph expected")
    out["abstracted"] = " ".join(ab[0])
    wi = [k for k, p in enumerate(paras) if p[0] == "Witnesses (each violated):"]
    need(len(wi) == 1, rel, "one 'Witnesses (each violated):' paragraph expected")
    bullets = []
    for ln in paras[wi[0] + 1]:
        if ln.startswith("- "):
            bullets.append(ln[2:])
        else:
            need(ln.startswith("  ") and bullets, rel, f"witness list line {ln!r}")
            bullets[-1] += " " + ln.strip()
    out["witness_groups"] = [re.findall(r"`(Never\w+)`", b) for b in bullets]
    need(all(out["witness_groups"]), rel, "a witness bullet names no Never... operator")
    out["after"] = [" ".join(p) for p in paras[wi[0] + 2:]]
    need(len(out["after"]) == 2 and out["after"][1].startswith("**Rows.**"), rel,
         "two paragraphs (the flags, then **Rows.**) expected after the witness list")
    return out


def comment_block(rel):
    """The lines of the first (*** ... ***) block of a module, as their text between (* and *)."""
    lines = C.read(rel).splitlines()
    out = []
    for ln in lines[1:]:
        if ln.startswith("(****"):
            if out:
                break
            continue
        if not ln.startswith("(*"):
            break
        need(ln.rstrip().endswith("*)"), rel, f"header line does not close: {ln!r}")
        out.append(ln[2:ln.rindex("*)")].rstrip())
    need(out, rel, "no header comment block")
    return out


def entries(block, start, rel):
    """Entries of a header list: a line indented three spaces starts one, a deeper line continues it.
    Returns ([(name, text)], trailing paragraph text)."""
    k = next((i for i, ln in enumerate(block) if ln.strip().startswith(start)), None)
    need(k is not None, rel, f"no {start!r} in the header")
    k += 1
    while k < len(block) and not re.match(r"^   \S", block[k]):
        k += 1
    out, tail = [], []
    while k < len(block) and block[k].strip():
        ln = block[k]
        if re.match(r"^   \S", ln):
            name, _, rest = ln.strip().partition(" ")
            out.append([name, rest.strip()])
        elif ln.startswith("    ") and out and not tail:
            out[-1][1] += " " + ln.strip()
        else:
            tail.append(ln.strip())
        k += 1
    need(out, rel, f"no entries under {start!r}")
    return [tuple(e) for e in out], " ".join(tail)


def strengthening(block, rel):
    """THE INDUCTIVE STRENGTHENING, in prose: every line is indented alike, so an entry starts at a line whose first
    word is a property name of Judiciary.tla's Safety, or Shape."""
    names = set(re.findall(r"\b[A-Z]\w+\b", re.search(r"^Safety ==(.+?)\n\n", C.read("specs/Judiciary.tla"),
                                                        re.M | re.S).group(1))) | {"Shape"}
    k = next((i for i, ln in enumerate(block) if ln.strip().startswith("THE INDUCTIVE STRENGTHENING")), None)
    need(k is not None, rel, "no THE INDUCTIVE STRENGTHENING in the header")
    out = []
    for ln in block[k + 1:]:
        if not ln.strip():
            break
        first = re.split(r"[ ,:]", ln.strip(), 1)[0]
        if first in names:
            out.append(ln.strip())
        else:
            need(out, rel, f"strengthening text before its first entry: {ln!r}")
            out[-1] += " " + ln.strip()
    need(len(out) >= 3, rel, "fewer than three strengthening entries")
    return out


def paragraph(block, start, rel):
    """A header paragraph that starts with `start`; a leading capitals label ("ABSTRACTED.") is dropped, since the
    card's title names it."""
    k = next((i for i, ln in enumerate(block) if ln.strip().startswith(start)), None)
    need(k is not None, rel, f"no {start!r} paragraph in the header")
    out = []
    while k < len(block) and block[k].strip():
        out.append(block[k].strip())
        k += 1
    text = " ".join(out)
    if start.isupper() or start.endswith("."):
        need(text.startswith(start), rel, f"paragraph does not start {start!r}")
        text = text[len(start):].strip()
        text = text[0].upper() + text[1:]
    return text


def read_all():
    tf, pf = C.RESULTS[MOD]
    t, p = C.tlc_results(tf), C.proof_results(pf)
    need(p["module"] == MOD, pf, "not Judiciary_proof.tla's results")
    need(t["as_expected"] == t["total"] and not t["not"] and not t["error"], tf, "not every row is as expected")
    for res, rel in ((t, tf), (p, pf)):
        for f, digest in res["modules"].items():
            need(C.sha256(f"specs/{f}") == digest, rel, f"{f} has moved since it was checked")
    need(C.sha256(t["rows_file"]) == t["rows_sha"], tf, "the rows file has moved since the run")
    need(p["tlc_file"] == tf and C.sha256(tf) == p["tlc_sha"], pf, "does not name the TLC results file drawn")
    need(not any(r["kind"] in ("PROPERTY", "SIMULATE") for r in t["rows"]), tf,
         "a PROPERTY or SIMULATE row: this diagram draws none")

    spec = "specs/Judiciary.tla"
    hb = comment_block(spec)
    props_h, _ = entries(hb, "PROPERTIES", spec)
    muts_h, muts_tail = entries(hb, "MUTATIONS", spec)
    wits_h, _ = entries(hb, "WITNESSES", spec)
    hdr = {"props": dict(props_h), "muts": {}, "muts_tail": muts_tail, "wits": dict(wits_h),
           "abstracted": paragraph(hb, "ABSTRACTED.", spec), "liveness": paragraph(hb, "LIVENESS.", spec),
           "local": paragraph(hb, "HOW EACH IS LOCAL.", spec), "constants": paragraph(hb, "CONSTANTS.", spec),
           "changes": paragraph(hb, "Changes of meaning", spec)}
    for name, text in muts_h:
        m = re.search(r"Breaks ([A-Za-z, ]+?)\.", text)
        need(m, spec, f"header entry {name} has no 'Breaks ...'")
        hdr["muts"][name] = (text, set(x.strip() for x in m.group(1).split(",")))

    rows_rel = t["rows_file"]
    rows_breaks = {}
    for ln in C.read(rows_rel).splitlines():
        m = re.fullmatch(r"# (M_\w+): breaks (.+)", ln)
        if m:
            rows_breaks[m.group(1)] = set(x.strip() for x in m.group(2).split(","))

    m = re.search(r"is a COUNTEREXAMPLE exactly on: (.+?)\. Every Never", t["expected"])
    need(m, tf, "Expected: line has no 'is a COUNTEREXAMPLE exactly on: ...'")
    expected = {}
    for part in m.group(1).split("; "):
        toks = [x.strip(",") for x in part.split()]
        ms = [x for x in toks if x.startswith("M_")]
        ps = [x for x in toks if not x.startswith("M_")]
        need(ms and ps, tf, f"Expected: clause {part!r}")
        for x in ms:
            expected[x] = set(ps)

    rd = readme_section()
    readme_breaks = {}
    for mcell, _, bcell in rd["mutations"]:
        mm = re.fullmatch(r"`(M_\w+)`", mcell)
        need(mm, "README.md", f"mutation cell {mcell!r}")
        readme_breaks[mm.group(1)] = set(re.findall(r"`(\w+)`", bcell))

    prel = "specs/Judiciary_proof.tla"
    ptext = C.read(prel)
    pb = comment_block(prel)
    strength = strengthening(pb, prel)
    notproved = paragraph(pb, "NOT PROVED, and why.", prel)
    invs = {}
    plines = ptext.splitlines()
    for i, ln in enumerate(plines):
        mm = re.match(r"^(Inv\w+)\s*== (.+)$", ln)
        if mm:
            body = mm.group(2)
            k = i + 1
            while k < len(plines) and re.match(r"^\s+/\\", plines[k]):
                body += " " + plines[k].strip()
                k += 1
            invs[mm.group(1)] = body
    need(invs, prel, "no Inv... definitions")
    lemmas = {}
    for mm in re.finditer(r"^LEMMA (Mut\w+) ==\s*ASSUME (.+?)\s+PROVE\s+(.+?)\s*\nBY", ptext, re.M | re.S):
        lemmas[mm.group(1)] = (" ".join(mm.group(2).split()), " ".join(mm.group(3).split()))
    mut_lemmas = [x for x in p["lemmas"] if x.startswith("Mut")]
    need(sorted(lemmas) == sorted(mut_lemmas), prel, "the Mut... lemmas in the module are not the results file's")
    am = re.search(r"\(\* The base module's named assumptions are the only ones used:(.+?)\n-{5}", ptext, re.S)
    need(am, prel, "no 'named assumptions are the only ones used' comment")
    assumptions = " ".join(re.sub(r"\(\*|\*\)", " ", "The base module's named assumptions are the only ones used:"
                                  + am.group(1)).split())
    return dict(t=t, p=p, tf=tf, pf=pf, hdr=hdr, rows_breaks=rows_breaks, expected=expected, rd=rd,
                readme_breaks=readme_breaks, strength=strength, notproved=notproved, invs=invs, lemmas=lemmas,
                assumptions=assumptions)


def prop_name(theorem):
    base = theorem[:-len("Always")]
    return {"Safe": "Safety"}.get(base, base)


def side(r):
    return {"j": "judge-side", "c": "case-side", "b": "combined", "w": "witness", "d": "deadlock"}[r["name"][0]]


def nice(ov):
    """A row's KEY=value overrides as readable, wrappable text."""
    return " ".join(o.replace("=", " = ", 1).replace(",", ", ") for o in ov)


# ---------------------------------------------------------------------------------------------- the diagram
def build():
    D = read_all()
    t, p, hdr, rd = D["t"], D["p"], D["hdr"], D["rd"]
    rows = t["rows"]
    muts, props, cells = C.matrix(t)
    wit = C.witnesses(t)
    dead = [r for r in rows if r["kind"] == "DEADLOCK"]
    need(len(muts) - 1 == len(rd["mutations"]), D["tf"], "the results file's mutations are not the README table's")
    need(set(muts[1:]) == set(D["readme_breaks"]) == set(hdr["muts"]) == set(D["rows_breaks"])
         == set(D["expected"]), D["tf"], "README, header, rows file and Expected: name different mutations")

    ce = {m: {r["prop"] for r in rows if r["mut"] == m and r["verdict"] == "COUNTEREXAMPLE"} for m in muts[1:]}
    hyp = {}
    for th in p["theorems"]:
        for a in th["assume"]:
            mm = re.fullmatch(r'Mut # "(M_\w+)"', a)
            if mm:
                hyp.setdefault(mm.group(1), set()).add(prop_name(th["name"]))
    sources = {"README": D["readme_breaks"], "module header": {k: v[1] for k, v in hdr["muts"].items()},
               "rows file": D["rows_breaks"], "Expected: line": D["expected"], "proof hypotheses": hyp}
    disagree = []   # (mutation, property, source, "omits" | "lists")
    for m in muts[1:]:
        for src, mp in sources.items():
            got = mp.get(m, set())
            for x in sorted(ce[m] - got):
                disagree.append((m, x, src, "omits"))
            for x in sorted(got - ce[m]):
                disagree.append((m, x, src, "lists"))
    judge_props = [x for x in props if any(r["prop"] == x and r["name"].startswith("j-") and r["mut"] != "none"
                                           for r in rows)]
    case_props = [x for x in props if any(r["prop"] == x and r["name"].startswith("c-") and r["mut"] != "none"
                                          for r in rows)]
    n_obl, n_rows = p["obligations"], t["total"]

    title = ("`Judiciary.tla`: one Supreme Court, the courts Congress makes, their judges and their cases — every "
             "guarantee rests on a check TLC shows it depends on, and TLAPS proves it")
    c = Canvas(ID, title,
               f"{md(rd['intro'])} Congress establishes, abolishes, sizes, pays and strips the courts; judges are "
               f"nominated, confirmed and removed; a case is filed, tried, appealed up two tiers and closed. **{n(n_rows)} "
               f"TLC rows, all as expected**: every property holds under `Mut = \"none\"` and each of {len(muts) - 1} "
               f"mutations breaks exactly the properties the row list names for it. **{n(n_obl)} obligations, all "
               f"proved**, in {len(p['theorems'])} theorems of the form `Spec => []P` under hypotheses that name the "
               f"mutations which break `P`. Witnesses, counterexamples and the deadlock audit are checked, not "
               f"proved; no liveness is claimed. This models the text's procedure: \"This is an exercise, not law\" "
               f"(README, opening).",
               W, "README.md (opening; § How the specs are written and checked, the summary table; § `Judiciary.tla` "
               "— Article III and every federal court: the provisions table, Abstracted, the mutation table, "
               "Witnesses, the flags paragraph, Rows; § Findings: Checks made at nomination but not at "
               "confirmation, Two claims the earlier Judiciary.tla made); specs/Judiciary.tla (header: PROPERTIES, "
               "Changes of meaning, MUTATIONS, WITNESSES, HOW EACH IS LOCAL, ABSTRACTED, LIVENESS, CONSTANTS; the "
               "ASSUMEs; Init; the guards a mutation removes; Congress and the courts; Judges; Removal; Cases; the "
               "safety properties; the witnesses); specs/Judiciary.cfg; specs/Judiciary_proof.tla (header: "
               "THEOREMS, THE INDUCTIVE STRENGTHENING, NOT PROVED; the assumptions comment; the Inv… definitions; "
               "the Mut… lemmas); rows/Judiciary-rows.txt (header and section comments); "
               f"{D['tf']}; {D['pf']}; docs/ASSESSMENT.md § Limits, point 6")
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    items = [("Judiciary.tla", [("checked", f"{n(n_rows)} rows, {n(t['as_expected'])} as expected"),
                                ("proved", f"{n(n_obl)} obligations, {len(p['theorems'])} theorems")]),
             ("Safety properties", [("proved", f"{len(props) - 2} + TypeOK, Shape, Safety")]),
             ("Mutations' counterexamples", [("checked", f"{len(muts) - 1} mutations")]),
             ("Witnesses", [("checked", f"{len(wit)}, existential, not proved")]),
             ("No deadlock", [("notproved", f"{len(dead)} DEADLOCK rows, no theorem")]),
             ("TypeOK under each mutation", [("proved", "ShapeAlways, TypeOKAlways; not run")]),
             ("Liveness", [(("None claimed", "grey", "2 3"), "")]),
             ("Sampled rows", [(("None", "grey", "2 3"), "")]),
             ("President, presentment, who sits, Amend. VI–VII", [("abstracted", "")])]
    y = status_strip(c, X0, X1, y, items)
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row list. "
                "**Proved** means TLAPS discharged every obligation for every value of the constants the module's "
                "named assumptions admit. **Sampled** means random simulation found no error, and is never cited "
                "as a check. \"None of these is a claim about law or practice\" (README § How the specs are written "
                f"and checked). The TLC results are `{D['tf'][8:]}`, the proof results `{D['pf'][8:]}`, which names "
                "that TLC file by sha256; both are read when this diagram is built.", 14.5, "muted") + 34

    # ================================================================ band 1: the picture
    y = band(c, X0, y, "The mechanism: Congress, the courts, the judges and the cases (`Judiciary.tla`, its actions "
             "and the guards a mutation removes)")
    y += c.legend(X0, y, [("box", "teal", "an action or the state it changes"),
                          ("line", "violet", "a mutation, named in violet: the guard it removes"),
                          ("box", "grey", "abstracted", "2 3"),
                          ("arrow", "teal", "authority or a case moving"),
                          ("arrow", "red", "removal: off the bench, or jurisdiction withdrawn", "7 5")],
                  title="Key") + 30

    def V(m):
        return f"[[violet|{m}]]"

    congress = [
        ("`EstablishCourt(c, t, st, h, s)`", [
            "A `Statute(h, s)`: a majority of both houses. A court that is not yet established (`NewCourt`), of a "
            "tier in `EstablishableTiers` (Appeals, District, Article I); a district court sits in a State. Seats "
            "start at 1.",
            f"{V('M_REESTABLISH')} drops `c \\notin courts`; {V('M_COURT_OF_UNION')} adds \"Supreme\" to the "
            "tiers."], "teal", {}),
        ("`AbolishCourt(c, h, s)`", [
            "Any court but the Supreme Court (`Abolishable`), and not while it holds a live case. Its judges lose "
            "their seats and join `unseated` (Repeal Act of 1802; Stuart v. Laird).",
            f"{V('M_ABOLISH_SC')} drops `c # SupremeCourt`."], "teal", {}),
        ("`SetSeats(c, n, h, s)`", [
            "`n` in `1..MaxSeats`. `ByAttrition(c, n)`: never fewer seats than sitting judges; a reduction takes "
            "effect as seats fall vacant (Acts of 1801, 1866).",
            f"{V('M_SHRINK')} drops it."], "teal", {}),
        ("`SetSalary(c, n, h, s)`", [
            "`PayProtected(c, n)`: a sitting Article III bench's pay is never cut. `payCut` records any step that "
            "cuts it. An Article I judge or an empty court has no protection.",
            f"{V('M_PAYCUT')} drops it."], "teal", {}),
        ("`SetExceptions(E, h, s)`", [
            "Strips heads of jurisdiction from the Supreme Court's appellate docket, even while an appeal in that "
            "head is pending (McCardle). Original jurisdiction is fixed by the text (`HasOriginalJurisdiction`).",
            "The mutations are at `Appeal` and `AppellateDecide`."], "teal", {}),
        ("Votes; presentment abstracted", [
            "`Statute(h, s)` is `Majority` of House and of Senate; presentment and the President are abstracted "
            "(compose with `Constitution.tla`).",
            "The Senate confirms by `Majority`, convicts by `TwoThirds`; the House impeaches by `Majority`."],
         "grey", {"status": "abstracted"}),
    ]
    reg_top = y + 16
    cw6 = (WW - 48 - 5 * 22) / 6
    hcg = max(c.card(0, 0, cw6, s[0], s[1], draw=False, size=S, status=s[3].get("status")) for s in congress)
    c.region(X0, reg_top, WW, hcg + 62, "Congress (Art. I § 8 cl. 9, Art. III § 1–2): every act a `Statute`",
             "grey")
    for i, s in enumerate(congress):
        c.card(X0 + 24 + i * (cw6 + 22), reg_top + 32, cw6, s[0], s[1], accent=s[2], h=hcg, size=S, **s[3])
    cg_bot = reg_top + hcg + 62

    # three columns
    gap = 120
    colw = [1100, WW - 2 * 1100 - 2 * gap, 1100]
    colx = [X0, X0 + colw[0] + gap, X0 + colw[0] + gap + colw[1] + gap]
    top = cg_bot + 90
    inner = [w - 48 for w in colw]

    judges = [
        ("The President", ["Nominations just happen (header § ABSTRACTED)."], "grey", {"status": "abstracted"}),
        ("`NominateJudge(c, p)` · `NominateChief(p)`", [
            "`NominateJudge`: a vacancy (`HasVacancy`), no pending nominee, and `Eligible(p)`: not disqualified, "
            "not in Congress, not already a judge.",
            "`NominateChief`: no Chief Justice and no pending nominee; not disqualified, not in Congress, and either "
            "already on the Supreme Court (White 1910, Stone 1941, Rehnquist 1986) or not a judge.",
            "These checks carry no property alone; the re-checks at confirmation do (header § MUTATIONS).",
            f"{V('M_INCOMPAT')} drops `NotInCongress`; {V('M_DISQUAL')} drops `NotDisqualified`."], "teal", {}),
        ("`ConfirmJudge(c, ayes)` · `ConfirmChief(ayes)`", [
            "A Senate `Majority`, and the checks again, since the nominee may have been seated elsewhere or "
            "convicted, or the vacancy filled: `StillEligible`, `StillVacant`, `ChiefStillFits`. `RejectJudge`, "
            "`RejectChief` clear the nominee.",
            f"{V('M_CONFIRM_RECHECK')}, {V('M_VACANCY_RECHECK')}, {V('M_CHIEF_RECHECK')} each drop one re-check."],
         "teal", {}),
        ("Leaving the bench", [
            "`Resign(c, p)`: resignation or death. `TermExpires(c, p)`: only where `FixedTerm(c)`, an Article I "
            "court.",
            "`Impeach(p, ayes)`: a House majority. `Convict(p, ayes, dq)`: `Impeached(p)` and a Senate "
            "`ConvictionVote` of two-thirds; off every bench, and disqualified if `dq`. `Acquit(p)`.",
            "Any other removal of an Article III judge raises `offBenchOtherwise` (`GoodBehaviour`).",
            f"{V('M_TENURE')} lets terms reach Article III; {V('M_NOIMPEACH')} drops the impeachment; "
            f"{V('M_CHASE')} convicts by a majority."], "teal", {}),
    ]
    courts = [
        ("The Supreme Court (`SupremeCourt`)", [
            "`Init`: `courts = {SupremeCourt}`, one seat. `OneSupremeCourt`: it always exists and is the only "
            "court of its tier.",
            "Original docket: `OriginalKinds` only (Ambassador, StateIsParty, AgainstState), by `SupremeOriginal`. "
            f"{V('M_MARBURY')} opens it to any head.",
            "Takes appeals from a court of appeals, unless the head is in `exceptions`. The Chief Justice sits "
            "here (`ChiefJusticeSits`)."], "teal", {}),
        ("Courts of appeals (tier \"Appeals\")", [
            "Try nothing: `AppealsOriginal` is false. Hear appeals from district and Article I courts.",
            f"{V('M_CIRCUIT')} lets them try cases (the 1789–1911 circuit courts)."], "teal", {}),
        ("District courts (tier \"District\")", [
            "Sit in a State (`location`). Try any head a run includes, except a suit against a State by an "
            "outsider (`SuableState`, Amend. XI).",
            f"{V('M_CHISHOLM')} allows that suit."], "teal", {}),
        ("Article I tribunals (tier \"ArticleI\")", [
            "Try only public rights, \"Federal\" (`PublicRights`). Judges serve fixed terms; `ArticleIII(c)` is "
            "false, so neither the Compensation Clause nor good behaviour reaches them.",
            f"{V('M_NORTHERN_PIPELINE')} lets them try any head."], "teal", {}),
        ("Court state", [
            "`courts`, `tier`, `location`, `seats`, `salary`, `exceptions`; `bench[c]` is who sits.",
            "`CourtsAreEstablished`: a court exists iff it has a tier (holds under every mutation). "
            "`BenchFitsSeats`: `Cardinality(bench[c]) <= seats[c]`; seats are a number Congress sets."],
         "teal", {}),
    ]
    cases = [
        ("`File(x, k, c, st)`", [
            "`HasOriginalJurisdiction(k, c)`: the court exists, the head is suable, and the tier may try it. A "
            "crime names the State where it was committed.",
            "Writes `origCourt` and `trialTier` once: the tier when filed."], "teal", {}),
        ("`Decide(x, jury, w, conf, v)`", [
            "The trial, in the court of filing. A crime: `TrialByJury`, and `TriedWhereCommitted`. Treason: "
            "guilty only on two witnesses or a confession (`TreasonProven`).",
            f"{V('M_NOJURY')}, {V('M_VENUE')}, {V('M_TREASON')} each drop one.",
            "Writes jury, venue, witnesses, confession and verdict once."], "teal", {}),
        ("`Appeal(x, c)`", [
            "District or Article I to a court of appeals; a court of appeals to the Supreme Court if not excepted "
            "(`NotExcepted`). None from an acquittal (`NotAcquitted`, Amend. V); none from the Supreme Court.",
            "Taking an excepted appeal raises `exceptedTaken`.",
            f"{V('M_EXCEPTIONS')}, {V('M_KEPNER')} drop one each."], "teal", {}),
        ("`AppellateDecide(x, v)` · `Dismiss(x)`", [
            "Affirmed or Reversed; in the Supreme Court only if the head is still heard (`StillHeard`). Deciding "
            "an excepted case raises `exceptedDecided`.",
            "`Dismiss`: the Court dismisses an excepted head; the judgment below stands (Ex parte McCardle, 1869).",
            f"{V('M_MCCARDLE')} decides it anyway."], "teal", {}),
        ("`Close(x)`", ["No further review sought, or certiorari denied."], "teal", {}),
    ]
    vgap = 50

    def heights(stack, w):
        return [c.card(0, 0, w, s[0], s[1], draw=False, size=S, status=s[3].get("status")) for s in stack]

    hj, hc, hk = heights(judges, inner[0]), heights(courts, inner[1]), heights(cases, inner[2])
    tot = max(sum(hj) + vgap * (len(hj) - 1), sum(hc) + 22 * (len(hc) - 1), sum(hk) + vgap * (len(hk) - 1))
    reg_h = tot + 72
    labels = ["Judges (Art. II § 2, Art. III § 1, Art. I §§ 2–3): `bench`, `nominee`, `chiefJustice`, "
              "`impeached`, `disqualified`",
              "Courts (Art. III § 1): one Supreme Court, the inferior tiers",
              "Cases (Art. III §§ 2–3, Amend. V, XI): `case[x]`, one record each"]
    for i in range(3):
        c.region(colx[i], top, colw[i], reg_h, labels[i], "teal")

    def draw_stack(stack, hs, x, w, g, arrows=True, alabels=None):
        yy = top + 36
        pos = []
        for k, (s, h) in enumerate(zip(stack, hs)):
            c.card(x, yy, w, s[0], s[1], accent=s[2], h=h, size=S, **s[3])
            pos.append((yy, h))
            yy += h + g
        if arrows:
            for k in range(len(stack) - 1):
                y0, h0 = pos[k]
                lab = alabels[k] if alabels else None
                c.arrow([(x + w / 2, y0 + h0 + 4), (x + w / 2, pos[k + 1][0] - 4)], "teal", label=lab,
                        lpos=0.5, lsize=12)
        return pos

    pj = draw_stack(judges, hj, colx[0] + 24, inner[0], vgap,
                    alabels=["nominates", "the Senate votes", "sits during good behaviour"])
    pc = draw_stack(courts, hc, colx[1] + 24, inner[1], 22, arrows=False)
    pk = draw_stack(cases, hk, colx[2] + 24, inner[2], vgap,
                    alabels=["Pending", "Decided", "Pending, a tier up", "Decided"])

    # numbered arrows between the regions
    def num(cx, cy, k, acc):
        c.label(cx, cy, "①②③④⑤⑥⑦"[k - 1], acc, 13)

    mids = [colx[i] + colw[i] / 2 for i in range(3)]
    for k, (i, acc, dash) in enumerate([(1, "teal", None), (0, "teal", None), (2, "red", "7 5")], start=1):
        c.arrow([(mids[i], cg_bot + 4), (mids[i], top - 18)], acc, dash=dash)
        num(mids[i] + 26, (cg_bot + top - 18) / 2, k, acc)
    jx1, cx0, cx1, kx0 = colx[0] + 24 + inner[0], colx[1], colx[1] + colw[1], colx[2] + 24
    for k, (row, acc, dash) in ((4, (pj[2], "teal", None)), (5, (pj[3], "red", "7 5"))):
        yy = row[0] + row[1] / 2
        c.arrow([(jx1 + 4, yy), (cx0 - 4, yy)], acc, dash=dash)
        num((jx1 + cx0) / 2, yy - 22, k, acc)
    for k, (row, acc) in ((6, (pk[0], "teal")), (7, (pk[2], "teal"))):
        yy = row[0] + row[1] / 2
        c.arrow([(kx0 - 4, yy), (cx1 + 4, yy)], acc)
        num((kx0 + cx1) / 2, yy - 22, k, acc)
    y = top + reg_h + 30

    key = [
        "① Congress establishes, abolishes, sizes and pays courts, and sets `exceptions`.",
        "② The Senate confirms by majority and convicts by two-thirds; the House impeaches by majority.",
        "③ `SetExceptions` withdraws appellate jurisdiction from the Supreme Court, even over a pending appeal.",
        "④ `ConfirmJudge`, `ConfirmChief` seat the nominee on `bench[c]`.",
        "⑤ `Resign`, `TermExpires`, `Convict` and `AbolishCourt` take a judge off the bench.",
        "⑥ `File` puts a case in a court with original jurisdiction over its head; `Decide` tries it there.",
        "⑦ `Appeal` moves it one tier up; `AppellateDecide` or `Dismiss` ends it there.",
    ]
    kw = (WW - 30) / 2
    kh = max(c.card(0, 0, kw, "The arrows", key[:4], draw=False, size=S, bullets=False),
             c.card(0, 0, kw, "The arrows (continued)", key[4:], draw=False, size=S, bullets=False))
    c.card(X0, y, kw, "The arrows", key[:4], accent="grey", h=kh, size=S, bullets=False)
    c.card(X0 + kw + 30, y, kw, "The arrows (continued)", key[4:] + [
        "The one link between judges and cases is `AbolishCourt`'s rule against abolishing a court with a live "
        "case: no case reads a judge variable (header § ABSTRACTED)."], accent="grey", h=kh, size=S,
        bullets=False)
    y += kh + 30

    flags = [
        ("`payCut` · `CompensationClause`", ["Raised by `SetSalary` when it cuts a sitting Article III bench's pay. "
                                             "`CompensationClause == ~payCut`."], "teal", {}),
        ("`offBenchOtherwise` · `GoodBehaviour`", ["Raised by `TermExpires` on an Article III court, and by "
                                                   "`Convict` without an impeachment or two-thirds. "
                                                   "`GoodBehaviour == ~offBenchOtherwise`."], "teal", {}),
        ("`exceptedTaken` · `ExceptionsHonoured`", ["Raised by `Appeal` when it takes an excepted head to the "
                                                    "Supreme Court. `ExceptionsHonoured == ~exceptedTaken`."],
         "teal", {}),
        ("`exceptedDecided` · `ExceptionsBindPending`", ["Raised by `AppellateDecide` when the Supreme Court "
                                                         "decides an excepted head. "
                                                         "`ExceptionsBindPending == ~exceptedDecided`."], "teal", {}),
        ("How each is local (header)", [md(hdr["local"])], "teal", {}),
    ]
    c.text(X0, y + 16, "Flags, each raised only by the step that would violate a property (header, VARIABLES)", 16,
           "teal", bold=True)
    y += 30
    y += row_cards(c, X0, y, WW, 24, flags[:4]) + 20
    y += c.card(X0, y, WW, flags[4][0], flags[4][1], accent="teal", size=S) + 50

    # ================================================================ band 2: provisions
    y = band(c, X0, y, "The provisions and where the module states them (README § `Judiciary.tla`, its table, "
             "every row)")
    prov = [[md(a), md(b)] for a, b in rd["provisions"]]
    y += c.table(X0, y, [("Provision", 1300), ("Where", WW - 1300)], prov, size=13.5, accent="blue") + 30
    y += row_cards(c, X0, y, WW, 30, [
        ("Abstracted (README § `Judiciary.tla`)", [md(rd["abstracted"])], "grey", {"status": "abstracted"}),
        ("ABSTRACTED (`Judiciary.tla` header)", [md(hdr["abstracted"])], "grey", {"status": "abstracted"}),
        ("LIVENESS and CONSTANTS (`Judiciary.tla` header)", [md(hdr["liveness"]), md(hdr["constants"])], "grey",
         {}),
        ("The flags (README § `Judiciary.tla`)", [md(rd["after"][0])], "teal", {}),
    ]) + 50

    # ================================================================ band 3: profiles
    y = band(c, X0, y, "Two profiles: judge-side rows run with no cases, case-side rows with no persons "
             "(rows/Judiciary-rows.txt, header)")
    consts = t["constants"].split(" (")[0]
    y += c.card(X0, y, WW, "The rows file's header (\"# expected: Profiles.\"), as the results file's Expected: line "
                "repeats it", [md(t["expected"].split(" Mut = none HOLDS")[0])], accent="teal", size=S) + 20
    y += row_cards(c, X0, y, WW, 30, [
        ("README § `Judiciary.tla`, Rows", [md(rd["after"][1])], "blue", {}),
        ("Why it is sound (`Judiciary.tla` header § ABSTRACTED)", [
            "\"So a run with no cases reaches every judge-side state a run with cases reaches, and a run with no "
            "persons every case-side state; the row list checks each property at the profile its own variables "
            "need.\"",
            "\"Judiciary_proof.tla's hypotheses are the general claim\" (rows file header)."], "teal", {}),
        ("docs/ASSESSMENT.md § Limits, point 6 (as of commit `e86e3c9`)", [
            "\"The Judiciary rework traded some fidelity for checkability. A court may now decide a case without "
            "any sitting judge … The proof covers the unsplit spec, so the general claims do not depend on the "
            "split. But judges and cases are now linked only by `AbolishCourt`'s rule against abolishing a court "
            "with a live case …\""], "pink", {}),
    ]) + 24

    groups = [("j", "judge-side"), ("c", "case-side"), ("b", "combined"), ("d", "deadlock audit"),
              ("w", "witnesses")]
    prow = []
    for pre, lab in groups:
        rs = [r for r in rows if r["name"].startswith(pre + "-")]
        need(rs, D["tf"], f"no {pre}- rows")
        ovs = []
        for r in rs:
            o = " ".join(sorted(r["overrides"]))
            if o not in ovs:
                ovs.append(o)
        st = [r["states"] for r in rs]
        ps = []
        for r in rs:
            if r["prop"] not in ps:
                ps.append(r["prop"])
        prow.append([f"**{lab}**", f"`{pre}-`", str(len(rs)), str(len({r['mut'] for r in rs})),
                     ", ".join(f"`{x}`" for x in ps),
                     f"{len(ovs)}: " + "; ".join(nice(o.split()) if o else "the defaults" for o in ovs[:6])
                     + (f"; … {len(ovs) - 6} more" if len(ovs) > 6 else ""),
                     f"{n(min(st))} – {n(max(st))}"])
    need(sum(int(r[2]) for r in prow) == n_rows, D["tf"], "rows by prefix do not add up to the total")
    y += c.table(X0, y, [("Profile", 170), ("Prefix", 90), ("Rows (read)", 110), ("Mut values", 110),
                         ("Properties run", 1150), ("Constant sets on its rows (KEY = value over the defaults; "
                                                    "read)", 1500),
                         ("Distinct states (read)", WW - 3130)], prow, size=13.5) + 20
    y += c.para(X0, y, WW, f"Defaults (the results file's Constants: line): `{consts}`. `Judiciary.cfg`, used by "
                "the visualisers and ad hoc runs, sets seven persons, four court identifiers, two States, one case "
                "and every head: \"the state space here is far too large to check exhaustively\" (its comment). "
                "The checked results come from the row list.", 13.5, "muted") + 50

    # ================================================================ band 4: mutation table
    y = band(c, X0, y, "The mutations (README § `Judiciary.tla`, its table, every row) beside what each other "
             "record says it breaks")
    mrows = []
    for (mcell, rem, bcell) in rd["mutations"]:
        m = re.fullmatch(r"`(M_\w+)`", mcell).group(1)
        bad = [d for d in disagree if d[0] == m]
        ag = ("[[teal|all six agree]]" if not bad else
              "; ".join(f"[[red|{d[2]} {d[3]}]] `{d[1]}`" for d in bad))
        hb = hdr["muts"][m][1]
        hb_txt = ", ".join(f"`{x}`" for x in sorted(hb))
        if any(d[2] == "module header" for d in bad):
            hb_txt = f"[[red|{', '.join(sorted(hb))}]]"
        cells_ = [mcell, md(rem), md(bcell), hb_txt,
                  ", ".join(f"`{x}`" for x in sorted(D["rows_breaks"][m])),
                  ", ".join(f"`{x}`" for x in sorted(ce[m])),
                  ", ".join(f"`{x}Always`" for x in sorted(hyp.get(m, ()))), ag]
        mrows.append({"cells": cells_, "accent": "red"} if bad else cells_)
    y += c.table(X0, y, [("Mutation (README)", 250), ("Removes (reverts to) (README)", 680),
                         ("Breaks (README)", 430), ("Module header: \"Breaks\" (read)", 390),
                         ("rows file: \"# M_X: breaks\" (read)", 390),
                         ("Results: COUNTEREXAMPLE on (read)", 400),
                         ("Proof: theorems whose ASSUME names it (read)", 520),
                         ("Agreement with the results file (the diagram's check)", WW - 3060)],
                 mrows, size=13.5, accent="violet") + 20
    srcs = ", ".join(sources)
    y += c.para(X0, y, WW, f"Six records say what each mutation breaks: {srcs}, and the results file's "
                "COUNTEREXAMPLE rows. Where one differs from the results file the row is marked red and the "
                "difference named; nothing is reconciled. The module header also says: \""
                + md(hdr["muts_tail"]) + "\"", 13.5, "muted") + 50

    # ================================================================ band 5: the matrix
    n_inv = sum(1 for r in rows if r["kind"] == "INVARIANT" and r["spec"] == "Spec"
                and not r["prop"].startswith("Never"))
    y = band(c, X0, y, f"Every mutation × every property: the {n_inv} INVARIANT rows that are not witnesses, read "
             f"from `{D['tf'][8:]}`")
    mw = 268
    pw = (WW - mw) // len(props)
    mw = WW - pw * len(props)
    cols = [("Mutation", mw)] + [(camel(x, pw - 18), pw) for x in props]
    base_c = {"Persons={}", "Cases={x1}", 'Kinds={"Federal","Treason"}'}
    none_rows = {}
    for r in rows:
        if r["mut"] == "none" and r["kind"] == "INVARIANT" and not r["prop"].startswith("Never"):
            none_rows.setdefault(r["prop"], []).append(r)
    prof = ["**Profile** at `Mut = \"none\"`, and what each row adds"]
    for x in props:
        parts = []
        for r in none_rows[x]:
            extra = sorted(set(r["overrides"]) - (base_c if r["name"].startswith("c-") else set()))
            if r["name"].startswith("c-") and any(o.startswith("Kinds=") for o in extra):
                pass
            parts.append(f"**{r['name'][0]}**" + (" " + nice(extra) if extra else ""))
        prof.append("\n".join(parts))
    mrows = [{"cells": prof, "accent": "grey"}]
    dis_cells = {(d[0], d[1]): d for d in disagree}
    n_eq = n_cmp = 0
    for m in muts:
        lab = f"`{m}`"
        mr = [r for r in rows if r["mut"] == m and r["kind"] == "INVARIANT" and not r["prop"].startswith("Never")]
        if m != "none":
            jr = [set(r["overrides"]) for r in mr if r["name"].startswith("j-")]
            common = set.intersection(*jr) if jr else set()
            if common:
                lab += "\n+ " + nice(sorted(common)) + " (judge-side)"
        row = [lab]
        for x in props:
            rs = [r for r in mr if r["prop"] == x]
            if not rs:
                row.append("")
                continue
            lines = []
            for r in rs:
                v = r["verdict"]
                vt = "[[teal|HOLDS]]" if v == "HOLDS" else f"[[red|{v}]]"
                eq = ""
                if m != "none":
                    ref = [q for q in none_rows.get(x, []) if set(q["overrides"]) == set(r["overrides"])]
                    if ref:
                        n_cmp += 1
                        if ref[0]["states"] == r["states"]:
                            eq = " [[grey|=]]"
                            n_eq += 1
                st = n(r["states"]) if r["states"] is not None else "count not recorded"
                if len(rs) > 1:
                    lines.append(f"{vt} **{r['name'][0]}** {st}")
                else:
                    lines.append(f"{vt}\n{st}{eq}")
            if (m, x) in dis_cells:
                d = dis_cells[(m, x)]
                lines.append(f"[[red|{d[2]} {d[3]} it]]")
            row.append("\n".join(lines))
        mrows.append({"cells": row, "accent": "red"} if any(d[0] == m for d in disagree) else row)
    y += c.table(X0, y, cols, mrows, size=13, hsize=13, accent="violet") + 20
    jm = [m for m in muts[1:] if ce[m] <= set(judge_props) - set(case_props)]
    km = [m for m in muts[1:] if ce[m] <= set(case_props) - set(judge_props)]
    moved = []
    for m in jm:
        for r in rows:
            if r["mut"] == m and r["name"].startswith("c-"):
                ref = [q for q in none_rows[r["prop"]] if set(q["overrides"]) == set(r["overrides"])]
                if ref and ref[0]["states"] != r["states"] and m not in moved:
                    moved.append(m)
    y += c.para(X0, y, WW, "Each cell is one row: its verdict and its distinct-state count. **j**, **c** and "
                "**b** mark the judge-side, case-side and combined profiles where `Mut = \"none\"` runs a property "
                "at more than one (`TypeOK` at two, `Safety` at three: every one HOLDS). An empty cell is a row the "
                "list does not run: `TypeOK` and `Safety` run under `none` only, and \"under each mutation it is "
                "proved (`ShapeAlways`), not run\" (rows file header). Every row is as expected.", 13.5,
                "muted") + 8
    y += c.para(X0, y, WW, f"[[grey|=]] (the diagram's comparison): the same distinct-state count as the "
                f"`Mut = \"none\"` row of that property at the same constants; {n_eq} of the {n_cmp} cells that "
                "can be compared. A mutation only drops a guard, so the same count is in effect the same states: "
                "the mutation does nothing at that profile. Every case-side mutation is = on every judge-side row. "
                f"Of the {len(jm)} judge-side mutations, {len(jm) - len(moved)} are = on every case-side row; "
                + ", ".join(f"`{m}`" for m in moved)
                + " reach more case-side states than `none` (they change the courts, which cases read), and still "
                "HOLD there. The rows file header says \"A judge-side mutation is inert on a case-side row and the "
                "converse\".", 13.5, "muted") + 50

    # ================================================================ band 6: witnesses
    y = band(c, X0, y, "Witnesses: each `Never…` property must be violated under `Mut = \"none\"`, which shows the "
             "model reaches what the text allows", status="checked", extra="existential, never proved")
    groups_r = {w: i + 1 for i, g in enumerate(rd["witness_groups"]) for w in g}
    need(set(groups_r) == {r["prop"] for r in wit} == set(hdr["wits"]), D["tf"],
         "README, header and results name different witnesses")
    wrows = []
    for r in wit:
        wrows.append([f"`{r['prop']}`", f"bullet {groups_r[r['prop']]}", md(hdr["wits"][r["prop"]]),
                      f"`{r['name']}`", side_of_w(r), nice(r["overrides"]) or "the defaults",
                      "[[green|COUNTEREXAMPLE]]" if r["verdict"] == "COUNTEREXAMPLE" else f"[[red|{r['verdict']}]]",
                      n(r["states"]), "as expected" if r["ok"] else "[[red|NOT as expected]]"])
    y += c.table(X0, y, [("Witness (README list; results)", 330), ("README", 110),
                         ("What it reaches (`Judiciary.tla` header § WITNESSES)", 700), ("Row", 190),
                         ("Profile", 150), ("Constants over the defaults (read)", WW - 2050),
                         ("Verdict (read)", 210), ("Distinct states (read)", 190), ("", 170)],
                 wrows, size=13.5, accent="green") + 50

    # ================================================================ band 7: deadlock, liveness
    y = band(c, X0, y, "The deadlock audit, and no liveness", status="notproved", extra="no theorem")
    drows = [[f"`{r['name']}`", f"`{r['spec']} {r['kind']} {r['prop']}`", nice(r["overrides"]) or "the defaults",
              f"[[teal|{r['verdict']}]]", n(r["states"]), "as expected" if r["ok"] else "[[red|NOT]]"]
             for r in dead]
    th = c.table(0, 0, [("Row", 260), ("Run", 330), ("Constants", 760), ("Verdict", 120), ("States", 120),
                        ("", 140)], drows, draw=False)
    lw_ = WW - 1730 - 30
    lh = c.card(0, 0, lw_, "LIVENESS (`Judiciary.tla` header)", [md(hdr["liveness"]),
                "The proof module claims \"Nothing about liveness: the module claims none\", and no theorem "
                "states that no state is terminal: the audit is checked by TLC only."], draw=False, size=S)
    hh = max(th, lh)
    c.table(X0, y, [("Row", 260), ("Run", 330), ("Constants", 760), ("Verdict", 120), ("States", 120),
                    ("", 140)], drows, size=13.5, accent="amber")
    c.card(X0 + 1730 + 30, y, lw_, "LIVENESS (`Judiciary.tla` header)", [md(hdr["liveness"]),
           "The proof module claims \"Nothing about liveness: the module claims none\", and no theorem states "
           "that no state is terminal: the audit is checked by TLC only."], accent="amber", h=lh, size=S)
    y += hh + 50

    # ================================================================ band 8: the proofs
    y = band(c, X0, y, f"The proofs: {len(p['theorems'])} theorems, {len(p['lemmas'])} lemmas, {n(n_obl)} "
             f"obligations (`{D['pf'][8:]}`)", status="proved", extra=f"{n(n_obl)} obligations")
    trows = []
    for th in p["theorems"]:
        pr = prop_name(th["name"])
        inv = [k for k, v in D["invs"].items() if re.search(rf"\b{pr}\b", v)] if pr != "Shape" else []
        hm = {re.fullmatch(r'Mut # "(M_\w+)"', a).group(1) for a in th["assume"]
              if re.fullmatch(r'Mut # "(M_\w+)"', a)}
        if pr in props and pr not in ("TypeOK", "Safety"):
            got = {m for m in muts[1:] if pr in ce[m]}
            agree = "[[teal|equal]]" if got == hm else f"[[red|differ: {', '.join(sorted(got ^ hm))}]]"
            ce_txt = ", ".join(f"`{m}`" for m in muts[1:] if pr in ce[m]) or "none"
        else:
            agree, ce_txt = "—", {"TypeOK": "run under `none` only (rows file header)",
                                  "Shape": "not a TLC row: the proof module's own"}.get(pr, "run under `none` only")
        prof_ = ("judge-side" if pr in judge_props else "case-side" if pr in case_props else
                 "j, c, b" if pr == "Safety" else "j, c" if pr == "TypeOK" else "—")
        trows.append([f"`{th['name']}`", ", ".join(f"`{a}`" for a in th["assume"]) or "none: every mutation",
                      f"`{th['prove']}`", prof_,
                      "; ".join(f"`{k} == {D['invs'][k]}`" for k in inv)
                      or ("every `Inv…` conjoins `Shape`" if pr == "Shape" else "—"),
                      ce_txt, agree, md(hdr["props"].get(pr, "")) or {
                          "Shape": "`JudgeTypes /\\ CaseTypes /\\ FiledInCourt`: `TypeOK`, split, and a filed case "
                                   "sits in a court (`Judiciary_proof.tla`)",
                          "TypeOK": "the type of every variable (`Judiciary.tla` `TypeOK`; not in the header's "
                                    "list)"}.get(pr, "")])
    y += c.table(X0, y, [("Theorem (read)", 340), ("ASSUME: hypotheses (read)", 560), ("PROVE (read)", 330),
                         ("Profile", 120),
                         ("Inductive invariant: the `Inv…` that states the property (the diagram's join)", 620),
                         ("Mutations with a COUNTEREXAMPLE on it (results, read)", 430),
                         ("ASSUME = counter-examples?", 150),
                         ("The property (`Judiciary.tla` header § PROPERTIES)", WW - 2550)],
                 trows, size=13.5, accent="blue") + 20
    y += c.para(X0, y, WW, "The proof module's header lists each theorem \"with its hypothesis: exactly the "
                "mutations whose rows in results/Judiciary-results-*.txt read COUNTEREXAMPLE for it\"; the column "
                "ASSUME = counterexamples checks that sentence against the results file drawn. " + D["assumptions"],
                13.5, "muted") + 30

    c.text(X0, y + 16, "The inductive strengthening, in prose (`Judiciary_proof.tla` header)", 16, "blue",
           bold=True)
    y += 30
    st_specs = [("", [md(tx)], "blue", {}) for tx in D["strength"]]
    half = (len(st_specs) + 1) // 2
    y += row_cards(c, X0, y, WW, 24, st_specs[:half]) + 16
    if st_specs[half:]:
        y += row_cards(c, X0, y, WW, 24, st_specs[half:]) + 30

    lrows = []
    for nm in [x for x in p["lemmas"] if x.startswith("Mut")]:
        a, pr_ = D["lemmas"][nm]
        mm = re.search(r'Mut = "(M_\w+)"', a)
        need(mm, "specs/Judiciary_proof.tla", f"{nm} assumes no Mut = ...")
        lrows.append([f"`{mm.group(1)}`", f"`{nm}`", f"`{a}`", f"`{pr_}`"])
    lt = c.table(0, 0, [("Mutation", 250), ("Lemma (read)", 470), ("ASSUME", 640),
                       ("PROVE: what it admits", 740)], lrows, draw=False)
    others = [x for x in p["lemmas"] if not x.startswith("Mut")]
    helpers = [x for x in others if not re.match(r"(Init|Next)Inv", x)]
    pairs = [x for x in others if re.match(r"(Init|Next)Inv", x)]
    rw = WW - 2100 - 30
    right = [
        ("The other lemmas (read)", [f"**{len(helpers)} helpers:** " + ", ".join(f"`{x}`" for x in helpers),
                                     f"**{len(pairs)} Init/Next steps**, one pair per invariant: "
                                     + ", ".join(f"`{x}`" for x in pairs)], "blue", {}),
        ("The prover (read)", [f"`{p['prover']}`", f"Backends: {p['backends']}",
                               f"Command: `{p['command']}`", f"Words: \"{p['words']}\""], "blue",
         {"status": "proved", "status_extra": f"{n(n_obl)} obligations"}),
        ("NOT PROVED, and why (`Judiciary_proof.tla` header)", [md(D["notproved"])], "red", {}),
    ]
    c.text(X0, y + 16, "One lemma per mutation, saying what it admits (`Judiciary_proof.tla`, the `Mut…` lemmas, "
           "read)", 16, "violet", bold=True)
    y += 30
    c.table(X0, y, [("Mutation", 250), ("Lemma (read)", 470), ("ASSUME", 640),
                    ("PROVE: what it admits", 740)], lrows, size=13.5, accent="violet")
    ry = y
    for tt, b, acc, k in right:
        ry += c.card(X0 + 2100 + 30, ry, rw, tt, b, accent=acc, size=S, **k) + 16
    y = max(y + lt, ry - 16) + 50

    # ================================================================ band 9: findings
    bugs_cite = "Bugs TLC found" in hdr["changes"] and "Bugs TLC found" not in C.read("README.md")
    y = band(c, X0, y, "What TLC found in the earlier text (README § Findings; `Judiciary.tla` header)",
             status="refuted")
    y += row_cards(c, X0, y, WW, 30, [
        ("Checks made at nomination but not at confirmation (README § Findings)", [
            "\"`Judiciary.tla` — a Chief Justice nominee could be confirmed to a district court while pending, "
            "then confirmed as Chief Justice, and sit on two courts (`M_CHIEF_RECHECK`).\"",
            "Each such bug \"is now a mutation that restores the bug\"."], "red", {"status": "refuted"}),
        ("Two claims the earlier `Judiciary.tla` made, which TLC refutes (README § Findings)", [
            "`ExceptionsHonoured`, as a state predicate, failed when Congress excepted a head while an appeal in it "
            "was pending: Ex parte McCardle itself. It is now checked at the step that takes the appeal, with "
            "`ExceptionsBindPending` and `Dismiss` for the step that decides it.",
            "`AppealsCourtsAreAppellate` failed when a closed case's district court was abolished and its "
            "identifier re-established as a court of appeals. It now reads the tier recorded at filing."], "red",
         {"status": "refuted"}),
        ("Changes of meaning (`Judiciary.tla` header)", [md(hdr["changes"])] + (
            ["[[red|The header cites README \"Bugs TLC found\"; README has no such heading.]] The refuted claims "
             "are in README § Findings (the diagram's check)."] if bugs_cite else []), "teal", {}),
    ]) + 20
    return c


def side_of_w(r):
    if "Persons={}" in r["overrides"]:
        return "case-side"
    return "judge-side"
