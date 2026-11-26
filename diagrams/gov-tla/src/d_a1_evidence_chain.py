"""A1 — How every count in the README is made, and checked against its results file at build time.

The family's overview: the pipeline from a module to its two results files, the method's five rules, the README's
summary table drawn whole beside the same counts read from the named results files, and what is not proved.

Build-time checks (each raises, so the generator prints ERROR, like a gate):
  - every count in the README's summary table equals the count read from the module's named results files;
  - the named results file is the newest committed one of its kind (scripts/compare_results.py's rule);
  - every digest on a results file's Modules: line equals the sha256 of that file in specs/ now;
  - a proof results file's TLC results line names the module's named TLC results file, by its sha256.
"""
from lib import Canvas, STATUS, text_width, linked, poster_link, POSTER_MODULE, STATE_ELECTIONS_FIX, AMENDED_ELECTIONS
import corpus as C

ID, SLUG = "A1", "evidence-chain"

W = 3400
S = 14


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


PID = {m: k for k, m in POSTER_MODULE.items()}    # module -> its diagram's id


# ---------------------------------------------------------------------------------------------- build-time reads
def read_all():
    readme = C.readme_summary()
    data = {}
    for m in C.MODULES:
        tf, pf = C.RESULTS[m]
        for kind, rel in (("tlc", tf), ("proof", pf)):
            if C.newest(kind, m) != rel:
                raise C.CorpusError(f"{m}: the named {kind} results file {rel} is not the newest committed one, "
                                    f"{C.newest(kind, m)}; move corpus.RESULTS on purpose, with an amendment")
        t, p = C.tlc_results(tf), C.proof_results(pf)
        for res, rel in ((t, tf), (p, pf)):
            for f, digest in res["modules"].items():
                if C.sha256(f"specs/{f}") != digest:
                    raise C.CorpusError(f"{rel}: {f} has moved since it was checked (Modules: line digest differs)")
        if C.sha256(t["rows_file"]) != t["rows_sha"]:
            raise C.CorpusError(f"{tf}: {t['rows_file']} has moved since the run")
        if p["tlc_file"] != tf or C.sha256(tf) != p["tlc_sha"]:
            raise C.CorpusError(f"{pf}: names TLC results {p['tlc_file']}, not {tf} at its current digest")
        read = dict(rows=t["total"], mutations=len(C.mutations(t)), witnesses=len(C.witnesses(t)),
                    obligations=p["obligations"])
        for k, v in read.items():
            if readme[m][k] != v:
                raise C.CorpusError(f"README summary table: {m} {k} is {readme[m][k]}, the results files give {v}")
        if t["as_expected"] != t["total"] or t["not"] or t["error"]:
            raise C.CorpusError(f"{tf}: not every row is as expected")
        data[m] = dict(t=t, p=p, tf=tf, pf=pf, read=read)
    return readme, data


# ---------------------------------------------------------------------------------------------- the diagram
def build():
    readme, D = read_all()
    tot_rows = sum(d["read"]["rows"] for d in D.values())
    tot_obl = sum(d["read"]["obligations"] for d in D.values())
    gaps = C.proof_gaps()

    c = Canvas(ID, "How every count in the README is made: six modules, two results files each, and the build "
               "that checks the README against them",
               f"Each module is checked by TLC from its row list and proved by TLAPS in a proof module that extends "
               f"it; each run writes a dated results file that is never edited. **{n(tot_rows)} TLC rows, every one "
               f"as expected, and {n(tot_obl)} proof obligations, every one proved**, read from the twelve named "
               f"files below when this diagram is built. The build fails if any README count, digest or file name "
               f"disagrees. **Liveness and `Government.tla`'s global reachability claims are checked, not proved**, "
               f"and none of it is a claim about law or practice.",
               W, "README.md § How the specs are written and checked (its bullets, the summary table, the flip-test "
               "sentence, What is not proved), § Running (the scripts, Pins, CI); scripts/tlc_rows.py, "
               "proof_results.py, proof_sync.py, compare_results.py, ci_plan.py, flip_test.py (docstrings); "
               ".github/workflows/checks.yml; docs/ASSESSMENT.md § Strengths, point 2; PROOF-GAPS.txt; "
               + "; ".join(f"{d['tf']}, {d['pf']}" for d in D.values())
               + "; specs/*.tla digests compared at build time",
               state=STATE_ELECTIONS_FIX, note=AMENDED_ELECTIONS, pin=C.PIN_ELECTIONS_FIX)
    X0, X1 = c.x0, c.x1
    WW = X1 - X0
    y = c.y

    # ---- status strip
    items = [(linked(poster_link(PID[m]), f"{m}.tla"), [("checked", f"{n(D[m]['read']['rows'])} rows"),
                           ("proved", f"{n(D[m]['read']['obligations'])} obligations")]) for m in C.MODULES]
    items += [("Liveness (the README's list)", [("notproved", "5 properties"), ("proved", "ExecutiveIsFilled")]),
              ("Government Reach claims", [("notproved", "")]),
              ("Witnesses", [("checked", "existential")]),
              ("Flip tests", [(("No results file", "red", "2 3"), "")])]
    y = status_strip(c, X0, X1, y, items)
    y += c.para(X0, y, WW, "**Checked** means TLC explored every reachable state at the constants in the row list. "
                "**Proved** means TLAPS discharged every obligation for every value of the constants the module's "
                "named assumptions admit. **Sampled** means random simulation found no error, and is never cited "
                "as a check. \"None of these is a claim about law or practice\" (README § How the specs are written "
                "and checked). `PROOF-GAPS.txt` lists " + (f"{len(gaps)} modules" if gaps else "no module")
                + " without a proof module.", 14.5, "muted") + 34

    # ---- band 1: the pipeline
    y = band(c, X0, y, "From a module to its evidence: two generators that write, four scripts that only read "
             "(README § Running)")
    gap = 120
    cw = (WW - 3 * gap - 80) / 4
    cx = [X0 + 40 + i * (cw + gap) for i in range(4)]
    lane1 = [
        ("`specs/<Module>.tla` and `.cfg`", ["The model. Its header names each mutation and the property it must "
         "break. `Mut = \"none\"` is the text (README § How …, Mutations)."], "teal", {}),
        ("`rows/<Module>-rows.txt`", ["The only input of a TLC run: header comments give the module, title, prose "
         "expectation and default constants; each row is one run and the verdict it must give "
         "(`tlc_rows.py` docstring)."], "teal", {}),
        ("`scripts/tlc_rows.py`", ["Runs every row with `-workers 1`. Writes the dated file **only if every row is "
         "as expected**, never overwrites one; a differing rerun gets a letter suffix. Refuses a TLC not in "
         "`tools/TLC-PIN` (README § Running, Pins)."], "teal", {}),
        ("`results/<Module>-results-<date>.txt`", ["Names the checker by sha256, every module and the row list by "
         "sha256, the constants and the expectation, then one line per row and a summary line."], "teal",
         {"status": "checked"}),
    ]
    lane2 = [
        ("`specs/<Module>_proof.tla`", ["Extends the module without editing it. Proves each safety property as "
         "`Spec => []P`, assuming only that the mutations which break `P` are absent; `SafeAlways` under "
         "`Mut = \"none\"`; one lemma per mutation saying what it admits (README § How …, Proofs)."], "blue", {}),
        None,
        ("`scripts/proof_results.py`", ["Runs `tools/tlapm --cleanfp --strict` with a throwaway cache. Writes the "
         "file **only if every obligation is proved**. `tools/tlapm` refuses a prover not in `tools/TLAPS-PIN` "
         "(README § Running)."], "blue", {}),
        ("`results/<Module>-proof-results-<date>.txt`", ["Names every module of the EXTENDS chain and the prover "
         "by sha256, each theorem with its hypotheses, the lemmas, and the TLC results file that holds the "
         "mutations' counterexamples and the witnesses, by sha256."], "blue", {"status": "proved"}),
    ]
    h1 = max(c.card(0, 0, cw, t, b, draw=False, size=S, status=k.get("status")) for t, b, _, k in lane1)
    h2 = max(c.card(0, 0, cw, t, b, draw=False, size=S, status=k.get("status")) for t, b, _, k in
             [s for s in lane2 if s])
    top = y + 30
    y1, y2 = top + 26, top + 26 + h1 + 120
    region_h = (y2 + h2 + 30) - top
    c.region(X0, top, WW, region_h, "Generators: write results/ only when everything is as expected", "teal",
             dash="10 6")
    for i, s in enumerate(lane1):
        c.card(cx[i], y1, cw, s[0], s[1], accent=s[2], h=h1, size=S, **s[3])
    for i, s in enumerate(lane2):
        if s:
            c.card(cx[i], y2, cw, s[0], s[1], accent=s[2], h=h2, size=S, **s[3])
    for i in range(3):
        c.arrow([(cx[i] + cw + 6, y1 + h1 / 2), (cx[i + 1] - 6, y1 + h1 / 2)], "teal")
    c.arrow([(cx[0] + cw + 6, y2 + h2 / 2), (cx[2] - 6, y2 + h2 / 2)], "blue", label="the proof module and its "
            "EXTENDS chain", lpos=0.5, lw=cw - 40)
    c.arrow([(cx[2] + cw + 6, y2 + h2 / 2), (cx[3] - 6, y2 + h2 / 2)], "blue")
    c.arrow([(cx[0] + cw / 2, y1 + h1 + 6), (cx[0] + cw / 2, y2 - 6)], "blue", label="EXTENDS, never edits",
            lpos=0.5)
    c.arrow([(cx[3] + cw / 2, y2 - 6), (cx[3] + cw / 2, y1 + h1 + 6)], "grey", label="cites it by sha256",
            lpos=0.5)
    y = top + region_h + 50

    audits = [
        ("`scripts/proof_sync.py`", ["For every module, compares each digest on the newest results files' "
         "Modules: lines with the tree, and the checker and prover with their pins: IN SYNC, STALE or MISSING. "
         "A module with no proof module needs a line in `PROOF-GAPS.txt` (docstring)."], "grey", {}),
        ("`scripts/compare_results.py` in CI", ["`.github/workflows/checks.yml` reruns row lists and proofs in the "
         "tla-kit image pinned by digest (`tools/TLA-KIT-PIN`) and compares each fresh file with the newest "
         "committed one, line for line except the date. **CI never writes to results/** (README § Running, "
         "CI)."], "grey", {}),
        ("`scripts/ci_plan.py`", ["Chooses the modules a change can affect: its EXTENDS chain, row list, "
         "committed results, the scripts, the pins or the workflow. One row list can take two hours on a "
         "2-CPU runner; a manual run checks every module (docstring; README § Running)."], "grey", {}),
        ("`scripts/flip_test.py`", ["Flips one `Mut # \"M_X\"` hypothesis to `Mut = \"M_X\"` in a scratch copy "
         "and requires the proof to fail in a statement that carries it. **Writes nothing to the tree** (\"a "
         "mutated proof is not an artefact\", docstring)."], "grey", {}),
    ]
    ha = max(c.card(0, 0, cw, t, b, draw=False, size=S) for t, b, _, _ in audits)
    c.region(X0, y, WW, ha + 56, "Audits: read the results files and the tree, never write results/", "grey",
             dash="10 6")
    for i, s in enumerate(audits):
        c.card(cx[i], y + 28, cw, s[0], s[1], accent=s[2], h=ha, size=S)
    y += ha + 56 + 50

    # ---- band 2: the method
    y = band(c, X0, y, "What every module must have (README § How the specs are written and checked)")
    y += row_cards(c, X0, y, WW, 30, [
        ("Local properties", ["One action could break each property, and that action's guard decides whether it "
         "does.", "Three kinds: a state predicate whose inductive step is that guard; a flag the violating step "
         "would raise (`tenDayBreach`, `payCut`, `warWithoutStatute`); a record written once and checked against "
         "the guard of the step that wrote it."], "teal", {}),
        ("Mutations", ["A constant `Mut`: `\"none\"` is the text; each other value removes exactly one check, and "
         "the module header names the property that removal must break.", "Where they exist, real earlier law. "
         "TLC must find a counterexample for every mutation against every property it breaks, **and none against "
         "any other**."], "violet", {}),
        ("Witnesses", ["Each `Never…` property says something the text allows never happens. TLC must find each "
         "one violated, which shows the model reaches those states.", "Without them, a property could hold only "
         "because the state it forbids is unreachable."], "green", {}),
        ("Proofs", ["`<Module>_proof.tla` extends the module without editing it and proves each safety property "
         "as `Spec => []P`, assuming only that the mutations which break `P` are absent.", "Also `SafeAlways` "
         "under `Mut = \"none\"`, and one lemma per mutation saying what it admits."], "blue", {}),
        ("Evidence", ["All of it is in `results/`, generated by `scripts/` and never edited.", "Each file is "
         "dated and names the checker or prover, and every module it covers, by sha256."], "grey", {}),
    ]) + 50

    # ---- band 3: the README summary table, whole, beside the reads
    y = band(c, X0, y, "The README's summary table, every row and column, and the same counts read from the "
             "named results files")
    cols = [("Module", 250, {"mono": True, "bold": True}),
            ("TLC rows (all as expected)", 220), ("Mutations", 150), ("Witnesses", 150),
            ("Proof obligations (all proved)", 250),
            ("Read from the results files (the diagram's check; the build fails on any difference)", 560),
            ("TLC results file named", 430), ("Proof results file named", 470),
            ("Theorems · lemmas (proof results)", 250)]
    cols.append(("Newest of its kind · digests match specs/ now (the diagram's check)", WW - sum(x[1] for x in cols)))
    rows = []
    for m in C.MODULES:
        r, d = readme[m], D[m]
        rd = d["read"]
        rows.append([f"{m}.tla", linked(C.file_url(d["tf"], C.PIN_ELECTIONS_FIX), n(r["rows"])),
                     linked(poster_link(PID[m], "mutations"), str(r["mutations"])),
                     linked(poster_link(PID[m], "witnesses"), str(r["witnesses"])),
                     linked(C.file_url(d["pf"], C.PIN_ELECTIONS_FIX), n(r["obligations"])),
                     f"[[teal|{n(rd['rows'])}]] rows · [[violet|{rd['mutations']}]] mutations · "
                     f"[[green|{rd['witnesses']}]] witnesses · [[blue|{n(rd['obligations'])}]] obligations: all "
                     f"equal",
                     f"`{d['tf'][8:]}`", f"`{d['pf'][8:]}`",
                     linked(poster_link(PID[m], "theorems"), f"{len(d['p']['theorems'])} · {len(d['p']['lemmas'])}"),
                     "[[teal|yes]] · [[teal|yes]], " + ", ".join(f"`{f}`" for f in d["p"]["modules"])])
    rows.append({"cells": ["Total", f"**{n(sum(r['rows'] for r in readme.values()))}**",
                           f"**{sum(r['mutations'] for r in readme.values())}**",
                           f"**{sum(r['witnesses'] for r in readme.values())}**",
                           f"**{n(sum(r['obligations'] for r in readme.values()))}**",
                           "Totals are the diagram's sums; the README states none.", "", "", "", ""],
                 "accent": "grey"})
    y += c.table(X0, y, cols, rows, size=13.5) + 24
    y += c.para(X0, y, WW, "A witness is counted as an unmutated row on a `Never…` property, invariant or temporal; "
                "a mutation as each `Mut` value other than `\"none\"` that a results file runs. With those two "
                "readings every README count matches (the diagram's definitions, not the README's, which states "
                "none).", 13.5, "muted") + 40

    # ---- band 4: rows by kind, read
    y = band(c, X0, y, "Every TLC row by kind and verdict, read from the named results files")
    kinds = [("INVARIANT", "HOLDS"), ("INVARIANT", "COUNTEREXAMPLE"), ("PROPERTY", "HOLDS"),
             ("PROPERTY", "COUNTEREXAMPLE"), ("DEADLOCK", "HOLDS"), ("DEADLOCK", "DEADLOCK"),
             ("SIMULATE", "NO-ERROR-SAMPLED")]
    cols = [("Module", 250, {"mono": True, "bold": True})]
    cols += [(f"{k} · {v}", 270) for k, v in kinds]
    cols += [("Rows", 140), ("Largest distinct-state count", 260), ("Run date · checker", 0)]
    cols[-1] = (cols[-1][0], WW - sum(x[1] for x in cols[:-1]))
    rows = []
    for m in C.MODULES:
        t = D[m]["t"]
        cells = [f"{m}.tla"]
        for k, v in kinds:
            k_n = sum(1 for r in t["rows"] if r["kind"] == k and r["verdict"] == v)
            acc = {"HOLDS": "teal", "COUNTEREXAMPLE": "red", "DEADLOCK": "teal", "NO-ERROR-SAMPLED": "grey"}[v]
            cells.append(f"[[{acc}|{k_n}]]" if k_n else "0")
        if sum(1 for _ in t["rows"]) != sum(sum(1 for r in t["rows"] if r["kind"] == k and r["verdict"] == v)
                                            for k, v in kinds):
            raise C.CorpusError(f"{D[m]['tf']}: a row of a kind and verdict this table does not draw")
        big = max(r["states"] for r in t["rows"] if r["states"] is not None and not r["sampled"])
        cells += [str(t["total"]), n(big), f"{t['date']} · " + t["checker"].split(" (")[0]]
        rows.append(cells)
    y += c.table(X0, y, cols, rows, size=13.5) + 24
    y += c.para(X0, y, WW, "A COUNTEREXAMPLE row is as expected when the row list expects it: a mutation's broken "
                "property or a witness. A DEADLOCK row runs with the deadlock check on: HOLDS means none was "
                "reached, DEADLOCK that one was, as its row list expects. NO-ERROR-SAMPLED is a sample and **never a check** (each results file's "
                "Words: line). Every row in every file is as expected; the build fails otherwise.", 13.5,
                "muted") + 40

    # ---- band 5: what is not proved; the flip tests, two sources side by side
    y = band(c, X0, y, "What is not proved, and why (README § How …, What is not proved)", status="notproved")
    y += row_cards(c, X0, y, WW, 30, [
        ("Liveness properties", ["`PresentedBillsResolve`, `ActingEventuallyEnds`, "
         "`UnconstitutionalEdgesAreStruck`, `MajorityPrevails`, `ReconciliationPrevails` are checked by TLC, "
         "not proved.", "Each is a leads-to quantified over bills, agencies or edges, and the pinned prover has "
         "no sound route for a quantified leads-to.", "`Elections.tla`'s `ExecutiveIsFilled` has no quantifier "
         "and is proved, by one WF1 step."], "amber", {"status": "notproved"}),
        ("`Government.tla`'s global reachability claims", ["Checked, not proved. They are stated over `Reach`, a "
         "recursive function the prover has no fixpoint theory for.", "Each one's local form is proved."],
         "amber", {"status": "notproved"}),
        ("Witnesses and counterexamples", ["Existential, and stay with TLC: a run that reaches a state is "
         "evidence that it is reachable at those constants, and no proof is attempted."], "green",
         {"status": "checked"}),
    ]) + 40

    y = band(c, X0, y, "The flip tests: two records side by side (the diagram's juxtaposition; no results file "
             "records a flip)")
    y += row_cards(c, X0, y, WW, 30, [
        ("README § How the specs are written and checked", ["\"Every flip test fails as required: with one "
         "mutation hypothesis flipped to `Mut = \"M_X\"`, each proof breaks in the lemma of the property that "
         "mutation must break.\""], "blue", {}),
        ("docs/ASSESSMENT.md § Strengths, point 2", ["\"The recorded flips ran under the script's earlier rule (a failure "
         "anywhere outside `SafeAlways`) … The script now requires a failure in a statement that carries the "
         "flipped hypothesis, and **the flips have not been re-run under that rule**.\"", "The assessment is "
         "of four modules, as of commit `e86e3c9` (its opening)."], "pink", {}),
        ("What the tree holds", ["`scripts/flip_test.py` writes nothing to the tree, by design, so neither "
         "statement has a results file behind it, and no file says which rule each recorded flip ran under.",
         "`results/` holds TLC and proof results files only."], "red", {}),
    ]) + 20
    return c
