# Authoring a gov-tla family diagram

One module per diagram: `d_<id>_<slug>.py` exposing `ID`, `SLUG` and `build() -> Canvas`.
`uv run --no-project --python 3.9 python diagrams/gen-gov-tla-family.py <ID>` writes
`diagrams/gov-tla/<ID>-<SLUG>-<DATE>.svg` and prints any overlap warnings. A diagram is finished only when it prints
no warnings and both themes have been looked at as rendered images.

The method is TOPAK's `generating-corpus-diagrams` skill
(`skills/generating-corpus-diagrams/skills/generating-corpus-diagrams/` in TOPAK). This file is the family's
binding text: where the two differ, this file says how gov-tla does it. The library (`lib.py`, `metrics.py`) is
ported from TOPAK's; see its docstring.

## The records

The corpus is the **tracked** tree of this repository at the commit named in `lib.STATE`:

| Record | Cite as | What it says |
|---|---|---|
| `specs/<Module>.tla` | `` `Module.tla` `` and the operator: `` `Constitution.tla` `Override` `` | the model; its header names each mutation and the property it must break |
| `specs/<Module>.cfg` | `` `Module.cfg` `` | the default constants and the spec TLC runs |
| `specs/<Module>_proof.tla` | `` `Module_proof.tla` `` and the theorem | the proofs and their hypotheses |
| `rows/<Module>-rows.txt` | `rows/Module-rows.txt` | the row list: every TLC run, its constants and the expected verdict |
| `results/*.txt` | the file name | the evidence, generated and never edited; dated, digests of what it covers |
| `README.md` | README § and the heading: README § `Constitution.tla` | provisions, mutations, witnesses, abstractions, findings, what is not proved |
| `docs/*.md` | the file and its heading: `ASSESSMENT.md § Limits`, point 3 | the assessment and the dated findings |
| `PROOF-GAPS.txt` | `PROOF-GAPS.txt` | modules with no proof module (none, at d3c9aed) |

**Untracked files are not records** (`NOTES.md`, `TODO.md`, drafts, `docs/SESSION-GATE-PLAN-2026.11.17.md` at
d3c9aed): never draw from them.

## Content rules

- **Every statement traces to a record**, cited on the card or in the table, and every source is listed in the
  Canvas `sources` string. Draw from the records, not from memory, a brief or a summary.
- **Read results at build time, through `corpus.py`.** Counts, verdicts, mutation-by-property matrices, theorems
  and their hypotheses come from the results file `corpus.RESULTS` names for the module, not from copied numbers.
  `corpus.py` raises on any file that does not parse, so the generator prints `ERROR` and the build fails. Never
  select "the newest results file": A1 checks that the named one is the newest.
- **Where two sources disagree** (a README table and a results file, a module header and the README), draw what each
  says and report it. Do not reconcile them on the diagram.

### The vocabulary of claims

These are the README's words (§ How the specs are written and checked). Keep them distinct:

| Word | Said of |
|---|---|
| *checked* | TLC explored every reachable state at the constants in the row list (HOLDS, COUNTEREXAMPLE, DEADLOCK) |
| *proved* | TLAPS discharged every obligation for every value of the constants the module's named assumptions admit, as `Spec => []P` under the theorem's hypotheses |
| *sampled* | random simulation found no error (NO-ERROR-SAMPLED); **never** cited as a check |
| *refuted* | TLC found a counterexample to a claim the model was expected to satisfy (README § A claim TLC refuted) |

None of them is a claim about law or practice. Say so where a diagram could be read that way: *this is an exercise,
not law* (README, opening).

### Status is shown, not implied

- A **status strip** at the top of every diagram of a module: the module with its TLC status (rows, all as
  expected), its proof status (obligations, all proved), and what is checked but not proved (liveness, `Reach`
  claims). Use the library's statuses (`checked`, `proved`, `notproved`, `sampled`, `refuted`, `abstracted`,
  `open`, `notwritten`, `superseded`) and custom pills for what it lacks.
- **Never draw** a liveness property, a global `Reach` claim or a witness as proved. Never draw a sampled row as
  checked. Never draw an abstracted provision as modelled.
- **A mutation is earlier law, doctrine or practice, or no history at all.** Draw the README's "Earlier text,
  doctrine or practice" cell as it stands, including "—".

### Full tables

When a README section or a doc has a table, draw all of it: every row, every column. Diagrams are read zoomed in and
printed at poster size, so width may go to 3600 px and height is computed. A results file's rows are drawn whole as a
matrix (mutation by property), not sampled.

### The diagram's own claims

- A cross-reference the records do not make (a provision beside a theorem, a mutation beside a lemma) is allowed
  when it helps, and is headed as the diagram's own in the column or card title.
- A number no record states is labelled illustrative.
- A paraphrase is not a quotation. Quote exactly, or say "in effect".

### Footers, dates and amendments

The family shares one `DATE`. A diagram drawn against a later commit passes `state=`; an amended one passes `note=`.
An unamended diagram regenerates byte for byte. A diagram that changes on regeneration because its input moved is a
finding until someone decides to amend it.

## Visual language

| Accent | Meaning here |
|---|---|
| `blue` | proved (TLAPS); the text as written (`Mut = "none"`) |
| `teal` | the mechanism: actions, state, the model; checked (TLC) |
| `green` | witnesses: what the text allows, reached; the safe direction |
| `amber` | checked, not proved (liveness, `Reach`) |
| `violet` | mutations: one removed check, earlier law or doctrine |
| `red` | counterexamples, gaps, refuted claims, what is not proved or not modelled as written |
| `brown` | the People, the States, electors: actors outside the three branches |
| `pink` | findings (docs/) |
| `grey` | abstracted, external, neutral; sampled |

- Solid arrows carry authority or data; dashed arrows (`dash="7 5"`) are removal, denial, or a path that only
  removes authority (a veto, a removal, a court striking a law).
- Body text is 13.5–15 px, card titles 16 px, section headings 19–22 px. TLA+ names in code font.

## Library (src/lib.py) and reads (src/corpus.py)

- `Canvas(id, title, subtitle, width, sources, note=None, state=None)`; content starts at `c.y`, between `c.x0`
  and `c.x1`.
- `c.card(x, y, w, title, [rich strings], accent, status=, h=, size=, bullets=, tint=, dash=, draw=)` returns its
  height; `draw=False` measures only, which is how rows of cards are given equal heights.
- `c.table(x, y, [(title, width, {mono, bold, accent})...], rows, size=, accent=)`. A row is a list of rich
  strings, `{"group": label, "accent": a}` or `{"cells": [...], "accent": a}`. Returns its height.
- `c.region(x, y, w, h, label, accent, dash=, tint=)`; `c.arrow([(x, y), ...], accent, dash=, label=, lpos=,
  loff=, both=)`; `c.para`, `c.text`, `c.pill`, `c.status`, `c.label`, `c.line`, `c.legend`, `c.heading`.
- Rich text: `**bold**`, `` `code` ``, `[[red|accented bold]]`, and `\n` for a hard break.
- `corpus.tlc_results(rel)`, `corpus.proof_results(rel)`, `corpus.mutations(res)`, `corpus.witnesses(res)`,
  `corpus.matrix(res, spec)`, `corpus.readme_summary()`, `corpus.proof_gaps()`, `corpus.read(rel)`,
  `corpus.sha256(rel)`, `corpus.RESULTS[module]`.
