# Diagrams

Generated diagrams of the gov-tla corpus: the modules, their row lists, their results files and the README that
describes them. A diagram is a derived artifact. It describes the records and never decides anything. **Where a
diagram and a record disagree, the record wins.** None of it is a claim about law or practice.

Each diagram is an SVG that adapts to light and dark themes (`prefers-color-scheme`; renderers without CSS fall
back to light), sized to be read zoomed in or printed at poster scale. Where a record has a table, the diagram
draws all of it. Diagrams read the results files at build time through
[`gov-tla/src/corpus.py`](gov-tla/src/corpus.py), so their counts and verdicts are the files', and a build fails
(`ERROR`) when a file no longer parses or no longer agrees with what the diagram checks.

The method is TOPAK's `generating-corpus-diagrams` skill
(`skills/generating-corpus-diagrams/skills/generating-corpus-diagrams/` on TOPAK's `main`). The family's binding
rules are [`gov-tla/src/AUTHORING.md`](gov-tla/src/AUTHORING.md). The drawing library
([`lib.py`](gov-tla/src/lib.py), [`metrics.py`](gov-tla/src/metrics.py)) is ported from TOPAK's
`diagrams/topak/src/` (the same author, at TOPAK commit `e25dcf4`).

## Generating, looking, checking

```bash
# Generate (all, or by id). The interpreter is pinned: Python 3.12 changed sum() over floats, which moves
# coordinates, so the family is generated under 3.9 and regenerates byte for byte only under it.
uv run --no-project --python 3.9 python diagrams/gen-gov-tla-family.py [A1 B1 ...]

# Render both themes, whole or cropped, to look at (light: rsvg-convert; dark: headless Chrome)
SK=<TOPAK>/skills/generating-corpus-diagrams/skills/generating-corpus-diagrams
uv run $SK/scripts/render.py A1 --family-dir diagrams/gov-tla
uv run $SK/scripts/render.py A1 --family-dir diagrams/gov-tla --needle "The flip tests" --h 900 --width 1800

# The regression check: regenerate everything; any change not declared with --expect is a finding
uv run $SK/scripts/regen_check.py --generator diagrams/gen-gov-tla-family.py --family-dir diagrams/gov-tla [--expect B5]
```

A change that the regression check reports as **unexpected** means something a diagram reads has moved: a
results file, a row list, a spec, the README's tables, or the library. Read the diff before amending or restoring.
A new results file changes no diagram until `corpus.RESULTS` names it, and A1 fails to build until it does.

## Links

The diagrams link to each other and to the sources they draw, following the `linking-posters` method of the
proof-posters plugin (`plugins/proof-posters/skills/linking-posters/` in riemann-diagrams). Open a diagram in a
browser to follow them. **GitHub's file viewer shows an SVG as an image, without its links or its style.**

**What a link opens.** Names are linked, not prose: a name in code font, and A1's counts.

| From | To |
|---|---|
| A name a diagram anchors (a mutation, a property, a theorem, a row, an action's card) | that row or card, on the same diagram |
| Any other name the diagram's module declares or defines, or a row name of its row list | its line in the module, proof module or row list, at the pinned commit |
| A module's file name (`Executive.tla`) | that module's diagram, at its top; on its own diagram, the file at the pin |
| A file name (`scripts/tlc_rows.py`, `results/…`, `README.md`) | the file at the pinned commit |
| A B diagram's header label (`GOV-TLA · B3`) | that module's row in A1's summary table |
| A1: a module name; its mutation, witness and theorem counts | the module's diagram: its top, its mutation table, witness table, theorem table |
| A1: a row or obligation count | the results file that lists the rows or states the count, at the pin |

A module diagram links a name only within its own module. The modules are independent, and a name declared in two
of them (`president`, `Senators`, `Elect`) is two things, so it is never linked from one module's diagram to
another's. A1, which is no one module's, links a name to the one diagram that anchors it, or to the one module
that defines it.

**Anchors.** Every diagram's header is `#top`. A card titled with one code-font name, and a table row whose first
cell is one, take that name as their id: `B1-constitution-2026.11.25.svg#M_ORIGIN`. Where a name is drawn twice,
the first drawn keeps it. Each B diagram also anchors four lists by name: `#mutations`, `#matrix`, `#witnesses`
and `#theorems`. The ids are the sources' own names, so a link stays good when a layout changes.

**The pin.** Every link out is to `github.com/scottcochran/gov-tla/blob/<PIN_COMMIT>/…`, where
`corpus.PIN_COMMIT` is the commit `lib.STATE` names (`d3c9aed`). Line numbers are read from the file at that
commit (`git show`), not from the tree, so a link lands on the line the diagram drew even after the file moves on.

**The manifest and the second run.** `gov-tla/manifest.json` lists every diagram's anchors and its links by kind.
A diagram links to another's anchor only when the committed manifest lists it. When a run moves any diagram's
anchors, the generator updates the manifest, prints a `NOTE` line and exits 1. Run it again, and the links follow.

**Where you land.** The target is framed when it opens: a card or list shows an amber halo, and a row is
recoloured amber. The frame pulses three times and then stays. Under `prefers-reduced-motion` it does not pulse.
A renderer that runs no CSS shows the diagram exactly as before: the light and dark renders are pixel-identical to
the unlinked diagrams.

```bash
# Every link lands: parse every output, no duplicate id, every target exists and is framed, every link out pinned
uv run --no-project --python 3.12 python <riemann-diagrams>/plugins/proof-posters/skills/linking-posters/scripts/check-links.py \
  --config diagrams/proof-posters.toml
```

The generator makes the same checks and prints a `WARNING` for any failure, so the regression check fails on a
link that lands nowhere.

## CI, releases and the Pages site

Three workflows, adapted from riemann-diagrams':

- **`diagrams.yml`** runs on every pull request and push to `main`. It regenerates the family under Python 3.9
  and fails on any `WARNING`, `ERROR` or `NOTE` line. It also fails on any difference from the committed SVGs and
  manifest, and on any link `check-links.py` rejects. The script is fetched from riemann-diagrams at a pinned
  commit and checked by its sha256.
- **`release.yml`** runs when the custodian pushes an annotated `vMAJOR.MINOR.PATCH` tag on `main`. It runs
  `diagrams.yml` on the tag, then creates a GitHub release. The release holds the SVGs and `pins.json`, which
  records the tag, the state-of-record commit, the generator's commit and the run. It also holds `SHA256SUMS`
  over all of them, and notes that open with the tag's message. Then it calls `pages.yml`.
- **`pages.yml`** publishes one release to GitHub Pages. It checks the tag's SVGs against the release's
  `SHA256SUMS` before it deploys, so the site is the release and nothing else. It serves the SVGs at
  `diagrams/gov-tla/…`, the paths they have in the tree, and an index: this README, rendered, above the list of
  diagrams. It ends by reading `pins.json` back from the site, and fails unless the site names the tag. Run it by
  hand from `main` with an existing tag to republish a release.

To release, tag `main` and push the tag. The message says what changed and which diagrams a reader must re-read:

```bash
git tag -s v0.1.0 -m "v0.1.0: …" && git push origin v0.1.0
```

The site holds one release at a time; every release stays on its release page. Diagrams opened from the site
are served as `image/svg+xml`, so their links and target frames work there.

## The gov-tla diagram family (2026.11.25)

Drawn against `main` at `d3c9aed` (2026.11.20), tracked files only.

**Drawn 2026.11.25**: seven diagrams, A1 by hand and B1–B6 by six drawing agents in parallel, one per module, each reviewed in both themes and its reported inconsistencies checked against the files. The family's statuses are the README's words: *checked*, *proved*, *sampled* and *refuted*, with *checked, not proved* for liveness and `Reach` claims. Drawing surfaced ten verified findings and seven unchecked leads, none of which changes a verdict: see [FINDINGS-2026.11.25.md](FINDINGS-2026.11.25.md). No record was changed to match a diagram.

### A — the corpus and its evidence

| Id | Diagram | What it shows |
|---|---|---|
| A1 | [How every count in the README is made](gov-tla/A1-evidence-chain-2026.11.25.svg) | The pipeline from a module to its two results files (generators that write, audits that only read), the method's five rules, the README's summary table drawn whole beside the same counts read from the twelve named results files, every TLC row by kind and verdict, what is not proved, and the flip tests' two records side by side. **Builds only if** every README count equals its results file's, each named file is the newest of its kind, and every digest matches the current specs. |

### B — one diagram per module

| Id | Diagram | What it shows |
|---|---|---|
| B1 | [Constitution.tla: legislation, the Executive and Article V](gov-tla/B1-constitution-2026.11.25.svg) | The three machines over one Executive and one sitting of Congress, each with numbered action arrows and a key of guards, mutations and flags; the thirteen properties as the header states them; how each row switches on only the machine its property reads, with the inert cells checked against state counts; the README's provisions and mutation tables whole beside the header, the Expected: line, the counterexamples and the proof hypotheses; the 20 × 15 matrix with distinct states; 14 witnesses; the liveness and deadlock rows; 14 theorems with their hypotheses; the README's findings and the session-gate finding. |
| B2 | [Judiciary.tla: one Supreme Court, the courts Congress makes, their judges and their cases](gov-tla/B2-judiciary-2026.11.25.svg) | Congress, judges, courts and cases with seven numbered arrows and the guard each mutation removes; the four flags; the README's provisions and mutation tables whole beside the header, the rows comments, the counterexamples and the proof hypotheses (`M_REESTABLISH` drawn red: the header omits `BenchFitsSeats`); the judge-side and case-side profiles; the 24 × 20 matrix with distinct states; witnesses; the two deadlock rows (no liveness); 21 theorems, 23 mutation lemmas; what TLC found in the earlier text. |
| B3 | [Executive.tla: Article II and the administrative state](gov-tla/B3-executive-2026.11.25.svg) | Three machines over one President, one Congress and the agencies it charters: the Amendment XXV inability machine (arrows ①–⑧ with a key); agencies from the six `KnownCharters` (the three `Chartered` checks evaluated at build time), head appointment, three removals and the FVRA acting chain; eligibility, impeachment, pardon, treaties, war and sessions. The README's provisions and mutation tables whole beside the header, the Expected: line, the counterexamples and the proof hypotheses; the matrix over 14 properties; 19 witnesses; the liveness rows (`ActingEventuallyEnds`: checked, not proved); 14 theorems with their hypotheses. |
| B4 | [Government.tla: the authority graph](gov-tla/B4-government-2026.11.25.svg) | The grant layer read from the module's edge sets (`Founding`, `Adds`, `Drops`, `AgencyEdges`, `CourtEdges`), nodes in `Rank` order, the edges that run back drawn below; the control layer as a holder × target table; every edge and every action of `Next` as the module writes them; the README's claims and mutation tables whole, joined to theorems and rows; the configurations; the mutation × configuration matrix; witnesses; the liveness rows (`UnconstitutionalEdgesAreStruck`: checked, not proved); the five `Reach` claims checked, not proved, their local forms proved; the one sampled row drawn sampled; 27 theorems; the claim TLC **refuted**, with its trace; one band from `SESSION-GATE-FINDINGS-2026.11.17.md` § 5. |
| B5 | [Elections.tla: the presidential cycle](gov-tla/B5-elections-2026.11.25.svg) | The `stage` and `clock` lanes, and who acts at each stage with the guard each mutation removes (ten numbered arrows and a key); the README's provisions and mutation tables whole beside the header and the counterexamples; the matrix with one line per mutation and set of constants (529 rows on `Spec`); 24 witnesses; the liveness rows, with `ExecutiveIsFilled` **proved** by one WF1 step; 22 theorems with their hypotheses; the 24 `Mut…Admits` lemmas drawn red, after the first end-of-module line of `Elections_proof.tla`; `Elections.cfg` beside `c-cfg-safety`; one band from `MUTATION-MATRIX-FINDINGS-2026.11.17.md`. |
| B6 | [SenateRules.tla: the filibuster](gov-tla/B6-senate-rules-2026.11.25.svg) | The floor (stages, numbered steps) and each kind's cloture threshold, which only falls; the vote ladder at seven and five Senators (the diagram's arithmetic, checked against the operators at build time); the README's rule and mutation tables whole beside the module header; the mutation × property matrix with the seven- and five-Senator rows apart; the eight witnesses; the temporal rows (`MajorityPrevails`, `ReconciliationPrevails`, `NoBehaviour`: checked, not proved); the seven theorems with their hypotheses; why there are two TLC results files dated 2026.11.19. |
