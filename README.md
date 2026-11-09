# gov-tla

A TLA+ model of the *procedural* core of the United States Constitution.

This is an exercise, not law. The Constitution is, for the most part, a set of
state machines gated by supermajorities. This spec models those machines and
checks the invariants the text actually guarantees.

## What is modelled

| Provision | Where |
|---|---|
| Art. I §6 — Incompatibility Clause | `Incompatibility` |
| Art. I §7 — origination, bicameralism, presentment, veto, pocket veto, ten-day rule, override | `Introduce` … `FailOverride` |
| Art. I §§2–3, Art. II §4 — impeachment and trial | `Impeach`, `Convict`, `Acquit` |
| Art. II §1 — eligibility, succession | `Elect`, `PresidentVacates` |
| Art. II §2 — advice and consent, recess appointments | `Nominate`, `Consent`, `RecessAppoint`, `Adjourn` |
| Art. V — both proposal routes, equal-suffrage entrenchment | `ProposeByCongress`, `ProposeByConvention`, `Ratify` |
| Amend. XXII — two-term limit | `TwoTermLimit` |
| Amend. XXV — VP succession and VP vacancy | `Convict`, `NominateVP`, `ConfirmVP` |

Deliberately abstracted away: quorum, Sundays, elections themselves, judicial
review, the age/residency/natural-born tests (folded into the constant
`Eligible`), and the "more than two years of another's term" nuance in the
22nd Amendment.

## Modules

### `Constitution.tla` — Articles I, II, V

Properties:

- `Safety` — bicameralism, origination, presentment, incompatibility,
  members of Congress are not impeachable (Blount, 1799), two-term limit,
  disqualification bars office, Article V thresholds including the
  all-States requirement for suffrage amendments.
- `PresentedBillsResolve` — the ten-day rule is the only liveness guarantee
  the text gives; a presented bill cannot sit on the President's desk forever.

### `Judiciary.tla` — Article III and every federal court

Covers the one Supreme Court, the inferior Article III courts Congress
ordains and establishes, and Article I tribunals.

| Provision | Where |
|---|---|
| Art. III §1 — one Supreme Court, never abolished, size set by Congress | `OneSupremeCourt`, `SetSeats` |
| Art. III §1 — inferior courts by statute; abolition unseats judges (Stuart v. Laird) | `EstablishCourt`, `AbolishCourt` |
| Art. III §1 — tenure during good behaviour | `GoodBehaviour` (action property) |
| Art. III §1 — Compensation Clause | `CompensationClause` (action property) |
| Art. III §2 — original vs. appellate jurisdiction; Marbury | `HasOriginalJurisdiction`, `OriginalJurisdiction` |
| Art. III §2 — Exceptions Clause (McCardle) | `SetExceptions`, `ExceptionsHonoured` |
| Art. III §2 — jury and venue for crimes | `JuryAndVenue` |
| Art. III §3 — treason needs two witnesses or open-court confession | `TreasonProof` |
| Art. II §2 — advice and consent; Chief Justice as a separate office | `NominateJudge`, `ConfirmChief` |
| Art. II §4 — judges removable only by impeachment | `Impeach`, `Convict` |
| Amend. V — no appeal from an acquittal | `NoDoubleJeopardy` |
| Amend. XI — no federal suit against a State by an outsider | `EleventhAmendment` |
| Article I judges serve fixed terms | `TermExpires` |

The President and presentment are abstracted (a "statute" is a majority of
both houses); compose with `Constitution.tla` for the full path.

### `Executive.tla` — Article II and the administrative state

The Constitution creates no bureaus. It refers to "executive Departments"
and their "principal Officer[s]", but every department, agency and
commission is a creature of statute, so `Init` has none. Congress creates
them, and the model asks the questions the case law asks: who appoints their
officers, who may remove them, and which branch they belong to.

| Provision | Where |
|---|---|
| Art. II §1 — one President; VP as Acting President has the full power | `Executive`, `OneExecutive` |
| Art. II §2 — pardons for federal offences only, never impeachment | `Pardon`, `PardonScope` |
| Art. II §2 — treaties need two-thirds of the Senate | `RatifyTreaty` |
| Art. II §2 — principal officers by advice and consent; inferior officers vested in President, courts or heads (Buckley: never Congress) | `ConfirmHead`, `AppointInferior`, `NoCongressionalAppointment` |
| Art. II §3 — President may convene Congress | `ConveneByPresident` |
| Art. I §8 — Congress creates departments and declares war | `CreateAgency`, `DeclareWar`, `WarIsCongressional` |
| Amend. XXV §§3–4 — inability, voluntary and involuntary, and the contest before Congress | `DeclareInability` … `CongressDecides` |
| Bowsher v. Synar — an officer who executes the laws is in the Executive branch and not removable by Congress | `ExecutionIsExecutive`, `CongressDoesNotRemoveExecutors` |
| Trump v. Slaughter (2026) — for-cause removal protection only for a body with no executive power | `UnitaryExecutive` |
| Federal Vacancies Reform Act — acting officers are time-limited | `ActAsHead`, `ActingIsTemporary`, `ActingEventuallyEnds` |

Legislative-branch agencies (GAO, CBO) and judicial-branch agencies
(Administrative Office, Sentencing Commission) are modelled by `branch`;
they can exist, but they cannot execute the laws.

### `Government.tla` — the authority graph

The other three modules model what each branch does. This one models how
authority runs *between* them: a directed, labelled multigraph over the
People, the States, the Constitution, the three branches, the Vice President,
and the agencies and inferior courts Congress creates. Edges come in two
layers:

- **Grant** — where authority comes from: `Power` (vesting clauses, enabling
  acts), `Select` (elections, nomination, consent), `Amend` (Articles V, VII).
- **Control** — one holder acting on another's exercise of power: veto,
  override, purse, impeachment, removal, review, pardon.

Every exercise of authority is the firing of an edge present in the graph at
that moment, under its condition (a sitting Congress, a seated President, a
pending case, a presidential trial). Firing can reshape the graph: statutes
add and remove edges and nodes, amendments rewrite text edges (XVII moves the
Senate from the States to the People; XXV lets the President nominate a Vice
President whom Congress confirms, and adds the inability edges), and courts
sever unconstitutional statutory edges.

| Claim | Where |
|---|---|
| Grant layer is nearly linear: outside the People, the States and the Vice Presidency it is acyclic, and every edge but the President's nomination of a Vice President runs forward along Constitution → Congress → Vice President → Executive → Judiciary → statute | `GrantCyclesPassThroughPeopleStatesOrVP`, `GrantFollowsChainExceptXXV` |
| The President–Vice President loop is the only grant cycle among government bodies, and exists exactly while XXV is in force | `OnlyGrantCycleIsXXV` |
| *Refuted:* every grant cycle closes through the People or the States, and the grant layer runs strictly forward (see below) | `GrantCyclesPassThroughPeopleOrStates`, `GrantFollowsChain`, checked by `Government_strict.cfg` |
| Only the People and the States write the Constitution | `ConstitutionWrittenByPeopleAndStates` |
| Every branch, agency and court traces back to the People; power (as opposed to office) reaches them only through the Constitution | `PowerTracesToPeople`, `ConstitutionIsTheOnlyDoor` |
| Agencies and inferior courts exist only by statute | `EveryBodyIsCreatedByLaw` |
| Control layer is cyclic and complete among the branches | `MutualChecks`, `ControlLayerIsCyclic` |
| Control layer is asymmetric toward Congress | `LegislativePrimacy` |
| Text edges change only by Article V; statutory edges only by presentment, override or judicial review | `TextChangesOnlyByArticleV`, `StatutesChangeOnlyByLawOrCourt` |
| Every act is an edge firing by an active node | `EveryActIsAnEdge` |
| Buckley, Bowsher, Chadha, Seila Law / Slaughter, Compensation Clause: forbidden statutory edges can be enacted, but once challenged are severed | `Forbidden`, `Sever`, `UnconstitutionalEdgesAreStruck` |
| Inferior-court judges leave only by resignation, impeachment, or abolition | `GoodBehaviour` |

## Running

```
java -cp tla2tools.jar tlc2.TLC -workers auto -config Constitution.cfg Constitution.tla
java -cp tla2tools.jar tlc2.TLC -workers auto -config Judiciary.cfg Judiciary.tla
java -cp tla2tools.jar tlc2.TLC -workers auto -config Executive.cfg Executive.tla
java -cp tla2tools.jar tlc2.TLC -workers auto -config Government.cfg Government.tla
```

With the tools installed by `./install-tla.sh` (see
[Visualization Tools](#visualization-tools)), `./tlc-workers -config
Constitution.cfg Constitution.tla` does the same.

The configs describe a tiny republic: three Representatives, two Senators, a
handful of States, one bill, one office, one amendment, one case. Even so the
exhaustive state space runs into the millions, so for a quick check use
simulation mode:

```
java -cp tla2tools.jar tlc2.TLC -simulate num=100000 -depth 40 -workers auto -config Judiciary.cfg Judiciary.tla
```

All three specs pass `Safety` and their action and liveness properties
across several hundred thousand random traces of depth 40–50.
`Government.tla` (with the Vice President) passes `TypeOK` and `Safety`
exhaustively for every behaviour of up to four steps (884,039 distinct
states), and `Safety` plus its four action properties across about 1.9
million states of random simulation at depth 40. The liveness property
`UnconstitutionalEdgesAreStruck` has not been checked: simulation with it
stalls. `Government_strict.cfg` gives the counterexample below.

### A claim TLC refuted

`Government.tla` first folded the Vice President into the Executive, and
claimed that, with the People and the States set aside, the grant layer is
acyclic and runs strictly down the chain Constitution → Congress →
Executive → Judiciary. With the Vice President as a node of its own (chosen
by electors or the Senate, presiding over the Senate, succeeding a departing
President), TLC refutes both claims in two steps:

```
State 1: <Initial predicate>
State 2: <Propose>   amendment = [XVII |-> "None", XXV |-> "Proposed"]
State 3: <Ratify>    amendment = [XVII |-> "None", XXV |-> "Ratified"]
Error: Invariant GrantCyclesPassThroughPeopleOrStates is violated.
```

Section 2 of the Twenty-fifth Amendment lets the President nominate a Vice
President, and the Vice President may succeed the President, so
Executive → Vice President → Executive is a cycle of authority that never
passes through the People or the States. It is how Gerald Ford became
President in 1974, nominated by Nixon in 1973 and confirmed by Congress, and
how Ford then chose Nelson Rockefeller. Before XXV the claims hold: a vacant
Vice Presidency simply stayed vacant.

The original properties are kept, unchanged, as refuted claims;
`Government_strict.cfg` checks them and reproduces the counterexample:

```
java -cp tla2tools.jar tlc2.TLC -workers 1 -config Government_strict.cfg Government.tla
```

`Safety` now checks what does hold instead: the inner grant layer is acyclic
once the Vice Presidency is also set aside, every grant edge but the
nomination runs forward, and the President–Vice President loop is the only
cycle, present exactly when XXV is ratified.

### Bugs TLC found while writing this

Both were the same shape: a check made at nomination but not at confirmation.

- `Constitution.tla` — a Vice-Presidential nominee could be impeached,
  convicted and disqualified while pending, then confirmed anyway.
- `Judiciary.tla` — a Chief Justice nominee could be confirmed to a district
  court while pending, then confirmed as Chief Justice and sit on two courts.

## Visualization Tools

Three scripts draw what the specs do. A tic-tac-toe board has a few
thousand states, so its whole state graph can be dumped once and drawn;
these specs have millions, so each script instead runs TLC on a small
wrapper module that bounds the run (a depth `CONSTRAINT` for breadth-first
search, a length `INVARIANT` for simulation) and parses the states TLC
prints. The modules and their `.cfg` files are used as they are; the
wrappers live in a temporary directory.

Every state is drawn as **what differs from the initial state**, with
records and functions flattened to paths such as `bill.b1.status` or
`agency.ag1.head`, and coloured by who acted to reach it:

| Color | Who acted |
|-------|-----------|
| Yellow | Initial state |
| Light Blue | Congress (either house): bills, overrides, consent, statutes |
| Orange/Salmon | The President or the executive: signing, vetoes, nominations, removals |
| Green | The courts: decisions, appeals, judicial review |
| Red/Coral | Impeachment and trial |
| Plum | The People and the States: elections, Article V, filing suit |
| Gray | Time, death, resignation |

### Setup (Required Once)

Install the TLA+ tools (into `tools/`, which is ignored) and the `./tlc`
and `./tlc-workers` wrappers:

```bash
./install-tla.sh
```

You also need Java and the GraphViz system binaries:
```bash
# macOS
brew install graphviz

# Ubuntu/Debian
sudo apt install graphviz

# Windows
winget install graphviz
```

The scripts run under [uv](https://docs.astral.sh/uv/), which installs the
`graphviz` Python package from `pyproject.toml`. Each takes `--help`.

---

### visualize_states.py

Draws the state graph of one module to a limited depth: every behaviour of
up to `depth` steps from the initial state.

**Usage:**
```bash
uv run python visualize_states.py [module] [depth]
```

- `module` (optional): `Constitution` (default), `Executive`, `Judiciary` or `Government`
- `depth` (optional): steps from the initial state (default: 2 for
  `Constitution`, 1 for the others, whose fan-out is much wider)
- `--merge N`: at the deepest level, collapse `N` or more sibling states
  reached by the same action into one dashed node that lists what they
  share and which variables vary (default 4; `0` draws every state)
- `--all-edges`: also draw, dotted, edges that do not go one level deeper
- `--keep-dot`: keep TLC's raw dump as `{module}_states_depth{N}.dot`

**Examples:**
```bash
uv run python visualize_states.py                   # Constitution, 2 steps
uv run python visualize_states.py Government        # the authority graph's first moves
uv run python visualize_states.py Judiciary         # 127 ways to set exceptions, merged
uv run python visualize_states.py Executive 2 --merge 0   # all 731 states
```

**Output:**
- `{module}_depth{N}.png`, e.g. [`Constitution_depth2.png`](Constitution_depth2.png)
  and [`Government_depth1.png`](Government_depth1.png)
- Console output: states by depth, and transitions by action

| Module | Depth 1 | Depth 2 |
|--------|---------|---------|
| Constitution | 10 | 68 |
| Executive | 47 | 731 |
| Judiciary | 147 | 2,801 |
| Government | 65 | 1,182 |

(Distinct states within that many steps of the initial state, with the
configs in this repository.)

---

### simulate_trace.py

Simulates and visualizes one random behaviour. TLC chooses every step
(`-simulate` with a seed, so a run can be repeated) and stops after
`--steps` steps, or earlier if no action is enabled.

**Usage:**
```bash
uv run python simulate_trace.py [module] [seed] [--steps N]
```

- `seed` (optional): random seed for a reproducible behaviour; without
  one a seed is chosen and printed
- `--steps` (optional): length of the behaviour (default: 20)

**Examples:**
```bash
uv run python simulate_trace.py                     # random Constitution run
uv run python simulate_trace.py Constitution 42     # reproducible run
uv run python simulate_trace.py Government 3 --steps 40
```

**Output:**
- Console output showing each step, who acted, and what it changed
- `{module}_trace.png` or `{module}_trace_seed{N}.png`, e.g.
  [`Constitution_trace_seed42.png`](Constitution_trace_seed42.png): one
  node per state, the lines changed by that step in bold and marked `▸`

**Sample console output** (`Constitution 42`):
```
Step 4: Elect  (People and States (elections, Art. V, suits))
  president: NoOne → F
  vicePresident: NoOne → G
  terms.F: 0 → 1
--------------------
Step 5: Elect  (People and States (elections, Art. V, suits))
  president: F → G
  vicePresident: G → F
  terms.G: 0 → 1
--------------------
Step 6: ProposeByCongress  (Congress (either house))
  amend.a1.status: None → Proposed
```

`Government.tla`'s `Sue` and `Exercise` sit under `\E e \in edges`, which
TLC cannot split into separate actions, so it reports them as `Next`; the
scripts tell them apart by the edge recorded in `last`.

---

### authority_graph.py

`Government.tla`'s state *is* a graph, so this script draws the `edges`
variable itself: nodes for the People, the States, the Constitution, the
branches and the agencies and courts in existence; edges colored by kind
(Power blue, Select green, Amend purple, Control gray), dashed if put there
by statute rather than the Constitution.

**Usage:**
```bash
uv run python authority_graph.py [seed] [--steps N] [--layer grant|control|all]
```

- No seed: the graph of 1789, [`Government_authority.png`](Government_authority.png)
- With a seed: simulate `--steps` steps (default 40) and draw the graph as
  it ends, marking edges added by amendment (bold), edges repealed (dotted
  gray), statutory edges under challenge (red, ⚖) and the edge that fired
  last, e.g. [`Government_authority_seed6.png`](Government_authority_seed6.png)
  (XXV ratified and XVII proposed, an agency created, and two of its
  statutory edges challenged in court)
- `--layer` draws only the grant layer or only the control layer

---

### authority_poster.py

The same graph as a 24 × 36 in print poster, for the founding graph or for
any later year:
[`Government_authority_poster_1789.pdf`](Government_authority_poster_1789.pdf)
and [`Government_authority_poster_2026.pdf`](Government_authority_poster_2026.pdf)
(previews: [1789](Government_authority_poster_1789.png),
[2026](Government_authority_poster_2026.png)).

**Usage:**
```bash
uv run python authority_poster.py               # 1789: the founding graph
uv run python authority_poster.py --year 2026   # as amended through 2026
```

`--year` applies every amendment in the model ratified by that year: XVII
(1913) moves the Senate's Select edge from the States to the People, and XXV
(1967) lets the President nominate a Vice President whom Congress confirms,
and adds the inability edges. What each amendment
changes comes from the model: the script compares the text edges just before
and just after the `Ratify` step in simulated behaviours. Only the years are
written into the script, in `RATIFIED`, and it stops if the model gains an
amendment that has no year there.

Instead of one tangle of edges, the poster separates the two layers.
The grant layer is drawn as a chain read top to bottom. The control layer
draws one arrow per direction between branches, its width the number of
checks, with the checks listed beside it. Headline numbers (edge counts,
Congress's checks against the other branches', grant cycles among
government bodies: none in 1789, the President–Vice President loop from 1967)
are computed from the graph, and the edges come from TLC.
The script stops if the model has an edge the poster's layout does not
place.

Writes `Government_authority_poster_YEAR.html`, then renders the PDF and PNG if
Node.js and Playwright are installed; otherwise print the HTML to PDF at
24 × 36 in from a browser.

---

## Ideas for next steps

- Refinement mappings from `Constitution.tla`, `Executive.tla` and
  `Judiciary.tla` to `Government.tla`, so every action in the detailed
  modules is shown to be the firing of an edge in the authority graph.
- Judicial review as a holding that voids a law in `Constitution.tla`.
- Staggered Senate classes (Art. I §3 cl. 2).
- Named-member votes instead of counts, to express conflict-of-interest rules
  such as the Chief Justice presiding at a presidential trial.
