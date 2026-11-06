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
People, the States, the Constitution, the three branches, and the agencies
and inferior courts Congress creates. Edges come in two layers:

- **Grant** — where authority comes from: `Power` (vesting clauses, enabling
  acts), `Select` (elections, nomination, consent), `Amend` (Articles V, VII).
- **Control** — one holder acting on another's exercise of power: veto,
  override, purse, impeachment, removal, review, pardon.

Every exercise of authority is the firing of an edge present in the graph at
that moment, under its condition (a sitting Congress, a seated President, a
pending case, a presidential trial). Firing can reshape the graph: statutes
add and remove edges and nodes, amendments rewrite text edges (XVII moves the
Senate from the States to the People; XXV gives Congress two new edges onto
the Executive), and courts sever unconstitutional statutory edges.

| Claim | Where |
|---|---|
| Grant layer is partially linear: outside the People and the States it is acyclic and every edge runs forward along Constitution → Congress → Executive → Judiciary → statute | `GrantCyclesPassThroughPeopleOrStates`, `GrantFollowsChain` |
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

The configs describe a tiny republic: three Representatives, two Senators, a
handful of States, one bill, one office, one amendment, one case. Even so the
exhaustive state space runs into the millions, so for a quick check use
simulation mode:

```
java -cp tla2tools.jar tlc2.TLC -simulate num=100000 -depth 40 -workers auto -config Judiciary.cfg Judiciary.tla
```

All three specs pass `Safety` and their action and liveness properties
across several hundred thousand random traces of depth 40–50.
`Government.tla` has not yet been run through TLC.

### Bugs TLC found while writing this

Both were the same shape: a check made at nomination but not at confirmation.

- `Constitution.tla` — a Vice-Presidential nominee could be impeached,
  convicted and disqualified while pending, then confirmed anyway.
- `Judiciary.tla` — a Chief Justice nominee could be confirmed to a district
  court while pending, then confirmed as Chief Justice and sit on two courts.

## Ideas for next steps

- Refinement mappings from `Constitution.tla`, `Executive.tla` and
  `Judiciary.tla` to `Government.tla`, so every action in the detailed
  modules is shown to be the firing of an edge in the authority graph.
- Judicial review as a holding that voids a law in `Constitution.tla`.
- Staggered Senate classes (Art. I §3 cl. 2).
- Named-member votes instead of counts, to express conflict-of-interest rules
  such as the Chief Justice presiding at a presidential trial.
