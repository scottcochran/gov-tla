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

## Running

```
java -cp tla2tools.jar tlc2.TLC -workers auto -config Constitution.cfg Constitution.tla
java -cp tla2tools.jar tlc2.TLC -workers auto -config Judiciary.cfg Judiciary.tla
```

The configs describe a tiny republic: three Representatives, two Senators, a
handful of States, one bill, one office, one amendment, one case. Even so the
exhaustive state space runs into the millions, so for a quick check use
simulation mode:

```
java -cp tla2tools.jar tlc2.TLC -simulate num=100000 -depth 40 -workers auto -config Judiciary.cfg Judiciary.tla
```

Both specs pass `Safety` and the action properties across several hundred
thousand random traces of depth 40–50.

### Bugs TLC found while writing this

Both were the same shape: a check made at nomination but not at confirmation.

- `Constitution.tla` — a Vice-Presidential nominee could be impeached,
  convicted and disqualified while pending, then confirmed anyway.
- `Judiciary.tla` — a Chief Justice nominee could be confirmed to a district
  court while pending, then confirmed as Chief Justice and sit on two courts.

## Ideas for next steps

- A `Government.tla` that instantiates both modules so statutes go through
  real presentment and judges are nominated by the modelled President.
- Judicial review as a holding that voids a law in `Constitution.tla`.
- Staggered Senate classes (Art. I §3 cl. 2).
- Named-member votes instead of counts, to express conflict-of-interest rules
  such as the Chief Justice presiding at a presidential trial.
