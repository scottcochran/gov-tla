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

## Running

```
java -jar tla2tools.jar -config Constitution.cfg Constitution.tla
```

or open `Constitution.tla` in the TLA+ Toolbox / VS Code extension and use
`Constitution.cfg` as the model. The config describes a tiny republic: three
Representatives, two Senators, four States, one bill, one office, one
amendment.

## Properties

- `Safety` — bicameralism, origination, presentment, incompatibility,
  members of Congress are not impeachable (Blount, 1799), two-term limit,
  disqualification bars office, Article V thresholds including the
  all-States requirement for suffrage amendments.
- `PresentedBillsResolve` — the ten-day rule is the only liveness guarantee
  the text gives; a presented bill cannot sit on the President's desk forever.

## Ideas for next steps

- A `Judiciary` module: life tenure, original vs. appellate jurisdiction.
- Staggered Senate classes (Art. I §3 cl. 2).
- Named-member votes instead of counts, to express conflict-of-interest rules
  such as the Chief Justice presiding at a presidential trial.
