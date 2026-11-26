# What drawing the diagram family found, 2026.11.25

Drawing the seven diagrams of the family (A1, B1–B6) against `main` at `d3c9aed` surfaced the findings below. Each
is a lead for whoever maintains the records: **no record was changed**, and the diagrams draw each disagreement as
the records state it. "Verified" means checked against the files after the drawing agent reported it; the rest are
the drawing agents' reports, not re-checked.

Nothing below changes a verdict. Every TLC row in every results file is as expected, every proof obligation is
proved, every README summary count equals its results file, and every results file's digests match the current
specs (A1 builds only if all of that holds).

## Verified

| # | Where | Finding |
|---|---|---|
| 1 | `specs/Elections_proof.tla:1372` | An end-of-module line (`====`) ends the module after `ExecutiveIsFilledAlways`. The 24 `Mut…Admits` lemmas (lines 1379–1520) follow it, before a second `====` at line 1525. TLA+ tools stop at the first, so those lemmas were almost certainly never checked (not confirmed by running tlapm). No theorem cites them, so the proved properties and the 1,121 obligations are unaffected. But README § How the specs are written and checked ("one lemma per mutation saying what that mutation admits") does not hold of Elections as proved. No other module has a second `====`. |
| 2 | `rows/Constitution-rows.txt:20-22` | Lists `M_VP_RECHECK` among the mutations inert against the legislative and Article V properties. It is not: `m-vprecheck-bicam` reaches 30,732 states against `p-none-bicam`'s 13,644, and `m-vprecheck-artv` 12,810 against 5,690. Its check is in `ConfirmVP`, part of the shared Executive, which no row switches off. Verdicts are unaffected (HOLDS, as expected). |
| 3 | `specs/Judiciary.tla:81-83` | The header says `M_REESTABLISH` "Breaks OneSupremeCourt, ChiefJusticeSits". The README (line 218), the rows file, the results file (`j-reestablish-seats` COUNTEREXAMPLE) and `BenchFitsSeatsAlways`'s hypothesis all add `BenchFitsSeats`. That also falsifies the header's lines 150–151 ("The column "Breaks" above is what the TLC results file shows"). |
| 4 | `rows/Judiciary-rows.txt`, header | "A judge-side mutation is inert on a case-side row" does not hold for state counts: `c-abolishsc-original` reaches 3,192 states against `c-none-original`'s 136 (also `M_COURT_OF_UNION`, `M_REESTABLISH`). Verdicts unaffected. |
| 5 | `specs/Judiciary.tla:50` | Cites README "Bugs TLC found"; the README has no such heading (the material is in § Findings). |
| 6 | `specs/Constitution_proof.tla:31-33` | Says the flags are "raised only by one action". `tenDayBreach` is written by two, `BecomeLawUnsigned` and `PocketVeto` (`Constitution.tla:383, 392`). |
| 7 | `specs/Government.tla:132-135` | The header names only safety properties for `M_UPHOLD` and `M_HUMPHREY`. The README (lines 608–609) adds "liveness", and `l-a-uphold-struck` and `l-a-humphrey-struck` are COUNTEREXAMPLE. Also: the README says `M_UPHOLD` breaks "the five doctrine properties", but `WillHonoured` breaks only in configuration c (`a-uphold-will` HOLDS, `c-uphold-will` COUNTEREXAMPLE). |
| 8 | README.md:76 and `docs/ASSESSMENT.md` § Strengths, point 2 | The README says "Every flip test fails as required". The assessment says the recorded flips ran under the script's earlier rule, and "the flips have not been re-run under that rule". `scripts/flip_test.py` writes nothing to the tree, so no file records which rule a flip ran under. |
| 9 | README § `SenateRules.tla`, Abstracted (lines 536–540) | Omits four items `specs/SenateRules.tla:104-113` lists: the motion to proceed's own cloture, what may be reconciled, cloture on a reconciliation bill, the House. The section's prose names 2 of the 8 witnesses. |
| 10 | README § `Executive.tla`, provisions table | "Two-thirds of the Senate" for treaties; the header (`Executive.tla:60`) says "two-thirds of the Senators present". The header's ABSTRACTED paragraph (lines 142–154) also lists items the README's does not. |

## Reported by the drawing agents, not re-checked

- `docs/ASSESSMENT.md` § Strengths, point 1 counts "133 of the rows" as inert in Constitution; the rows header's
  list gives 98 cells. The assessment is of four modules, as of `e86e3c9`; some of its line references are stale.
- README § `Constitution.tla`, Rows: "2.8 million states" with all three machines on; the rows header (line 25) says
  "both machines on, … 2,756,172 states".
- README § `Elections.tla`, Proof: "Eleven properties are flags and prove at the one action that sets each"; the
  header gives two setting actions for `ChoiceFromTheList` and for `TwoTermLimit`.
- README and rows header for Elections say two rows are larger; three exceed a million states.
- `docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md` § 2 and § 7.6 say 25 mutations and 25 flip tests; the results
  file runs 24 mutations, and the proof has 26 `Mut #` hypotheses.
- `specs/Elections.cfg` and row `c-cfg-safety` differ in `Persons` and `Eligible`; the rows header says the extra
  persons add no state.
- The module header's LIVENESS in `Judiciary.tla` says "the DEADLOCK row"; there are two.

## Checked and not a finding

- `M_PREROGATIVE` (Executive): the README's "only a statute changes the state of war" names the check the mutation
  removes, and `WarAuthorised`'s added disjunct removes exactly that "only". README and code agree.
