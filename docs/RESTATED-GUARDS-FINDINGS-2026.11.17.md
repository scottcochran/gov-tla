# Do the proved properties restate their own guards, and is that a `sorry`?

> What do you think of the criticism that gov-tla's most proved properties
> restate their own guards.
> Is it the same as Lean's "sorry"?
> Write this up as a derived doc

(The maintainer's questions of 2026.11.17.)

**2026.11.17** · findings · a derived document: a reading of the five
modules, their proof modules and the committed results files, and one
scratch TLC experiment; not a change to the tree and not evidence ·
prepared by Claude at the maintainer's request · read against commit
`bf8e08f` on `main`: `specs/Constitution.tla` (sha256 `b31449a7bb6d…`),
`Judiciary.tla` (`08090cdddea2…`), `Executive.tla` (`8c1d836f4408…`),
`Government.tla` (`36200c8223b9…`), `Elections.tla` (`87692583cde1…`),
their `_proof.tla` modules, and the five
`results/*-proof-results-2026.11.17.txt`

---

## 1. What this is

The criticism is limit 1 of [`ASSESSMENT.md`](ASSESSMENT.md): "Most
proved properties restate a guard the module itself wrote." This note
counts how many do, says what the criticism gets right and what it misses,
reports one experiment on a weakness it does not mention, and answers
whether a restated guard is the same thing as a `sorry` in Lean.

The short answers:

- **The criticism is accurate.** In the four procedural modules, 49 of
  62 safety properties are inductive with the type invariant alone: one
  guard decides each (§3).
- **It is aimed at the proofs and belongs to the properties.** A rule of
  the form "X may happen only when Y" has no content beyond its guard,
  whatever proves it (§4). What the proofs add is in their hypotheses, not
  their statements (§5).
- **It understates one thing.** A flag property sees only the actions
  that write the flag. A second route to the same outcome leaves it
  proved (§6, checked by TLC on a scratch copy).
- **It is not a `sorry`.** A `sorry` is a missing proof of a statement
  that may be false. A restated guard is a complete proof of a statement
  that is true and says little (§7).

Nothing here decides anything. §8 lists changes the maintainer may want.
The scratch runs used the pinned TLC jar (`tools/TLC-PIN`, sha256
`936a2620…`, compared after download) on copies outside the tree. No
module, row list or results file was changed, and the prover was not run.

---

## 2. What "restates a guard" means here

The README names three kinds of local property. All three get their truth
from one guard:

- **A flag.** `BecomeLawUnsigned` is guarded by
  `Mut = "M_NO_POCKET" \/ inSession` and sets
  `tenDayBreach' = (tenDayBreach \/ ~inSession)`
  (`specs/Constitution.tla:369-373`). `TenDayRule == ~tenDayBreach`.
  Under `Mut # "M_NO_POCKET"` the step is propositional: the guard gives
  `inSession`, so the flag stays down.
- **A record written once.** `JuryAndVenue` reads `case[x].jury` and
  `case[x].venue`, which `Decide` writes under `TrialByJury(jury)` and
  `TriedWhereCommitted(...)`, and no later step rewrites.
- **A state predicate whose step is the guard.** `Bicameralism` says a
  presented bill has `passed = Chambers`, and `PassChamber` sets the
  status to `"Presented"` exactly when `BothHouses` holds.

In each case the theorem `Spec => []P` says that the action which could
break `P` checks that it does not. The module wrote both halves.

---

## 3. A count

Each proof module's header says, in prose, which properties are inductive
as stated and which need more. The table sorts the safety properties by
that prose. "Alone" means the inductive invariant is the property and the
type invariant, with nothing added.

| Module | Safety properties | Flags, inductive alone | Not flags, inductive alone | Need more |
|---|---|---|---|---|
| `Constitution.tla` | 13 | 4 | 5 | 4 |
| `Judiciary.tla` | 18 | 4 | 10 | 4 |
| `Executive.tla` | 12 | 2 | 7 | 3 |
| `Elections.tla` | 19 | 11 | 6 | 2 |
| Total | 62 | 21 | 28 | 13 |

So 49 of 62, about four in five, are decided by one guard. The thirteen
that need more:

- **`Constitution.tla`**: `Incompatibility` (`IncompatPW`),
  `Disqualification` (`DisqPW`), `PresidentNotVP` (`PresidentNotVPInv`),
  and `CongressNotImpeachable`, which rests on `IncompatPW`.
- **`Judiciary.tla`**: `BenchFitsSeats` (`EmptyWhenAbsent` and the
  cardinality lemmas), `JudgesAreNotInCongress` and
  `DisqualifiedDoNotSit` (every pending nominee passed the test),
  `ChiefJusticeSits` (the Supreme Court exists and keeps its tier).
- **`Executive.tla`**: `Disqualification` (`DistinctOffices`),
  `NoCongressionalAppointment` (`CongressVestingOK`),
  `CongressDoesNotRemoveExecutors` (`ExecutionIsExecutive`).
- **`Elections.tla`**: `PledgesBind` (`BallotNeedsPledge`) and
  `CountCanClose` (`TwoNamesOnBallots` and the pigeonhole).

Three qualifications on the table:

- **Two flags are not trivial.** `ElectorsChoose` and
  `DevolvesOnlyWithoutMajority` are flags whose guard is a count. They
  are inductive alone, but their steps rest on the cardinality lemmas
  (`Sizes`, `VoteSizes`, `DisjointVotes`, `MajorityCarries`).
- **Two flags need a strengthening.** `Executive.tla` has four flag
  variables. Two of the properties over them are in the last column, not
  the first.
- **`Presentment` is half flag.** One conjunct is `~shortOverride`; the
  other reads the bill record. It is counted as not a flag.

`Government.tla` does not sort this way and is left out of the table. Its
proof has one invariant, `Shape`, under every mutation. Of the 23 local
state properties it proves:

- nine are flags, read off the sets `breaches` and `stray` (`FlagInv`);
- eleven are part of `Shape` or follow, in the header's words, "in one
  state step, from Shape and a fact about the text", that is, from the
  founding edge list as amended;
- three carry their own invariant (`EdgesConnectLiveNodes`,
  `OfficesAreLive`, `ExecutorsAreRemovable`).

The eleven are not restated guards. They are facts about a hand-written
list, which is limit 3 of the assessment and a different complaint. The
five global forms are checked by TLC and not proved.

---

## 4. Why a single-step rule can only be a guard

Most of what the modules encode has the form "X may happen only when Y":
a bill becomes law unsigned only while Congress sits, a treaty is ratified
only by two-thirds, a conviction only by two-thirds. A rule of that form
can be written three ways:

- as a guard on X and a flag that records a step taken without Y;
- as a record of Y written at X and read later;
- as an action property, `[][X => Y]_vars`.

All three are the guard. No choice of prover or proof style changes that,
because the rule has no consequence to derive: it is a precondition and
nothing else. The criticism is therefore about which properties were
chosen, not about how they were proved.

The properties that are not of that form are predicates over state that
several actions touch: who holds office, who sits on which bench, what
the ballots say. Eleven of the thirteen in the last column of §3 are of
this kind; the other two are the `Executive.tla` flags whose guard reads
state another action wrote. Some in the third column are of this kind
too: `NoJudgeOnTwoCourts` is inductive alone only because both
confirmations re-check. The findings with content came from here: a
nominee convicted or seated elsewhere between nomination and
confirmation (`M_VP_RECHECK` against `Disqualification`,
`M_CHIEF_RECHECK` against `NoJudgeOnTwoCourts` and `BenchFitsSeats`),
and the `M_SAMEPERSON` correction.

---

## 5. Where the information is

The theorem statements carry little. The hypothesis lists carry more.
Each theorem assumes `Mut # "M_X"` for exactly the mutations that break
its property, and `scripts/flip_test.py` requires the proof to fail when
one is flipped. That makes each list a checked claim about which guards a
property rests on. A proof of a restated guard still checks the author's
belief about the module, and on the record it corrected or sharpened that
belief three times:

- `Executive.tla`'s `M_SAMEPERSON` also breaks `Disqualification`. The
  expected-results line had not listed it; a failed proof step pointed
  there, and TLC then confirmed it.
- `M_PRE_XII` and `M_PLURALITY` hold `CountCanClose` at two candidates
  and break it at three, so two HOLDS cells were artefacts of the
  constants. The rows file had already added three-candidate rows; the
  hypothesis list says it at every number of candidates.
- `CollegeWF`, that `Binding` lies within `Electors`, is load-bearing for
  `PledgesBind`. The note written before the proof did not list it, and
  nothing in the rows could have shown it.

These are corrections to what the author thought the model did. None is a
finding about the Constitution. That is the true core of the criticism,
and the assessment already says it: the matrix "records the module's own
choices, not facts about the law".

---

## 6. What the criticism understates: a flag sees only its own action

A flag property is weaker than a state predicate in a way that has
nothing to do with insight. `FlagFrame` (`specs/Elections_proof.tla:289`)
states it as a lemma: each flag is changed by one action, two for
`offList` and `thirdTerm`, and every other step leaves it alone. So an
action added later, which reaches the forbidden outcome by another route
and does not write the flag, leaves the property proved.

### 6.1 What was tried

Two scratch copies of `Constitution.tla`, run at the constants of the
`p-none-tenday` row (legislation on, the other two machines empty), with
`Mut = "none"`.

- **Base.** The module with one definition added, the ten-day rule as an
  action property over every step:

      TenDayRuleStep ==
        [][\A b \in Bills :
             (bill[b].status = "Presented" /\ bill'[b].status = "Law"
                /\ bill'[b].how = "Unsigned") => inSession]_vars

- **Second route.** The base, plus one action added to `Next`: an
  unreturned bill becomes law while Congress is adjourned, written
  without the session check and without the flag.

      LapseAnyway(b) ==
        /\ bill[b].status = "Presented"
        /\ ~inSession
        /\ bill' = [bill EXCEPT ![b].status = "Law", ![b].how = "Unsigned"]
        /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend, flagVars>>

| Copy | `TenDayRule` (the flag) | `Safety` | `TenDayRuleStep` | Distinct states |
|---|---|---|---|---|
| base | HOLDS | HOLDS | HOLDS | 13,644 |
| second route | HOLDS | HOLDS | VIOLATED, by a six-state trace | 13,644 |

The base count is the committed row's (`p-none-tenday`, 13,644 distinct
states in `results/Constitution-results-2026.11.16.txt`).

### 6.2 What it shows

- **The flag does not see the second route.** A bill becomes law
  unsigned with Congress adjourned, which is what the ten-day rule
  forbids, and `TenDayRule` and all of `Safety` still hold.
- **No state predicate over the existing variables could see it.** The
  second route reaches no new state: 13,644 in both copies. A bill that
  is law unsigned with Congress adjourned is already reachable lawfully,
  by `BecomeLawUnsigned` and then `Adjourn`. The breach is in the step,
  not in any state.
- **An action property sees it.** `TenDayRuleStep` reads what changed,
  whichever action changed it. It is the same guard restated, so it adds
  no insight. It adds protection against the module growing.

The proof would not catch the second route either. `NextTenDayRule` would
gain one case, in which `tenDayBreach` is unchanged, and close. This was
not run (§9).

### 6.3 A by-product

The counterexample's first five states use only the module's own actions:
`Adjourn`, `Introduce`, `PassChamber`, `PassChamber`. So the unmodified
module lets a bill be introduced and passed by both Houses while
`inSession = FALSE`. Neither action reads `inSession`. No property says
otherwise, because no guard does. Whether that is intended (the variable
standing only for whether Congress can receive a returned bill) or an
omission is the maintainer's to say; the module header does not. It is an
instance of the point of §4 turned round: a rule nobody wrote as a guard
is a rule nobody checks.

---

## 7. Is it the same as Lean's `sorry`?

No. They are failures of different things.

| | What is wrong | Is the statement true? | Where the risk is |
|---|---|---|---|
| `sorry` | the proof is missing | unknown | the statement may be false, and everything that uses it inherits that |
| A restated guard | nothing in the proof; the statement is weak | yes, in the module | the statement is about the encoding, and reads as if it were about the law |

In Lean, `sorry` closes any goal. The theorem is accepted and is recorded
as depending on the axiom `sorryAx`, which `#print axioms` shows. The
TLAPS counterpart is the leaf proof `OMITTED`, or a statement with no
proof at all.

**There are none here.** A script over the five proof modules, with
comments stripped, finds 449 `THEOREM` and `LEMMA` statements, every one
followed by a proof, no `OMITTED`, and no module-level `ASSUME` or `AXIOM`
in any proof module. The results files report every obligation proved
(1,092, 2,150, 814, 1,563 and 1,121). The check on statements is worth
making separately, because an obligation count says nothing about a
statement that generated no obligation.

The closer Lean analogy to a restated guard is a theorem that closes by
`rfl` or by `simp [myDef]`: fully checked, and true because of how the
definition was written.

What in the repository is nearest to a `sorry` is narrower, and the
README states each:

- **Properties checked and not proved.** The quantified leads-tos
  (`PresentedBillsResolve`, `ActingEventuallyEnds`,
  `UnconstitutionalEdgesAreStruck`) and `Government.tla`'s five global
  reachability forms. These are disclosed gaps with TLC evidence at small
  constants. A `sorry` has no evidence.
- **The named `ASSUME`s on the constants.** These are hypotheses, as a
  Lean theorem's are. Each theorem holds only for constants that satisfy
  them, and each proof header lists which it uses.
- **The prover's trusted base.** This is a third thing, neither a hole
  nor a weak statement. Lean's kernel rechecks every proof term. These
  results files record a `tlapm --cleanfp --strict` run with the backends
  Z3, Zenon, Isabelle and LS4, and the skill's `evidence.md` says what
  that leaves trusted: the front end and each backend's soundness. TLC
  agreeing at small constants is the cross-check, as §8 of the
  [mutation-matrix findings](MUTATION-MATRIX-FINDINGS-2026.11.17.md)
  says.

---

## 8. What follows

For the maintainer to weigh. None of it was done.

- **Say which kind each property is.** The Elections section of the
  README already does: "Eighteen properties are each decided by a check
  at the step that could break them. This one is not." A column in each
  module's table, or the counts of §3, would put the same sentence beside
  every obligation count. Cost: a README edit.
- **Reword the opening claim.** "Prove with TLAPS that the rules hold"
  reads as a claim about rules. For four properties in five of the
  procedural modules it is a claim that the guard is where the header
  says it is. Cost: one sentence.
- **Consider an action-property twin for each flag.** `Government.tla`
  already states and proves two action properties
  (`TextChangesOnlyByArticleV`, `StatutesChangeOnlyByLawOrCourt`), so the
  form has precedent. A twin costs a definition, a row and a
  `Spec => [][A]_vars` theorem per flag, and a module edit that
  regenerates that module's results files. What it buys is §6: a second
  route is caught. It would matter most if the modules are still growing.
- **Put new effort where no guard decides.** This is recommendation 3 of
  the assessment, and §4 says why it is the only remedy: properties that
  span actions or modules, counts and coalitions, and sequences that
  unfold while something is pending. The thirteen properties of §3 and
  `CountCanClose` in particular are the model to copy.

---

## 9. What was not checked

- **The prover was not run.** Every "proved" here is what the committed
  results files of 2026.11.17 say. The claim in §6.2 that the proof would
  not catch the second route is read from the shape of `NextTenDayRule`.
- **The count in §3 follows the proof headers' prose.** It was checked
  against the invariant definitions for `Executive_proof.tla` only. For
  the other three modules a header that understates what its proof uses
  would move a property between columns.
- **The experiment covers one flag in one module.** The argument is the
  same for every flag, since it rests on the frame, but only
  `tenDayBreach` was run.
- **The scratch runs are not rows.** They were run by hand, in a
  container, with the command the mutation-matrix findings give for an
  invariant row (appendix A), and wrote nothing under `results/`.
- **The by-product in §6.3 was not followed up.** It was seen in one
  trace. No row was written for it and the other modules were not read
  for the same pattern.
- **The statement check in §7 is a text search**, not a parse. It splits
  each proof module at `THEOREM` and `LEMMA` and looks for a proof step
  before the next one.
- **Nothing here is a claim about Lean beyond `sorry` and `rfl`.** No
  Lean development of these modules exists in this repository.

---

## Appendix A. Reproducing the experiment

Copy `specs/Constitution.tla` to two scratch directories. In both, insert
`TenDayRuleStep` (§6.1) before the closing `====` line. In the second,
insert `LapseAnyway` before `Next` and add `\/ LapseAnyway(b)` to the
disjunct of `Next` that holds `BecomeLawUnsigned(b)`. In each directory
write three configs that differ in their last line:

    SPECIFICATION Spec
    CONSTANTS
      Mut                = "none"
      Persons            = {h1, s1, p1, p2}
      House              = {h1}
      Senate             = {s1}
      Eligible           = {p1, p2}
      States             = {t1, t2, t3, t4}
      Bills              = {b1}
      RevenueBills       = {b1}
      Offices            = {}
      Amendments         = {}
      SuffrageAmendments = {}
      NoOne              = NoOne
    CONSTRAINT ElectionsBound
    INVARIANT TenDayRule

with `INVARIANT Safety` and `PROPERTY TenDayRuleStep` in the other two.
Then, in that directory, for each config:

    java -XX:+UseParallelGC -Xmx2g -cp <repo>/tools/tla2tools.jar tlc2.TLC \
      -config <name>.cfg -workers 1 -metadir "$PWD/meta" -deadlock Constitution.tla

The violated run ends at `LapseAnyway` in state 6, with
`tenDayBreach = FALSE` and `inSession = FALSE` in every state from the
second.
