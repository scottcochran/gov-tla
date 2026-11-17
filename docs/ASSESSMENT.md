# Assessment: what the TLA+ specs and proofs are good for

A self-assessment by Claude of the four modules, their TLC result tables
and their TLAPS proofs, as of commit `e86e3c9`, the commit that added the
skill. That commit includes all four reworks.

- **Who wrote what.** Claude wrote the modules and proofs in one Claude
  Code session. Claude wrote this assessment in a separate session, which
  had not written them. The prompt was "dont run anything. just read the
  repo and assess the utility of the tla+ specs and proofs". It was not
  asked to be adversarial.
- **The revision.** The session that wrote the specs revised the
  assessment, as listed below, so the revision is not independent of the
  work it reviews.
- **What was checked.** The review was done by reading only. Nothing was
  re-run, so every "HOLDS", "COUNTEREXAMPLE" and "proved" below is what
  the committed results files say, not something this review checked
  again.

Treat it as the model's own reading of its work, not as an outside or
human review.

*Revised after a second reading against the code:*

- *corrected the commit label, a line reference, and the claims about
  what TLC runs and what the flip test showed;*
- *added the findings the first reading left out;*
- *confirmed the* Trump v. Slaughter *holding that limit 4 had left
  unverified;*
- *qualified "true by construction" and the summary of what the proofs
  add.*

*This assessment predates `Elections.tla`. An
[addendum of 2026.11.17](#addendum-20261117-electionstla), by a third
session, covers that module and what has changed since.*

## Summary

As a formal-methods artefact this repository is unusually good. As a
source of insight about the Constitution it adds little. Most proved
properties restate a guard the module itself wrote, so the proofs show the
encoding is internally consistent rather than telling us anything about
the law. The few findings with real constitutional content all involve
something changing while something else is pending (see
[A pattern across the findings](#a-pattern-across-the-findings)), and that
is the most promising direction for further work.

## What is here

| Module | TLC rows (all as expected) | Mutations | Proof obligations (all proved) |
|---|---|---|---|
| `Constitution.tla`: Arts. I, II, V; Amends. XXII, XXV | 302 | 19 | 1,092 |
| `Judiciary.tla`: Art. III | 451 | 23 | 2,150 |
| `Executive.tla`: Art. II, the agencies | 208 | 14 | 814 |
| `Government.tla`: the authority graph | 565 | 14 | 1,563 |

## Strengths

1. **Mutation testing.** Each check the text imposes has a named mutation
   that removes it, usually tied to a real historical alternative (the
   Articles of Confederation, Humphrey's Executor, the 2012 pro forma
   recess appointments, Chisholm v. Georgia). TLC runs every (mutation ×
   property) pair, and each theorem is proved under exactly the mutations
   that TLC refutes it under.

   One caveat is in `Constitution.tla`. There, 133 of the rows that check
   a mutation does *not* break a property switch on only the part of the
   model the property reads. So the mutation in those rows does nothing,
   and only the proof covers those cells. The row list says so.
2. **Checks against vacuous results.** The `Never…` witnesses show each
   behaviour the properties talk about can actually happen. `NoBehaviour`
   shows the fairness assumptions leave some behaviour. `scripts/flip_test.py`
   flips each `Mut # "M_X"` hypothesis and requires the proof to break, so
   no proof survives without the hypothesis it claims to need.

   The recorded flips ran under the script's earlier rule (a failure
   anywhere outside `SafeAlways`), and in each one the property's own
   lemma failed. Some `Judiciary.tla` flips also failed in unrelated
   lemmas, which were timeouts on a loaded machine. The script now requires
   a failure in a statement that carries the flipped hypothesis, and the
   flips have not been re-run under that rule. Most production TLA+ work
   does none of this.
3. **The proofs cover cases TLC cannot.** The `Constitution.tla` rows use
   one Representative and one Senator (`House = {h1}`,
   `Senate = {s1}`, the defaults in `Constitution.cfg` and the row list),
   and at that size two-thirds and a majority are the same vote. The
   threshold mutations still show up in the rows, because they drop the
   threshold altogether and a vote of none then carries. But only the
   TLAPS theorems hold for every size the named ASSUMEs allow, which is
   what the threshold properties need. (`Judiciary.tla`'s `M_CHASE` rows
   use five Senators, so TLC tells the two apart there too.
   `Executive.tla` records a vote as the threshold it meets, so the
   question does not arise there.)
4. **Provenance.** Each results file records the SHA-256 of the modules
   it covers and the pinned tool versions, plus a "Words:" line saying
   what "proved" or "HOLDS" does and does not mean.
5. **Findings with substance:**
   - checks made at nomination but not repeated at confirmation, in
     `Constitution.tla` (`M_VP_RECHECK`) and `Judiciary.tla`
     (`M_CHIEF_RECHECK`);
   - *Ex parte McCardle*: a state invariant "no pending Supreme Court
     appeal is in an excepted head" is false, because Congress may except
     the head while the appeal is pending. The property is now split
     between taking the appeal (`ExceptionsHonoured`) and deciding it
     (`ExceptionsBindPending`), with a new `Dismiss` action;
   - XXV §2 creates a cycle of authority, President → Vice President →
     President, that never passes through the People or the States;
   - the ten-day rule needs fairness on the clock, not on the President,
     because the Presidency can be vacant (`l-president-resolve` is a
     COUNTEREXAMPLE);
   - the proof, not TLC, found that `Executive.tla`'s `M_SAMEPERSON` (one
     person as both President and Vice President) also breaks
     `Disqualification`. Convicting that person passes the presidency to
     themself. The expected-results line had not listed it, and TLC
     confirmed it once the proof's failed step pointed there;
   - `AppealsCourtsAreAppellate`, as first written, failed when a closed
     case's district court was abolished and its identifier re-used for a
     court of appeals. This is a modelling artefact rather than law, but
     another instance of state changing after the fact;
   - `Government.tla`'s re-check of a bill's applicability at enactment is
     redundant: `M_RECHECK` reaches exactly the states of `none`, because
     only one bill is in flight at a time.

## Limits

1. **Most properties are true by construction.** Many are flags. For
   example, `tenDayBreach' = (tenDayBreach \/ ~inSession)` sits in an
   action whose guard is `inSession` (`Constitution.tla:369-375`), and
   `Judiciary.tla`'s `GoodBehaviour` flag is the negation of `Convict`'s
   own guard (`Judiciary.tla:587-589`). Other properties read a record
   field written once, under the guard of the step that writes it. Most
   obligations come from boilerplate per-action case splits, and the
   mutation lemmas are one-line `BY DEF` unfoldings
   (`Constitution_proof.tla:1141-1243`). In `Judiciary_proof.tla:123-141`,
   most invariants are just the property plus type information.

   This is partly by design. The method makes each property local so that
   one guard decides it, and the information is in the "Breaks under"
   matrix (which guard each property rests on), not in the theorem
   statement. The matrix was corrected at least once by a failed proof
   step (`M_SAMEPERSON`, above). Still, the matrix records the module's
   own choices, not facts about the law.

   The proofs with real content are the inductive strengthenings: `IncompatPW`,
   `DisqPW` and `PresidentNotVPInv` in `Constitution_proof.tla`; the
   nominee strengthenings, and `BenchFitsSeats` with its cardinality
   lemmas, in `Judiciary_proof.tla`; and the grant-chain and reachability
   work in `Government_proof.tla`. A large obligation count here means
   volume, not depth.
2. **The legal content lives in the abstractions, which are not checked.**
   An election is one step. A vote is a count, or in `Executive.tla:199`
   just the label `"Fails"`, `"Majority"` or `"TwoThirds"`. Contested
   questions such as "is this a recess?", "does this body execute the
   laws?" or "is this an inferior officer?" are boolean inputs. The models
   cannot reach any question that is open in law; they assume the answers.
3. **`Government.tla`'s structural claims are about a hand-written list.**
   `LegislativePrimacy` counts control edges, so it depends on choices
   such as making impeachment one edge rather than separate House and
   Senate edges (`Government.tla:248-299`). Proving `MutualChecks` mostly
   proves facts about the `Founding` set.
4. **Recent doctrine is encoded as settled.** `UnitaryExecutive` and the
   `M_HUMPHREY` mutations treat *Trump v. Slaughter* (2026) as having
   replaced Humphrey's Executor.

   That holding is now confirmed. The Court decided the case 6–3 on 29
   June 2026, held the FTC commissioners' for-cause protection
   unconstitutional, and overruled *Humphrey's Executor*, while treating
   the Federal Reserve separately
   ([CRS](https://www.congress.gov/crs-product/LSB11448),
   [Venable](https://www.venable.com/insights/publications/2026/06/supreme-court-overrules-humphreys-executor)).
   The model matches: `Executive.tla` abstracts the Federal Reserve away.

   The general point still stands. The encoding fixes one reading of a
   line of cases that is still being worked out for other agencies, and
   it will need revisiting as those cases come down.
5. **The modules are never combined.** Each one models impeachment,
   disqualification and the Presidency in its own way. `Constitution.tla`
   allows several impeachments pending at once, `Executive.tla` one;
   `Judiciary.tla` adds a third version, and no longer requires members
   of Congress to be among `Persons`, which `Constitution.tla` still
   assumes. Nothing checks that the modules agree, or how they interact.
6. **The Judiciary rework traded some fidelity for checkability.** A court
   may now decide a case without any sitting judge
   (`Judiciary.tla:189-198`). That lets TLC check judge-side properties
   with no cases and case-side properties with no persons. The proof
   covers the unsplit spec, so the general claims do not depend on the
   split. But judges and cases are now linked only by `AbolishCourt`'s
   rule against abolishing a court with a live case: the "never combined"
   problem again, inside one module.
7. **Liveness is checked by TLC only**, at small constants; the proof
   modules say so.
8. **Housekeeping.** The four `*_TTrace_*.bin` TLC trace files are
   committed. *(Removed on 2026.11.17; see the addendum.)*

## Do refinement mappings into `Government.tla` fix limit 5?

Only partly. They would show each detailed module is consistent with the
authority graph, not that the detailed modules are consistent with each
other.

**What they would settle.** A proof of
`Constitution!Spec => Government!Spec` would show every detailed step is
an edge firing (or a step Government doesn't see), extending
`EveryActIsAnEdge` to the detailed modules. Writing the mappings would
also expose real disagreements, because Government is specific enough to
reject some detailed behaviours:

- `Constitution.tla`'s `NominateVP` (lines 435-444) has no amendment
  guard, so XXV is always in force. Government starts from 1789 and has
  the `NominateVP` edge only while XXV is ratified.
- `Constitution.tla` allows any number of bills in flight; Government's
  `bill` holds one (`Government.tla:125`).
- `Constitution.tla`'s `impeached` is a set; Government's `trial` is a
  single office (`Government.tla:456`).

**What they would not settle.**

- `Government.tla` has no persons (header, line 166). The cross-module
  questions that matter most are about persons: can someone disqualified
  in one module hold office in another; can a judge also be an executive
  officer; does Incompatibility hold across all offices at once? None of
  these can be stated in Government, so no refinement into it checks them.
- Two modules can each refine Government while disagreeing on everything
  it abstracts away.
- A mapping can hide a disagreement, for example by choosing one member
  of the impeached set to be Government's `trial`.
- The proofs would need step simulation and history variables, which is
  far more work than the current invariant proofs.

**What would settle it.**

1. Agree on one meaning for impeachment and trial, Presidential vacancy
   and succession, XXV, sessions and disqualification.
2. Write one combined spec in which shared state (`president`,
   `vicePresident`, `impeached`, `disqualified`, `inSession`, and every
   officeholder, judges included) is a single variable and every module's
   actions are steps of one `Next`. State and check properties across
   modules: Incompatibility and Disqualification over every office, and
   no one holding two offices across branches.
3. Then refine that combined spec into `Government.tla`.

Assume–guarantee reasoning, where each module states and discharges its
assumptions about the shared variables, is a lighter alternative to step 2.

## A pattern across the findings

Every finding with constitutional content is about something changing
while something else is pending:

- a nominee convicted or seated elsewhere between nomination and
  confirmation;
- Congress removing jurisdiction while an appeal is pending (McCardle);
- a presented bill whose fate turns on whether Congress is sitting when
  the ten days run out;
- a court identifier re-used after the court's case was closed
  (`AppealsCourtsAreAppellate`, a modelling artefact).

Seat reductions taking effect only as seats fall vacant (`M_SHRINK`)
belong to the same family, but as a rule the model encodes, not a
finding.

Checks of single-step rules produced little comparable. The exception is
`M_SAMEPERSON`: a single conviction step, made interesting by a state
(one person in two offices) that a guard elsewhere is meant to exclude.

## Usefulness by audience

- **Teaching formal methods** (mutation-backed specs, inductive
  strengthening, guarding against vacuous results): **high**. It is a good
  example to copy.
- **Teaching how the Constitution is structured:** **moderate.** The
  posters, the XXV cycle, McCardle and the ten-day liveness result are
  good material.
- **Analysing the Constitution or doctrine:** **low.** Apart from the
  pending-step findings, the properties restate the text as encoded.
- **What the proofs add beyond TLC:** real but narrow:
  - the threshold properties, which the one-member TLC configurations
    cannot tell apart;
  - every constant the named assumptions admit, rather than the row
    lists' few;
  - the cells TLC leaves unexercised in `Constitution.tla`;
  - one correction to the "Breaks under" matrix (`M_SAMEPERSON`).

## Recommendations

1. Write more properties about sequences that unfold while something is
   pending, rather than more single-step rules. That is where every
   substantive finding has come from.
2. Build the combined spec described above, then refine it into
   `Government.tla`.
3. Ask questions whose answer is not written into a guard. For example:
   the smallest coalition of members and States that can remove a judge,
   entrench a rule, or keep an acting officer indefinitely; or which
   sequences of vacancy, impeachment and recess reach a state nobody
   intended.
4. Remove the committed `*_TTrace_*.bin` files. *(Done on 2026.11.17.)*

## Addendum, 2026.11.17: `Elections.tla`

Everything above is about four modules at commit `e86e3c9`. This addendum
reads the fifth, `Elections.tla`, with its row list, its proof module and
the findings note beside this file, at commit `bf8e08f`.

- **Who wrote it.** Claude, in a third session, which wrote neither the
  modules nor the assessment above.
- **Why.** The maintainer had asked whether the repository was worth
  posting about, and then for a cleanup before posting. This addendum is
  part of that cleanup, so it was written with a reason to make the
  repository look ready. Read it with that in mind.
- **What was checked.** Reading only. The one thing run was
  `scripts/proof_sync.py`, which reports every results file IN SYNC with
  the tree and the pins. No row and no proof was re-run.

### What is there now

| Module | TLC rows (all as expected) | Mutations | Witnesses | Proof obligations (all proved) |
|---|---|---|---|---|
| `Elections.tla`: Art. II §1; Amends. XII, XX, XXII | 579 | 24 | 24 | 1,121 |

With the four above that is 2,105 rows, 94 mutations and 6,740
obligations. The counts are the results files' own: each file's rows
marked "as expected", and each proof file's "Result:" line.

### The summary still holds, with one exception

Eighteen of the nineteen safety properties are true by construction, as
limit 1 describes. Eleven are flags: `lateAppointment` is raised in
`Appoint` by the negation of `Appoint`'s own guard (`Elections.tla:498`,
with `AppointmentOpen` at `:402`). Seven are state predicates that one
guard decides.

`CountCanClose` (`Elections.tla:822`) is the exception, and the first
property in the repository of the kind recommendation 3 asked for. No
guard says that some result can always be announced. It holds because
two majorities of the same electors share an elector, and that elector's
ballot names two persons. The proof is a pigeonhole over the electors
counted (`Pigeonhole` and `ClosesUnderInv` in `Elections_proof.tla`),
and it holds for every finite college and any number of candidates.

That proof also corrected the rows. `M_PRE_XII` and `M_PLURALITY` leave
`CountCanClose` standing at two candidates and break it at three, so two
HOLDS cells were artefacts of the constants. A HOLDS at small constants
is weaker evidence than a table of them suggests.

### The limits, read against the new module

- **Limit 2, the abstractions, applies with more force.** The module
  leaves out competing slates, the one-fifth of each House needed to
  object, the House's delegations, the calendar, and who decides a
  qualification. Those are where the contested questions about a count
  have been. It also fixes three readings, which its header states. The
  proved `ChoiceFromTheList` is about the guard `c \in pList`; nothing
  checks that `PTop`, with its rule for ties, is what "the highest
  numbers not exceeding three" means, and the rows cannot tell three
  highest from four.
- **Limit 5, the modules are never combined, is now about five.**
  `Elections.tla` is a fourth account of the Presidency. It does put one
  disagreement on the record: `M_XXII_SERVICE` is, in its header's words,
  the term limit "as `Constitution.tla`'s `TermAllowed` does"
  (`Constitution.tla:283` counts elections only). So `Constitution.tla`
  proves `TwoTermLimit` of a rule that `Elections.tla` lists as a
  mutation of the text. `Constitution.tla`'s header says the two-years
  clause is abstracted; the README's "Abstracted" list for that module
  does not.
- **Limit 7, liveness, has its first exception.** `ExecutiveIsFilled` is
  proved, under `FairSpec` and without `M_NO_STATUTE`, by one WF1 step.
  Its leads-to has no quantifier, which is why. The other three are
  still checked only. That the weaker fairness conditions fail, and that
  `FairSpec` has a behaviour at all, are TLC's results at small
  constants.
- **Limit 8 is gone.** The trace files are removed.

### The pattern across the findings no longer covers them all

Some of the `Elections.tla` findings are of the pending kind: the whole
number of electors changes while the count is open, and noon can strike
before a President elect has qualified. Others are not. `CountCanClose`
under a plurality rule, and the quorum mutations that bind at five
States and not at four, are arithmetic over thresholds. That is a second
source of findings, and the one the proofs are best placed to work,
since TLC sees a threshold only at the sizes a row uses.

None of the findings is offered here as new to election law. That an
elector held not lawfully certified leaves the whole number appointed is
the statute's own rule, as the module cites it (3 U.S.C. §15(e)(2)). This
reading did not search the literature for the others.

### Two things a reader of the evidence should know

- **The flip tests leave no file.** The README says every flip fails as
  required. `scripts/flip_test.py` writes nothing to the tree, by
  design, so that sentence and §7.6 of the findings note are the only
  record. (The note says 25 flips for `Elections.tla`; the module has 24
  mutations and `none`.) The assessment above recorded that the four
  modules' flips ran under the script's earlier rule. Nothing in the
  tree says whether they were run again after the prover pin moved on
  2026.11.17.
- **The proofs are written to rules, not scanned.** The method's
  `references/prover-habits.md` describes two unsound cases in the
  prover's translation, reported upstream as tlapm #309 and #310. As
  read on 2026.11.17, #309 is closed as completed and #310 is open. The
  findings note says of these proofs that they are "written to the
  method's rules but unscanned". Whether the pinned build `ff40755`
  carries either fix, this reading did not establish. The method asks a
  project in that position to say so where it names its prover, and the
  README does not yet.

### Usefulness by audience, revised

- **Teaching formal methods:** still **high**, and higher. The module
  adds a worked cardinality proof, a leads-to proved without a measure,
  and a case of a proof correcting the row list's expectations.
- **Teaching how the Constitution is structured:** **moderate**, with
  better material than before: election by rejection, the statute that
  keeps the office filled, and the count that always closes.
- **Analysing the Constitution or doctrine:** still **low**. The
  findings hold of the encoding, with competing slates and the grounds
  of objection abstracted away.

### Recommendations, revised

1. Recommendations 1 and 3 are partly taken up. More properties like
   `CountCanClose`, whose truth no guard states, are what would move the
   third rating.
2. Recommendation 2, the combined spec, is untouched and now larger.
   Short of it, either give `Constitution.tla` the two-years clause or
   name the clause in the README's list of what that module abstracts.
3. Keep a dated file of each flip run in `results/`, as the rows and the
   proofs have.
4. State in the README, beside the prover's name, that the proofs are
   written to the method's rules for the two translation cases and are
   not scanned for them.
