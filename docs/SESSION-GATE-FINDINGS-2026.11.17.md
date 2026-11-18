# What `inSession` gates in Constitution.tla, and what it does not

> Constitution.tla lets a bill be introduced and passed by both Houses while
> inSession = FALSE; neither Introduce nor PassChamber reads it.

(An item in the maintainer's TODO list of 2026.11.17.)

**2026.11.17** · findings · a reading of `specs/Constitution.tla` and
`specs/Government.tla` and nine TLC runs on a scratch copy; nothing in the
tree was changed · prepared by Claude at the maintainer's request · read
against commit `bf8e08f` on `main`: `specs/Constitution.tla` (sha256
`b31449a7bb6d…`, the digest that `results/Constitution-results-2026.11.16.txt`
and `results/Constitution-proof-results-2026.11.17.txt` cite)

---

## 1. Summary

- **The TODO item is right, and the problem is wider than it says.** Four
  actions read `inSession`, apart from `Convene` and `Adjourn`: `Veto`,
  `BecomeLawUnsigned`, `PocketVeto` and `RecessAppoint`. Twelve actions of
  Congress ignore it. These include introduction, passage, override,
  confirmation, consent, impeachment, trial and the proposal of an
  amendment.
- **TLC confirms it.** Each of eight acts of Congress is reachable while
  Congress is adjourned. A control, `Veto`, is not reachable while
  adjourned (§3).
- **Nothing checked or proved is wrong.** No safety property mentions the
  session except `TenDayRule` and `RecessAppointmentsInRecess`, and the
  actions those two depend on do read it (§4). The gap is in the
  documentation. The variable is commented "is Congress sitting?", and the
  header's ABSTRACTED paragraph does not say that sessions gate only two
  things.
- **`Government.tla` does it differently.** Its `Pass` and `Override` both
  require `inSession`, so the two modules disagree about whether an
  adjourned Congress can legislate. No mutation removes Government's two
  guards, so nothing checks that they matter (§5).
- **Recommendation: document the abstraction rather than add guards (§6).**
  The plan is in `docs/SESSION-GATE-PLAN-2026.11.17.md`.

---

## 2. What reads `inSession`

| Action | Reads `inSession` | How |
|---|---|---|
| `Convene`, `Adjourn` | yes | guard, and the only writers |
| `Veto` | yes | guard: a bill is returned only to a sitting Congress |
| `BecomeLawUnsigned` | yes | guard (removed by `M_NO_POCKET`), and the `tenDayBreach` flag |
| `PocketVeto` | yes | guard (removed by `M_POCKET_SITTING`), and the `tenDayBreach` flag |
| `RecessAppoint` | yes | `SenateInRecess` (removed by `M_PRO_FORMA`), and the `recessWhileSitting` flag |
| `Introduce`, `PassChamber` | no | |
| `Override`, `FailOverride` | no | |
| `ConfirmVP`, `RejectVP` | no | |
| `Consent`, `Reject` | no | |
| `Impeach`, `Convict`, `Acquit` | no | |
| `ProposeByCongress` | no | |

The other actions are not acts of Congress, so the session is irrelevant
to them. They are `Sign`, `Elect`, `NominateVP`, `Nominate`, the vacancy
and resignation steps, `ProposeByConvention` and `Ratify`.

In practice, then, `inSession` is not "is Congress sitting?". It answers
two narrower questions: can a bill be returned, and is the Senate in
Recess.

---

## 3. What TLC shows

A scratch module, `SessionProbe`, extends an unmodified copy of
`Constitution.tla` (same digest) with one action property per act. Each
property says the act never happens while `~inSession`. If the act is
reachable while adjourned, TLC reports the property violated. The
constants are the row list's defaults, with each run switching on only
the machine it needs, as the row list does. Appendix A has the module and
the command.

| Property | Act | Result | Distinct states |
|---|---|---|---|
| `NeverIntroducedAdjourned` | `Introduce` | violated | 6 when it stopped |
| `NeverPresentedAdjourned` | `PassChamber` presenting the bill | violated | 92 when it stopped |
| `NeverOverriddenAdjourned` | `Override` making the bill law | violated | 2,878 when it stopped |
| `NeverVPConfirmedAdjourned` | `ConfirmVP` | violated | 215 when it stopped |
| `NeverConsentAdjourned` | `Consent` | violated | 143 when it stopped |
| `NeverImpeachedAdjourned` | `Impeach` | violated | 31 when it stopped |
| `NeverConvictedAdjourned` | `Convict` | violated | 157 when it stopped |
| `NeverProposedAdjourned` | `ProposeByCongress` | violated | 9 when it stopped |
| `NeverVetoedAdjourned` (control) | `Veto` | **holds** | 13,644 |

The control's 13,644 states equals the count in the committed `p-` rows
for the legislative machine, which confirms the probe explores the same
space as the row list.

The two legislative traces:

- **Passage.** Initial state (sitting) → `Adjourn` → `Introduce` →
  `PassChamber` (House of origin) → `PassChamber` (the other House; the
  bill is presented). Congress is adjourned at every step after the first.
- **Override.** The bill passes and is presented while Congress sits → a
  President is elected → `Veto` (sitting) → `Adjourn` → `Override` (House
  of origin) → `Override` (the other House; the bill is law). Congress is
  adjourned throughout the override.

In the passage trace, a `Sign` is then enabled, because `Sign` does not
read the session. Such a bill becomes law without Congress ever sitting
after it was introduced.

---

## 4. Why nothing checked or proved is wrong

The thirteen safety properties fall into two groups.

- **`TenDayRule` and `RecessAppointmentsInRecess`** are about the session.
  The actions that could break them read it: `BecomeLawUnsigned` and
  `PocketVeto` for the first, `RecessAppoint` for the second. Each guard
  has its mutation, and each mutation has its COUNTEREXAMPLE row.
- **The other eleven** (`Bicameralism`, `Origination`, `Presentment`,
  `Incompatibility` and the rest) say nothing about when an act happens.
  Each is true or false in a state whatever the value of `inSession`.

Adding `inSession` to the guards of the twelve actions in §2 would remove
behaviours and add none. Every invariant would still hold, and every
`Next` lemma in `Constitution_proof.tla` would still go through, with one
more conjunct in each affected action's hypotheses. That is argued, not
run (§7).

So the results files and the proof are accurate about the module. What is
missing is a statement that the module lets an adjourned Congress act.

### What the text says, briefly

No single clause of the Constitution says a House acts only while sitting.
The closest are these:

- **Art. I §5 cl. 1:** a majority "shall constitute a Quorum to do
  Business". The module already abstracts quorum away.
- **Art. I §5 cl. 4:** neither House may adjourn for more than three days
  without the other's consent. One `inSession` for both Houses cannot
  express this, and so cannot express a Senate in recess while the House
  sits. `SenateInRecess` reads the Congress-wide flag.
- **Art. I §7 cl. 2:** the pocket-veto clause ("unless the Congress by
  their Adjournment prevent its Return") is the one place where the
  session decides an outcome. The module models it.

One modelling detail matters for any guard. `PassChamber` merges the
second House's passage with presentment. In practice, presenting an
enrolled bill after Congress adjourns is common and lawful; passing it
while adjourned is not. A guard on `PassChamber` would forbid both.
Nothing that can be reached is lost, though: the order `PassChamber`,
`Adjourn`, then `PocketVeto` gives the same states.

---

## 5. Government.tla gates what Constitution.tla does not

`Government.tla` models the same session with the same name (`inSession`,
commented "is Congress sitting?"). There, `Pass` (line 646) and `Override`
(line 698) both require it, as do `Veto`, `PocketVeto` and `Lapse`, the
last through `CanReturn`.

That leaves two discrepancies:

1. **The modules disagree.** In `Government.tla` an adjourned Congress
   cannot pass a bill or override a veto. In `Constitution.tla` it can.
   Neither header says so.
2. **Government's two guards are untested.** The method makes every check
   a guard that one mutation removes, and requires that removal to break a
   property. No mutation removes `inSession` from `Pass` or `Override`, and
   no property says passage happens only in session. TLC has never been
   shown that either guard changes anything. This was not investigated
   further.

---

## 6. Options

| Option | What it changes | Cost | Assessment |
|---|---|---|---|
| **1. Document** (recommended) | Comments in `Constitution.tla`'s header and on the variable; one sentence in the README | the digest changes, so both Constitution results files regenerate with identical rows and obligation counts | Makes the claim accurate. Changes no behaviour. |
| 2. Guard, with a property and a mutation | `inSession` on the twelve actions; a flag such as `adjournedAct`; a property `ActsInSession`; a mutation `M_ADJOURNED_ACT` | new rows, a new theorem, a flip test, and every results file regenerated | The property would restate its own guard. That is limit 1 in `docs/ASSESSMENT.md` and an open TODO item. It would add a row that proves the model and says nothing new about the text. |
| 3. Guard, without a property | `inSession` on the twelve actions | the same regeneration as 2, with changed state counts | A guard that no mutation removes, which is the method's anti-pattern and Government's situation in §5. |
| 4. Model each House's sitting | two session variables, Art. I §5 cl. 4's consent rule, `SenateInRecess` on the Senate's flag only | a module rework | The faithful version, and the only one that could express a Senate recess while the House sits. Larger than this finding warrants on its own. |

Option 1 is the only one that fixes the inaccuracy without adding a
property whose sole content is the guard it restates. If the maintainer
later wants sessions modelled, option 4 is the version worth building, and
it would be a separate piece of work.

---

## 7. What was not checked

- The probe ran TLC v1.7.4 (`tools/tla2tools.jar`, TLC2 2.19, rev
  `5a47802`) on an arm64 laptop, not in the tla-kit image. It wrote nothing
  to `results/` and added no rows.
- §4's claim that adding the guards would leave every invariant, witness
  and proof intact is argued from the definitions, not run. In particular,
  no `Never…` witness was rerun with the guards added.
- Government's two guards (§5) were not mutated. Whether removing them
  changes any property is open.
- §4's reading of the text is a modeller's reading, not legal advice.

---

## Appendix A. Reproducing §3

Copy `specs/Constitution.tla` into a scratch directory and add this module
beside it:

```tla
---- MODULE SessionProbe ----
EXTENDS Constitution
NeverIntroducedAdjourned ==
  [][~(\E b \in Bills, c \in Chambers : Introduce(b, c) /\ ~inSession)]_vars
NeverPresentedAdjourned ==
  [][~(\E b \in Bills, c \in Chambers : \E n \in VotesIn(c) :
         PassChamber(b, c, n) /\ ~inSession /\ bill'[b].status = "Presented")]_vars
NeverOverriddenAdjourned ==
  [][~(\E b \in Bills, c \in Chambers : \E n \in VotesIn(c) :
         Override(b, c, n) /\ ~inSession /\ bill'[b].status = "Law")]_vars
NeverVPConfirmedAdjourned ==
  [][~(\E h \in VotesIn("House"), s \in VotesIn("Senate") : ConfirmVP(h, s) /\ ~inSession)]_vars
NeverConsentAdjourned ==
  [][~(\E o \in Offices, n \in VotesIn("Senate") : Consent(o, n) /\ ~inSession)]_vars
NeverImpeachedAdjourned ==
  [][~(\E p \in Persons, n \in VotesIn("House") : Impeach(p, n) /\ ~inSession)]_vars
NeverConvictedAdjourned ==
  [][~(\E p \in Persons, n \in VotesIn("Senate"), dq \in BOOLEAN : Convict(p, n, dq) /\ ~inSession)]_vars
NeverProposedAdjourned ==
  [][~(\E a \in Amendments, h \in VotesIn("House"), s \in VotesIn("Senate") :
         ProposeByCongress(a, h, s) /\ ~inSession)]_vars
NeverVetoedAdjourned ==
  [][~(\E b \in Bills : Veto(b) /\ ~inSession)]_vars
====
```

Each run's config takes the row list's default constants (`Persons = {h1,
s1, p1, p2}`, `House = {h1}`, `Senate = {s1}`, `Eligible = {p1, p2}`,
`States = {t1, t2, t3, t4}`, `NoOne = NoOne`, `Mut = "none"`) and sets
the rest of the constants by machine:

- **Legislative runs:** `Bills = RevenueBills = {b1}`, everything else
  empty.
- **`Consent`, `Impeach` and `Convict` runs:** `Offices = {o1}`.
- **`ConfirmVP` run:** every machine empty.
- **Proposal run:** `Amendments = SuffrageAmendments = {a1}`.

Each config has `SPECIFICATION Spec` and one `PROPERTY`. Run them with the
flags `scripts/tlc_rows.py` uses for a PROPERTY row:

    java -XX:+UseParallelGC -Xmx2g -cp <repo>/tools/tla2tools.jar tlc2.TLC \
      -config <run>.cfg -workers 1 -deadlock -fp 0 -metadir "$PWD/meta" SessionProbe.tla
