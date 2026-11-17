# Where the Elections row list spends its 71 minutes, and two ways of cutting its largest row

> What is causing the space explosion on Elections.tla? Is the Mutation Matrix?
> Is there a way to split Elections.cfg into a breadth depth pair?
> Try "at most one death" on the product row.
> How do these findings inform the proof effort for Elections.tla?

(The maintainer's questions of 2026.11.17, after the CI run for PR 9 spent
71 minutes on `rows/Elections-rows.txt`.)

**2026.11.17** · findings · a reading of one CI log and three scratch TLC
runs, not a change to the tree · prepared by Claude at the maintainer's
request · read against commit `4cc473b` on `main`: `specs/Elections.tla`
(sha256 `87692583cde1…`), `rows/Elections-rows.txt` (sha256
`7e3cdb2b3bc3…`), `results/Elections-results-2026.11.16.txt`, and the log
of CI job `tlc (Elections)` in run 43984352598

---

## 1. What this is

The Elections row list is the slowest thing CI does. This note says where
its time goes, names the pattern responsible, and reports two experiments
on the single largest row: splitting its constants into a "breadth" row and
a "depth" row, and bounding it with a state constraint. Both experiments
ran the pinned TLC (`tools/TLC-PIN`, tla2tools v1.7.4) on scratch copies
outside `results/`. Nothing in the tree was changed; no results file was
written or regenerated.

The timings in §3 are reconstructed, not measured directly: the CI log
timestamps each row as it completes, `scripts/tlc_rows.py` runs rows in a
pool of two workers dispatched in file order, so each row's start is the
completion of the row two slots before it. The reconstruction sums to
139.8 minutes of slot time against a measured 70.7 minutes of wall clock,
which is what two workers predict. The timings in §4 and §5 are from a
laptop and compare with each other, not with CI.

Nothing here decides anything. §4 is a change the maintainer may want; §5
is one they probably do not; §6 is the larger change neither experiment
touches; §7 says what the findings meant for the proof module Elections
did not yet have, and what the proof then showed; §8 says what the proof
means for the matrix; §9 answers three questions the maintainer asked
afterwards.

---

## 2. The pattern: MutationMatrix

Every module in this repository checks its properties the same way. Each
mutation `M_X` removes one guard. For each mutation, and for each set of
constants at which its check binds, the row list has one row per property:
TypeOK, the property the mutation is expected to break (COUNTEREXAMPLE),
and every other property (HOLDS). A row is one TLC launch with one
INVARIANT or PROPERTY in its config. The results file then has one line
per cell, and each line attests one verdict about one property under one
mutation.

Call this the MutationMatrix pattern: the grid of (mutation × property ×
constants), one launch per cell. It is deliberate. The header of
`rows/Elections-rows.txt` says why: "a HOLDS in its block says the mutation
is live and leaves that property alone", and the unmutated `c-` rows at the
same constants say "a COUNTEREXAMPLE in a mutation's block is the
mutation's and not the constants'". Each cell is independently
attributable and independently rerunnable with `--only`.

What the pattern costs is that TLC explores the whole reachable state space
on every launch, whichever invariant it is checking. The twenty rows of one
mutation's block explore the same space twenty times. The results file
shows this directly: every row in a block reports the same distinct state
count.

For Elections the grid is 25 mutations, 20 properties (TypeOK plus
nineteen), and about a dozen constant sets, giving 490 `m-` rows out of
579.

---

## 3. Where the time goes

### 3.1 No single row is large

The row list's default constants give 38,180 states. A mutation row
explores between 38,000 and 122,000 states and takes 8 to 23 seconds. Only
three rows exceed a million states, and one witness row, which TLC stops
at its counterexample without recording a count, is slow for its depth:

| Row | States | Slot time |
|---|---|---|
| `c-cfg-safety` (the constants of `Elections.cfg`) | 2,060,728 | 9.3 min |
| `w-offsenatelist` (five electors, three candidates) | not recorded | 6.2 min |
| `c-three-safety` (three candidates) | 1,301,661 | 4.6 min |
| `p-none-canclose-3` (three candidates) | 1,301,661 | 4.5 min |
| next largest (`c-four2-safety`) | 178,946 | 0.6 min |

Those four rows together are 25 of the 140 minutes.

### 3.2 The grid is the rest

| Row group | Rows | Slot time | Share |
|---|---|---|---|
| `m-` mutation × property | 490 | 102.8 min | 74% |
| `c-` unmutated at each constant set | 32 | 20.3 min | 15% |
| `p-` every property unmutated | 20 | 7.6 min | 5% |
| `w-` reachability witnesses | 25 | 7.3 min | 5% |
| `l-`, `s-`, `t-`, `d-` | 12 | 1.8 min | 1% |
| Total | 579 | 139.8 min slot, 70.7 min wall | |

### 3.3 Each launch has a fixed cost

A least-squares fit of median row time against distinct states, over the
invariant rows grouped by state count, gives

    time ≈ 4.2 s per launch + 0.13 s per 1,000 states

The 4.2 seconds is JVM start, class loading and TLC's parse of the module
before any state is generated. Over 579 launches that is 41 minutes, 29%
of the slot time, spent before exploring anything. The per-state cost of
the whole file (36.5 million distinct states across the rows that record a
count) is about 80 minutes.

So the answer to the first question is no: the state space is not
exploding. The grid is wide, each cell re-explores a small space, and a
third of the time is launch overhead. Both are properties of the pattern,
not of the module.

---

## 4. Method A: split the product row into breadth and depth

### 4.1 What was tried

The largest row, `c-cfg-safety`, checks Safety at the constants of
`Elections.cfg`: both candidates mortal, two bound electors and one free,
every elector's vote open to objection, the Inhabitants pairs. It is a
product: the college's variety in one election, multiplied by the deaths
that can interleave with every college step. The experiment ran that row
and three others through `scripts/tlc_rows.py` from a scratch rows file
(appendix A.1), four rows in parallel, 2 min 22 s wall clock.

| Row | Constants (over the row-list defaults) | Distinct states |
|---|---|---|
| product (today's `c-cfg-safety`) | `Mortal={a,b} Inhabitants={{e1,a},{e2,b}} Binding={e1,e2} Contestable={e1,e2,e3}` | 2,060,728 |
| breadth: the whole college, nobody mortal | same with `Mortal={}` | 400,970 |
| depth: one elector, both candidates mortal | `Mortal={a,b} Electors={e1} Binding={e1} Contestable={e1} Inhabitants={{e1,a}}` | 14,062 |
| depth, two electors | `Mortal={a,b} Electors={e1,e2} Binding={e1} Contestable={e1,e2} Inhabitants={{e1,a},{e2,b}}` | 182,828 |

Safety HOLDS on all four. The product is five times the breadth and depth
rows together. At CI's rate the pair would take about two minutes of slot
time in place of nine.

### 4.2 Why the pair checks what the product checks

Every property in `Safety` is local, and the module's header says so
property by property: each is a flag set by one action, or a predicate
over one group of variables. `CountCanClose` reads ballots and objections.
`Qualifications`, `Disability`, `ActingOrder` and `PresidentNotVP` read
the office variables. `TwoTermLimit` and `VPElectBecomesOnlyOnDeath` need
deaths and repeated elections, which one elector supplies (the existing
`c-mortal-safety` row, at 9,246 states, already checks them that way). No
property reads an objection and the dead set together, so the states the
product adds, in which a death is interleaved with a contested count,
exercise no guard the two halves do not reach separately.

That is an argument from the shape of the properties, not a proof. A
property added later that spans both sides would need the product row
back.

### 4.3 What the results file would lose

The row exists to say that Safety holds at the constants of
`Elections.cfg`, the config kept for ad hoc runs (rows file, line 37). After
the split no results line says that. The honest wording is that the cfg's
college is checked without deaths and its deaths with a smaller college,
and that the cfg itself is for exploration.

### 4.4 Cost to adopt

A rows-file edit: replace one row with two (or three, keeping the
two-elector depth row), and reword the header comment and the `Expected:`
lines. Because the rows file's digest is in the results file, the Elections
results regenerate, which is the 71-minute CI run. Saving: about seven
minutes of slot time per run thereafter, roughly four minutes of wall
clock.

---

## 5. Method B: bound the product row with a constraint

### 5.1 What was tried

TLC's `CONSTRAINT` keeps exploration to states that satisfy a predicate,
reached through states that satisfy it. The rows file already uses one:
`constraint=ElectionsBound` on the `M_XXII` rows, whose count of elections
is otherwise unbounded. The experiment added an operator to a scratch copy
of the module,

    AtMostOneDeath == Cardinality(dead) <= 1

and ran the product row's config (appendix A.2) with and without
`CONSTRAINT AtMostOneDeath`, one worker each as CI runs them, side by side
on the same machine.

| Product row, Safety | Distinct states | States generated | Time | Graph depth |
|---|---|---|---|---|
| unconstrained | 2,060,728 | 12,334,853 | 2 min 29 s | 61 |
| `CONSTRAINT AtMostOneDeath` | 1,514,318 | 9,512,921 | 2 min 07 s | 61 |

Safety HOLDS in both. The constraint removed 27% of the states and 15% of
the time.

### 5.2 Why it is weak

With two mortal candidates the dead set takes four values, and the
constraint removes one. States with both candidates dead are at most a
quarter of the space, and the run removed about that. The product row is
not large because many deaths happen; it is large because a death can
interleave with every appointment, ballot, objection and announcement, and
that multiplies the 400,970 college states by about five. A constraint
that cut the interleaving would have to forbid deaths during particular
stages, and those are the interesting cases, such as a President elect
dying between the vote and the count.

### 5.3 Cost to adopt

A module edit, which changes `Elections.tla`'s digest and so regenerates
every Elections results file, plus the row's wording changing from "every
reachable state" to "every state within the bound", as the `M_XXII` rows
already say. For that, about twenty seconds per run of one row. Not worth
adding.

---

## 6. What neither method touches

Both experiments work on one row that is 7% of the slot time. The pattern
in §2 is 74% of it. Two things about that pattern, for the record.

**CHOOSE cannot short-circuit it.** It carries nothing between launches;
each row is a fresh JVM with a fresh fingerprint set, and TLC's only
cross-run mechanism, checkpoint and recover, resumes the same run with the
same config. Inside the module, replacing an `\E` in `Next` with `CHOOSE`
would pick one successor and discard the rest, so HOLDS would then cover
one ordering rather than every reachable state, which is exactly the claim
the results file makes.

**One launch per block would.** TLC checks every invariant listed in a
config on every state in a single pass. One run per (mutation × constant
set), listing TypeOK and every property expected to HOLD, replaces the
nineteen rows that re-explore the same space. The property the mutation
is expected to break stays its own row, since TLC stops at the first
violation and the results file wants that counterexample attributed to it.
If a combined run ever failed, the block would be rerun property by
property to find which one moved.

The arithmetic: about 490 launches become about 50; the fixed cost falls
from 41 minutes to about 4; the re-exploration disappears. Estimated slot
time for the file is 25 minutes against 140, so around 13 minutes of wall
clock on the two-CPU runner. The trade is in the results file: one line
would attest "these nineteen hold under M_X at these constants" instead of
nineteen lines each naming one property. The evidence is the same, since
one exploration checked all of them. The row format, the `Expected:`
header, `scripts/tlc_rows.py`'s config writer and `compare_results.py`
would change together, and so would every module's rows file if the
pattern is kept uniform. This was not tried and is not costed beyond the
arithmetic above.

---

## 7. What this means for a proof of Elections.tla

Elections has no proof module. `PROOF-GAPS.txt` records it as checked and
not proved. The other four modules follow one pattern: a theorem per
property, `Spec => []P`, under exactly the mutation hypotheses
(`Mut # "M_X"`) that break P; `SafeAlways` under `Mut = "none"`; and a
flip test per mutation (`scripts/flip_test.py`) showing each cited
hypothesis is load-bearing. The findings above bear on that effort in four
ways.

### 7.1 The matrix's cost is TLC's, not a proof's

A proof is indifferent to state count. The 490 cells that take 74% of CI
exist to show that each mutation leaves eighteen properties alone, at one
set of constants each. A theorem for P that cites only `Mut # "M_P"` says
the same for every other mutation at every constant, and says it
structurally: the proof never needed the other guards. The flip test then
checks that each cited hypothesis is load-bearing, which is 25 tlapm runs,
one per mutation, against 490 TLC launches. So a proof delivers the
one-launch-per-block consolidation of §6, and more, without changing the
rows file. What stays with TLC is what the Constitution proof's header
already leaves there: the COUNTEREXAMPLE cells, the `Never...` witnesses
and the liveness row.

### 7.2 The breadth/depth argument is a proof obligation in disguise

§4.2 claims no property reads the college variables and the dead set
together, and §10 admits that was argued from the text, not checked.
Writing the per-property inductive invariants would check it. If every
invariant mentions one side only, the split is sound at all constants. If
some property needs an invariant spanning both, §4.2 was wrong and the
product row earns its place. The proof is the missing check, and it would
decide the split better than any further TLC run.

### 7.3 CountCanClose is where the effort goes

Eleven of the nineteen properties are flags (`~lateVote` and the like),
and their proofs follow the `FlagFrame` pattern of `Executive_proof.tla`
almost mechanically, though the frame lemmas will be long: `Next` has
nineteen disjuncts with wide UNCHANGED tuples. The state predicates need
small strengthenings, such as a ballot implying a pledge
(`ballot[e] # NoBallot => pledge[e] # NoOne`), which no single action
states but every action preserves.

`CountCanClose` is the one the module's header says no guard decides, and
it is a pigeonhole: two majorities of the electors appointed share an
elector, and that elector's ballot names two persons, so one person cannot
carry both lists. Formally, `PMajority(p) /\ VMajority(p)` gives
`Cardinality(PFor(p)) + Cardinality(VFor(p)) > Whole >= Cardinality(Counted)`,
so `PFor(p) \cap VFor(p)` is non-empty, and an elector in it has
`ballot[e].p = ballot[e].v`, which `TwoNames` forbids. That needs
cardinality of a union over finite sets, which `Judiciary_proof.tla` and
`Government_proof.tla` already do with `FiniteSetTheorems`, so there is
precedent in the repository. The theorem's hypotheses would be
`Mut \notin {"M_SAME_NAME", "M_PRE_XII", "M_PLURALITY"}`, and the proof
would be honest where the rows are not: the `m-prexii-canclose` and
`m-plurality-canclose` HOLDS cells are artefacts of two candidates, which
the rows file acknowledges by adding the three-candidate rows.

### 7.4 The product row's residual value becomes the proof's

The rows file says what it cannot reach: the House's list of three
excluding a fourth person voted for, which needs seven electors and four
candidates. A proof holds at any finite college, so it covers those
constants and the ones `Elections.cfg` uses, which is the claim §4.3 says
the split would lose.

### 7.5 Two cautions

`ExecutiveIsFilled` is a leads-to under weak fairness. The Constitution
proof's header records that shape as the case the pinned prover has no
sound route for under the writing rules, so it would stay a TLC row, as
`PresentedBillsResolve` does. And the obligation count will likely match
or exceed Government's 1,563, given the size of `Next`, so this is a
multi-session effort rather than a quick addition.

### 7.6 What happened when the proof was written

The proof module was written the same day, after this section, and
`specs/Elections_proof.tla` is beside this note. Against the estimates
above:

- 1,121 obligations, all proved by the pinned prover; 25 flip tests, one
  per mutation, each failing in the lemma that carries the hypothesis.
  The count is below Government's, not above it (§7.5).
- The hypothesis lists came out as §7.3 predicted, including
  `DevolvesOnlyWithoutMajority` under `M_PLURALITY` only excluding
  `M_ENTITLED`, which needed the lemma that a majority of the whole number
  beats every other candidate.
- Two strengthenings, not one: `BallotNeedsPledge` for `PledgesBind`, and
  `TwoNamesOnBallots` carrying Vote's `TwoNames` to the count for
  `CountCanClose`. The second was named in §7.3; the first was not.
- `CollegeWF` (Binding within Electors) turned out to be load-bearing,
  for `PledgesBind`'s quantifier over Binding; §7 did not list it.
- §7.2 is settled: every inductive invariant mentions one side only. The
  office-side invariants are over `president`, `vicePresident`, `acting`
  and `relieved`; the college-side over `pledge`, `ballot` and
  `objection`; the flags over their one action. No invariant reads an
  objection and the dead set together, so the breadth/depth split of §4
  loses nothing a property can see, now by proof rather than by reading.
- The liveness caution in §7.5 was wrong in Elections' case.
  `ExecutiveIsFilled` has no quantifier inside its leads-to, which is the
  shape the method's prover does handle, and it proved by one WF1 step
  with no measure. The quantified leads-tos of the other modules remain
  where §7.5 left them.

---

## 8. What the proof means for the matrix

> How does finding the proof inform the MutationMatrix issue?

The proof changes what the matrix's HOLDS cells are for, and that is what
opens the door to cutting them.

**What the HOLDS cells were.** Each mutation's block has one
COUNTEREXAMPLE row and eighteen or nineteen HOLDS rows. The HOLDS rows
carried two claims: the mutation leaves that property alone, and it does
so at these constants. The method describes those rows as the "Breaks
under" column that the proof's hypotheses will later restate. Elections
now has that restatement: each theorem cites exactly the mutations that
break its property, and the 25 flip tests show every cited hypothesis is
load-bearing. The proof says, for every finite college and any number of
candidates, what 440 rows said at three electors and two candidates.

**What the matrix still does that the proof cannot.** The COUNTEREXAMPLE
rows are existential and stay with TLC, as the method insists. So do the
witnesses, the deadlock audits and the liveness rows that show the weaker
fairness conditions fail and `FairSpec` has a behaviour. None of that is
in the 103 minutes the HOLDS cells cost.

**Where the proof corrected the matrix.** Two HOLDS cells were artefacts
of constants: `M_PRE_XII` and `M_PLURALITY` hold `CountCanClose` at two
candidates and break it at three. The rows file already patches this with
the three-candidate rows, but the proof's hypothesis list is the honest
column, and nothing in the matrix could have told you that `CollegeWF`,
Binding within Electors, is load-bearing. A HOLDS at small constants is
weaker evidence than it looks, and that weakens the case for paying for
440 of them.

**What the HOLDS cells become: a cross-check.** The pinned prover has two
known unsound translation cases, and these proofs are written to the
method's rules but unscanned. TLC agreeing with the prover at small
constants is a second route, and worth keeping. But a cross-check does not
need per-cell attribution, since the proof already attributes. That is
exactly the case for the consolidation of §6: one TLC run per mutation and
constant set, listing every property the proof says holds, in place of
nineteen launches.

**What the Elections rows could become.**

| Row group | Today | With the proof |
|---|---|---|
| HOLDS cells (`m-`, TypeOK plus 18 properties per block) | 440 rows, ~95 min | one combined run per block, ~25 rows, ~6 min |
| COUNTEREXAMPLE rows, witnesses, liveness, deadlock audits | ~80 rows, ~12 min | unchanged |
| Unmutated `p-` rows and small `c-` Safety rows | ~40 rows, ~15 min | unchanged, as the cross-check |
| `c-cfg-safety` at 2.06M states | 1 row, 9 min | drop: Safety is proved at those constants |
| Three-candidate rows | 3 rows, 9 min | keep: they check the pigeonhole at the constant where it bites |

Roughly 140 minutes of slot time becomes about 45, with every claim the
results file makes still backed by either a check or a proof. The other
four modules have the same shape, proof and full matrix both, so this is a
repository-wide policy choice rather than an Elections tweak. The rows are
unchanged as of this note.

---

## 9. Three questions

### 9.1 How the matrix investigation informed the proof

- **It set the goal.** Once §3 showed the cost was the grid and not the
  state space, the proof's job was clear: restate the HOLDS column as
  hypotheses, with each theorem citing only the mutations that break it.
  That is why `DevolvesOnlyWithoutMajority` is proved under `M_PLURALITY`
  with the extra lemma `MajorityCarries` instead of taking the easier
  hypothesis; the weakest hypothesis is what makes the proof a replacement
  for the cells and not a parallel claim.
- **It gave the inventory.** The identical state count down every block
  was the symptom of locality, and §7.3's sorting of the properties, eleven
  flags, seven state predicates, one valid-not-inductive, became the
  proof's layout: `FlagFrame` for the flags, `CollegeFrame` and
  `OfficeFrame` for the predicates, `ClosesUnderInv` for `CountCanClose`.
  The sort was right in every case.
- **It chose the frames.** §4.2's argument that no property reads both the
  college and the dead set said which variables each invariant should
  mention, and the frame lemmas were grouped on the module's own variable
  tuples accordingly. The proof confirmed the partition.
- **It wrote the hard lemma in advance.** The pigeonhole in §7.3 was
  transcribed into `Pigeonhole` and `ClosesUnderInv` almost line for line,
  and the first thing run in the prover was a six-line smoke test of that
  argument over `FiniteSetTheorems`. The riskiest step was settled before
  the module existed.
- **It warned about the HOLDS column.** The two-candidate artefact told
  the proof to take hypotheses from the definitions a property reads, not
  from the rows' verdicts, and to let the flip test arbitrate.
- **It said what not to prove.** The witnesses and counterexamples stay
  TLC's, and the liveness rows are what make `ExecutiveIsFilledAlways`
  non-vacuous: `FairSpec` has a behaviour, and each weaker fairness fails.
- **It got one thing wrong usefully.** §5's finding that deaths interleave
  with everything predicted a `Die` case in every office-side lemma, which
  is there; stating `Die`'s primed values once per lemma and never
  expanding it again kept those cases to one step each.

### 9.2 How the proof informed the two options

- **The breadth/depth split (§4).** Its soundness rested on §4.2, argued
  from the text. The proof settles it: every inductive invariant mentions
  one side only, so the split loses nothing a property can see. But the
  proof also supersedes it. The product row's remaining claim, Safety at
  the constants of `Elections.cfg`, is now proved outright at those
  constants and every other, so the row can be dropped rather than split.
  What survives of the idea is the cross-check at small constants, which
  the existing small `c-` rows already give.
- **The one-death constraint (§5).** The proof shows deaths matter only
  through the office variables and `relieved`, which is why bounding their
  number cut a quarter of the states and none of the interleavings a
  property reads. With the proof covering any number of deaths the
  constraint is moot, and the module edit it needed would now also stale
  the proof's digest. The recommendation against it stands, for a stronger
  reason.
- **Both options were about one row.** They addressed 7% of the slot
  time; the proof reframes the 74%. The next change to the rows should be
  the one in §8, not either of these.

### 9.3 What could go upstream to the writing-tla-specs-and-proofs skill

Each item names the reference it would change.

- **The role of HOLDS cells after a proof** (`model-checking.md`,
  `anti-patterns.md`). The skill says the HOLDS rows are what the proof's
  hypotheses will restate, and its rationalisation table rightly rejects
  "no need for the mutation rows now that the invariant is proved". It
  should say which rows that sentence protects: the COUNTEREXAMPLE rows,
  the witnesses, the liveness rows. The HOLDS rows change role once the
  proof exists, from evidence to cross-check, and a cross-check can be one
  combined run per block. That needs a row kind that lists several
  invariants, which the bundled `tlc_rows.py` does not have.
- **A cost model for row lists** (`model-checking.md`). Cost scales with
  launches, not states: about four seconds of JVM and parse per launch,
  and TLC explores the whole space whichever invariant it checks. The
  skill has a cost model for proofs ("actions times invariant clauses")
  and none for row lists; this is the matching one.
- **A step-hygiene rule for `CASE` steps** (`proof-style.md`,
  `prover-habits.md`). The first prover run failed 41 obligations, every
  one a `CASE` step inside a lemma whose goal was `Inv'`, so the step's
  goal was `TypeOK' /\ P'` while the `BY` proved `P'`. Either give the
  `Next` lemma the bare property as its goal, as the Executive proof does,
  or state `<1> SUFFICES P'` once `TypeOK'` is established. One sentence
  in "Steps that fail for want of scope" would have saved the run.
- **`Cardinality` in an invariant, done once** (`prover-habits.md`). The
  skill lists "`Cardinality` in an invariant" under what the SMT backend
  handles "not well" and says to design it out. Elections could not: the
  majority rule is a count. What worked is stating the finiteness and
  ordering facts once (`Sizes`, `VoteSizes`, `DisjointVotes`,
  `Pigeonhole`) and letting every property step use the counts as terms
  in `Nat`. That is the liveness-measure exception generalised, and the
  entry should say so.
- **The measureless leads-to** (`proof-style.md`). The skill's liveness
  shape is a measure, one WF1 step and `Nat` induction. `ExecutiveIsFilled`
  is the degenerate case: one fair step reaches the goal, so the proof is
  three state lemmas and one `PTL` step with no measure. Worth recording
  as the first shape to try, since it is the one many "someone acts"
  obligations have.
- **Hypotheses against constant-size artefacts** (`proof-style.md`,
  "weakest hypothesis"). Add the Elections example: a HOLDS at two
  candidates that is a COUNTEREXAMPLE at three. The rule is to take the
  hypothesis list from the definitions the property reads, verify it by
  flip, and then read the rows file's expected clauses against the theorem
  list, because the rows may be the ones that are wrong.
- **A mutation that breaks only liveness** (`evidence.md`, the flip test).
  `flip_test.py` exits non-zero for a mutation with no `Mut #` hypothesis
  in the module, which `M_NO_STATUTE` was until the liveness theorem
  existed. Say that such a mutation is covered by the liveness theorem's
  flip, or by its mutation lemma alone, and that the flip list is the
  theorems' hypotheses, not the mutation list.
- **Running the pinned prover in a container** (`evidence.md`, pins). The
  skill's scripts assume a native `tlapm` matching the pin. On a platform
  the pin does not cover, the route is the pinned image with the prover's
  digest in the image pin, `--user` for file ownership and the scripts run
  unchanged inside it. Nothing in the method changes; the wrapper's
  override is never needed.
- **Frames first, grouped on the module's tuples** (`proof-style.md`).
  After `TypeOK`, write one frame lemma per variable group the module
  already declares, with the actions that touch it as the disjuncts.
  Every `Next` lemma then has one case per touching action and one for
  "unchanged", and the obligation count stays near actions times
  properties rather than actions times properties times clauses.
- **A pre-proof note as an artefact** (`proof-style.md`, "write the prose
  first"). §7 was that prose at module scale: each property's rung on the
  ladder, its expected hypotheses, the one hard argument. It was right
  often enough to be worth the hour, and wrong in two places (§7.6) that
  the proof then corrected on the record. The skill asks for the header's
  prose before the definitions; a dated note like this one, kept beside the
  proof, is the same discipline with a place to record what changed.

---

## 10. What was not checked

- The §3 timings assume the pool dispatches rows strictly in file order,
  which is what `ThreadPoolExecutor` does; the sum matching two workers'
  wall clock is the only check on that.
- The §4 and §5 runs were on an arm64 laptop with the pinned jar; CI is a
  two-CPU x86_64 runner in the tla-kit image. Ratios transfer, absolute
  times do not.
- §4.2 argues from the properties as written on 2026.11.17. It was not
  checked by running each property separately on the pair, nor by the
  invariants a proof would need (§7.2).
- §7.1 to §7.5 were written before the proof; §7.6 records what the
  proof then showed, and supersedes them where they differ.
- No mutation row was run on the split constants. If the split is adopted,
  the `c-` convention says the new constant sets need their own `c-`
  Safety and deadlock rows, which the appendix's rows are.

---

## Appendix A. Reproducing the experiments

### A.1 Scratch rows file for §4

The `# const:` block is the one in `rows/Elections-rows.txt`; run with
`scripts/tlc_rows.py <file> -j 4 --out <path>`.

    # module: Elections
    # title: split experiment
    # expected: experiment
    x-cfg-product  none Spec INVARIANT Safety HOLDS Mortal={a,b} Inhabitants={{e1,a},{e2,b}} Binding={e1,e2} Contestable={e1,e2,e3}
    x-breadth      none Spec INVARIANT Safety HOLDS Mortal={} Inhabitants={{e1,a},{e2,b}} Binding={e1,e2} Contestable={e1,e2,e3}
    x-depth        none Spec INVARIANT Safety HOLDS Mortal={a,b} Electors={e1} Binding={e1} Contestable={e1} Inhabitants={{e1,a}}
    x-depth2       none Spec INVARIANT Safety HOLDS Mortal={a,b} Electors={e1,e2} Binding={e1} Contestable={e1,e2} Inhabitants={{e1,a},{e2,b}}

### A.2 Config and command for §5

Copy `specs/Elections.tla` to a scratch directory, insert
`AtMostOneDeath == Cardinality(dead) <= 1` before the closing `====` line,
write `MC.cfg` with the row-list defaults overridden as in `x-cfg-product`
above, `INVARIANT Safety`, and for the constrained run
`CONSTRAINT AtMostOneDeath`. Then, in that directory:

    java -XX:+UseParallelGC -Xmx2g -cp <repo>/tools/tla2tools.jar tlc2.TLC \
      -config MC.cfg -workers 1 -metadir "$PWD/meta" -deadlock Elections.tla

These are the flags `scripts/tlc_rows.py` uses for an INVARIANT row.
