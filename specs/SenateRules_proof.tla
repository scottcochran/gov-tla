------------------------- MODULE SenateRules_proof -------------------------
(****************************************************************************)
(* TLAPS proofs of the safety properties of SenateRules.tla. The base       *)
(* module is extended, never edited; the proof results file names it by    *)
(* digest.                                                                  *)
(*                                                                          *)
(* THEOREMS, each Spec => []P under exactly the mutations that break P in   *)
(* the TLC results file (results/SenateRules-results-*.txt):                *)
(*   ClotureThresholdAlways     [Mut # M_PREVIOUS_QUESTION]                 *)
(*   DebateEndsByClotureAlways  [Mut # M_TIME_LIMIT]                        *)
(*   MajorityFloorAlways        [Mut # M_NO_MAJORITY]                       *)
(*   RulesByTwoThirdsAlways     [Mut # M_CONSTITUTIONAL_OPTION]             *)
(*   ClosedOnThreeFifthsAlways  [Mut # M_PREVIOUS_QUESTION,                 *)
(*                               Mut # M_TIME_LIMIT]                        *)
(*   TypeOKAlways               [none: every mutation]                      *)
(*   SafeAlways                 [Mut = "none"]: Spec => []Safety            *)
(* and one lemma per mutation (Mut...Admits) saying what it lets through.   *)
(*                                                                          *)
(* ASSUMPTIONS: the base module's named ASSUME FiniteSenate, and only for   *)
(* TypeOK (the count 0 is a count of the Senate). MutOK and KindsDisjoint   *)
(* are not used. So the theorems hold for a Senate of any size and any      *)
(* number of bills, nominations and reconciliation bills; the rows' seven   *)
(* Senators and one measure of each kind are TLC's business.                *)
(*                                                                          *)
(* INDUCTIVE STRENGTHENING, in prose:                                       *)
(*  - TypeOK, under every mutation, cited by every lemma that reads a       *)
(*    function after an EXCEPT.                                             *)
(*  - ClotureThreshold, DebateEndsByCloture, MajorityFloor and              *)
(*    RulesByTwoThirds are flags set by one action each (InvokeCloture,     *)
(*    DebateExpires, Pass, AmendRule). Each is inductive with TypeOK alone, *)
(*    the flag's condition being the negation of the guard its mutation     *)
(*    removes; every other action leaves the flag unchanged.                *)
(*  - ClosedOnThreeFifths is inductive with TypeOK as stated. A measure     *)
(*    leaves Debate only by InvokeCloture, whose guard is the threshold     *)
(*    (Mut # M_PREVIOUS_QUESTION), or by DebateExpires, which only a        *)
(*    reconciliation bill can take (Mut # M_TIME_LIMIT). Support is fixed   *)
(*    once a measure leaves Pending. A threshold only falls (Nuclear and    *)
(*    AmendRule set one kind to "Majority"), so a kind that is three-fifths *)
(*    after a step was three-fifths before it (ThresholdOnlyFalls).         *)
(*                                                                          *)
(* NOT PROVED                                                               *)
(*  - MajorityPrevails and ReconciliationPrevails: each is a leads-to       *)
(*    quantified over measures, and the pinned prover has no sound route    *)
(*    for a quantified leads-to (README, "What is not proved"). They are    *)
(*    checked by TLC in the liveness rows, with NoBehaviour.                *)
(*  - Reachability (the Never... witnesses) and the mutations'              *)
(*    counterexamples: existential, so TLC's.                               *)
(*                                                                          *)
(* CHECK: scripts/proof_results.py SenateRules (tools/tlapm --cleanfp       *)
(* --strict --cache-dir <tmp> SenateRules_proof.tla); flip a hypothesis     *)
(* with scripts/flip_test.py SenateRules M_X.                               *)
(****************************************************************************)
EXTENDS SenateRules, FiniteSetTheorems, TLAPS

-----------------------------------------------------------------------------
(* Facts about the constants                                                *)

LEMMA NNat == N \in Nat
BY FiniteSenate, FS_CardinalityType DEF N

LEMMA KindType == \A m \in Measures : Kind(m) \in Kinds
BY DEF Kind, Kinds

-----------------------------------------------------------------------------
(* The type invariant, under every mutation                                 *)

LEMMA InitTypeOK == Init => TypeOK
BY NNat DEF Init, TypeOK, Stages, Counts, Thresholds, Routes

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  OBVIOUS
<1> USE DEF ruleVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, TypeOK
<1>2. ASSUME NEW m \in Measures, NEW n \in Counts, Proceed(m, n) PROVE TypeOK'
  BY <1>2 DEF Proceed, TypeOK, Stages
<1>3. ASSUME NEW m \in Measures, InvokeCloture(m) PROVE TypeOK'
  BY <1>3 DEF InvokeCloture, TypeOK, Stages
<1>4. ASSUME NEW m \in Measures, DebateExpires(m) PROVE TypeOK'
  BY <1>4 DEF DebateExpires, TypeOK, Stages
<1>5. ASSUME NEW m \in Measures, Pass(m) PROVE TypeOK'
  BY <1>5 DEF Pass, TypeOK, Stages
<1>6. ASSUME NEW m \in Measures, Reject(m) PROVE TypeOK'
  BY <1>6 DEF Reject, TypeOK, Stages
<1>7. ASSUME NEW m \in Measures, Nuclear(m) PROVE TypeOK'
  BY <1>7, KindType DEF Nuclear, TypeOK, Thresholds, Routes
<1>8. ASSUME NEW k \in Kinds, NEW ayes \in Counts, NEW present \in Counts,
             AmendRule(k, ayes, present)
      PROVE  TypeOK'
  BY <1>8 DEF AmendRule, TypeOK, Thresholds, Routes
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Next

THEOREM TypeOKAlways == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec

-----------------------------------------------------------------------------
(* The flags: each set by one action, and left alone by every other         *)

\* The four flags change only at the action that sets each; the rules
\* change only at Nuclear and AmendRule; support only at Proceed.
LEMMA NextCases ==
  ASSUME [Next]_vars
  PROVE  \/ UNCHANGED vars
         \/ \E m \in Measures, n \in Counts : Proceed(m, n)
         \/ \E m \in Measures : InvokeCloture(m)
         \/ \E m \in Measures : DebateExpires(m)
         \/ \E m \in Measures : Pass(m)
         \/ \E m \in Measures : Reject(m)
         \/ \E m \in Measures : Nuclear(m)
         \/ \E k \in Kinds, ayes \in Counts, present \in Counts : AmendRule(k, ayes, present)
BY DEF Next

LEMMA NextClotureThreshold ==
  ASSUME Mut # "M_PREVIOUS_QUESTION"
  PROVE  ClotureThreshold /\ [Next]_vars => ClotureThreshold'
<1> SUFFICES ASSUME ClotureThreshold, [Next]_vars PROVE ClotureThreshold'
  OBVIOUS
<1> USE DEF ClotureThreshold, ruleVars, flagVars, vars
<1>1. ASSUME NEW m \in Measures, InvokeCloture(m) PROVE ClotureThreshold'
  BY <1>1 DEF InvokeCloture, ClotureCarries
<1> QED
  BY <1>1, NextCases DEF Proceed, DebateExpires, Pass, Reject, Nuclear, AmendRule

LEMMA NextDebateEndsByCloture ==
  ASSUME Mut # "M_TIME_LIMIT"
  PROVE  DebateEndsByCloture /\ [Next]_vars => DebateEndsByCloture'
<1> SUFFICES ASSUME DebateEndsByCloture, [Next]_vars PROVE DebateEndsByCloture'
  OBVIOUS
<1> USE DEF DebateEndsByCloture, ruleVars, flagVars, vars
<1>1. ASSUME NEW m \in Measures, DebateExpires(m) PROVE DebateEndsByCloture'
  BY <1>1 DEF DebateExpires, TimeLimited
<1> QED
  BY <1>1, NextCases DEF Proceed, InvokeCloture, Pass, Reject, Nuclear, AmendRule

LEMMA NextMajorityFloor ==
  ASSUME Mut # "M_NO_MAJORITY"
  PROVE  MajorityFloor /\ [Next]_vars => MajorityFloor'
<1> SUFFICES ASSUME MajorityFloor, [Next]_vars PROVE MajorityFloor'
  OBVIOUS
<1> USE DEF MajorityFloor, ruleVars, flagVars, vars
<1>1. ASSUME NEW m \in Measures, Pass(m) PROVE MajorityFloor'
  BY <1>1 DEF Pass, PassCarries
<1> QED
  BY <1>1, NextCases DEF Proceed, InvokeCloture, DebateExpires, Reject, Nuclear, AmendRule

LEMMA NextRulesByTwoThirds ==
  ASSUME Mut # "M_CONSTITUTIONAL_OPTION"
  PROVE  RulesByTwoThirds /\ [Next]_vars => RulesByTwoThirds'
<1> SUFFICES ASSUME RulesByTwoThirds, [Next]_vars PROVE RulesByTwoThirds'
  OBVIOUS
<1> USE DEF RulesByTwoThirds, ruleVars, flagVars, vars
<1>1. ASSUME NEW k \in Kinds, NEW ayes \in Counts, NEW present \in Counts,
             AmendRule(k, ayes, present)
      PROVE  RulesByTwoThirds'
  BY <1>1 DEF AmendRule, RulesCarry
<1> QED
  BY <1>1, NextCases DEF Proceed, InvokeCloture, DebateExpires, Pass, Reject, Nuclear

THEOREM ClotureThresholdAlways ==
    ASSUME Mut # "M_PREVIOUS_QUESTION"
    PROVE  Spec => []ClotureThreshold
<1>1. ClotureThreshold /\ [Next]_vars => ClotureThreshold'
  BY NextClotureThreshold
<1>2. Init => ClotureThreshold
  BY DEF Init, ClotureThreshold
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM DebateEndsByClotureAlways ==
    ASSUME Mut # "M_TIME_LIMIT"
    PROVE  Spec => []DebateEndsByCloture
<1>1. DebateEndsByCloture /\ [Next]_vars => DebateEndsByCloture'
  BY NextDebateEndsByCloture
<1>2. Init => DebateEndsByCloture
  BY DEF Init, DebateEndsByCloture
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM MajorityFloorAlways ==
    ASSUME Mut # "M_NO_MAJORITY"
    PROVE  Spec => []MajorityFloor
<1>1. MajorityFloor /\ [Next]_vars => MajorityFloor'
  BY NextMajorityFloor
<1>2. Init => MajorityFloor
  BY DEF Init, MajorityFloor
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM RulesByTwoThirdsAlways ==
    ASSUME Mut # "M_CONSTITUTIONAL_OPTION"
    PROVE  Spec => []RulesByTwoThirds
<1>1. RulesByTwoThirds /\ [Next]_vars => RulesByTwoThirds'
  BY NextRulesByTwoThirds
<1>2. Init => RulesByTwoThirds
  BY DEF Init, RulesByTwoThirds
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* The filibuster: ClosedOnThreeFifths                                      *)

InvC == TypeOK /\ ClosedOnThreeFifths

PastDebate == {"Closed", "Passed", "Rejected"}

\* A threshold only falls: a kind that is three-fifths after a step was
\* three-fifths before it. Under every mutation.
LEMMA ThresholdOnlyFalls ==
  ASSUME TypeOK, [Next]_vars, NEW k \in Kinds, cloture'[k] = "ThreeFifths"
  PROVE  cloture[k] = "ThreeFifths"
<1> USE DEF ruleVars, flagVars, vars
<1>1. ASSUME NEW m \in Measures, Nuclear(m) PROVE cloture[k] = "ThreeFifths"
  <2>1. CASE k = Kind(m)
    BY <1>1, <2>1, KindType DEF Nuclear, TypeOK
  <2>2. CASE k # Kind(m)
    BY <1>1, <2>2, KindType DEF Nuclear, TypeOK
  <2> QED
    BY <2>1, <2>2
<1>2. ASSUME NEW j \in Kinds, NEW ayes \in Counts, NEW present \in Counts,
             AmendRule(j, ayes, present)
      PROVE  cloture[k] = "ThreeFifths"
  <2>1. CASE k = j
    BY <1>2, <2>1 DEF AmendRule, TypeOK
  <2>2. CASE k # j
    BY <1>2, <2>2 DEF AmendRule, TypeOK
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, NextCases DEF Proceed, InvokeCloture, DebateExpires, Pass, Reject

LEMMA NextInvC ==
  ASSUME Mut # "M_PREVIOUS_QUESTION", Mut # "M_TIME_LIMIT"
  PROVE  InvC /\ [Next]_vars => InvC'
<1> SUFFICES ASSUME InvC, [Next]_vars PROVE InvC'
  OBVIOUS
<1>0. TypeOK'
  BY NextTypeOK DEF InvC
<1> SUFFICES ASSUME NEW x \in Measures \ Reconciliations,
                    stage'[x] \in PastDebate,
                    cloture'[Kind(x)] = "ThreeFifths"
             PROVE  ThreeFifths(support'[x])
  BY <1>0 DEF InvC, ClosedOnThreeFifths, PastDebate
<1>1. cloture[Kind(x)] = "ThreeFifths"
  BY ThresholdOnlyFalls, KindType DEF InvC
\* Before the step, x was past debate (and so done), or it closed now.
<1> USE DEF ruleVars, flagVars, vars
<1>2. CASE UNCHANGED vars
  BY <1>1, <1>2 DEF InvC, ClosedOnThreeFifths, PastDebate
<1>3. ASSUME NEW m \in Measures, NEW n \in Counts, Proceed(m, n)
      PROVE  ThreeFifths(support'[x])
  <2>1. x # m
    BY <1>3 DEF Proceed, InvC, TypeOK, PastDebate
  <2> QED
    BY <1>1, <1>3, <2>1 DEF Proceed, InvC, TypeOK, ClosedOnThreeFifths, PastDebate
<1>4. ASSUME NEW m \in Measures, InvokeCloture(m)
      PROVE  ThreeFifths(support'[x])
  <2>1. CASE x = m
    BY <1>1, <1>4, <2>1 DEF InvokeCloture, ClotureCarries, Meets
  <2>2. CASE x # m
    BY <1>1, <1>4, <2>2 DEF InvokeCloture, InvC, TypeOK, ClosedOnThreeFifths, PastDebate
  <2> QED
    BY <2>1, <2>2
<1>5. ASSUME NEW m \in Measures, DebateExpires(m)
      PROVE  ThreeFifths(support'[x])
  <2>1. x # m
    BY <1>5 DEF DebateExpires, TimeLimited
  <2> QED
    BY <1>1, <1>5, <2>1 DEF DebateExpires, InvC, TypeOK, ClosedOnThreeFifths, PastDebate
<1>6. ASSUME NEW m \in Measures, Pass(m)
      PROVE  ThreeFifths(support'[x])
  BY <1>1, <1>6 DEF Pass, InvC, TypeOK, ClosedOnThreeFifths, PastDebate
<1>7. ASSUME NEW m \in Measures, Reject(m)
      PROVE  ThreeFifths(support'[x])
  BY <1>1, <1>7 DEF Reject, InvC, TypeOK, ClosedOnThreeFifths, PastDebate
<1>8. ASSUME NEW m \in Measures, Nuclear(m)
      PROVE  ThreeFifths(support'[x])
  BY <1>1, <1>8 DEF Nuclear, InvC, ClosedOnThreeFifths, PastDebate
<1>9. ASSUME NEW k \in Kinds, NEW ayes \in Counts, NEW present \in Counts,
             AmendRule(k, ayes, present)
      PROVE  ThreeFifths(support'[x])
  BY <1>1, <1>9 DEF AmendRule, InvC, ClosedOnThreeFifths, PastDebate
<1> QED
  BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, NextCases

THEOREM ClosedOnThreeFifthsAlways ==
    ASSUME Mut # "M_PREVIOUS_QUESTION", Mut # "M_TIME_LIMIT"
    PROVE  Spec => []ClosedOnThreeFifths
<1>1. InvC /\ [Next]_vars => InvC'
  BY NextInvC
<1>2. Init => InvC
  BY InitTypeOK DEF Init, InvC, ClosedOnThreeFifths
<1>3. InvC => ClosedOnThreeFifths
  BY DEF InvC
<1> QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

-----------------------------------------------------------------------------
(* The rules as written                                                     *)

THEOREM SafeAlways ==
  ASSUME Mut = "none"
  PROVE  Spec => []Safety
<1>1. Spec => []ClotureThreshold
  BY ClotureThresholdAlways
<1>2. Spec => []DebateEndsByCloture
  BY DebateEndsByClotureAlways
<1>3. Spec => []MajorityFloor
  BY MajorityFloorAlways
<1>4. Spec => []RulesByTwoThirds
  BY RulesByTwoThirdsAlways
<1>5. Spec => []ClosedOnThreeFifths
  BY ClosedOnThreeFifthsAlways
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, PTL DEF Safety

-----------------------------------------------------------------------------
(* What each mutation admits. The counterexamples themselves are TLC's.     *)

\* A majority closes debate, whatever the threshold.
LEMMA MutPreviousQuestionAdmits ==
  ASSUME Mut = "M_PREVIOUS_QUESTION", NEW m \in Measures, Majority(support[m])
  PROVE  ClotureCarries(m)
BY DEF ClotureCarries

\* Debate on any measure runs out.
LEMMA MutTimeLimitAdmits ==
  ASSUME Mut = "M_TIME_LIMIT", NEW m \in Measures
  PROVE  TimeLimited(m)
BY DEF TimeLimited

\* A measure passes on any count.
LEMMA MutNoMajorityAdmits ==
  ASSUME Mut = "M_NO_MAJORITY", NEW m \in Measures
  PROVE  PassCarries(m)
BY DEF PassCarries

\* A majority amends the rule, however many are present.
LEMMA MutConstitutionalOptionAdmits ==
  ASSUME Mut = "M_CONSTITUTIONAL_OPTION", NEW ayes \in Counts, NEW present \in Counts,
         Majority(ayes)
  PROVE  RulesCarry(ayes, present)
BY DEF RulesCarry

=============================================================================
