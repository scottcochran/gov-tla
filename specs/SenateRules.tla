----------------------------- MODULE SenateRules -----------------------------
(***************************************************************************)
(* The Senate filibuster: Rule XXII cloture, the reconciliation time      *)
(* limit, and the two ways the cloture threshold is lowered - by amending *)
(* the rule, and by precedent (the "nuclear option"). A SKETCH, unproved.  *)
(*                                                                         *)
(* This is not constitutional text. Art. I s.5 cl.2 lets each House       *)
(* "determine the Rules of its Proceedings"; everything here is what the  *)
(* Senate has determined under it, layered on the majority passage that   *)
(* Constitution.tla models in PassChamber. The module stands alone and    *)
(* does not extend Constitution.tla, which is cited by digest and frozen; *)
(* a later refinement would show that every Pass here is a PassChamber    *)
(* for the Senate there.                                                  *)
(*                                                                         *)
(* Rules as of 1975 (Init): cloture on any measure or nomination by three-*)
(* fifths of the Senators duly chosen and sworn (Rule XXII cl.2); cloture *)
(* on a measure amending the rules by two-thirds of those present and    *)
(* voting (the same clause); debate on a reconciliation bill limited by   *)
(* statute (Congressional Budget Act of 1974, s.310(e)), so it needs no   *)
(* cloture. The precedents of 21 Nov 2013 (nominations other than to the  *)
(* Supreme Court) and 6 Apr 2017 (the Supreme Court) are both the one     *)
(* step Nuclear(m) for a nomination; the module does not split them.      *)
(*                                                                         *)
(* PROPERTIES (each a state predicate; a "flag" is a variable the one     *)
(* violating action would set, and never clears)                           *)
(*   ClotureThreshold     Rule XXII  debate on a measure is closed by     *)
(*                        cloture only when the votes meet the threshold  *)
(*                        then in force for its kind (flag shortCloture). *)
(*   DebateEndsByCloture  Rule XXII; Budget Act s.310(e)  debate on a      *)
(*                        measure ends without cloture only if it is a    *)
(*                        reconciliation bill (flag debateCut).           *)
(*   MajorityFloor        Art. I s.5, s.7, as Constitution.tla reads them  *)
(*                        no measure passes without a majority of the      *)
(*                        Senate; the rules raise the bar and never lower *)
(*                        it (flag minorityPassage).                      *)
(*   RulesByTwoThirds     Rule XXII cl.2; Rule V cl.2 (1959)  the cloture *)
(*                        rule is amended, as a rule, only on two-thirds  *)
(*                        of those present and voting, a quorum present   *)
(*                        (flag shortRulesChange).                        *)
(*   ClosedOnThreeFifths  the filibuster itself: no measure other than a  *)
(*                        reconciliation bill is past debate (Closed,     *)
(*                        Passed or Rejected) while three-fifths cloture  *)
(*                        governs its kind unless three-fifths support    *)
(*                        it. Not a flag: it holds because the threshold  *)
(*                        only falls, so if it is three-fifths now it was *)
(*                        three-fifths when debate closed.                *)
(*                                                                         *)
(* MUTATIONS (Mut; each removes one check, and the property it must       *)
(* break is named; it must break no other)                                 *)
(*   M_PREVIOUS_QUESTION  a majority closes debate, as the House does by  *)
(*                        the previous question. The Senate's rules of    *)
(*                        1789 had a previous-question motion, dropped in *)
(*                        1806; whether it ever served to close debate is *)
(*                        doubted. Breaks ClotureThreshold and            *)
(*                        ClosedOnThreeFifths. Binds only where a         *)
(*                        majority is less than three-fifths (seven       *)
(*                        Senators, not five).                            *)
(*   M_TIME_LIMIT         every measure is under a statutory debate       *)
(*                        limit, as reconciliation is. No earlier law.    *)
(*                        Breaks DebateEndsByCloture and                  *)
(*                        ClosedOnThreeFifths.                            *)
(*   M_NO_MAJORITY        a closed measure passes without a majority. No  *)
(*                        earlier law. Breaks MajorityFloor.              *)
(*   M_CONSTITUTIONAL_OPTION  Rule XXII amended by a majority: the        *)
(*                        "constitutional option", that a new Senate may  *)
(*                        adopt its rules by majority, argued in 1917,    *)
(*                        1953, 1957 (Vice President Nixon's advisory     *)
(*                        opinion) and 1975, and never adopted; Rule V    *)
(*                        cl.2 (1959) says the rules continue. Breaks     *)
(*                        RulesByTwoThirds.                               *)
(*                                                                         *)
(* WITNESSES (each must be VIOLATED unmutated, so that what it forbids is *)
(* reachable)                                                              *)
(*   NeverPassed, NeverRejected   a measure passes; one is rejected.      *)
(*   NeverReconciledOnMajority    a reconciliation bill passes with a     *)
(*                        majority short of three-fifths: the statute's   *)
(*                        route around the filibuster.                    *)
(*   NeverLawOnMajority   a bill passes with a majority short of three-   *)
(*                        fifths. Reachable only after a majority lowers  *)
(*                        the threshold: the filibuster is not entrenched *)
(*                        against the majority it binds.                  *)
(*   NeverConfirmedOnMajority     the same for a nomination (2013, 2017). *)
(*   NeverPrecedent, NeverRulesChange   each route to a lower threshold.  *)
(*   NeverNominationsOnly the rules since 2013: majority cloture on       *)
(*                        nominations, three-fifths on legislation.       *)
(*                                                                         *)
(* LIVENESS. MajorityPrevails: a measure a majority supports, once taken  *)
(* up, passes. Under FairSpec (the floor votes whenever a vote would      *)
(* carry, and the reconciliation clock runs) it is VIOLATED: a bill with  *)
(* a majority short of three-fifths is debated forever. That is the       *)
(* filibuster, stated as the failure of a leads-to. It HOLDS under        *)
(* M_PREVIOUS_QUESTION and M_TIME_LIMIT, and under NuclearSpec, which     *)
(* adds that a majority facing a filibuster eventually goes nuclear: the  *)
(* filibuster delays only a majority that declines to end it.             *)
(* ReconciliationPrevails HOLDS under FairSpec and fails without the      *)
(* clock (SpecNoClock). NoBehaviour is violated under each fair spec, so  *)
(* each has a behaviour.                                                  *)
(*                                                                         *)
(* DEADLOCK. Once every measure is decided and both thresholds lowered,   *)
(* nothing is enabled. The rows run with -deadlock; one DEADLOCK row      *)
(* shows that end is reached.                                             *)
(*                                                                         *)
(* ABSTRACTED: who the Senators are (votes are counts, and a measure's    *)
(* support is fixed when it is taken up, so every vote on it is the same  *)
(* count: no Senator changes sides); the motion to proceed and its own    *)
(* cloture (Proceed is one unconditional step); the thirty hours after    *)
(* cloture, amendments, holds, unanimous consent and the "talking"         *)
(* filibuster (debate either goes on or is closed); vacancies (three-     *)
(* fifths is of the whole Senate); the Vice President's casting vote (no  *)
(* row has an even Senate); the Byrd rule and what may be reconciled;     *)
(* cloture on a reconciliation bill (never needed, not modelled);         *)
(* raising the threshold again (it only falls); the House.                *)
(*                                                                         *)
(* CONSTANTS are unconstrained beyond the named ASSUMEs.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Mut,              \* "none", or the one check removed
  Senators,         \* the Senate
  Legislation,      \* bills and resolutions under Rule XXII
  Nominations,      \* nominations under Rule XXII
  Reconciliations   \* reconciliation bills: debate limited by statute

Muts == {"none", "M_PREVIOUS_QUESTION", "M_TIME_LIMIT", "M_NO_MAJORITY",
         "M_CONSTITUTIONAL_OPTION"}

ASSUME MutOK          == Mut \in Muts
ASSUME FiniteSenate   == IsFiniteSet(Senators) /\ Senators # {}
ASSUME KindsDisjoint  == /\ Legislation \cap Nominations = {}
                         /\ Legislation \cap Reconciliations = {}
                         /\ Nominations \cap Reconciliations = {}

Measures   == Legislation \cup Nominations \cup Reconciliations
N          == Cardinality(Senators)
Counts     == 0..N

\* The kinds a cloture threshold is kept for. A reconciliation bill never
\* needs one.
Kinds      == {"Legislation", "Nomination"}
Kind(m)    == IF m \in Nominations THEN "Nomination" ELSE "Legislation"
Stages     == {"Pending", "Debate", "Closed", "Passed", "Rejected"}
Thresholds == {"ThreeFifths", "Majority"}
Routes     == {"None", "Rules", "Precedent"}

Majority(n)       == 2 * n > N
ThreeFifths(n)    == 5 * n >= 3 * N     \* of the Senators duly chosen and sworn
TwoThirdsOf(n, p) == 3 * n >= 2 * p     \* of those present and voting
Meets(t, n)       == IF t = "ThreeFifths" THEN ThreeFifths(n) ELSE Majority(n)

VARIABLES
  stage,            \* each measure's place on the floor
  support,          \* how many Senators support it (fixed when taken up)
  cloture,          \* the threshold in force for each kind
  changedBy,        \* how each kind's threshold was lowered, if it was
  shortCloture,     \* debate was closed on fewer votes than the threshold
  debateCut,        \* debate ended without cloture on a non-reconciliation measure
  minorityPassage,  \* a measure passed without a majority
  shortRulesChange  \* Rule XXII was amended on fewer than two-thirds present

ruleVars == <<cloture, changedBy>>
flagVars == <<shortCloture, debateCut, minorityPassage, shortRulesChange>>
vars     == <<stage, support, ruleVars, flagVars>>

TypeOK ==
  /\ stage     \in [Measures -> Stages]
  /\ support   \in [Measures -> Counts]
  /\ cloture   \in [Kinds -> Thresholds]
  /\ changedBy \in [Kinds -> Routes]
  /\ shortCloture \in BOOLEAN /\ debateCut \in BOOLEAN
  /\ minorityPassage \in BOOLEAN /\ shortRulesChange \in BOOLEAN

Init ==
  /\ stage     = [m \in Measures |-> "Pending"]
  /\ support   = [m \in Measures |-> 0]
  /\ cloture   = [k \in Kinds |-> "ThreeFifths"]
  /\ changedBy = [k \in Kinds |-> "None"]
  /\ shortCloture = FALSE /\ debateCut = FALSE
  /\ minorityPassage = FALSE /\ shortRulesChange = FALSE

(* ---- The checks each mutation removes -------------------------------- *)

ClotureCarries(m) ==
  IF Mut = "M_PREVIOUS_QUESTION" THEN Majority(support[m])
                                 ELSE Meets(cloture[Kind(m)], support[m])
TimeLimited(m)    == Mut = "M_TIME_LIMIT" \/ m \in Reconciliations
PassCarries(m)    == Mut = "M_NO_MAJORITY" \/ Majority(support[m])
RulesCarry(ayes, present) ==
  IF Mut = "M_CONSTITUTIONAL_OPTION" THEN Majority(ayes)
                                     ELSE TwoThirdsOf(ayes, present)

(* ---- The floor -------------------------------------------------------- *)

\* A measure is taken up, with the support it will have throughout.
Proceed(m, n) ==
  /\ stage[m] = "Pending"
  /\ stage'   = [stage EXCEPT ![m] = "Debate"]
  /\ support' = [support EXCEPT ![m] = n]
  /\ UNCHANGED <<ruleVars, flagVars>>

\* Rule XXII: debate is closed when enough Senators sign and vote cloture.
InvokeCloture(m) ==
  /\ stage[m] = "Debate"
  /\ m \notin Reconciliations
  /\ ClotureCarries(m)
  /\ stage' = [stage EXCEPT ![m] = "Closed"]
  /\ shortCloture' = (shortCloture \/ ~Meets(cloture[Kind(m)], support[m]))
  /\ UNCHANGED <<support, ruleVars, debateCut, minorityPassage, shortRulesChange>>

\* Budget Act s.310(e): debate on a reconciliation bill runs out.
DebateExpires(m) ==
  /\ stage[m] = "Debate"
  /\ TimeLimited(m)
  /\ stage' = [stage EXCEPT ![m] = "Closed"]
  /\ debateCut' = (debateCut \/ m \notin Reconciliations)
  /\ UNCHANGED <<support, ruleVars, shortCloture, minorityPassage, shortRulesChange>>

\* The vote on passage (or confirmation): a majority.
Pass(m) ==
  /\ stage[m] = "Closed"
  /\ PassCarries(m)
  /\ stage' = [stage EXCEPT ![m] = "Passed"]
  /\ minorityPassage' = (minorityPassage \/ ~Majority(support[m]))
  /\ UNCHANGED <<support, ruleVars, shortCloture, debateCut, shortRulesChange>>

Reject(m) ==
  /\ stage[m] = "Closed"
  /\ ~Majority(support[m])
  /\ stage' = [stage EXCEPT ![m] = "Rejected"]
  /\ UNCHANGED <<support, ruleVars, flagVars>>

(* ---- Lowering the threshold ------------------------------------------- *)

\* The nuclear option: during debate on m, a point of order that cloture
\* on m's kind needs only a majority; the chair rules against it, and the
\* majority that supports m overturns the ruling. A precedent, not a rule.
Nuclear(m) ==
  /\ stage[m] = "Debate"
  /\ m \notin Reconciliations
  /\ cloture[Kind(m)] = "ThreeFifths"
  /\ Majority(support[m])
  /\ cloture'   = [cloture EXCEPT ![Kind(m)] = "Majority"]
  /\ changedBy' = [changedBy EXCEPT ![Kind(m)] = "Precedent"]
  /\ UNCHANGED <<stage, support, flagVars>>

\* Rule XXII amended as a rule: cloture on the resolution by two-thirds of
\* those present and voting, a quorum (a majority) present.
AmendRule(k, ayes, present) ==
  /\ cloture[k] = "ThreeFifths"
  /\ Majority(present)
  /\ ayes <= present
  /\ RulesCarry(ayes, present)
  /\ cloture'   = [cloture EXCEPT ![k] = "Majority"]
  /\ changedBy' = [changedBy EXCEPT ![k] = "Rules"]
  /\ shortRulesChange' = (shortRulesChange \/ ~TwoThirdsOf(ayes, present))
  /\ UNCHANGED <<stage, support, shortCloture, debateCut, minorityPassage>>

Next ==
  \/ \E m \in Measures :
       \/ \E n \in Counts : Proceed(m, n)
       \/ InvokeCloture(m) \/ DebateExpires(m)
       \/ Pass(m) \/ Reject(m) \/ Nuclear(m)
  \/ \E k \in Kinds, ayes \in Counts, present \in Counts : AmendRule(k, ayes, present)

Spec == Init /\ [][Next]_vars

(* ---- Safety ----------------------------------------------------------- *)

ClotureThreshold    == ~shortCloture
DebateEndsByCloture == ~debateCut
MajorityFloor       == ~minorityPassage
RulesByTwoThirds    == ~shortRulesChange
ClosedOnThreeFifths ==
  \A m \in Measures \ Reconciliations :
    (stage[m] \in {"Closed", "Passed", "Rejected"} /\ cloture[Kind(m)] = "ThreeFifths")
      => ThreeFifths(support[m])

Safety ==
  /\ ClotureThreshold /\ DebateEndsByCloture /\ MajorityFloor
  /\ RulesByTwoThirds /\ ClosedOnThreeFifths

(* ---- Witnesses: each must be violated --------------------------------- *)

PassedShort(S) == \E m \in S : stage[m] = "Passed" /\ ~ThreeFifths(support[m])

NeverPassed               == \A m \in Measures : stage[m] # "Passed"
NeverRejected             == \A m \in Measures : stage[m] # "Rejected"
NeverReconciledOnMajority == ~PassedShort(Reconciliations)
NeverLawOnMajority        == ~PassedShort(Legislation)
NeverConfirmedOnMajority  == ~PassedShort(Nominations)
NeverPrecedent            == \A k \in Kinds : changedBy[k] # "Precedent"
NeverRulesChange          == \A k \in Kinds : changedBy[k] # "Rules"
NeverNominationsOnly      ==
  ~(cloture["Nomination"] = "Majority" /\ cloture["Legislation"] = "ThreeFifths")

(* ---- Liveness ---------------------------------------------------------- *)

Backed(m) == stage[m] = "Debate" /\ Majority(support[m])

MajorityPrevails       == \A m \in Measures : Backed(m) ~> (stage[m] = "Passed")
ReconciliationPrevails == \A m \in Reconciliations : Backed(m) ~> (stage[m] = "Passed")

\* The floor's obligation: a vote that would carry is taken.
FloorVotes == \A m \in Measures : WF_vars(InvokeCloture(m)) /\ WF_vars(Pass(m))
\* The statute's: limited debate runs out.
ClockRuns  == \A m \in Measures : WF_vars(DebateExpires(m))
\* Not an obligation of anyone: the majority's choice to end a filibuster.
MajorityGoesNuclear == \A m \in Measures : WF_vars(Nuclear(m))

FairSpec    == Spec /\ FloorVotes /\ ClockRuns
SpecNoClock == Spec /\ FloorVotes
NuclearSpec == FairSpec /\ MajorityGoesNuclear

NoBehaviour == <>(shortCloture /\ ~shortCloture)

=============================================================================
