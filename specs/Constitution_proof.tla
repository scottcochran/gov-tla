------------------------- MODULE Constitution_proof -------------------------
(***************************************************************************)
(* TLAPS proofs of the safety properties of Constitution.tla. The base    *)
(* module is extended and not edited; its digest is on the Modules: line  *)
(* of results/Constitution-proof-results-*.txt. Each theorem is Spec =>   *)
(* []P for every value of the constants the base module's named ASSUMEs   *)
(* admit, under the hypothesis in brackets: exactly the mutations whose   *)
(* rows against P read COUNTEREXAMPLE in results/Constitution-results-*.  *)
(*                                                                         *)
(*   BicameralismAlways        [Mut # M_UNICAMERAL]                       *)
(*   OriginationAlways         [Mut # M_ORIGIN]                           *)
(*   PresentmentAlways         [Mut # M_OVR_ONE_HOUSE, M_OVR_VOTE]        *)
(*   TenDayRuleAlways          [Mut # M_NO_POCKET, M_POCKET_SITTING]      *)
(*   IncompatibilityAlways     [Mut # M_INCOMPAT]                         *)
(*   CongressNotImpeachableAlways [Mut # M_INCOMPAT, M_BLOUNT]            *)
(*   ConvictionTwoThirdsAlways [Mut # M_CONVICT_VOTE]                     *)
(*   TwoTermLimitAlways        [Mut # M_XXII]                             *)
(*   DisqualificationAlways    [Mut # M_DQ, M_VP_RECHECK,                 *)
(*                              M_CONSENT_RECHECK, M_NO_REMOVAL]          *)
(*   PresidentNotVPAlways      [Mut # M_ONE_PERSON]                       *)
(*   XXVBothHousesAlways       [Mut # M_XXV_SENATE]                       *)
(*   RecessAppointmentsInRecessAlways [Mut # M_PRO_FORMA]                 *)
(*   ArticleVAlways            [Mut # M_RATIFY_VOTE, M_SUFFRAGE]          *)
(*   SafeAlways                [Mut = "none"]  Spec => []Safety           *)
(* TypeOK is proved under every mutation (InitTypeOK, NextTypeOK).        *)
(*                                                                         *)
(* INDUCTIVE STRENGTHENING, in prose. Bicameralism, Origination,          *)
(* Presentment, TwoTermLimit and ArticleV are inductive as stated, with   *)
(* TypeOK: the one action that could break each is decided by its guard,  *)
(* and a bill's or amendment's record is never touched once it is law or  *)
(* ratified. TenDayRule, ConvictionTwoThirds, XXVBothHouses and           *)
(* RecessAppointmentsInRecess are flags, false initially and raised only  *)
(* by one action, whose guard makes the raised value false. Three need    *)
(* more:                                                                  *)
(*   Incompatibility: IncompatPW, the property pointwise, and no pending  *)
(*     nominee (Vice President or officer) is a member of Congress, so    *)
(*     ConfirmVP and Consent cannot seat one. CongressNotImpeachable rests *)
(*     on it: Impeach reaches only officeholders, and officeholders are   *)
(*     not members; hence M_INCOMPAT among its hypotheses.               *)
(*   Disqualification: DisqPW, the property pointwise; Convict removes   *)
(*     the person it disqualifies from every office and the successor is  *)
(*     not disqualified by the invariant itself.                          *)
(*   PresidentNotVP: PresidentNotVPInv, while a XXV s.2 nomination is     *)
(*     pending the Vice Presidency is vacant and the nominee is not the   *)
(*     President, so confirmation and every succession keep the two       *)
(*     offices apart.                                                     *)
(* Next is split once (NextDef) into the session, legislation, the        *)
(* Executive, appointments, impeachment and Article V; three frame lemmas *)
(* say which variables each part leaves alone, so each Next lemma has one *)
(* step per action of the machine its property reads.                     *)
(*                                                                         *)
(* NAMED ASSUMPTIONS used: the base module's NoOneIsNoPerson,             *)
(* CongressPersons, EligiblePersons, RevenueAreBills,                     *)
(* SuffrageAreAmendments and FiniteBodies (for StateVotesNat). Nothing    *)
(* else is assumed: no bound on any constant, no chamber or State count.  *)
(*                                                                         *)
(* MUTATION LEMMAS (last section) state what each mutation admits, as an  *)
(* ENABLED fact or as the guard it opens; the counterexamples are TLC's.  *)
(*                                                                         *)
(* NOT PROVED. The witnesses (Never...), which are existential and stay   *)
(* with TLC. PresentedBillsResolve, the ten-day rule's leads-to: it is    *)
(* quantified over bills inside the temporal body (\A b : P(b) ~> Q(b))   *)
(* with an ENABLED premise over b for WF1, the case for which the pinned  *)
(* prover has no sound route under the writing rules; it is checked by    *)
(* TLC only, in the liveness rows. ElectionsBound is a TLC device only.  *)
(*                                                                         *)
(* CHECK: python3 scripts/proof_results.py Constitution --threads 2, then *)
(* python3 scripts/flip_test.py Constitution <each mutation above>.       *)
(***************************************************************************)
EXTENDS Constitution, FiniteSetTheorems, TLAPS

-----------------------------------------------------------------------------
(* The steps of Next, grouped as Next groups them.                         *)

BillStep(b) ==
  \/ \E c \in Chambers : Introduce(b, c)
  \/ \E c \in Chambers : \E n \in VotesIn(c) : PassChamber(b, c, n)
  \/ Sign(b) \/ Veto(b)
  \/ BecomeLawUnsigned(b) \/ PocketVeto(b) \/ FailOverride(b)
  \/ \E c \in Chambers : \E n \in VotesIn(c) : Override(b, c, n)

ExecStep ==
  \/ \E p, v \in Persons : Elect(p, v)
  \/ PresidentVacates \/ VicePresidentVacates \/ RejectVP
  \/ \E p \in Persons : NominateVP(p)
  \/ \E h \in VotesIn("House"), s \in VotesIn("Senate") : ConfirmVP(h, s)

OfficeStep(o) ==
  \/ \E p \in Persons : Nominate(o, p) \/ RecessAppoint(o, p)
  \/ \E n \in VotesIn("Senate") : Consent(o, n)
  \/ Reject(o) \/ OfficerResigns(o)

PersonStep(p) ==
  \/ \E n \in VotesIn("House") : Impeach(p, n)
  \/ \E n \in VotesIn("Senate"), dq \in BOOLEAN : Convict(p, n, dq)
  \/ Acquit(p)

AmendStep(a) ==
  \/ \E h \in VotesIn("House"), s \in VotesIn("Senate") : ProposeByCongress(a, h, s)
  \/ \E n \in StateVotes : ProposeByConvention(a, n)
  \/ \E n \in StateVotes : Ratify(a, n)

-----------------------------------------------------------------------------
(* The inductive strengthenings.                                           *)

\* Incompatibility, pointwise, and the pending nominees: no nominee is a
\* member, so confirmation cannot seat one.
IncompatPW ==
  /\ president \notin Congress
  /\ vicePresident \notin Congress
  /\ \A o \in Offices : officer[o] \notin Congress
  /\ vpNominee \notin Congress
  /\ \A o \in Offices : nominee[o] \notin Congress

\* Disqualification, pointwise.
DisqPW ==
  /\ president \notin disqualified
  /\ vicePresident \notin disqualified
  /\ \A o \in Offices : officer[o] \notin disqualified

\* While a XXV s.2 nomination is pending the Vice Presidency is vacant and
\* the nominee is not the President.
PresidentNotVPInv ==
  /\ PresidentNotVP
  /\ vpNominee # NoOne => vpNominee # president /\ vicePresident = NoOne

-----------------------------------------------------------------------------
(* Next, split; and what each part leaves alone.                           *)

LEMMA NextDef ==
  Next <=> \/ Convene \/ Adjourn
           \/ \E bl \in Bills : BillStep(bl)
           \/ ExecStep
           \/ \E of \in Offices : OfficeStep(of)
           \/ \E pp \in Persons : PersonStep(pp)
           \/ \E am \in Amendments : AmendStep(am)
BY DEF Next, BillStep, ExecStep, OfficeStep, PersonStep, AmendStep

LEMMA NonBillFrame ==
  ASSUME Convene \/ Adjourn \/ ExecStep \/ (\E of \in Offices : OfficeStep(of))
         \/ (\E pp \in Persons : PersonStep(pp)) \/ (\E am \in Amendments : AmendStep(am))
  PROVE  UNCHANGED <<bill, shortOverride, tenDayBreach>>
<1> USE DEF billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE Convene \/ Adjourn
  BY <1>1 DEF Convene, Adjourn
<1>2. CASE ExecStep
  BY <1>2 DEF ExecStep, Elect, PresidentVacates, VicePresidentVacates, RejectVP, NominateVP, ConfirmVP
<1>3. CASE \E of \in Offices : OfficeStep(of)
  BY <1>3 DEF OfficeStep, Nominate, RecessAppoint, Consent, Reject, OfficerResigns
<1>4. CASE \E pp \in Persons : PersonStep(pp)
  BY <1>4 DEF PersonStep, Impeach, Convict, Acquit
<1>5. CASE \E am \in Amendments : AmendStep(am)
  BY <1>5 DEF AmendStep, ProposeByCongress, ProposeByConvention, Ratify
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA NonExecFrame ==
  ASSUME Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  PROVE  UNCHANGED <<execVars, apptVars, impVars, shortConviction, vpWithoutHouse, recessWhileSitting>>
<1> USE DEF billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE Convene
  BY <1>1 DEF Convene
<1>2. CASE \E bl \in Bills : BillStep(bl)
  BY <1>2 DEF BillStep, Introduce, PassChamber, Sign, Veto, BecomeLawUnsigned, PocketVeto,
              FailOverride, Override
<1>3. CASE \E am \in Amendments : AmendStep(am)
  BY <1>3 DEF AmendStep, ProposeByCongress, ProposeByConvention, Ratify
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA NonAmendFrame ==
  ASSUME Convene \/ Adjourn \/ (\E bl \in Bills : BillStep(bl)) \/ ExecStep
         \/ (\E of \in Offices : OfficeStep(of)) \/ (\E pp \in Persons : PersonStep(pp))
  PROVE  UNCHANGED amend
<1> USE DEF billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE Convene \/ Adjourn
  BY <1>1 DEF Convene, Adjourn
<1>2. CASE \E bl \in Bills : BillStep(bl)
  BY <1>2 DEF BillStep, Introduce, PassChamber, Sign, Veto, BecomeLawUnsigned, PocketVeto,
              FailOverride, Override
<1>3. CASE ExecStep
  BY <1>3 DEF ExecStep, Elect, PresidentVacates, VicePresidentVacates, RejectVP, NominateVP, ConfirmVP
<1>4. CASE \E of \in Offices : OfficeStep(of)
  BY <1>4 DEF OfficeStep, Nominate, RecessAppoint, Consent, Reject, OfficerResigns
<1>5. CASE \E pp \in Persons : PersonStep(pp)
  BY <1>5 DEF PersonStep, Impeach, Convict, Acquit
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5

-----------------------------------------------------------------------------
(* The type invariant, under every mutation.                               *)

LEMMA StateVotesNat == StateVotes \subseteq Nat
<1>1. Cardinality(States) \in Nat
  BY FiniteBodies, FS_CardinalityType
<1> QED
  BY <1>1 DEF StateVotes

LEMMA InitTypeOK == Init => TypeOK
BY NoOneIsNoPerson DEF Init, TypeOK, BillRec, BillStatus, Hows, AmendRec, Seat

LEMMA NextTypeOK ==
  ASSUME TypeOK, [Next]_vars
  PROVE  TypeOK'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, BillRec, BillStatus, Hows, AmendRec, Seat, Chambers, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene
  BY <1>2 DEF Convene
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. ASSUME NEW bl \in Bills, BillStep(bl)
      PROVE  TypeOK'
  <2>1. ASSUME NEW ch \in Chambers, Introduce(bl, ch)
        PROVE  TypeOK'
    BY <2>1 DEF Introduce
  <2>2. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), PassChamber(bl, ch, k)
        PROVE  TypeOK'
    BY <2>2 DEF PassChamber
  <2>3. CASE Sign(bl)
    BY <2>3 DEF Sign
  <2>4. CASE Veto(bl)
    BY <2>4 DEF Veto
  <2>5. CASE BecomeLawUnsigned(bl)
    BY <2>5 DEF BecomeLawUnsigned
  <2>6. CASE PocketVeto(bl)
    BY <2>6 DEF PocketVeto
  <2>7. CASE FailOverride(bl)
    BY <2>7 DEF FailOverride
  <2>8. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), Override(bl, ch, k)
        PROVE  TypeOK'
    BY <2>8 DEF Override
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF BillStep
<1>5. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  TypeOK'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  TypeOK'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  TypeOK'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>6. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  TypeOK'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  TypeOK'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  TypeOK'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  TypeOK'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>7. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  TypeOK'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  TypeOK'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  TypeOK'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>7, <2>1, <2>2, <2>3 DEF PersonStep
<1>8. ASSUME NEW am \in Amendments, AmendStep(am)
      PROVE  TypeOK'
  <2>1. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ProposeByCongress(am, hk, sk)
        PROVE  TypeOK'
    BY <2>1 DEF ProposeByCongress
  <2>2. ASSUME NEW k \in StateVotes, ProposeByConvention(am, k)
        PROVE  TypeOK'
    BY <2>2 DEF ProposeByConvention
  <2>3. ASSUME NEW k \in StateVotes, Ratify(am, k)
        PROVE  TypeOK'
    BY <2>3, StateVotesNat DEF Ratify
  <2> QED
    BY <1>8, <2>1, <2>2, <2>3 DEF AmendStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextDef

-----------------------------------------------------------------------------
(* Art. I s.7                                                              *)

LEMMA InitBicameralism == Init => Bicameralism
BY DEF Init, Bicameralism

LEMMA NextBicameralism ==
  ASSUME Mut # "M_UNICAMERAL", TypeOK, Bicameralism, [Next]_vars
  PROVE  Bicameralism'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, Bicameralism, BothHouses, BillRec, Chambers, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ Adjourn \/ ExecStep \/ (\E of \in Offices : OfficeStep(of))
         \/ (\E pp \in Persons : PersonStep(pp)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonBillFrame
<1>3. ASSUME NEW bl \in Bills, BillStep(bl)
      PROVE  Bicameralism'
  <2>1. ASSUME NEW ch \in Chambers, Introduce(bl, ch)
        PROVE  Bicameralism'
    BY <2>1 DEF Introduce
  <2>2. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), PassChamber(bl, ch, k)
        PROVE  Bicameralism'
    BY <2>2 DEF PassChamber
  <2>3. CASE Sign(bl)
    BY <2>3 DEF Sign
  <2>4. CASE Veto(bl)
    BY <2>4 DEF Veto
  <2>5. CASE BecomeLawUnsigned(bl)
    BY <2>5 DEF BecomeLawUnsigned
  <2>6. CASE PocketVeto(bl)
    BY <2>6 DEF PocketVeto
  <2>7. CASE FailOverride(bl)
    BY <2>7 DEF FailOverride
  <2>8. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), Override(bl, ch, k)
        PROVE  Bicameralism'
    BY <2>8 DEF Override
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF BillStep
<1> QED
  BY <1>1, <1>2, <1>3, NextDef

THEOREM BicameralismAlways ==
    ASSUME Mut # "M_UNICAMERAL"
    PROVE  Spec => []Bicameralism
<1>1. TypeOK /\ Bicameralism /\ [Next]_vars => (TypeOK /\ Bicameralism)'
    BY NextTypeOK, NextBicameralism
<1> QED
    BY InitTypeOK, InitBicameralism, <1>1, PTL DEF Spec

LEMMA InitOrigination == Init => Origination
BY RevenueAreBills DEF Init, Origination

LEMMA NextOrigination ==
  ASSUME Mut # "M_ORIGIN", TypeOK, Origination, [Next]_vars
  PROVE  Origination'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, Origination, MayOriginate, BillRec, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ Adjourn \/ ExecStep \/ (\E of \in Offices : OfficeStep(of))
         \/ (\E pp \in Persons : PersonStep(pp)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonBillFrame
<1>3. ASSUME NEW bl \in Bills, BillStep(bl)
      PROVE  Origination'
  <2>1. ASSUME NEW ch \in Chambers, Introduce(bl, ch)
        PROVE  Origination'
    BY <2>1 DEF Introduce
  <2>2. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), PassChamber(bl, ch, k)
        PROVE  Origination'
    BY <2>2 DEF PassChamber
  <2>3. CASE Sign(bl)
    BY <2>3 DEF Sign
  <2>4. CASE Veto(bl)
    BY <2>4 DEF Veto
  <2>5. CASE BecomeLawUnsigned(bl)
    BY <2>5 DEF BecomeLawUnsigned
  <2>6. CASE PocketVeto(bl)
    BY <2>6 DEF PocketVeto
  <2>7. CASE FailOverride(bl)
    BY <2>7 DEF FailOverride
  <2>8. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), Override(bl, ch, k)
        PROVE  Origination'
    BY <2>8 DEF Override
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF BillStep
<1> QED
  BY <1>1, <1>2, <1>3, NextDef

THEOREM OriginationAlways ==
    ASSUME Mut # "M_ORIGIN"
    PROVE  Spec => []Origination
<1>1. TypeOK /\ Origination /\ [Next]_vars => (TypeOK /\ Origination)'
    BY NextTypeOK, NextOrigination
<1> QED
    BY InitTypeOK, InitOrigination, <1>1, PTL DEF Spec

LEMMA InitPresentment == Init => Presentment
BY DEF Init, Presentment

LEMMA NextPresentment ==
  ASSUME Mut # "M_OVR_ONE_HOUSE", Mut # "M_OVR_VOTE", TypeOK, Presentment, [Next]_vars
  PROVE  Presentment'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, Presentment, OverrideCarries, OverrideComplete, BillRec, Chambers, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ Adjourn \/ ExecStep \/ (\E of \in Offices : OfficeStep(of))
         \/ (\E pp \in Persons : PersonStep(pp)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonBillFrame
<1>3. ASSUME NEW bl \in Bills, BillStep(bl)
      PROVE  Presentment'
  <2>1. ASSUME NEW ch \in Chambers, Introduce(bl, ch)
        PROVE  Presentment'
    BY <2>1 DEF Introduce
  <2>2. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), PassChamber(bl, ch, k)
        PROVE  Presentment'
    BY <2>2 DEF PassChamber
  <2>3. CASE Sign(bl)
    BY <2>3 DEF Sign
  <2>4. CASE Veto(bl)
    BY <2>4 DEF Veto
  <2>5. CASE BecomeLawUnsigned(bl)
    BY <2>5 DEF BecomeLawUnsigned
  <2>6. CASE PocketVeto(bl)
    BY <2>6 DEF PocketVeto
  <2>7. CASE FailOverride(bl)
    BY <2>7 DEF FailOverride
  <2>8. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), Override(bl, ch, k)
        PROVE  Presentment'
    BY <2>8 DEF Override
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF BillStep
<1> QED
  BY <1>1, <1>2, <1>3, NextDef

THEOREM PresentmentAlways ==
    ASSUME Mut # "M_OVR_ONE_HOUSE", Mut # "M_OVR_VOTE"
    PROVE  Spec => []Presentment
<1>1. TypeOK /\ Presentment /\ [Next]_vars => (TypeOK /\ Presentment)'
    BY NextTypeOK, NextPresentment
<1> QED
    BY InitTypeOK, InitPresentment, <1>1, PTL DEF Spec

LEMMA InitTenDayRule == Init => TenDayRule
BY DEF Init, TenDayRule

LEMMA NextTenDayRule ==
  ASSUME Mut # "M_NO_POCKET", Mut # "M_POCKET_SITTING", TypeOK, TenDayRule, [Next]_vars
  PROVE  TenDayRule'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, TenDayRule, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ Adjourn \/ ExecStep \/ (\E of \in Offices : OfficeStep(of))
         \/ (\E pp \in Persons : PersonStep(pp)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonBillFrame
<1>3. ASSUME NEW bl \in Bills, BillStep(bl)
      PROVE  TenDayRule'
  <2>1. ASSUME NEW ch \in Chambers, Introduce(bl, ch)
        PROVE  TenDayRule'
    BY <2>1 DEF Introduce
  <2>2. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), PassChamber(bl, ch, k)
        PROVE  TenDayRule'
    BY <2>2 DEF PassChamber
  <2>3. CASE Sign(bl)
    BY <2>3 DEF Sign
  <2>4. CASE Veto(bl)
    BY <2>4 DEF Veto
  <2>5. CASE BecomeLawUnsigned(bl)
    BY <2>5 DEF BecomeLawUnsigned
  <2>6. CASE PocketVeto(bl)
    BY <2>6 DEF PocketVeto
  <2>7. CASE FailOverride(bl)
    BY <2>7 DEF FailOverride
  <2>8. ASSUME NEW ch \in Chambers, NEW k \in VotesIn(ch), Override(bl, ch, k)
        PROVE  TenDayRule'
    BY <2>8 DEF Override
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF BillStep
<1> QED
  BY <1>1, <1>2, <1>3, NextDef

THEOREM TenDayRuleAlways ==
    ASSUME Mut # "M_NO_POCKET", Mut # "M_POCKET_SITTING"
    PROVE  Spec => []TenDayRule
<1>1. TypeOK /\ TenDayRule /\ [Next]_vars => (TypeOK /\ TenDayRule)'
    BY NextTypeOK, NextTenDayRule
<1> QED
    BY InitTypeOK, InitTenDayRule, <1>1, PTL DEF Spec

-----------------------------------------------------------------------------
(* Art. I s.6 cl.2, Art. II s.4                                            *)

LEMMA InitIncompatPW == Init => IncompatPW
BY NoOneIsNoPerson, CongressPersons DEF Init, IncompatPW, Congress

LEMMA IncompatPWImplies == IncompatPW => Incompatibility
BY DEF IncompatPW, Incompatibility, Officeholders

LEMMA NextIncompatPW ==
  ASSUME Mut # "M_INCOMPAT", TypeOK, IncompatPW, [Next]_vars
  PROVE  IncompatPW'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, IncompatPW, Compatible, Seat, Congress, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  IncompatPW'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  IncompatPW'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  IncompatPW'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  IncompatPW'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  IncompatPW'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  IncompatPW'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  IncompatPW'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  IncompatPW'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  IncompatPW'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  IncompatPW'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM IncompatibilityAlways ==
    ASSUME Mut # "M_INCOMPAT"
    PROVE  Spec => []Incompatibility
<1>1. TypeOK /\ IncompatPW /\ [Next]_vars => (TypeOK /\ IncompatPW)'
    BY NextTypeOK, NextIncompatPW
<1>2. TypeOK /\ IncompatPW => Incompatibility
    BY IncompatPWImplies
<1> QED
    BY InitTypeOK, InitIncompatPW, <1>1, <1>2, PTL DEF Spec

LEMMA InitCongressNotImpeachable == Init => CongressNotImpeachable
BY DEF Init, CongressNotImpeachable

LEMMA NextCongressNotImpeachable ==
  ASSUME Mut # "M_INCOMPAT", Mut # "M_BLOUNT", TypeOK, IncompatPW, CongressNotImpeachable, [Next]_vars
  PROVE  CongressNotImpeachable'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, IncompatPW, CongressNotImpeachable, Impeachable, Officeholders, Seat, Congress, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  CongressNotImpeachable'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  CongressNotImpeachable'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  CongressNotImpeachable'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  CongressNotImpeachable'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  CongressNotImpeachable'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  CongressNotImpeachable'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  CongressNotImpeachable'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  CongressNotImpeachable'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  CongressNotImpeachable'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  CongressNotImpeachable'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM CongressNotImpeachableAlways ==
    ASSUME Mut # "M_INCOMPAT", Mut # "M_BLOUNT"
    PROVE  Spec => []CongressNotImpeachable
<1>1. TypeOK /\ IncompatPW /\ CongressNotImpeachable /\ [Next]_vars
        => (TypeOK /\ IncompatPW /\ CongressNotImpeachable)'
    BY NextTypeOK, NextIncompatPW, NextCongressNotImpeachable
<1> QED
    BY InitTypeOK, InitIncompatPW, InitCongressNotImpeachable, <1>1, PTL DEF Spec

-----------------------------------------------------------------------------
(* Art. I s.3, Amend. XXII, Art. II s.1, Amend. XXV                        *)

LEMMA InitConvictionTwoThirds == Init => ConvictionTwoThirds
BY DEF Init, ConvictionTwoThirds

LEMMA NextConvictionTwoThirds ==
  ASSUME Mut # "M_CONVICT_VOTE", TypeOK, ConvictionTwoThirds, [Next]_vars
  PROVE  ConvictionTwoThirds'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, ConvictionTwoThirds, ConvictionCarries, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  ConvictionTwoThirds'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  ConvictionTwoThirds'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  ConvictionTwoThirds'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  ConvictionTwoThirds'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  ConvictionTwoThirds'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  ConvictionTwoThirds'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  ConvictionTwoThirds'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  ConvictionTwoThirds'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  ConvictionTwoThirds'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  ConvictionTwoThirds'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM ConvictionTwoThirdsAlways ==
    ASSUME Mut # "M_CONVICT_VOTE"
    PROVE  Spec => []ConvictionTwoThirds
<1>1. TypeOK /\ ConvictionTwoThirds /\ [Next]_vars => (TypeOK /\ ConvictionTwoThirds)'
    BY NextTypeOK, NextConvictionTwoThirds
<1> QED
    BY InitTypeOK, InitConvictionTwoThirds, <1>1, PTL DEF Spec

LEMMA InitTwoTermLimit == Init => TwoTermLimit
BY DEF Init, TwoTermLimit

LEMMA NextTwoTermLimit ==
  ASSUME Mut # "M_XXII", TypeOK, TwoTermLimit, [Next]_vars
  PROVE  TwoTermLimit'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, TwoTermLimit, TermAllowed, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  TwoTermLimit'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  TwoTermLimit'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  TwoTermLimit'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  TwoTermLimit'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  TwoTermLimit'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  TwoTermLimit'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  TwoTermLimit'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  TwoTermLimit'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  TwoTermLimit'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  TwoTermLimit'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM TwoTermLimitAlways ==
    ASSUME Mut # "M_XXII"
    PROVE  Spec => []TwoTermLimit
<1>1. TypeOK /\ TwoTermLimit /\ [Next]_vars => (TypeOK /\ TwoTermLimit)'
    BY NextTypeOK, NextTwoTermLimit
<1> QED
    BY InitTypeOK, InitTwoTermLimit, <1>1, PTL DEF Spec

LEMMA InitDisqPW == Init => DisqPW
BY DEF Init, DisqPW

LEMMA DisqPWImplies == TypeOK /\ DisqPW => Disqualification
BY NoOneIsNoPerson DEF TypeOK, DisqPW, Disqualification, Officeholders

LEMMA NextDisqPW ==
  ASSUME Mut # "M_DQ", Mut # "M_VP_RECHECK", Mut # "M_CONSENT_RECHECK", Mut # "M_NO_REMOVAL", TypeOK, DisqPW, [Next]_vars
  PROVE  DisqPW'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, DisqPW, Qualified, RemovedBy, Seat, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  DisqPW'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  DisqPW'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  DisqPW'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  DisqPW'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  DisqPW'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  DisqPW'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  DisqPW'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  DisqPW'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  DisqPW'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  DisqPW'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM DisqualificationAlways ==
    ASSUME Mut # "M_DQ", Mut # "M_VP_RECHECK", Mut # "M_CONSENT_RECHECK", Mut # "M_NO_REMOVAL"
    PROVE  Spec => []Disqualification
<1>1. TypeOK /\ DisqPW /\ [Next]_vars => (TypeOK /\ DisqPW)'
    BY NextTypeOK, NextDisqPW
<1>2. TypeOK /\ DisqPW => Disqualification
    BY DisqPWImplies
<1> QED
    BY InitTypeOK, InitDisqPW, <1>1, <1>2, PTL DEF Spec

LEMMA InitPresidentNotVPInv == Init => PresidentNotVPInv
BY DEF Init, PresidentNotVPInv, PresidentNotVP

LEMMA NextPresidentNotVPInv ==
  ASSUME Mut # "M_ONE_PERSON", TypeOK, PresidentNotVPInv, [Next]_vars
  PROVE  PresidentNotVPInv'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, PresidentNotVPInv, PresidentNotVP, TwoPersons, Seat, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  PresidentNotVPInv'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  PresidentNotVPInv'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  PresidentNotVPInv'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  PresidentNotVPInv'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  PresidentNotVPInv'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  PresidentNotVPInv'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  PresidentNotVPInv'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  PresidentNotVPInv'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  PresidentNotVPInv'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  PresidentNotVPInv'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM PresidentNotVPAlways ==
    ASSUME Mut # "M_ONE_PERSON"
    PROVE  Spec => []PresidentNotVP
<1>1. TypeOK /\ PresidentNotVPInv /\ [Next]_vars => (TypeOK /\ PresidentNotVPInv)'
    BY NextTypeOK, NextPresidentNotVPInv
<1>2. PresidentNotVPInv => PresidentNotVP
    BY DEF PresidentNotVPInv
<1> QED
    BY InitTypeOK, InitPresidentNotVPInv, <1>1, <1>2, PTL DEF Spec

LEMMA InitXXVBothHouses == Init => XXVBothHouses
BY DEF Init, XXVBothHouses

LEMMA NextXXVBothHouses ==
  ASSUME Mut # "M_XXV_SENATE", TypeOK, XXVBothHouses, [Next]_vars
  PROVE  XXVBothHouses'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, XXVBothHouses, HouseConfirms, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  XXVBothHouses'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  XXVBothHouses'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  XXVBothHouses'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  XXVBothHouses'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  XXVBothHouses'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  XXVBothHouses'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  XXVBothHouses'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  XXVBothHouses'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  XXVBothHouses'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  XXVBothHouses'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM XXVBothHousesAlways ==
    ASSUME Mut # "M_XXV_SENATE"
    PROVE  Spec => []XXVBothHouses
<1>1. TypeOK /\ XXVBothHouses /\ [Next]_vars => (TypeOK /\ XXVBothHouses)'
    BY NextTypeOK, NextXXVBothHouses
<1> QED
    BY InitTypeOK, InitXXVBothHouses, <1>1, PTL DEF Spec

-----------------------------------------------------------------------------
(* Art. II s.2 cl.3                                                        *)

LEMMA InitRecessAppointmentsInRecess == Init => RecessAppointmentsInRecess
BY DEF Init, RecessAppointmentsInRecess

LEMMA NextRecessAppointmentsInRecess ==
  ASSUME Mut # "M_PRO_FORMA", TypeOK, RecessAppointmentsInRecess, [Next]_vars
  PROVE  RecessAppointmentsInRecess'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, RecessAppointmentsInRecess, SenateInRecess, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ (\E bl \in Bills : BillStep(bl)) \/ (\E am \in Amendments : AmendStep(am))
  BY <1>2, NonExecFrame
<1>3. CASE Adjourn
  BY <1>3 DEF Adjourn
<1>4. CASE ExecStep
  <2>1. ASSUME NEW pp \in Persons, NEW vv \in Persons, Elect(pp, vv)
        PROVE  RecessAppointmentsInRecess'
    BY <2>1 DEF Elect
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates
  <2>3. CASE VicePresidentVacates
    BY <2>3 DEF VicePresidentVacates
  <2>4. CASE RejectVP
    BY <2>4 DEF RejectVP
  <2>5. ASSUME NEW pp \in Persons, NominateVP(pp)
        PROVE  RecessAppointmentsInRecess'
    BY <2>5 DEF NominateVP
  <2>6. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ConfirmVP(hk, sk)
        PROVE  RecessAppointmentsInRecess'
    BY <2>6 DEF ConfirmVP
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF ExecStep
<1>5. ASSUME NEW of \in Offices, OfficeStep(of)
      PROVE  RecessAppointmentsInRecess'
  <2>1. ASSUME NEW pp \in Persons, Nominate(of, pp)
        PROVE  RecessAppointmentsInRecess'
    BY <2>1 DEF Nominate
  <2>2. ASSUME NEW pp \in Persons, RecessAppoint(of, pp)
        PROVE  RecessAppointmentsInRecess'
    BY <2>2 DEF RecessAppoint
  <2>3. ASSUME NEW k \in VotesIn("Senate"), Consent(of, k)
        PROVE  RecessAppointmentsInRecess'
    BY <2>3 DEF Consent
  <2>4. CASE Reject(of)
    BY <2>4 DEF Reject
  <2>5. CASE OfficerResigns(of)
    BY <2>5 DEF OfficerResigns
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5 DEF OfficeStep
<1>6. ASSUME NEW pp \in Persons, PersonStep(pp)
      PROVE  RecessAppointmentsInRecess'
  <2>1. ASSUME NEW k \in VotesIn("House"), Impeach(pp, k)
        PROVE  RecessAppointmentsInRecess'
    BY <2>1 DEF Impeach
  <2>2. ASSUME NEW k \in VotesIn("Senate"), NEW dd \in BOOLEAN, Convict(pp, k, dd)
        PROVE  RecessAppointmentsInRecess'
    BY <2>2 DEF Convict
  <2>3. CASE Acquit(pp)
    BY <2>3 DEF Acquit
  <2> QED
    BY <1>6, <2>1, <2>2, <2>3 DEF PersonStep
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, NextDef

THEOREM RecessAppointmentsInRecessAlways ==
    ASSUME Mut # "M_PRO_FORMA"
    PROVE  Spec => []RecessAppointmentsInRecess
<1>1. TypeOK /\ RecessAppointmentsInRecess /\ [Next]_vars => (TypeOK /\ RecessAppointmentsInRecess)'
    BY NextTypeOK, NextRecessAppointmentsInRecess
<1> QED
    BY InitTypeOK, InitRecessAppointmentsInRecess, <1>1, PTL DEF Spec

-----------------------------------------------------------------------------
(* Art. V                                                                  *)

LEMMA InitArticleV == Init => ArticleV
BY DEF Init, ArticleV

LEMMA NextArticleV ==
  ASSUME Mut # "M_RATIFY_VOTE", Mut # "M_SUFFRAGE", TypeOK, ArticleV, [Next]_vars
  PROVE  ArticleV'
<1> USE NoOneIsNoPerson, CongressPersons, EligiblePersons, RevenueAreBills, SuffrageAreAmendments DEF TypeOK, ArticleV, Ratifies, AmendRec, vars, billVars, execVars, apptVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, billVars, execVars, apptVars, impVars, flagVars
<1>2. CASE Convene \/ Adjourn \/ (\E bl \in Bills : BillStep(bl)) \/ ExecStep
         \/ (\E of \in Offices : OfficeStep(of)) \/ (\E pp \in Persons : PersonStep(pp))
  BY <1>2, NonAmendFrame
<1>3. ASSUME NEW am \in Amendments, AmendStep(am)
      PROVE  ArticleV'
  <2>1. ASSUME NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"), ProposeByCongress(am, hk, sk)
        PROVE  ArticleV'
    BY <2>1 DEF ProposeByCongress
  <2>2. ASSUME NEW k \in StateVotes, ProposeByConvention(am, k)
        PROVE  ArticleV'
    BY <2>2 DEF ProposeByConvention
  <2>3. ASSUME NEW k \in StateVotes, Ratify(am, k)
        PROVE  ArticleV'
    BY <2>3 DEF Ratify
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3 DEF AmendStep
<1> QED
  BY <1>1, <1>2, <1>3, NextDef

THEOREM ArticleVAlways ==
    ASSUME Mut # "M_RATIFY_VOTE", Mut # "M_SUFFRAGE"
    PROVE  Spec => []ArticleV
<1>1. TypeOK /\ ArticleV /\ [Next]_vars => (TypeOK /\ ArticleV)'
    BY NextTypeOK, NextArticleV
<1> QED
    BY InitTypeOK, InitArticleV, <1>1, PTL DEF Spec

-----------------------------------------------------------------------------
(* The mechanism as written: every property at once.                       *)

THEOREM SafeAlways ==
    ASSUME Mut = "none"
    PROVE  Spec => []Safety
<1>1.  Spec => []Bicameralism                BY BicameralismAlways
<1>2.  Spec => []Origination                 BY OriginationAlways
<1>3.  Spec => []Presentment                 BY PresentmentAlways
<1>4.  Spec => []TenDayRule                  BY TenDayRuleAlways
<1>5.  Spec => []Incompatibility             BY IncompatibilityAlways
<1>6.  Spec => []CongressNotImpeachable      BY CongressNotImpeachableAlways
<1>7.  Spec => []ConvictionTwoThirds         BY ConvictionTwoThirdsAlways
<1>8.  Spec => []TwoTermLimit                BY TwoTermLimitAlways
<1>9.  Spec => []Disqualification            BY DisqualificationAlways
<1>10. Spec => []PresidentNotVP              BY PresidentNotVPAlways
<1>11. Spec => []ArticleV                    BY ArticleVAlways
<1>12. Spec => []XXVBothHouses               BY XXVBothHousesAlways
<1>13. Spec => []RecessAppointmentsInRecess  BY RecessAppointmentsInRecessAlways
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, PTL
    DEF Safety

-----------------------------------------------------------------------------
(* Why each mutation must fail: what it admits, in the module's terms. The *)
(* counterexamples themselves are TLC's, in results/Constitution-results-*. *)

LEMMA MutUnicameralPresentsAfterOneHouse ==
  ASSUME Mut = "M_UNICAMERAL", TypeOK, NEW bl \in Bills, NEW k \in Nat,
         bill[bl].status = "Pending", bill[bl].passed = {},
         PassChamber(bl, bill[bl].origin, k)
  PROVE  bill'[bl].status = "Presented" /\ bill'[bl].passed # Chambers
BY DEF PassChamber, BothHouses, TypeOK, BillRec, Chambers

LEMMA MutOriginLetsSenateRaiseRevenue ==
  ASSUME Mut = "M_ORIGIN", NEW bl \in RevenueBills, bill[bl].status = "Unintroduced"
  PROVE  ENABLED Introduce(bl, "Senate")
BY ExpandENABLED DEF Introduce, MayOriginate, execVars, apptVars, impVars, flagVars

LEMMA MutOvrOneHouseEndsAtOrigin ==
  ASSUME Mut = "M_OVR_ONE_HOUSE"
  PROVE  OverrideComplete({"House"}) /\ {"House"} # Chambers
BY DEF OverrideComplete, Chambers

LEMMA MutOvrVoteCountsAnyVote ==
  ASSUME Mut = "M_OVR_VOTE", NEW ch \in Chambers
  PROVE  OverrideCarries(0, ch)
BY DEF OverrideCarries

LEMMA MutNoPocketMakesLawInRecess ==
  ASSUME Mut = "M_NO_POCKET", NEW bl \in Bills, bill[bl].status = "Presented", ~inSession
  PROVE  ENABLED BecomeLawUnsigned(bl)
BY ExpandENABLED DEF BecomeLawUnsigned, execVars, apptVars, impVars, flagVars

LEMMA MutPocketSittingKillsInSession ==
  ASSUME Mut = "M_POCKET_SITTING", NEW bl \in Bills, bill[bl].status = "Presented", inSession
  PROVE  ENABLED PocketVeto(bl)
BY ExpandENABLED DEF PocketVeto, execVars, apptVars, impVars, flagVars

LEMMA MutIncompatAdmitsMembers ==
  ASSUME Mut = "M_INCOMPAT", NEW pp \in Congress
  PROVE  Compatible(pp)
BY DEF Compatible

LEMMA MutBlountImpeachesMembers ==
  ASSUME Mut = "M_BLOUNT", NEW pp \in Congress
  PROVE  Impeachable(pp)
BY DEF Impeachable

LEMMA MutConvictVoteCountsAnyVote ==
  ASSUME Mut = "M_CONVICT_VOTE"
  PROVE  ConvictionCarries(0)
BY DEF ConvictionCarries

LEMMA MutXXIIAllowsThirdElection ==
  ASSUME Mut = "M_XXII", NEW pp \in Persons, terms[pp] = 2
  PROVE  TermAllowed(pp)
BY DEF TermAllowed

LEMMA MutDQAdmitsDisqualified ==
  ASSUME Mut = "M_DQ", NEW pp \in disqualified
  PROVE  Qualified(pp)
BY DEF Qualified

LEMMA MutVPRecheckConfirmsDisqualified ==
  ASSUME Mut = "M_VP_RECHECK", vpNominee \in disqualified, TypeOK,
         NEW hk \in VotesIn("House"), NEW sk \in VotesIn("Senate"),
         Majority(hk, House), Majority(sk, Senate)
  PROVE  ENABLED ConfirmVP(hk, sk)
BY NoOneIsNoPerson, ExpandENABLED
   DEF ConfirmVP, HouseConfirms, TypeOK, billVars, apptVars, impVars, flagVars

LEMMA MutConsentRecheckSeatsDisqualified ==
  ASSUME Mut = "M_CONSENT_RECHECK", TypeOK, NEW of \in Offices, nominee[of] \in disqualified,
         NEW k \in VotesIn("Senate"), Majority(k, Senate)
  PROVE  ENABLED Consent(of, k)
BY NoOneIsNoPerson, ExpandENABLED
   DEF Consent, TypeOK, billVars, execVars, impVars, flagVars

LEMMA MutNoRemovalKeepsTheConvicted ==
  ASSUME Mut = "M_NO_REMOVAL", NEW pp, NEW x
  PROVE  ~RemovedBy(pp, x)
BY DEF RemovedBy

LEMMA MutOnePersonHoldsBoth ==
  ASSUME Mut = "M_ONE_PERSON", NEW pp
  PROVE  TwoPersons(pp, pp)
BY DEF TwoPersons

LEMMA MutRatifyVoteRatifiesWithNone ==
  ASSUME Mut = "M_RATIFY_VOTE", NEW am \in Amendments \ SuffrageAmendments
  PROVE  Ratifies(am, 0)
BY DEF Ratifies

LEMMA MutSuffrageNeedsOnlyThreeQuarters ==
  ASSUME Mut = "M_SUFFRAGE", NEW am \in Amendments, NEW k, ThreeQuarters(k, States)
  PROVE  Ratifies(am, k)
BY DEF Ratifies

LEMMA MutXXVSenateSkipsTheHouse ==
  ASSUME Mut = "M_XXV_SENATE"
  PROVE  HouseConfirms(0)
BY DEF HouseConfirms

LEMMA MutProFormaAppointsInSession ==
  ASSUME Mut = "M_PRO_FORMA", inSession, president # NoOne,
         NEW of \in Offices, officer[of] = NoOne,
         NEW pp \in Persons, Qualified(pp), Compatible(pp)
  PROVE  ENABLED RecessAppoint(of, pp)
BY ExpandENABLED DEF RecessAppoint, SenateInRecess, billVars, execVars, impVars, flagVars

=============================================================================
