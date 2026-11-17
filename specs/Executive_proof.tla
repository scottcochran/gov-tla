-------------------------- MODULE Executive_proof --------------------------
(****************************************************************************)
(* TLAPS proofs of the safety properties of Executive.tla. The base module  *)
(* is extended, never edited; the proof results file names it by digest.    *)
(*                                                                          *)
(* THEOREMS, each Spec => []P under exactly the mutations that break P in   *)
(* the TLC results file (results/Executive-results-*.txt):                  *)
(*   OneExecutiveAlways        [Mut # M_SAMEPERSON, Mut # M_NOVP]           *)
(*   IncompatibilityAlways     [Mut # M_PLACEMEN]                           *)
(*   DisqualificationAlways    [Mut # M_DISQUAL, Mut # M_SAMEPERSON]        *)
(*   ActingIsNotHeadAlways     [Mut # M_ACTWHILEFILLED]                     *)
(*   ActingIsTemporaryAlways   [Mut # M_PREFVRA]                            *)
(*   NoCongressionalAppointmentAlways [Mut # M_FECA]                        *)
(*   ExecutionIsExecutiveAlways [Mut # M_GRH]                               *)
(*   UnitaryExecutiveAlways    [Mut # M_HUMPHREY]                           *)
(*   PardonScopeAlways         [Mut # M_DANBY, Mut # M_STATECRIME]          *)
(*   WarIsCongressionalAlways  [Mut # M_PREROGATIVE]                        *)
(*   CongressDoesNotRemoveExecutorsAlways [Mut # M_JOINTRES, Mut # M_GRH]   *)
(*   TreatiesByTwoThirdsAlways [Mut # M_AUG6]                               *)
(*   TypeOKAlways              [none: every mutation]                       *)
(*   SafeAlways                [Mut = "none"]: Spec => []Safety             *)
(* and one lemma per mutation (Mut...Admits) saying what it lets through.   *)
(*                                                                          *)
(* ASSUMPTIONS: the base module's named ASSUMEs NoOneWF, EligibleWF,        *)
(* CongressWF, ChartersWF and ActingLimitWF (MutKnown is not used). So the  *)
(* theorems hold for every set of persons, agencies and treaties, every     *)
(* set of charters drawn from CharterRecord and every ActingLimit in Nat;   *)
(* the rows' constants (one agency, KnownCharters, ActingLimit = 1) and     *)
(* the bound DaysBound are TLC's business and are not assumed.              *)
(*                                                                          *)
(* INDUCTIVE STRENGTHENING, in prose:                                       *)
(*  - TypeOK, under every mutation, cited by every lemma.                   *)
(*  - OneExecutive splits in two, each inductive alone: DistinctOffices     *)
(*    (Elect's TwoPeople; vacancy and conviction move the VP up and leave   *)
(*    the Vice Presidency empty) and ActingSeated (DeclareInability's       *)
(*    VPToAct; every step that empties an office resets inability).         *)
(*  - NoNewOfficer, under every mutation: a step seats no one new except    *)
(*    by Elect, ConfirmHead or AppointInferior, and those seat only someone *)
(*    EligibleOfficer admits. Incompatibility is then "no member of         *)
(*    Congress in office" (NotIn(Congress)) with no case split: a member    *)
(*    newly in office passed NotMember. Disqualification is NotIn of the    *)
(*    disqualified, strengthened by DistinctOffices: a newly seated         *)
(*    disqualified person passed NotDisqualified, and the one newly         *)
(*    disqualified person is the convict, whom Convict removes from every   *)
(*    office provided President and VP are two people (ConvictRemoves);     *)
(*    hence M_SAMEPERSON breaks it.                                         *)
(*  - ActingIsNotHead and ActingIsTemporary are inductive alone, one step   *)
(*    per agency action, decided by ActAsHead's OfficeVacant and            *)
(*    ActingTick's WithinLimit.                                             *)
(*  - StatuteFrame, under every mutation: an agency's statute fields are    *)
(*    kept, lost on abolition, or copied from a charter Chartered admits.   *)
(*    ExecutionIsExecutive and UnitaryExecutive follow under their check;   *)
(*    NoCongressionalAppointment is strengthened by CongressVestingOK (no   *)
(*    live agency both executes the laws and vests appointment in           *)
(*    Congress: Chartered's Buckley check written over the state), and      *)
(*    CongressDoesNotRemoveExecutors by ExecutionIsExecutive (Congress      *)
(*    removes only its own officers, none of whom executes the laws).       *)
(*  - PardonScope, WarIsCongressional, TreatiesByTwoThirds: inductive       *)
(*    alone, each decided at its one action (FlagFrame).                    *)
(*                                                                          *)
(* NOT PROVED                                                               *)
(*  - ActingEventuallyEnds. It is a leads-to quantified over Agencies       *)
(*    inside the temporal body, with fairness on ActingTick(a) and          *)
(*    ActingExpires(a) for each a: the case the method's prover habits      *)
(*    record as having no sound route in this prover (a quantified          *)
(*    leads-to hypothesis that PTL cannot combine from instances). It is    *)
(*    checked by TLC at one agency and ActingLimit = 1 and 2, with each     *)
(*    fairness condition shown necessary and the fair spec non-empty.       *)
(*  - Reachability (the Never... witnesses) and the mutations'              *)
(*    counterexamples: existential, so TLC's.                               *)
(*                                                                          *)
(* CHECK: scripts/proof_results.py Executive (tools/tlapm --cleanfp         *)
(* --strict --cache-dir <tmp> Executive_proof.tla); flip a hypothesis       *)
(* with scripts/flip_test.py Executive M_X.                                 *)
(****************************************************************************)
EXTENDS Executive, TLAPS

-----------------------------------------------------------------------------
(* Inductive invariants                                                     *)

DistinctOffices == president = NoOne \/ president # vicePresident
ActingSeated    == Acting => (president # NoOne /\ vicePresident # NoOne)

\* No one in S holds an office.
NotIn(S) == \A x \in S : ~InOffice(x)

\* The statute fields of an agency record, and what the checks require of them.
SameCharter(r, s) ==
  /\ r.exists = s.exists /\ r.branch = s.branch /\ r.executesLaw = s.executesLaw
  /\ r.removal = s.removal /\ r.vesting = s.vesting
FromCharter(r, c) ==
  /\ r.exists /\ r.branch = c.branch /\ r.executesLaw = c.executesLaw
  /\ r.removal = c.removal /\ r.vesting = c.vesting
VestOK(r) == (r.exists /\ r.vesting = "Congress") => ~r.executesLaw
CongressVestingOK == \A a \in Agencies : VestOK(agency[a])

InvOE  == TypeOK /\ DistinctOffices /\ ActingSeated
InvInc == TypeOK /\ NotIn(Congress)
InvDis == TypeOK /\ DistinctOffices /\ NotIn(disqualified)
InvANH == TypeOK /\ ActingIsNotHead
InvAT  == TypeOK /\ ActingIsTemporary
InvEE  == TypeOK /\ ExecutionIsExecutive
InvUE  == TypeOK /\ UnitaryExecutive
InvNCA == TypeOK /\ CongressVestingOK /\ NoCongressionalAppointment
InvCDR == TypeOK /\ ExecutionIsExecutive /\ CongressDoesNotRemoveExecutors

-----------------------------------------------------------------------------
(* The type invariant, under every mutation                                 *)

LEMMA InitTypeOK == Init => TypeOK
BY NoOneWF DEF Init, TypeOK, Blank, AgencyRecord, Seat, Inability, TreatyStates, Branches,
               Removal, Vestings

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  OBVIOUS
<1> USE DEF execVars, sideVars, impVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, TypeOK
<1>2. CASE OfficeSteps
  <2>1. ASSUME NEW p \in Persons, NEW v \in Persons, Elect(p, v) PROVE TypeOK'
    BY <2>1, EligibleWF DEF Elect, TypeOK, Seat, Inability
  <2>2. CASE DeclareInability
    BY <2>2 DEF DeclareInability, TypeOK, Inability
  <2>3. CASE CabinetDeclares
    BY <2>3 DEF CabinetDeclares, TypeOK, Inability
  <2>4. CASE DeclareAble
    BY <2>4 DEF DeclareAble, TypeOK, Inability
  <2>5. ASSUME NEW v \in Votes, CongressDecides(v) PROVE TypeOK'
    BY <2>5 DEF CongressDecides, TypeOK, Inability
  <2>6. CASE PresidentVacates
    BY <2>6 DEF PresidentVacates, TypeOK, Seat, Inability
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF OfficeSteps
<1>3. CASE AgencySteps
  <2>1. ASSUME NEW a \in Agencies, NEW c \in Charters, CreateAgency(a, c) PROVE TypeOK'
    BY <2>1, ChartersWF, NoOneWF DEF CreateAgency, TypeOK, Blank, AgencyRecord, CharterRecord, Seat
  <2>2. ASSUME NEW a \in Agencies, AbolishAgency(a) PROVE TypeOK'
    BY <2>2, NoOneWF DEF AbolishAgency, TypeOK, Blank, AgencyRecord, Seat, Branches, Removal,
                         Vestings
  <2>3. ASSUME NEW a \in Agencies, NEW p \in Persons, NominateHead(a, p) PROVE TypeOK'
    BY <2>3 DEF NominateHead, TypeOK, AgencyRecord, Seat
  <2>4. ASSUME NEW a \in Agencies, ConfirmHead(a) PROVE TypeOK'
    BY <2>4 DEF ConfirmHead, TypeOK, AgencyRecord, Seat
  <2>5. ASSUME NEW a \in Agencies, RejectHead(a) PROVE TypeOK'
    BY <2>5 DEF RejectHead, TypeOK, AgencyRecord, Seat
  <2>6. ASSUME NEW a \in Agencies, NEW p \in Persons, AppointInferior(a, p) PROVE TypeOK'
    BY <2>6 DEF AppointInferior, TypeOK, AgencyRecord, Seat
  <2>7. ASSUME NEW a \in Agencies, ActAsHead(a) PROVE TypeOK'
    BY <2>7 DEF ActAsHead, TypeOK, AgencyRecord, Seat
  <2>8. ASSUME NEW a \in Agencies, ActingTick(a) PROVE TypeOK'
    BY <2>8 DEF ActingTick, TypeOK, AgencyRecord
  <2>9. ASSUME NEW a \in Agencies, ActingExpires(a) PROVE TypeOK'
    BY <2>9 DEF ActingExpires, TypeOK, AgencyRecord, Seat
  <2>10. ASSUME NEW a \in Agencies, NEW c \in BOOLEAN, PresidentRemovesHead(a, c) PROVE TypeOK'
    BY <2>10 DEF PresidentRemovesHead, TypeOK, AgencyRecord, Seat
  <2>11. ASSUME NEW a \in Agencies, PresidentRemovesInferior(a) PROVE TypeOK'
    BY <2>11 DEF PresidentRemovesInferior, TypeOK, AgencyRecord, Seat
  <2>12. ASSUME NEW a \in Agencies, CongressRemovesHead(a) PROVE TypeOK'
    BY <2>12 DEF CongressRemovesHead, TypeOK, AgencyRecord, Seat
  <2>13. ASSUME NEW a \in Agencies, Resign(a) PROVE TypeOK'
    BY <2>13 DEF Resign, TypeOK, AgencyRecord, Seat
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
       <2>12, <2>13 DEF AgencySteps
<1>4. CASE TrialSteps
  <2>1. ASSUME NEW p \in Persons, Impeach(p) PROVE TypeOK'
    BY <2>1 DEF Impeach, TypeOK
  <2>2. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq) PROVE TypeOK'
    BY <2>2 DEF Convict, TypeOK, Purge, AgencyRecord, Seat, Inability
  <2>3. ASSUME NEW p \in Persons, Acquit(p) PROVE TypeOK'
    BY <2>3 DEF Acquit, TypeOK
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3 DEF TrialSteps
<1>5. CASE OtherSteps
  <2>1. ASSUME NEW v \in Votes, DeclareWar(v) PROVE TypeOK'
    BY <2>1 DEF DeclareWar, TypeOK
  <2>2. CASE Adjourn \/ Convene \/ ConveneByPresident
    BY <2>2 DEF Adjourn, Convene, ConveneByPresident, TypeOK
  <2>3. ASSUME NEW k \in Offences, Pardon(k) PROVE TypeOK'
    BY <2>3 DEF Pardon, TypeOK
  <2>4. ASSUME NEW t \in Treaties, Negotiate(t) PROVE TypeOK'
    BY <2>4 DEF Negotiate, TypeOK, TreatyStates
  <2>5. ASSUME NEW t \in Treaties, NEW v \in Votes, RatifyTreaty(t, v) PROVE TypeOK'
    BY <2>5 DEF RatifyTreaty, TypeOK, TreatyStates
  <2>6. ASSUME NEW t \in Treaties, RejectTreaty(t) PROVE TypeOK'
    BY <2>6 DEF RejectTreaty, TypeOK, TreatyStates
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF OtherSteps
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

-----------------------------------------------------------------------------
(* Frames: which steps can change which variables                           *)

LEMMA ExecFrame ==
  ASSUME [Next]_vars
  PROVE  \/ OfficeSteps
         \/ \E p \in Persons, dq \in BOOLEAN : Convict(p, dq)
         \/ UNCHANGED execVars
<1> USE DEF execVars, sideVars, impVars, flagVars
<1>1. AgencySteps => UNCHANGED execVars
  BY DEF AgencySteps, CreateAgency, AbolishAgency, NominateHead, ConfirmHead, RejectHead,
         AppointInferior, ActAsHead, ActingTick, ActingExpires, PresidentRemovesHead,
         PresidentRemovesInferior, CongressRemovesHead, Resign
<1>2. OtherSteps => UNCHANGED execVars
  BY DEF OtherSteps, DeclareWar, Adjourn, Convene, ConveneByPresident, Pardon, Negotiate,
         RatifyTreaty, RejectTreaty
<1>3. TrialSteps => (\E p \in Persons, dq \in BOOLEAN : Convict(p, dq)) \/ UNCHANGED execVars
  BY DEF TrialSteps, Impeach, Acquit
<1> QED
  BY <1>1, <1>2, <1>3 DEF Next, vars

LEMMA AgencyFrame ==
  ASSUME [Next]_vars
  PROVE  \/ AgencySteps
         \/ \E p \in Persons, dq \in BOOLEAN : Convict(p, dq)
         \/ UNCHANGED agency
<1> USE DEF execVars, sideVars, impVars, flagVars
<1>1. OfficeSteps => UNCHANGED agency
  BY DEF OfficeSteps, Elect, DeclareInability, CabinetDeclares, DeclareAble, CongressDecides,
         PresidentVacates
<1>2. OtherSteps => UNCHANGED agency
  BY DEF OtherSteps, DeclareWar, Adjourn, Convene, ConveneByPresident, Pardon, Negotiate,
         RatifyTreaty, RejectTreaty
<1>3. TrialSteps => (\E p \in Persons, dq \in BOOLEAN : Convict(p, dq)) \/ UNCHANGED agency
  BY DEF TrialSteps, Impeach, Acquit
<1> QED
  BY <1>1, <1>2, <1>3 DEF Next, vars

\* The variables only OtherSteps changes.
LEMMA SideFrame ==
  ASSUME [Next]_vars
  PROVE  OtherSteps \/ UNCHANGED sideVars
<1> USE DEF execVars, sideVars, impVars, flagVars
<1>1. OfficeSteps => UNCHANGED sideVars
  BY DEF OfficeSteps, Elect, DeclareInability, CabinetDeclares, DeclareAble, CongressDecides,
         PresidentVacates
<1>2. AgencySteps => UNCHANGED sideVars
  BY DEF AgencySteps, CreateAgency, AbolishAgency, NominateHead, ConfirmHead, RejectHead,
         AppointInferior, ActAsHead, ActingTick, ActingExpires, PresidentRemovesHead,
         PresidentRemovesInferior, CongressRemovesHead, Resign
<1>3. TrialSteps => UNCHANGED sideVars
  BY DEF TrialSteps, Impeach, Convict, Acquit
<1> QED
  BY <1>1, <1>2, <1>3 DEF Next, vars

LEMMA DisqualifiedFrame ==
  ASSUME [Next]_vars
  PROVE  (\E p \in Persons, dq \in BOOLEAN : Convict(p, dq)) \/ UNCHANGED disqualified
<1> USE DEF execVars, sideVars, impVars, flagVars
<1>1. OfficeSteps => UNCHANGED disqualified
  BY DEF OfficeSteps, Elect, DeclareInability, CabinetDeclares, DeclareAble, CongressDecides,
         PresidentVacates
<1>2. AgencySteps => UNCHANGED disqualified
  BY DEF AgencySteps, CreateAgency, AbolishAgency, NominateHead, ConfirmHead, RejectHead,
         AppointInferior, ActAsHead, ActingTick, ActingExpires, PresidentRemovesHead,
         PresidentRemovesInferior, CongressRemovesHead, Resign
<1>3. OtherSteps => UNCHANGED disqualified
  BY DEF OtherSteps, DeclareWar, Adjourn, Convene, ConveneByPresident, Pardon, Negotiate,
         RatifyTreaty, RejectTreaty
<1>4. TrialSteps => (\E p \in Persons, dq \in BOOLEAN : Convict(p, dq)) \/ UNCHANGED disqualified
  BY DEF TrialSteps, Impeach, Acquit
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next, vars

\* Each flag is changed by one action only.
LEMMA FlagFrame ==
  ASSUME [Next]_vars
  PROVE  /\ (\E a \in Agencies, p \in Persons : AppointInferior(a, p))
              \/ UNCHANGED congressAppointed
         /\ (\E a \in Agencies : CongressRemovesHead(a)) \/ UNCHANGED congressRemoved
         /\ (\E v \in Votes : DeclareWar(v)) \/ UNCHANGED warWithoutStatute
         /\ (\E t \in Treaties, v \in Votes : RatifyTreaty(t, v)) \/ UNCHANGED treatyShort
         /\ (\E k \in Offences : Pardon(k)) \/ UNCHANGED pardoned
<1> USE DEF execVars, sideVars, impVars, flagVars
<1>1. OfficeSteps => UNCHANGED <<flagVars, pardoned>>
  BY DEF OfficeSteps, Elect, DeclareInability, CabinetDeclares, DeclareAble, CongressDecides,
         PresidentVacates
<1>2. TrialSteps => UNCHANGED <<flagVars, pardoned>>
  BY DEF TrialSteps, Impeach, Convict, Acquit
<1>3. AgencySteps => /\ (\E a \in Agencies, p \in Persons : AppointInferior(a, p))
                        \/ UNCHANGED congressAppointed
                     /\ (\E a \in Agencies : CongressRemovesHead(a)) \/ UNCHANGED congressRemoved
                     /\ UNCHANGED <<warWithoutStatute, treatyShort, pardoned>>
  BY DEF AgencySteps, CreateAgency, AbolishAgency, NominateHead, ConfirmHead, RejectHead,
         AppointInferior, ActAsHead, ActingTick, ActingExpires, PresidentRemovesHead,
         PresidentRemovesInferior, CongressRemovesHead, Resign
<1>4. OtherSteps => /\ UNCHANGED <<congressAppointed, congressRemoved>>
                    /\ (\E v \in Votes : DeclareWar(v)) \/ UNCHANGED warWithoutStatute
                    /\ (\E t \in Treaties, v \in Votes : RatifyTreaty(t, v))
                         \/ UNCHANGED treatyShort
                    /\ (\E k \in Offences : Pardon(k)) \/ UNCHANGED pardoned
  BY DEF OtherSteps, DeclareWar, Adjourn, Convene, ConveneByPresident, Pardon, Negotiate,
         RatifyTreaty, RejectTreaty
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next, vars

-----------------------------------------------------------------------------
(* Who can come to hold an office. Every step but Elect, ConfirmHead and    *)
(* AppointInferior seats no one new; those three seat only someone          *)
(* EligibleOfficer admits. Under every mutation.                            *)

LEMMA NoNewOfficer ==
  ASSUME TypeOK, [Next]_vars, NEW x \in Persons, InOffice(x)', ~InOffice(x)
  PROVE  EligibleOfficer(x)
<1> USE NoOneWF DEF execVars, sideVars, impVars, flagVars
<1>0. x # NoOne
  OBVIOUS
<1>1. CASE UNCHANGED <<execVars, agency>>
  BY <1>1 DEF InOffice, Live
<1>2. CASE OfficeSteps
  <2>1. ASSUME NEW p \in Persons, NEW v \in Persons, Elect(p, v) PROVE EligibleOfficer(x)
    BY <2>1 DEF Elect, InOffice, Live
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates, InOffice, Live
  <2>3. CASE DeclareInability \/ CabinetDeclares \/ DeclareAble
                \/ \E v \in Votes : CongressDecides(v)
    <3>1. UNCHANGED <<execVars, agency>> \/ UNCHANGED <<president, vicePresident, agency>>
      BY <2>3 DEF DeclareInability, CabinetDeclares, DeclareAble, CongressDecides
    <3> QED
      BY <3>1 DEF InOffice, Live
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3 DEF OfficeSteps
<1>3. CASE AgencySteps
  <2>0. UNCHANGED <<president, vicePresident>>
    BY <1>3 DEF AgencySteps, CreateAgency, AbolishAgency, NominateHead, ConfirmHead, RejectHead,
         AppointInferior, ActAsHead, ActingTick, ActingExpires, PresidentRemovesHead,
         PresidentRemovesInferior, CongressRemovesHead, Resign
  <2>1. PICK b \in Agencies : agency'[b].exists
                              /\ x \in {agency'[b].head, agency'[b].inferior, agency'[b].acting}
    BY <2>0 DEF InOffice, Live
  <2>2. ~(agency[b].exists /\ x \in {agency[b].head, agency[b].inferior, agency[b].acting})
    BY DEF InOffice, Live
  <2>3. ASSUME NEW a \in Agencies, NEW c \in Charters, CreateAgency(a, c) PROVE FALSE
    BY <2>1, <2>2, <2>3 DEF CreateAgency, TypeOK, Blank
  <2>4. ASSUME NEW a \in Agencies, AbolishAgency(a) PROVE FALSE
    BY <2>1, <2>2, <2>4 DEF AbolishAgency, TypeOK, Blank
  <2>5. ASSUME NEW a \in Agencies, NEW p \in Persons, NominateHead(a, p) PROVE FALSE
    BY <2>1, <2>2, <2>5 DEF NominateHead, TypeOK, AgencyRecord
  <2>6. ASSUME NEW a \in Agencies, ConfirmHead(a) PROVE EligibleOfficer(x)
    BY <2>1, <2>2, <2>6 DEF ConfirmHead, TypeOK, AgencyRecord
  <2>7. ASSUME NEW a \in Agencies, RejectHead(a) PROVE FALSE
    BY <2>1, <2>2, <2>7 DEF RejectHead, TypeOK, AgencyRecord
  <2>8. ASSUME NEW a \in Agencies, NEW p \in Persons, AppointInferior(a, p) PROVE EligibleOfficer(x)
    BY <2>1, <2>2, <2>8 DEF AppointInferior, TypeOK, AgencyRecord
  <2>9. ASSUME NEW a \in Agencies, ActAsHead(a) PROVE FALSE
    BY <2>1, <2>2, <2>9 DEF ActAsHead, TypeOK, AgencyRecord
  <2>10. ASSUME NEW a \in Agencies, ActingTick(a) PROVE FALSE
    BY <2>1, <2>2, <2>10 DEF ActingTick, TypeOK, AgencyRecord
  <2>11. ASSUME NEW a \in Agencies, ActingExpires(a) PROVE FALSE
    BY <2>1, <2>2, <2>11 DEF ActingExpires, TypeOK, AgencyRecord
  <2>12. ASSUME NEW a \in Agencies, NEW c \in BOOLEAN, PresidentRemovesHead(a, c) PROVE FALSE
    BY <2>1, <2>2, <2>12 DEF PresidentRemovesHead, TypeOK, AgencyRecord
  <2>13. ASSUME NEW a \in Agencies, PresidentRemovesInferior(a) PROVE FALSE
    BY <2>1, <2>2, <2>13 DEF PresidentRemovesInferior, TypeOK, AgencyRecord
  <2>14. ASSUME NEW a \in Agencies, CongressRemovesHead(a) PROVE FALSE
    BY <2>1, <2>2, <2>14 DEF CongressRemovesHead, TypeOK, AgencyRecord
  <2>15. ASSUME NEW a \in Agencies, Resign(a) PROVE FALSE
    BY <2>1, <2>2, <2>15 DEF Resign, TypeOK, AgencyRecord
  <2> QED
    BY <1>3, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
       <2>14, <2>15 DEF AgencySteps
<1>4. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq) PROVE FALSE
  <2>1. x # president' \/ x = president \/ x = vicePresident
    BY <1>4 DEF Convict
  <2>2. x # vicePresident' \/ x = vicePresident
    BY <1>4 DEF Convict
  <2>3. ASSUME NEW b \in Agencies, agency'[b].exists,
               x \in {agency'[b].head, agency'[b].inferior, agency'[b].acting}
        PROVE  agency[b].exists /\ x \in {agency[b].head, agency[b].inferior, agency[b].acting}
    BY <1>4, <2>3 DEF Convict, Purge, TypeOK, AgencyRecord
  <2> QED
    BY <2>1, <2>2, <2>3 DEF InOffice, Live
<1>5. CASE TrialSteps
  <2>1. CASE \E p \in Persons : Impeach(p) \/ Acquit(p)
    <3>1. UNCHANGED <<execVars, agency>>
      BY <2>1 DEF Impeach, Acquit
    <3> QED
      BY <3>1, <1>1
  <2> QED
    BY <1>5, <1>4, <2>1 DEF TrialSteps
<1>6. CASE OtherSteps
  <2>1. UNCHANGED <<execVars, agency>>
    BY <1>6 DEF OtherSteps, DeclareWar, Adjourn, Convene, ConveneByPresident, Pardon, Negotiate,
             RatifyTreaty, RejectTreaty
  <2> QED
    BY <2>1, <1>1
<1>7. CASE UNCHANGED vars
  BY <1>7, <1>1 DEF vars
<1> QED
  BY <1>2, <1>3, <1>5, <1>6, <1>7 DEF Next

\* Conviction removes the convicted from every office, given that the
\* President and Vice President are two people.
LEMMA ConvictRemoves ==
  ASSUME TypeOK, DistinctOffices, NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq)
  PROVE  ~InOffice(p)'
<1> USE NoOneWF
<1>1. p # president'
  BY DEF Convict, DistinctOffices
<1>2. p # vicePresident'
  BY DEF Convict
<1>3. \A b \in Agencies : p \notin {agency'[b].head, agency'[b].inferior, agency'[b].acting}
  BY DEF Convict, Purge, TypeOK, AgencyRecord
<1> QED
  BY <1>1, <1>2, <1>3 DEF InOffice, Live

-----------------------------------------------------------------------------
(* OneExecutive [Mut # "M_SAMEPERSON", Mut # "M_NOVP"]                      *)

LEMMA InitInvOE == Init => InvOE
BY InitTypeOK DEF Init, InvOE, DistinctOffices, ActingSeated, Acting

LEMMA NextDistinctOffices ==
  ASSUME Mut # "M_SAMEPERSON", TypeOK, DistinctOffices, [Next]_vars
  PROVE  DistinctOffices'
<1> USE NoOneWF
<1>1. CASE OfficeSteps
  <2>1. ASSUME NEW p \in Persons, NEW v \in Persons, Elect(p, v) PROVE DistinctOffices'
    BY <2>1 DEF Elect, TwoPeople, DistinctOffices
  <2>2. CASE PresidentVacates
    BY <2>2 DEF PresidentVacates, DistinctOffices
  <2>3. CASE DeclareInability \/ CabinetDeclares \/ DeclareAble
                \/ \E v \in Votes : CongressDecides(v)
    BY <2>3 DEF DeclareInability, CabinetDeclares, DeclareAble, CongressDecides, DistinctOffices
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3 DEF OfficeSteps
<1>2. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq) PROVE DistinctOffices'
  BY <1>2 DEF Convict, DistinctOffices
<1>3. CASE UNCHANGED execVars
  BY <1>3 DEF execVars, DistinctOffices
<1> QED
  BY <1>1, <1>2, <1>3, ExecFrame

LEMMA NextActingSeated ==
  ASSUME Mut # "M_NOVP", TypeOK, ActingSeated, [Next]_vars
  PROVE  ActingSeated'
<1>1. CASE OfficeSteps
  <2>1. ASSUME NEW p \in Persons, NEW v \in Persons, Elect(p, v) PROVE ActingSeated'
    BY <2>1 DEF Elect, ActingSeated, Acting
  <2>2. CASE DeclareInability
    BY <2>2 DEF DeclareInability, VPToAct, ActingSeated, Acting
  <2>3. CASE CabinetDeclares
    BY <2>3 DEF CabinetDeclares, ActingSeated, Acting
  <2>4. CASE DeclareAble
    BY <2>4 DEF DeclareAble, ActingSeated, Acting
  <2>5. ASSUME NEW v \in Votes, CongressDecides(v) PROVE ActingSeated'
    BY <2>5 DEF CongressDecides, ActingSeated, Acting
  <2>6. CASE PresidentVacates
    BY <2>6 DEF PresidentVacates, ActingSeated, Acting
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF OfficeSteps
<1>2. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq) PROVE ActingSeated'
  BY <1>2 DEF Convict, ActingSeated, Acting
<1>3. CASE UNCHANGED execVars
  BY <1>3 DEF execVars, ActingSeated, Acting
<1> QED
  BY <1>1, <1>2, <1>3, ExecFrame

LEMMA NextInvOE ==
  ASSUME Mut # "M_SAMEPERSON", Mut # "M_NOVP", InvOE, [Next]_vars
  PROVE  InvOE'
BY NextTypeOK, NextDistinctOffices, NextActingSeated DEF InvOE

THEOREM OneExecutiveAlways ==
  ASSUME Mut # "M_SAMEPERSON", Mut # "M_NOVP"
  PROVE  Spec => []OneExecutive
<1>1. InvOE /\ [Next]_vars => InvOE'
  BY NextInvOE
<1>2. InvOE => OneExecutive
  BY DEF InvOE, OneExecutive, DistinctOffices, ActingSeated
<1> QED
  BY InitInvOE, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Incompatibility [Mut # "M_PLACEMEN"]                                     *)

LEMMA NotInOfficers ==
  ASSUME NEW S, S \subseteq Persons
  PROVE  NotIn(S) <=> Officers \cap S = {}
BY DEF NotIn, Officers

LEMMA InitNotIn ==
  ASSUME NEW S, S \subseteq Persons, Init
  PROVE  NotIn(S)
BY NoOneWF DEF Init, NotIn, InOffice, Live, Blank

LEMMA InitInvInc == Init => InvInc
BY InitTypeOK, InitNotIn, CongressWF DEF InvInc, Congress

LEMMA NextInvInc ==
  ASSUME Mut # "M_PLACEMEN", InvInc, [Next]_vars
  PROVE  InvInc'
<1>1. TypeOK'
  BY NextTypeOK DEF InvInc
<1>2. ASSUME NEW x \in Congress PROVE ~InOffice(x)'
  <2>1. x \in Persons
    BY CongressWF DEF Congress
  <2>2. ~InOffice(x)
    BY DEF InvInc, NotIn
  <2>3. ~EligibleOfficer(x)
    BY DEF EligibleOfficer, NotMember
  <2> QED
    BY <2>1, <2>2, <2>3, NoNewOfficer DEF InvInc
<1> QED
  BY <1>1, <1>2 DEF InvInc, NotIn

THEOREM IncompatibilityAlways ==
  ASSUME Mut # "M_PLACEMEN"
  PROVE  Spec => []Incompatibility
<1>1. InvInc /\ [Next]_vars => InvInc'
  BY NextInvInc
<1>2. InvInc => Incompatibility
  BY NotInOfficers, CongressWF DEF InvInc, Incompatibility, Congress
<1> QED
  BY InitInvInc, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Disqualification [Mut # "M_DISQUAL", Mut # "M_SAMEPERSON"]               *)

LEMMA InitInvDis == Init => InvDis
BY InitTypeOK, InitNotIn DEF InvDis, Init, DistinctOffices

LEMMA NextInvDis ==
  ASSUME Mut # "M_DISQUAL", Mut # "M_SAMEPERSON", InvDis, [Next]_vars
  PROVE  InvDis'
<1>1. TypeOK'
  BY NextTypeOK DEF InvDis
<1>2. DistinctOffices'
  BY NextDistinctOffices DEF InvDis
<1>3. ASSUME NEW x \in disqualified' PROVE ~InOffice(x)'
  <2>1. CASE x \in disqualified
    <3>1. x \in Persons
      BY <2>1 DEF InvDis, TypeOK
    <3>2. ~InOffice(x)
      BY <2>1 DEF InvDis, NotIn
    <3>3. ~EligibleOfficer(x)
      BY <2>1 DEF EligibleOfficer, NotDisqualified
    <3> QED
      BY <3>1, <3>2, <3>3, NoNewOfficer DEF InvDis
  <2>2. CASE x \notin disqualified
    <3>1. PICK p \in Persons, dq \in BOOLEAN : Convict(p, dq)
      BY <2>2, DisqualifiedFrame
    <3>2. x = p
      BY <2>2, <3>1 DEF Convict
    <3> QED
      BY <3>1, <3>2, ConvictRemoves DEF InvDis
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3 DEF InvDis, NotIn

THEOREM DisqualificationAlways ==
  ASSUME Mut # "M_DISQUAL", Mut # "M_SAMEPERSON"
  PROVE  Spec => []Disqualification
<1>1. InvDis /\ [Next]_vars => InvDis'
  BY NextInvDis
<1>2. InvDis => Disqualification
  BY NotInOfficers DEF InvDis, TypeOK, Disqualification
<1> QED
  BY InitInvDis, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* ActingIsNotHead [Mut # "M_ACTWHILEFILLED"]                               *)

LEMMA InitInvANH == Init => InvANH
BY InitTypeOK DEF Init, InvANH, ActingIsNotHead, Live, Blank

LEMMA NextInvANH ==
  ASSUME Mut # "M_ACTWHILEFILLED", InvANH, [Next]_vars
  PROVE  InvANH'
<1> USE DEF InvANH
<1>0. TypeOK /\ TypeOK'
  BY NextTypeOK
<1> SUFFICES ActingIsNotHead'
  BY <1>0
<1> USE DEF ActingIsNotHead, Live, TypeOK, AgencyRecord
<1>1. CASE UNCHANGED agency
  BY <1>1
<1>2. CASE AgencySteps
  <2>1. ASSUME NEW a \in Agencies, NEW c \in Charters, CreateAgency(a, c) PROVE ActingIsNotHead'
    BY <2>1 DEF CreateAgency, Blank
  <2>2. ASSUME NEW a \in Agencies, AbolishAgency(a) PROVE ActingIsNotHead'
    BY <2>2 DEF AbolishAgency, Blank
  <2>3. ASSUME NEW a \in Agencies, NEW p \in Persons, NominateHead(a, p) PROVE ActingIsNotHead'
    BY <2>3 DEF NominateHead
  <2>4. ASSUME NEW a \in Agencies, ConfirmHead(a) PROVE ActingIsNotHead'
    BY <2>4 DEF ConfirmHead
  <2>5. ASSUME NEW a \in Agencies, RejectHead(a) PROVE ActingIsNotHead'
    BY <2>5 DEF RejectHead
  <2>6. ASSUME NEW a \in Agencies, NEW p \in Persons, AppointInferior(a, p) PROVE ActingIsNotHead'
    BY <2>6 DEF AppointInferior
  <2>7. ASSUME NEW a \in Agencies, ActAsHead(a) PROVE ActingIsNotHead'
    BY <2>7 DEF ActAsHead, OfficeVacant
  <2>8. ASSUME NEW a \in Agencies, ActingTick(a) PROVE ActingIsNotHead'
    BY <2>8 DEF ActingTick
  <2>9. ASSUME NEW a \in Agencies, ActingExpires(a) PROVE ActingIsNotHead'
    BY <2>9 DEF ActingExpires
  <2>10. ASSUME NEW a \in Agencies, NEW c \in BOOLEAN, PresidentRemovesHead(a, c)
         PROVE ActingIsNotHead'
    BY <2>10 DEF PresidentRemovesHead
  <2>11. ASSUME NEW a \in Agencies, PresidentRemovesInferior(a) PROVE ActingIsNotHead'
    BY <2>11 DEF PresidentRemovesInferior
  <2>12. ASSUME NEW a \in Agencies, CongressRemovesHead(a) PROVE ActingIsNotHead'
    BY <2>12 DEF CongressRemovesHead
  <2>13. ASSUME NEW a \in Agencies, Resign(a) PROVE ActingIsNotHead'
    BY <2>13 DEF Resign
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
       <2>12, <2>13 DEF AgencySteps
<1>3. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq) PROVE ActingIsNotHead'
  BY <1>3 DEF Convict, Purge
<1> QED
  BY <1>1, <1>2, <1>3, AgencyFrame

THEOREM ActingIsNotHeadAlways ==
  ASSUME Mut # "M_ACTWHILEFILLED"
  PROVE  Spec => []ActingIsNotHead
<1>1. InvANH /\ [Next]_vars => InvANH'
  BY NextInvANH
<1>2. InvANH => ActingIsNotHead
  BY DEF InvANH
<1> QED
  BY InitInvANH, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* ActingIsTemporary [Mut # "M_PREFVRA"]                                    *)

LEMMA InitInvAT == Init => InvAT
BY InitTypeOK DEF Init, InvAT, ActingIsTemporary, Blank

LEMMA NextInvAT ==
  ASSUME Mut # "M_PREFVRA", InvAT, [Next]_vars
  PROVE  InvAT'
<1> USE DEF InvAT
<1>0. TypeOK /\ TypeOK'
  BY NextTypeOK
<1> SUFFICES ActingIsTemporary'
  BY <1>0
<1> USE ActingLimitWF DEF ActingIsTemporary, TypeOK, AgencyRecord
<1>1. CASE UNCHANGED agency
  BY <1>1
<1>2. CASE AgencySteps
  <2>1. ASSUME NEW a \in Agencies, NEW c \in Charters, CreateAgency(a, c) PROVE ActingIsTemporary'
    BY <2>1 DEF CreateAgency, Blank
  <2>2. ASSUME NEW a \in Agencies, AbolishAgency(a) PROVE ActingIsTemporary'
    BY <2>2 DEF AbolishAgency, Blank
  <2>3. ASSUME NEW a \in Agencies, NEW p \in Persons, NominateHead(a, p) PROVE ActingIsTemporary'
    BY <2>3 DEF NominateHead
  <2>4. ASSUME NEW a \in Agencies, ConfirmHead(a) PROVE ActingIsTemporary'
    BY <2>4 DEF ConfirmHead
  <2>5. ASSUME NEW a \in Agencies, RejectHead(a) PROVE ActingIsTemporary'
    BY <2>5 DEF RejectHead
  <2>6. ASSUME NEW a \in Agencies, NEW p \in Persons, AppointInferior(a, p) PROVE ActingIsTemporary'
    BY <2>6 DEF AppointInferior
  <2>7. ASSUME NEW a \in Agencies, ActAsHead(a) PROVE ActingIsTemporary'
    BY <2>7 DEF ActAsHead
  <2>8. ASSUME NEW a \in Agencies, ActingTick(a) PROVE ActingIsTemporary'
    <3>1. agency[a].actingDays \in Nat /\ agency[a].actingDays < ActingLimit
      BY <2>8 DEF ActingTick, WithinLimit
    <3>2. agency[a].actingDays + 1 <= ActingLimit
      BY <3>1
    <3> QED
      BY <2>8, <3>2 DEF ActingTick
  <2>9. ASSUME NEW a \in Agencies, ActingExpires(a) PROVE ActingIsTemporary'
    BY <2>9 DEF ActingExpires
  <2>10. ASSUME NEW a \in Agencies, NEW c \in BOOLEAN, PresidentRemovesHead(a, c)
         PROVE ActingIsTemporary'
    BY <2>10 DEF PresidentRemovesHead
  <2>11. ASSUME NEW a \in Agencies, PresidentRemovesInferior(a) PROVE ActingIsTemporary'
    BY <2>11 DEF PresidentRemovesInferior
  <2>12. ASSUME NEW a \in Agencies, CongressRemovesHead(a) PROVE ActingIsTemporary'
    BY <2>12 DEF CongressRemovesHead
  <2>13. ASSUME NEW a \in Agencies, Resign(a) PROVE ActingIsTemporary'
    BY <2>13 DEF Resign
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
       <2>12, <2>13 DEF AgencySteps
<1>3. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq) PROVE ActingIsTemporary'
  BY <1>3 DEF Convict, Purge
<1> QED
  BY <1>1, <1>2, <1>3, AgencyFrame

THEOREM ActingIsTemporaryAlways ==
  ASSUME Mut # "M_PREFVRA"
  PROVE  Spec => []ActingIsTemporary
<1>1. InvAT /\ [Next]_vars => InvAT'
  BY NextInvAT
<1>2. InvAT => ActingIsTemporary
  BY DEF InvAT
<1> QED
  BY InitInvAT, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* The statute fields: an agency's record keeps them, loses them on         *)
(* abolition, or takes them from a charter Chartered admits. Under every    *)
(* mutation; ExecutionIsExecutive, UnitaryExecutive and the Buckley fact    *)
(* each sit on top of it under their own check.                             *)

LEMMA StatuteFrame ==
  ASSUME TypeOK, [Next]_vars, NEW b \in Agencies
  PROVE  \/ SameCharter(agency'[b], agency[b])
         \/ ~agency'[b].exists
         \/ \E c \in Charters : Chartered(c) /\ FromCharter(agency'[b], c)
<1> USE DEF SameCharter, TypeOK, AgencyRecord
<1>1. CASE UNCHANGED agency
  BY <1>1
<1>2. CASE AgencySteps
  <2>1. ASSUME NEW a \in Agencies, NEW c \in Charters, CreateAgency(a, c)
        PROVE  SameCharter(agency'[b], agency[b]) \/ (Chartered(c) /\ FromCharter(agency'[b], c))
    BY <2>1 DEF CreateAgency, FromCharter, Blank
  <2>2. ASSUME NEW a \in Agencies, AbolishAgency(a)
        PROVE  SameCharter(agency'[b], agency[b]) \/ ~agency'[b].exists
    BY <2>2 DEF AbolishAgency, Blank
  <2>3. ASSUME NEW a \in Agencies, NEW p \in Persons, NominateHead(a, p)
        PROVE  SameCharter(agency'[b], agency[b])
    BY <2>3 DEF NominateHead
  <2>4. ASSUME NEW a \in Agencies, ConfirmHead(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>4 DEF ConfirmHead
  <2>5. ASSUME NEW a \in Agencies, RejectHead(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>5 DEF RejectHead
  <2>6. ASSUME NEW a \in Agencies, NEW p \in Persons, AppointInferior(a, p)
        PROVE  SameCharter(agency'[b], agency[b])
    BY <2>6 DEF AppointInferior
  <2>7. ASSUME NEW a \in Agencies, ActAsHead(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>7 DEF ActAsHead
  <2>8. ASSUME NEW a \in Agencies, ActingTick(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>8 DEF ActingTick
  <2>9. ASSUME NEW a \in Agencies, ActingExpires(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>9 DEF ActingExpires
  <2>10. ASSUME NEW a \in Agencies, NEW c \in BOOLEAN, PresidentRemovesHead(a, c)
         PROVE  SameCharter(agency'[b], agency[b])
    BY <2>10 DEF PresidentRemovesHead
  <2>11. ASSUME NEW a \in Agencies, PresidentRemovesInferior(a)
         PROVE  SameCharter(agency'[b], agency[b])
    BY <2>11 DEF PresidentRemovesInferior
  <2>12. ASSUME NEW a \in Agencies, CongressRemovesHead(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>12 DEF CongressRemovesHead
  <2>13. ASSUME NEW a \in Agencies, Resign(a) PROVE SameCharter(agency'[b], agency[b])
    BY <2>13 DEF Resign
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11,
       <2>12, <2>13 DEF AgencySteps
<1>3. ASSUME NEW p \in Persons, NEW dq \in BOOLEAN, Convict(p, dq)
      PROVE  SameCharter(agency'[b], agency[b])
  BY <1>3 DEF Convict, Purge
<1> QED
  BY <1>1, <1>2, <1>3, AgencyFrame

-----------------------------------------------------------------------------
(* ExecutionIsExecutive [Mut # "M_GRH"]                                     *)

LEMMA InitInvEE == Init => InvEE
BY InitTypeOK DEF Init, InvEE, ExecutionIsExecutive, Live, Blank

LEMMA NextExecutionIsExecutive ==
  ASSUME Mut # "M_GRH", TypeOK, ExecutionIsExecutive, [Next]_vars
  PROVE  ExecutionIsExecutive'
<1> SUFFICES ASSUME NEW a \in Agencies
             PROVE  (Live(a) /\ agency[a].executesLaw => agency[a].branch = "Executive")'
  BY DEF ExecutionIsExecutive
<1>1. \/ SameCharter(agency'[a], agency[a])
      \/ ~agency'[a].exists
      \/ \E c \in Charters : Chartered(c) /\ FromCharter(agency'[a], c)
  BY StatuteFrame
<1> QED
  BY <1>1 DEF ExecutionIsExecutive, Live, SameCharter, FromCharter, Chartered

LEMMA NextInvEE ==
  ASSUME Mut # "M_GRH", InvEE, [Next]_vars
  PROVE  InvEE'
BY NextTypeOK, NextExecutionIsExecutive DEF InvEE

THEOREM ExecutionIsExecutiveAlways ==
  ASSUME Mut # "M_GRH"
  PROVE  Spec => []ExecutionIsExecutive
<1>1. InvEE /\ [Next]_vars => InvEE'
  BY NextInvEE
<1>2. InvEE => ExecutionIsExecutive
  BY DEF InvEE
<1> QED
  BY InitInvEE, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* UnitaryExecutive [Mut # "M_HUMPHREY"]                                    *)

LEMMA InitInvUE == Init => InvUE
BY InitTypeOK DEF Init, InvUE, UnitaryExecutive, Live, Blank

LEMMA NextInvUE ==
  ASSUME Mut # "M_HUMPHREY", InvUE, [Next]_vars
  PROVE  InvUE'
<1>1. TypeOK'
  BY NextTypeOK DEF InvUE
<1>2. ASSUME NEW a \in Agencies
      PROVE  (Live(a) /\ agency[a].executesLaw => agency[a].removal = "AtWill")'
  <2>1. \/ SameCharter(agency'[a], agency[a])
        \/ ~agency'[a].exists
        \/ \E c \in Charters : Chartered(c) /\ FromCharter(agency'[a], c)
    BY StatuteFrame DEF InvUE
  <2> QED
    BY <2>1, ChartersWF DEF InvUE, UnitaryExecutive, Live, SameCharter, FromCharter, Chartered,
                            CharterRecord, Removal
<1> QED
  BY <1>1, <1>2 DEF InvUE, UnitaryExecutive

THEOREM UnitaryExecutiveAlways ==
  ASSUME Mut # "M_HUMPHREY"
  PROVE  Spec => []UnitaryExecutive
<1>1. InvUE /\ [Next]_vars => InvUE'
  BY NextInvUE
<1>2. InvUE => UnitaryExecutive
  BY DEF InvUE
<1> QED
  BY InitInvUE, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* NoCongressionalAppointment [Mut # "M_FECA"]                              *)
(* Strengthened by CongressVestingOK: no live agency both executes the      *)
(* laws and vests appointment in Congress, which is Chartered's Buckley     *)
(* check written over the state.                                            *)

LEMMA InitInvNCA == Init => InvNCA
BY InitTypeOK DEF Init, InvNCA, CongressVestingOK, VestOK, Blank, NoCongressionalAppointment

LEMMA NextInvNCA ==
  ASSUME Mut # "M_FECA", InvNCA, [Next]_vars
  PROVE  InvNCA'
<1>1. TypeOK'
  BY NextTypeOK DEF InvNCA
<1>2. CongressVestingOK'
  <2> SUFFICES ASSUME NEW a \in Agencies PROVE VestOK(agency[a])'
    BY DEF CongressVestingOK
  <2>1. \/ SameCharter(agency'[a], agency[a])
        \/ ~agency'[a].exists
        \/ \E c \in Charters : Chartered(c) /\ FromCharter(agency'[a], c)
    BY StatuteFrame DEF InvNCA
  <2> QED
    BY <2>1 DEF InvNCA, CongressVestingOK, VestOK, SameCharter, FromCharter, Chartered
<1>3. NoCongressionalAppointment'
  <2>1. CASE \E a \in Agencies, p \in Persons : AppointInferior(a, p)
    <3>1. PICK a \in Agencies, p \in Persons : AppointInferior(a, p)
      BY <2>1
    <3>2. ~(agency[a].vesting = "Congress" /\ agency[a].executesLaw)
      BY <3>1 DEF AppointInferior, Live, InvNCA, CongressVestingOK, VestOK
    <3> QED
      BY <3>1, <3>2 DEF AppointInferior, InvNCA, NoCongressionalAppointment
  <2>2. CASE UNCHANGED congressAppointed
    BY <2>2 DEF InvNCA, NoCongressionalAppointment
  <2> QED
    BY <2>1, <2>2, FlagFrame
<1> QED
  BY <1>1, <1>2, <1>3 DEF InvNCA

THEOREM NoCongressionalAppointmentAlways ==
  ASSUME Mut # "M_FECA"
  PROVE  Spec => []NoCongressionalAppointment
<1>1. InvNCA /\ [Next]_vars => InvNCA'
  BY NextInvNCA
<1>2. InvNCA => NoCongressionalAppointment
  BY DEF InvNCA
<1> QED
  BY InitInvNCA, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* CongressDoesNotRemoveExecutors [Mut # "M_JOINTRES", Mut # "M_GRH"]       *)
(* Strengthened by ExecutionIsExecutive: Congress removes only its own      *)
(* officers, and none of them executes the laws.                            *)

LEMMA InitInvCDR == Init => InvCDR
BY InitInvEE DEF InvEE, InvCDR, Init, CongressDoesNotRemoveExecutors

LEMMA NextInvCDR ==
  ASSUME Mut # "M_JOINTRES", Mut # "M_GRH", InvCDR, [Next]_vars
  PROVE  InvCDR'
<1>1. TypeOK' /\ ExecutionIsExecutive'
  BY NextTypeOK, NextExecutionIsExecutive DEF InvCDR
<1>2. CongressDoesNotRemoveExecutors'
  <2>1. CASE \E a \in Agencies : CongressRemovesHead(a)
    <3>1. PICK a \in Agencies : CongressRemovesHead(a)
      BY <2>1
    <3>2. agency[a].branch = "Legislative" /\ Live(a)
      BY <3>1 DEF CongressRemovesHead, OwnOfficer
    <3>3. ~agency[a].executesLaw
      BY <3>2 DEF InvCDR, ExecutionIsExecutive
    <3> QED
      BY <3>1, <3>3 DEF CongressRemovesHead, InvCDR, CongressDoesNotRemoveExecutors
  <2>2. CASE UNCHANGED congressRemoved
    BY <2>2 DEF InvCDR, CongressDoesNotRemoveExecutors
  <2> QED
    BY <2>1, <2>2, FlagFrame
<1> QED
  BY <1>1, <1>2 DEF InvCDR

THEOREM CongressDoesNotRemoveExecutorsAlways ==
  ASSUME Mut # "M_JOINTRES", Mut # "M_GRH"
  PROVE  Spec => []CongressDoesNotRemoveExecutors
<1>1. InvCDR /\ [Next]_vars => InvCDR'
  BY NextInvCDR
<1>2. InvCDR => CongressDoesNotRemoveExecutors
  BY DEF InvCDR
<1> QED
  BY InitInvCDR, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* PardonScope [Mut # "M_DANBY", Mut # "M_STATECRIME"]: inductive alone     *)

LEMMA NextPardonScope ==
  ASSUME Mut # "M_DANBY", Mut # "M_STATECRIME", PardonScope, [Next]_vars
  PROVE  PardonScope'
<1>1. CASE \E k \in Offences : Pardon(k)
  <2>1. PICK k \in Offences : Pardon(k)
    BY <1>1
  <2>2. k = "Federal"
    BY <2>1 DEF Pardon, PardonReaches, Offences
  <2> QED
    BY <2>1, <2>2 DEF Pardon, PardonScope
<1>2. CASE UNCHANGED pardoned
  BY <1>2 DEF PardonScope
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM PardonScopeAlways ==
  ASSUME Mut # "M_DANBY", Mut # "M_STATECRIME"
  PROVE  Spec => []PardonScope
<1>1. PardonScope /\ [Next]_vars => PardonScope'
  BY NextPardonScope
<1>2. Init => PardonScope
  BY DEF Init, PardonScope
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* WarIsCongressional [Mut # "M_PREROGATIVE"]: a flag, inductive alone      *)

LEMMA NextWar ==
  ASSUME Mut # "M_PREROGATIVE", WarIsCongressional, [Next]_vars
  PROVE  WarIsCongressional'
<1>1. CASE \E v \in Votes : DeclareWar(v)
  BY <1>1 DEF DeclareWar, WarAuthorised, WarIsCongressional
<1>2. CASE UNCHANGED warWithoutStatute
  BY <1>2 DEF WarIsCongressional
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM WarIsCongressionalAlways ==
  ASSUME Mut # "M_PREROGATIVE"
  PROVE  Spec => []WarIsCongressional
<1>1. WarIsCongressional /\ [Next]_vars => WarIsCongressional'
  BY NextWar
<1>2. Init => WarIsCongressional
  BY DEF Init, WarIsCongressional
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* TreatiesByTwoThirds [Mut # "M_AUG6"]: a flag, inductive alone            *)

LEMMA NextTreaty ==
  ASSUME Mut # "M_AUG6", TreatiesByTwoThirds, [Next]_vars
  PROVE  TreatiesByTwoThirds'
<1>1. CASE \E t \in Treaties, v \in Votes : RatifyTreaty(t, v)
  BY <1>1 DEF RatifyTreaty, TreatyVote, TreatiesByTwoThirds
<1>2. CASE UNCHANGED treatyShort
  BY <1>2 DEF TreatiesByTwoThirds
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM TreatiesByTwoThirdsAlways ==
  ASSUME Mut # "M_AUG6"
  PROVE  Spec => []TreatiesByTwoThirds
<1>1. TreatiesByTwoThirds /\ [Next]_vars => TreatiesByTwoThirds'
  BY NextTreaty
<1>2. Init => TreatiesByTwoThirds
  BY DEF Init, TreatiesByTwoThirds
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* The mechanism as specified                                               *)

THEOREM TypeOKAlways == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec

THEOREM SafeAlways ==
  ASSUME Mut = "none"
  PROVE  Spec => []Safety
<1>1. Spec => []OneExecutive
  BY OneExecutiveAlways
<1>2. Spec => []Incompatibility
  BY IncompatibilityAlways
<1>3. Spec => []Disqualification
  BY DisqualificationAlways
<1>4. Spec => []ActingIsNotHead
  BY ActingIsNotHeadAlways
<1>5. Spec => []ActingIsTemporary
  BY ActingIsTemporaryAlways
<1>6. Spec => []NoCongressionalAppointment
  BY NoCongressionalAppointmentAlways
<1>7. Spec => []ExecutionIsExecutive
  BY ExecutionIsExecutiveAlways
<1>8. Spec => []UnitaryExecutive
  BY UnitaryExecutiveAlways
<1>9. Spec => []PardonScope
  BY PardonScopeAlways
<1>10. Spec => []WarIsCongressional
  BY WarIsCongressionalAlways
<1>11. Spec => []CongressDoesNotRemoveExecutors
  BY CongressDoesNotRemoveExecutorsAlways
<1>12. Spec => []TreatiesByTwoThirds
  BY TreatiesByTwoThirdsAlways
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, PTL
  DEF Safety

-----------------------------------------------------------------------------
(* Why each mutation must fail: what it admits, in the module's terms. The  *)
(* counterexamples are TLC's (results/Executive-results-*.txt).             *)

\* The President and Vice President may be one person.
LEMMA MutSamePersonAdmits ==
  ASSUME Mut = "M_SAMEPERSON", NEW p \in Persons
  PROVE  TwoPeople(p, p)
BY DEF TwoPeople

\* A President with no Vice President may declare an inability; then no one
\* holds the executive power.
LEMMA MutNoVPAdmits ==
  ASSUME Mut = "M_NOVP", inability = "None", president # NoOne, vicePresident = NoOne
  PROVE  /\ ENABLED DeclareInability
         /\ (inability' = "SelfDeclared" /\ UNCHANGED vicePresident) => Executive' = NoOne
<1>1. ENABLED DeclareInability
  BY ExpandENABLED DEF DeclareInability, VPToAct, execVars, sideVars, impVars, flagVars
<1>2. (inability' = "SelfDeclared" /\ UNCHANGED vicePresident) => Executive' = NoOne
  BY DEF Executive, Acting
<1> QED
  BY <1>1, <1>2

\* A member of Congress passes EligibleOfficer's Incompatibility check.
LEMMA MutPlacemenAdmits ==
  ASSUME Mut = "M_PLACEMEN", NEW p \in Congress
  PROVE  NotMember(p)
BY DEF NotMember

\* A disqualified person passes EligibleOfficer's disqualification check.
LEMMA MutDisqualAdmits ==
  ASSUME Mut = "M_DISQUAL", NEW p \in disqualified
  PROVE  NotDisqualified(p)
BY DEF NotDisqualified

\* The first assistant may act beside a confirmed head.
LEMMA MutActWhileFilledAdmits ==
  ASSUME Mut = "M_ACTWHILEFILLED", NEW a \in Agencies, agency[a].head # NoOne
  PROVE  OfficeVacant(a)
BY DEF OfficeVacant

\* The day count may pass the limit.
LEMMA MutPreFVRAAdmits ==
  ASSUME Mut = "M_PREFVRA", NEW a \in Agencies, agency[a].actingDays = ActingLimit
  PROVE  WithinLimit(a)
BY DEF WithinLimit

\* Each charter mutation admits the statute its check refuses (KnownCharters).
LEMMA MutFECAAdmits ==
  ASSUME Mut = "M_FECA"
  PROVE  LET c == [branch |-> "Executive", executesLaw |-> TRUE, removal |-> "AtWill",
                   vesting |-> "Congress"]
         IN  Chartered(c) /\ c.vesting = "Congress" /\ c.executesLaw
BY DEF Chartered

LEMMA MutGRHAdmits ==
  ASSUME Mut = "M_GRH"
  PROVE  LET c == [branch |-> "Legislative", executesLaw |-> TRUE, removal |-> "AtWill",
                   vesting |-> "President"]
         IN  Chartered(c) /\ c.executesLaw /\ c.branch # "Executive"
BY DEF Chartered

LEMMA MutHumphreyAdmits ==
  ASSUME Mut = "M_HUMPHREY"
  PROVE  LET c == [branch |-> "Executive", executesLaw |-> TRUE, removal |-> "ForCause",
                   vesting |-> "President"]
         IN  Chartered(c) /\ c.executesLaw /\ c.removal # "AtWill"
BY DEF Chartered

\* Congress may remove the head of an agency outside its own branch.
LEMMA MutJointResAdmits ==
  ASSUME Mut = "M_JOINTRES", NEW a \in Agencies, agency[a].branch = "Executive"
  PROVE  OwnOfficer(a)
BY DEF OwnOfficer

LEMMA MutDanbyAdmits ==
  ASSUME Mut = "M_DANBY"
  PROVE  PardonReaches("Impeachment")
BY DEF PardonReaches

LEMMA MutStateCrimeAdmits ==
  ASSUME Mut = "M_STATECRIME"
  PROVE  PardonReaches("State")
BY DEF PardonReaches

\* A President may change the state of war on a vote that failed.
LEMMA MutPrerogativeAdmits ==
  ASSUME Mut = "M_PREROGATIVE", Executive # NoOne
  PROVE  WarAuthorised("Fails") /\ ~Majority("Fails")
BY DEF WarAuthorised, Majority

\* A treaty may be ratified by a majority short of two-thirds.
LEMMA MutAug6Admits ==
  ASSUME Mut = "M_AUG6"
  PROVE  TreatyVote("Majority") /\ ~TwoThirds("Majority")
BY DEF TreatyVote, Majority, TwoThirds

=============================================================================
