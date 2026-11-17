--------------------------- MODULE Elections_proof ---------------------------
(****************************************************************************)
(* TLAPS proofs of the safety properties of Elections.tla. The base module  *)
(* is extended, never edited; the proof results file names it by digest.    *)
(*                                                                          *)
(* THEOREMS, each Spec => []P under exactly the mutations that break P in   *)
(* the TLC results file (results/Elections-results-*.txt):                  *)
(*   ElectorsHoldNoOfficeAlways    [Mut # M_OFFICER_ELECTOR]                *)
(*   AppointedOnElectionDayAlways  [Mut # M_FAILED_CHOICE]                  *)
(*   SameDayAlways                 [Mut # M_LATE_VOTE]                      *)
(*   OneNotAnInhabitantAlways      [Mut # M_HABITATION]                     *)
(*   PledgesBindAlways             [Mut # M_FAITHLESS]                      *)
(*   NewCongressCountsAlways       [Mut # M_PRE_XX]                         *)
(*   CountIsCongressAlways         [Mut # M_PRESIDING]                      *)
(*   ElectorsChooseAlways          [Mut # M_PRE_XII, Mut # M_PLURALITY]     *)
(*   DevolvesOnlyWithoutMajorityAlways [Mut # M_ENTITLED]                   *)
(*   CountCanCloseAlways  [Mut # M_SAME_NAME, Mut # M_PRE_XII,              *)
(*                         Mut # M_PLURALITY]                               *)
(*   ChoiceFromTheListAlways       [Mut # M_OFF_LIST]                       *)
(*   HouseVoteAlways       [Mut # M_HOUSE_QUORUM, Mut # M_HOUSE_PRESENT]    *)
(*   SenateVoteAlways      [Mut # M_SENATE_QUORUM, Mut # M_SENATE_PRESENT]  *)
(*   PresidentNotVPAlways          [Mut # M_ONE_PERSON]                     *)
(*   QualificationsAlways          [Mut # M_UNQUALIFIED]                    *)
(*   DisabilityAlways              [Mut # M_XIV3]                           *)
(*   TwoTermLimitAlways            [Mut # M_XXII, Mut # M_XXII_SERVICE]     *)
(*   VPElectBecomesOnlyOnDeathAlways [Mut # M_XX3_BECOMES]                  *)
(*   ActingOrderAlways             [Mut # M_SPEAKER_FIRST]                  *)
(*   TypeOKAlways                  [none: every mutation]                   *)
(*   SafeAlways                    [Mut = "none"]: Spec => []Safety         *)
(*   ExecutiveIsFilledAlways       [Mut # M_NO_STATUTE]:                    *)
(*                                 FairSpec => ExecutiveIsFilled            *)
(* and one lemma per mutation (Mut...Admits) saying what it lets through.   *)
(* M_NO_STATUTE breaks no safety property, so no safety theorem cites it;   *)
(* it is the one hypothesis of the liveness theorem.                        *)
(*                                                                          *)
(* ASSUMPTIONS: the base module's named ASSUMEs PersonsWF, NoOneWF,         *)
(* SuccessorWF, FiniteWF and CollegeWF (MutKnown and InhabitantsWF are not  *)
(* used). So the theorems hold for every finite college, every set of       *)
(* candidates, States and Senators, every Inhabitants and every Binding     *)
(* within it; the rows' three seats and two candidates, and the bound       *)
(* ElectionsBound, are TLC's business and are not assumed. In particular    *)
(* CountCanClose and DevolvesOnlyWithoutMajority are proved at every        *)
(* number of candidates, where the rows reach two and three.                *)
(*                                                                          *)
(* INDUCTIVE STRENGTHENING, in prose:                                       *)
(*  - TypeOK, under every mutation, cited by every lemma that reads a       *)
(*    function after an EXCEPT.                                             *)
(*  - Eleven properties are flags set by one action each (FlagFrame); each  *)
(*    is inductive alone, the flag's condition being the negation of the    *)
(*    guard its mutation removes. ElectorsChoose and                        *)
(*    DevolvesOnlyWithoutMajority are flags whose guard is a count: their   *)
(*    steps rest on the cardinality lemmas (Sizes, VoteSizes,               *)
(*    DisjointVotes), which say that the votes counted are at most the      *)
(*    electors appointed, that one elector's ballot is on one list for      *)
(*    President, and so that a majority of the whole number beats every     *)
(*    plurality (MajorityCarries) and a carrying count is a majority        *)
(*    (CarriesIsMajority).                                                  *)
(*  - ElectorsHoldNoOffice and OneNotAnInhabitant are inductive alone over  *)
(*    the college variables (CollegeFrame), decided at Appoint and Vote.    *)
(*  - PledgesBind needs BallotNeedsPledge: a ballot is cast only by an      *)
(*    appointed elector, and Announce and OpenElection clear both. Without  *)
(*    it a seat could be appointed under a ballot already cast. Under every *)
(*    mutation.                                                             *)
(*  - CountCanClose is not inductive but valid: in every state whose        *)
(*    ballots each name two persons (TwoNamesOnBallots, from Vote's         *)
(*    TwoNames, under Mut # M_SAME_NAME) some pair can be announced. The    *)
(*    pair is whoever carries each list, or NoOne; that they are two        *)
(*    persons is the pigeonhole: a majority of the whole number on each     *)
(*    list shares an elector, whose ballot names two persons               *)
(*    (Pigeonhole, ClosesUnderInv).                                         *)
(*  - PresidentNotVP, Qualifications, Disability and ActingOrder are        *)
(*    inductive alone over the office variables (OfficeFrame), decided by   *)
(*    TwoPersons, VQualified and NoVP at each seating; Die only empties     *)
(*    seats or moves the Vice President up; relieved only grows.            *)
(*                                                                          *)
(*  - ExecutiveIsFilled is a leads-to with no quantifier, so it is one WF1  *)
(*    step (SomeoneCanAct, ActingFills, ClockLeavesFounding); no measure is *)
(*    needed, one fair step filling the vacancy.                            *)
(*                                                                          *)
(* NOT PROVED                                                               *)
(*  - That the weaker fairness conditions (SpecVPOnly, SpecSuccessorOnly,   *)
(*    SpecEachAlone) do not suffice, and that FairSpec has a behaviour at   *)
(*    all (NoBehaviour): existential, checked by TLC in the liveness rows.  *)
(*  - Reachability (the Never... witnesses) and the mutations'              *)
(*    counterexamples: existential, so TLC's. ElectionsBound is a TLC       *)
(*    device only.                                                          *)
(*                                                                          *)
(* CHECK: scripts/proof_results.py Elections (tools/tlapm --cleanfp         *)
(* --strict --cache-dir <tmp> Elections_proof.tla); flip a hypothesis with  *)
(* scripts/flip_test.py Elections M_X.                                      *)
(****************************************************************************)
EXTENDS Elections, FiniteSetTheorems, TLAPS

-----------------------------------------------------------------------------
(* Inductive invariants                                                     *)

\* A ballot is cast only by an appointed elector; Announce and OpenElection
\* clear ballots and pledges together.
BallotNeedsPledge == \A e \in Electors : ballot[e] # NoBallot => pledge[e] # NoOne

\* Every ballot cast names two persons (Vote's TwoNames).
TwoNamesOnBallots == \A e \in Electors : ballot[e] = NoBallot \/ ballot[e].p # ballot[e].v

InvEHNO == TypeOK /\ ElectorsHoldNoOffice
InvONI  == TypeOK /\ OneNotAnInhabitant
InvPB   == TypeOK /\ BallotNeedsPledge /\ PledgesBind
InvCC   == TypeOK /\ TwoNamesOnBallots
InvPNV  == TypeOK /\ PresidentNotVP
InvQ    == TypeOK /\ Qualifications
InvD    == TypeOK /\ Disability
InvAO   == TypeOK /\ ActingOrder

-----------------------------------------------------------------------------
(* The type invariant, under every mutation                                 *)

LEMMA InitTypeOK == Init => TypeOK
BY NoOneWF DEF Init, TypeOK, Blank, Stages, Clocks, Choice, Rulings, Seat

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  OBVIOUS
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, TypeOK
<1>2. CASE CollegeSteps
  <2>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE TypeOK'
    BY <2>1 DEF Appoint, TypeOK, Choice
  <2>2. CASE ElectionDayEnds
    BY <2>2 DEF ElectionDayEnds, TypeOK, Stages
  <2>3. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
        PROVE  TypeOK'
    BY <2>3 DEF Vote, TypeOK, Ballots
  <2>4. CASE ElectorsAdjourn
    BY <2>4 DEF ElectorsAdjourn, TypeOK, Stages
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4 DEF CollegeSteps
<1>3. CASE CountSteps
  <2>1. ASSUME NEW new \in BOOLEAN, OpenCount(new) PROVE TypeOK'
    BY <2>1 DEF OpenCount, TypeOK, Stages
  <2>2. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
        PROVE  TypeOK'
    BY <2>2 DEF Sustain, TypeOK, Grounds, Rulings
  <2>3. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE TypeOK'
    BY <2>3 DEF Announce, TypeOK, Stages, Blank, PTop, VTop, Choice, Rulings
  <2>4. ASSUME NEW c \in Candidates, NEW Q \in SUBSET States, NEW Y \in SUBSET Q,
               HouseChooses(c, Q, Y)
        PROVE  TypeOK'
    BY <2>4 DEF HouseChooses, TypeOK, Choice
  <2>5. ASSUME NEW c \in Candidates, NEW Q \in SUBSET Senators, NEW Y \in SUBSET Q,
               SenateChooses(c, Q, Y)
        PROVE  TypeOK'
    BY <2>5 DEF SenateChooses, TypeOK, Choice
  <2> QED
    BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5 DEF CountSteps
<1>4. CASE NoonSteps
  <2>0. vElect \in Seat /\ pElect \in Seat /\ (VQualified(vElect) => vElect \in Persons)
        /\ (VQualified(pElect) => pElect \in Persons)
    BY PersonsWF DEF TypeOK, Choice, Seat, VQualified
  <2>1. CASE NoonInaugurates
    <3>1. pElect \in Persons
      BY <2>0, <2>1 DEF NoonInaugurates, Qualified
    <3> QED
      BY <2>0, <2>1, <3>1 DEF NoonInaugurates, TypeOK, Clocks, Seat, VPSeat
  <2>2. CASE NoonSucceeds
    BY <2>0, <2>2 DEF NoonSucceeds, TypeOK, Clocks, Seat
  <2>3. CASE NoonVacant
    BY <2>0, <2>3 DEF NoonVacant, TypeOK, Clocks, Seat, VPSeat
  <2>4. CASE Qualify
    <3>1. pElect \in Persons
      BY <2>0, <2>4 DEF Qualify, Qualified
    <3> QED
      BY <2>0, <2>4, <3>1 DEF Qualify, TypeOK, Seat
  <2>5. CASE VPQualify
    BY <2>0, <2>5 DEF VPQualify, TypeOK, Seat
  <2>6. CASE VPActs
    BY <2>6 DEF VPActs, TypeOK
  <2>7. CASE SuccessorActs
    BY <2>7, SuccessorWF, PersonsWF DEF SuccessorActs, TypeOK, Seat
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF NoonSteps
<1>5. CASE TermSteps
  <2>1. ASSUME NEW x \in Persons, Die(x) PROVE TypeOK'
    BY <2>1 DEF Die, TypeOK, Seat
  <2>2. ASSUME NEW x \in Persons, RemoveDisability(x) PROVE TypeOK'
    BY <2>2 DEF RemoveDisability, TypeOK
  <2>3. CASE Midterm
    BY <2>3 DEF Midterm, TypeOK, Clocks
  <2>4. CASE OpenElection
    BY <2>4 DEF OpenElection, TypeOK, Clocks, Stages, Blank, Choice, Rulings
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4 DEF TermSteps
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

THEOREM TypeOKAlways == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec

-----------------------------------------------------------------------------
(* Frames: which steps can change which variables                           *)

\* The college variables change only at Appoint, Vote, Sustain, Announce and
\* OpenElection.
LEMMA CollegeFrame ==
  ASSUME [Next]_vars
  PROVE  \/ \E e \in Electors, c \in Candidates : Appoint(e, c)
         \/ \E e \in Electors, p, v \in Candidates : Vote(e, p, v)
         \/ \E e \in Electors, g \in Grounds, both \in BOOLEAN : Sustain(e, g, both)
         \/ \E p, v \in Choice : Announce(p, v)
         \/ OpenElection
         \/ UNCHANGED collegeVars
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE CollegeSteps
  BY <1>2 DEF CollegeSteps, ElectionDayEnds, ElectorsAdjourn
<1>3. CASE CountSteps
  BY <1>3 DEF CountSteps, OpenCount, HouseChooses, SenateChooses
<1>4. CASE NoonSteps
  BY <1>4 DEF NoonSteps, NoonInaugurates, NoonSucceeds, NoonVacant, Qualify, VPQualify,
                VPActs, SuccessorActs
<1>5. CASE TermSteps
  BY <1>5 DEF TermSteps, Die, RemoveDisability, Midterm
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

\* The elect and office variables change only at the count's end, the Houses'
\* choices, the next election, the noon steps and a death.
LEMMA ElectOfficeFrame ==
  ASSUME [Next]_vars
  PROVE  \/ \E p, v \in Choice : Announce(p, v)
         \/ \E c \in Candidates, Q \in SUBSET States : \E Y \in SUBSET Q : HouseChooses(c, Q, Y)
         \/ \E c \in Candidates, Q \in SUBSET Senators : \E Y \in SUBSET Q : SenateChooses(c, Q, Y)
         \/ OpenElection
         \/ NoonSteps
         \/ \E x \in Persons : Die(x)
         \/ UNCHANGED <<electVars, officeVars>>
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE CollegeSteps
  BY <1>2 DEF CollegeSteps, Appoint, ElectionDayEnds, Vote, ElectorsAdjourn
<1>3. CASE CountSteps
  BY <1>3 DEF CountSteps, OpenCount, Sustain
<1>4. CASE NoonSteps
  BY <1>4
<1>5. CASE TermSteps
  BY <1>5 DEF TermSteps, RemoveDisability, Midterm
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

\* The office variables change only at the noon steps and a death.
LEMMA OfficeFrame ==
  ASSUME [Next]_vars
  PROVE  NoonSteps \/ (\E x \in Persons : Die(x)) \/ UNCHANGED officeVars
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE CollegeSteps
  BY <1>2 DEF CollegeSteps, Appoint, ElectionDayEnds, Vote, ElectorsAdjourn
<1>3. CASE CountSteps
  BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce, HouseChooses, SenateChooses
<1>4. CASE NoonSteps
  BY <1>4
<1>5. CASE TermSteps
  BY <1>5 DEF TermSteps, RemoveDisability, Midterm, OpenElection
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

\* A disability once removed stays removed.
LEMMA RelievedGrows ==
  ASSUME [Next]_vars
  PROVE  relieved \subseteq relieved'
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE CollegeSteps
  BY <1>2 DEF CollegeSteps, Appoint, ElectionDayEnds, Vote, ElectorsAdjourn
<1>3. CASE CountSteps
  BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce, HouseChooses, SenateChooses
<1>4. CASE NoonSteps
  BY <1>4 DEF NoonSteps, NoonInaugurates, NoonSucceeds, NoonVacant, Qualify, VPQualify,
                VPActs, SuccessorActs
<1>5. CASE TermSteps
  BY <1>5 DEF TermSteps, Die, RemoveDisability, Midterm, OpenElection
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

\* Each flag is changed by one action only (two for offList and thirdTerm).
LEMMA FlagFrame ==
  ASSUME [Next]_vars
  PROVE  /\ (\E e \in Electors, c \in Candidates : Appoint(e, c)) \/ UNCHANGED lateAppointment
         /\ (\E e \in Electors, p, v \in Candidates : Vote(e, p, v)) \/ UNCHANGED lateVote
         /\ (\E new \in BOOLEAN : OpenCount(new)) \/ UNCHANGED lameDuck
         /\ (\E e \in Electors, g \in Grounds, both \in BOOLEAN : Sustain(e, g, both))
              \/ UNCHANGED rejectedAlone
         /\ (\E p, v \in Choice : Announce(p, v)) \/ UNCHANGED <<minorityElect, wronglyDevolved>>
         /\ \/ \E c \in Candidates, Q \in SUBSET States : \E Y \in SUBSET Q : HouseChooses(c, Q, Y)
            \/ \E c \in Candidates, Q \in SUBSET Senators : \E Y \in SUBSET Q : SenateChooses(c, Q, Y)
            \/ UNCHANGED offList
         /\ (\E c \in Candidates, Q \in SUBSET States : \E Y \in SUBSET Q : HouseChooses(c, Q, Y))
              \/ UNCHANGED houseShort
         /\ (\E c \in Candidates, Q \in SUBSET Senators : \E Y \in SUBSET Q : SenateChooses(c, Q, Y))
              \/ UNCHANGED senateShort
         /\ NoonInaugurates \/ Qualify \/ UNCHANGED thirdTerm
         /\ NoonSucceeds \/ UNCHANGED becameWithoutDeath
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE CollegeSteps
  <2>1. (\E e \in Electors, c \in Candidates : Appoint(e, c)) \/ UNCHANGED lateAppointment
    BY <1>2 DEF CollegeSteps, ElectionDayEnds, Vote, ElectorsAdjourn
  <2>2. (\E e \in Electors, p, v \in Candidates : Vote(e, p, v)) \/ UNCHANGED lateVote
    BY <1>2 DEF CollegeSteps, Appoint, ElectionDayEnds, ElectorsAdjourn
  <2>3. UNCHANGED <<lameDuck, rejectedAlone, minorityElect, wronglyDevolved, offList,
                    houseShort, senateShort, thirdTerm, becameWithoutDeath>>
    BY <1>2 DEF CollegeSteps, Appoint, ElectionDayEnds, Vote, ElectorsAdjourn
  <2> QED
    BY <2>1, <2>2, <2>3
<1>3. CASE CountSteps
  <2>1. (\E new \in BOOLEAN : OpenCount(new)) \/ UNCHANGED lameDuck
    BY <1>3 DEF CountSteps, Sustain, Announce, HouseChooses, SenateChooses
  <2>2. (\E e \in Electors, g \in Grounds, both \in BOOLEAN : Sustain(e, g, both))
          \/ UNCHANGED rejectedAlone
    BY <1>3 DEF CountSteps, OpenCount, Announce, HouseChooses, SenateChooses
  <2>3. (\E p, v \in Choice : Announce(p, v)) \/ UNCHANGED <<minorityElect, wronglyDevolved>>
    BY <1>3 DEF CountSteps, OpenCount, Sustain, HouseChooses, SenateChooses
  <2>4. \/ \E c \in Candidates, Q \in SUBSET States : \E Y \in SUBSET Q : HouseChooses(c, Q, Y)
        \/ \E c \in Candidates, Q \in SUBSET Senators : \E Y \in SUBSET Q : SenateChooses(c, Q, Y)
        \/ UNCHANGED offList
    BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce
  <2>5. (\E c \in Candidates, Q \in SUBSET States : \E Y \in SUBSET Q : HouseChooses(c, Q, Y))
          \/ UNCHANGED houseShort
    BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce, SenateChooses
  <2>6. (\E c \in Candidates, Q \in SUBSET Senators : \E Y \in SUBSET Q : SenateChooses(c, Q, Y))
          \/ UNCHANGED senateShort
    BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce, HouseChooses
  <2>7. UNCHANGED <<lateAppointment, lateVote, thirdTerm, becameWithoutDeath>>
    BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce, HouseChooses, SenateChooses
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
<1>4. CASE NoonSteps
  <2>1. NoonInaugurates \/ Qualify \/ UNCHANGED thirdTerm
    BY <1>4 DEF NoonSteps, NoonSucceeds, NoonVacant, VPQualify, VPActs, SuccessorActs
  <2>2. NoonSucceeds \/ UNCHANGED becameWithoutDeath
    BY <1>4 DEF NoonSteps, NoonInaugurates, NoonVacant, Qualify, VPQualify, VPActs, SuccessorActs
  <2>3. UNCHANGED <<lateAppointment, lateVote, lameDuck, rejectedAlone, minorityElect,
                    wronglyDevolved, offList, houseShort, senateShort>>
    BY <1>4 DEF NoonSteps, NoonInaugurates, NoonSucceeds, NoonVacant, Qualify, VPQualify,
                  VPActs, SuccessorActs
  <2> QED
    BY <2>1, <2>2, <2>3
<1>5. CASE TermSteps
  BY <1>5 DEF TermSteps, Die, RemoveDisability, Midterm, OpenElection
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

-----------------------------------------------------------------------------
(* The count, as finite sets: the votes counted are at most the electors    *)
(* appointed, which are at most the seats; one elector's ballot is on one   *)
(* list for President and one for Vice President.                          *)

LEMMA Sizes ==
  /\ Counted \subseteq Appointed /\ Appointed \subseteq Pledged /\ Pledged \subseteq Electors
  /\ IsFiniteSet(Pledged) /\ IsFiniteSet(Appointed) /\ IsFiniteSet(Counted)
  /\ Cardinality(Electors) \in Nat /\ Whole \in Nat /\ Cardinality(Counted) \in Nat
  /\ Cardinality(Counted) <= Whole /\ Whole <= Cardinality(Electors)
  /\ Base \in Nat /\ Whole <= Base
<1>1. Counted \subseteq Appointed /\ Appointed \subseteq Pledged /\ Pledged \subseteq Electors
  BY DEF Counted, Appointed, Pledged
<1>2. IsFiniteSet(Electors)
  BY FiniteWF
<1>3. IsFiniteSet(Pledged) /\ IsFiniteSet(Appointed) /\ IsFiniteSet(Counted)
  BY <1>1, <1>2, FS_Subset
<1>4. /\ Cardinality(Electors) \in Nat /\ Cardinality(Pledged) \in Nat
      /\ Cardinality(Appointed) \in Nat /\ Cardinality(Counted) \in Nat
  BY <1>2, <1>3, FS_CardinalityType
<1>5. /\ Cardinality(Counted) <= Cardinality(Appointed)
      /\ Cardinality(Appointed) <= Cardinality(Pledged)
      /\ Cardinality(Pledged) <= Cardinality(Electors)
  BY <1>1, <1>2, <1>3, FS_Subset
<1> QED
  BY <1>1, <1>3, <1>4, <1>5 DEF Whole, Base

LEMMA VoteSizes ==
  ASSUME NEW c
  PROVE  /\ PFor(c) \subseteq Counted /\ VFor(c) \subseteq Counted
         /\ IsFiniteSet(PFor(c)) /\ IsFiniteSet(VFor(c)) /\ IsFiniteSet(PFor(c) \cup VFor(c))
         /\ PVotes(c) \in Nat /\ VVotes(c) \in Nat /\ PCount(c) \in Nat
         /\ PVotes(c) <= Cardinality(Counted) /\ VVotes(c) <= Cardinality(Counted)
         /\ PVotes(c) <= PCount(c) /\ PCount(c) <= Cardinality(Counted)
         /\ Cardinality(PFor(c) \cup VFor(c)) \in Nat
         /\ Cardinality(PFor(c) \cup VFor(c)) <= Cardinality(Counted)
<1>1. /\ PFor(c) \subseteq Counted /\ VFor(c) \subseteq Counted
      /\ (PFor(c) \cup VFor(c)) \subseteq Counted /\ PFor(c) \subseteq PFor(c) \cup VFor(c)
  BY DEF PFor, VFor
<1>2. IsFiniteSet(Counted) /\ Cardinality(Counted) \in Nat
  BY Sizes
<1>3. IsFiniteSet(PFor(c)) /\ IsFiniteSet(VFor(c)) /\ IsFiniteSet(PFor(c) \cup VFor(c))
  BY <1>1, <1>2, FS_Subset
<1>4. /\ Cardinality(PFor(c)) \in Nat /\ Cardinality(VFor(c)) \in Nat
      /\ Cardinality(PFor(c) \cup VFor(c)) \in Nat
  BY <1>3, FS_CardinalityType
<1>5. /\ Cardinality(PFor(c)) <= Cardinality(Counted) /\ Cardinality(VFor(c)) <= Cardinality(Counted)
      /\ Cardinality(PFor(c) \cup VFor(c)) <= Cardinality(Counted)
  BY <1>1, <1>2, FS_Subset
<1>6. Cardinality(PFor(c)) <= Cardinality(PFor(c) \cup VFor(c))
  BY <1>1, <1>3, FS_Subset
<1> QED
  BY <1>1, <1>3, <1>4, <1>5, <1>6 DEF PVotes, VVotes, PCount

LEMMA DisjointVotes ==
  ASSUME NEW c, NEW d, c # d
  PROVE  /\ PVotes(c) + PVotes(d) <= Cardinality(Counted)
         /\ VVotes(c) + VVotes(d) <= Cardinality(Counted)
<1>1. PFor(c) \cap PFor(d) = {} /\ VFor(c) \cap VFor(d) = {}
  BY DEF PFor, VFor
<1>2. /\ IsFiniteSet(PFor(c)) /\ IsFiniteSet(PFor(d)) /\ IsFiniteSet(VFor(c)) /\ IsFiniteSet(VFor(d))
      /\ PVotes(c) \in Nat /\ PVotes(d) \in Nat /\ VVotes(c) \in Nat /\ VVotes(d) \in Nat
  BY VoteSizes
<1>3. /\ Cardinality(PFor(c) \cup PFor(d)) = Cardinality(PFor(c)) + Cardinality(PFor(d))
      /\ Cardinality(VFor(c) \cup VFor(d)) = Cardinality(VFor(c)) + Cardinality(VFor(d))
  BY <1>1, <1>2, FS_Union, FS_EmptySet DEF PVotes, VVotes
<1>4. (PFor(c) \cup PFor(d)) \subseteq Counted /\ (VFor(c) \cup VFor(d)) \subseteq Counted
  BY DEF PFor, VFor
<1>5. IsFiniteSet(Counted)
  BY Sizes
<1>6. /\ Cardinality(PFor(c) \cup PFor(d)) <= Cardinality(Counted)
      /\ Cardinality(VFor(c) \cup VFor(d)) <= Cardinality(Counted)
  BY <1>4, <1>5, FS_Subset
<1> QED
  BY <1>3, <1>6 DEF PVotes, VVotes

\* Two majorities of the whole number share an elector.
LEMMA Pigeonhole ==
  ASSUME NEW p, PVotes(p) + VVotes(p) > Cardinality(Counted)
  PROVE  \E e \in Counted : ballot[e].p = p /\ ballot[e].v = p
<1>1. /\ IsFiniteSet(PFor(p)) /\ IsFiniteSet(VFor(p)) /\ IsFiniteSet(PFor(p) \cup VFor(p))
      /\ PVotes(p) \in Nat /\ VVotes(p) \in Nat /\ Cardinality(Counted) \in Nat
      /\ Cardinality(PFor(p) \cup VFor(p)) <= Cardinality(Counted)
      /\ Cardinality(PFor(p) \cup VFor(p)) \in Nat
  BY VoteSizes, Sizes, FS_CardinalityType
<1>2. Cardinality(PFor(p) \cup VFor(p)) =
        Cardinality(PFor(p)) + Cardinality(VFor(p)) - Cardinality(PFor(p) \cap VFor(p))
  BY <1>1, FS_Union
<1>3. (PFor(p) \cap VFor(p)) \subseteq PFor(p)
  OBVIOUS
<1>4. IsFiniteSet(PFor(p) \cap VFor(p)) /\ Cardinality(PFor(p) \cap VFor(p)) \in Nat
  BY <1>1, <1>3, FS_Subset, FS_CardinalityType
<1>5. Cardinality(PFor(p) \cap VFor(p)) > 0
  BY <1>1, <1>2, <1>4 DEF PVotes, VVotes
<1>6. PFor(p) \cap VFor(p) # {}
  BY <1>4, <1>5, FS_EmptySet
<1> QED
  BY <1>6 DEF PFor, VFor

\* A majority of the whole number is more than any other candidate has.
LEMMA MajorityBeatsAll ==
  ASSUME NEW c, NEW d, c # d
  PROVE  /\ PMajority(c) => PVotes(c) > PVotes(d)
         /\ VMajority(c) => VVotes(c) > VVotes(d)
BY DisjointVotes, VoteSizes, Sizes DEF PMajority, VMajority

\* A majority of the whole number carries the list, by majority or by
\* plurality; only M_ENTITLED, whose base may exceed the whole number, can
\* deny it.
LEMMA MajorityCarries ==
  ASSUME Mut # "M_ENTITLED", NEW c \in Candidates
  PROVE  /\ PMajority(c) => PCarries(c)
         /\ VMajority(c) => VCarries(c)
<1>0. /\ PVotes(c) \in Nat /\ VVotes(c) \in Nat /\ PCount(c) \in Nat /\ Whole \in Nat
      /\ PVotes(c) <= PCount(c) /\ Base = Whole
  BY VoteSizes, Sizes DEF Base
<1>1. CASE Mut = "M_PLURALITY"
  <2>1. \A d \in Candidates \ {c} : (PMajority(c) => PVotes(c) > PVotes(d))
                                   /\ (VMajority(c) => VVotes(c) > VVotes(d))
    BY MajorityBeatsAll
  <2>2. (PMajority(c) => PVotes(c) > 0) /\ (VMajority(c) => VVotes(c) > 0)
    BY <1>0 DEF PMajority, VMajority
  <2>3. \A d \in Candidates : PCount(d) = PVotes(d)
    BY <1>1 DEF PCount
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3 DEF PCarries, VCarries
<1>2. CASE Mut # "M_PLURALITY"
  BY <1>0, <1>2 DEF PCarries, VCarries, PMajority, VMajority
<1> QED
  BY <1>1, <1>2

\* Whoever carries a list has a majority of the whole number, unless the
\* list counts both names (M_PRE_XII) or a plurality carries (M_PLURALITY).
LEMMA CarriesIsMajority ==
  ASSUME NEW c
  PROVE  /\ (Mut # "M_PRE_XII" /\ Mut # "M_PLURALITY" /\ PCarries(c)) => PMajority(c)
         /\ (Mut # "M_PLURALITY" /\ VCarries(c)) => VMajority(c)
<1>0. /\ PVotes(c) \in Nat /\ VVotes(c) \in Nat /\ PCount(c) \in Nat /\ Whole \in Nat
      /\ Base \in Nat /\ Whole <= Base
  BY VoteSizes, Sizes
<1>1. Mut # "M_PRE_XII" => PCount(c) = PVotes(c)
  BY DEF PCount
<1> QED
  BY <1>0, <1>1 DEF PCarries, VCarries, PMajority, VMajority

-----------------------------------------------------------------------------
(* ElectorsHoldNoOffice [Mut # "M_OFFICER_ELECTOR"]                         *)

LEMMA InitInvEHNO == Init => InvEHNO
BY InitTypeOK DEF Init, InvEHNO, ElectorsHoldNoOffice, Pledged, Blank

LEMMA NextInvEHNO ==
  ASSUME Mut # "M_OFFICER_ELECTOR", InvEHNO, [Next]_vars
  PROVE  InvEHNO'
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ ElectorsHoldNoOffice
  BY NextTypeOK DEF InvEHNO
<1> SUFFICES ElectorsHoldNoOffice'
  BY <1>0 DEF InvEHNO
<1>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE ElectorsHoldNoOffice'
  BY <1>0, <1>1 DEF Appoint, MayBeElector, Pledged, ElectorsHoldNoOffice, TypeOK
<1>2. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
      PROVE  ElectorsHoldNoOffice'
  BY <1>0, <1>2 DEF Vote, Pledged, ElectorsHoldNoOffice
<1>3. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
      PROVE  ElectorsHoldNoOffice'
  BY <1>0, <1>3 DEF Sustain, Pledged, ElectorsHoldNoOffice
<1>4. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE ElectorsHoldNoOffice'
  BY <1>4 DEF Announce, Blank, Pledged, ElectorsHoldNoOffice
<1>5. CASE OpenElection
  BY <1>5 DEF OpenElection, Blank, Pledged, ElectorsHoldNoOffice
<1>6. CASE UNCHANGED collegeVars
  BY <1>0, <1>6 DEF Pledged, ElectorsHoldNoOffice
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, CollegeFrame

THEOREM ElectorsHoldNoOfficeAlways ==
  ASSUME Mut # "M_OFFICER_ELECTOR"
  PROVE  Spec => []ElectorsHoldNoOffice
<1>1. InvEHNO /\ [Next]_vars => InvEHNO'
  BY NextInvEHNO
<1>2. InvEHNO => ElectorsHoldNoOffice
  BY DEF InvEHNO
<1> QED
  BY InitInvEHNO, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* AppointedOnElectionDay [Mut # "M_FAILED_CHOICE"]                         *)

LEMMA NextAppointedOnElectionDay ==
  ASSUME Mut # "M_FAILED_CHOICE", AppointedOnElectionDay, [Next]_vars
  PROVE  AppointedOnElectionDay'
<1>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE AppointedOnElectionDay'
  BY <1>1 DEF Appoint, AppointmentOpen, AppointedOnElectionDay
<1>2. CASE UNCHANGED lateAppointment
  BY <1>2 DEF AppointedOnElectionDay
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM AppointedOnElectionDayAlways ==
  ASSUME Mut # "M_FAILED_CHOICE"
  PROVE  Spec => []AppointedOnElectionDay
<1>1. AppointedOnElectionDay /\ [Next]_vars => AppointedOnElectionDay'
  BY NextAppointedOnElectionDay
<1>2. Init => AppointedOnElectionDay
  BY DEF Init, AppointedOnElectionDay
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* SameDay [Mut # "M_LATE_VOTE"]                                            *)

LEMMA NextSameDay ==
  ASSUME Mut # "M_LATE_VOTE", SameDay, [Next]_vars
  PROVE  SameDay'
<1>1. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
      PROVE  SameDay'
  BY <1>1 DEF Vote, PollsOpen, SameDay
<1>2. CASE UNCHANGED lateVote
  BY <1>2 DEF SameDay
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM SameDayAlways ==
  ASSUME Mut # "M_LATE_VOTE"
  PROVE  Spec => []SameDay
<1>1. SameDay /\ [Next]_vars => SameDay'
  BY NextSameDay
<1>2. Init => SameDay
  BY DEF Init, SameDay
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* OneNotAnInhabitant [Mut # "M_HABITATION"]                                *)

LEMMA InitInvONI == Init => InvONI
BY InitTypeOK DEF Init, InvONI, OneNotAnInhabitant, Blank

LEMMA NextInvONI ==
  ASSUME Mut # "M_HABITATION", InvONI, [Next]_vars
  PROVE  InvONI'
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ OneNotAnInhabitant
  BY NextTypeOK DEF InvONI
<1> SUFFICES OneNotAnInhabitant'
  BY <1>0 DEF InvONI
<1>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE OneNotAnInhabitant'
  BY <1>0, <1>1 DEF Appoint, OneNotAnInhabitant
<1>2. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
      PROVE  OneNotAnInhabitant'
  <2>1. /\ ballot' = [ballot EXCEPT ![e] = [p |-> p, v |-> v]]
        /\ ~(SameState(e, p) /\ SameState(e, v))
    BY <1>2 DEF Vote, Habitation
  <2> QED
    BY <1>0, <2>1 DEF OneNotAnInhabitant, TypeOK
<1>3. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
      PROVE  OneNotAnInhabitant'
  BY <1>0, <1>3 DEF Sustain, OneNotAnInhabitant
<1>4. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE OneNotAnInhabitant'
  BY <1>4 DEF Announce, Blank, OneNotAnInhabitant
<1>5. CASE OpenElection
  BY <1>5 DEF OpenElection, Blank, OneNotAnInhabitant
<1>6. CASE UNCHANGED collegeVars
  BY <1>0, <1>6 DEF OneNotAnInhabitant
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, CollegeFrame

THEOREM OneNotAnInhabitantAlways ==
  ASSUME Mut # "M_HABITATION"
  PROVE  Spec => []OneNotAnInhabitant
<1>1. InvONI /\ [Next]_vars => InvONI'
  BY NextInvONI
<1>2. InvONI => OneNotAnInhabitant
  BY DEF InvONI
<1> QED
  BY InitInvONI, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* PledgesBind [Mut # "M_FAITHLESS"], strengthened by BallotNeedsPledge     *)

LEMMA InitInvPB == Init => InvPB
BY InitTypeOK, CollegeWF DEF Init, InvPB, BallotNeedsPledge, PledgesBind, Blank

\* Under every mutation.
LEMMA NextBallotNeedsPledge ==
  ASSUME TypeOK, BallotNeedsPledge, [Next]_vars
  PROVE  BallotNeedsPledge'
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK'
  BY NextTypeOK
<1>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE BallotNeedsPledge'
  <2>1. c # NoOne
    BY NoOneWF, PersonsWF
  <2> QED
    BY <1>1, <2>1 DEF Appoint, BallotNeedsPledge, TypeOK
<1>2. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
      PROVE  BallotNeedsPledge'
  BY <1>2 DEF Vote, BallotNeedsPledge, TypeOK
<1>3. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
      PROVE  BallotNeedsPledge'
  BY <1>3 DEF Sustain, BallotNeedsPledge
<1>4. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE BallotNeedsPledge'
  BY <1>4 DEF Announce, Blank, BallotNeedsPledge
<1>5. CASE OpenElection
  BY <1>5 DEF OpenElection, Blank, BallotNeedsPledge
<1>6. CASE UNCHANGED collegeVars
  BY <1>6 DEF BallotNeedsPledge
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, CollegeFrame

LEMMA NextPledgesBind ==
  ASSUME Mut # "M_FAITHLESS", TypeOK, BallotNeedsPledge, PledgesBind, [Next]_vars
  PROVE  PledgesBind'
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE PledgesBind'
  <2>1. ballot[e] = NoBallot /\ ballot' = ballot /\ pledge' = [pledge EXCEPT ![e] = c]
    BY <1>1 DEF Appoint, BallotNeedsPledge
  <2> QED
    BY <2>1, CollegeWF DEF PledgesBind, TypeOK
<1>2. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
      PROVE  PledgesBind'
  <2>1. /\ ballot' = [ballot EXCEPT ![e] = [p |-> p, v |-> v]] /\ pledge' = pledge
        /\ (e \in Binding => p = pledge[e])
    BY <1>2 DEF Vote, Faithful
  <2> QED
    BY <2>1, CollegeWF DEF PledgesBind, TypeOK
<1>3. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
      PROVE  PledgesBind'
  BY <1>3 DEF Sustain, PledgesBind
<1>4. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE PledgesBind'
  BY <1>4, CollegeWF DEF Announce, Blank, PledgesBind
<1>5. CASE OpenElection
  BY <1>5, CollegeWF DEF OpenElection, Blank, PledgesBind
<1>6. CASE UNCHANGED collegeVars
  BY <1>6 DEF PledgesBind
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, CollegeFrame

LEMMA NextInvPB ==
  ASSUME Mut # "M_FAITHLESS", InvPB, [Next]_vars
  PROVE  InvPB'
BY NextTypeOK, NextBallotNeedsPledge, NextPledgesBind DEF InvPB

THEOREM PledgesBindAlways ==
  ASSUME Mut # "M_FAITHLESS"
  PROVE  Spec => []PledgesBind
<1>1. InvPB /\ [Next]_vars => InvPB'
  BY NextInvPB
<1>2. InvPB => PledgesBind
  BY DEF InvPB
<1> QED
  BY InitInvPB, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* NewCongressCounts [Mut # "M_PRE_XX"]                                     *)

LEMMA NextNewCongressCounts ==
  ASSUME Mut # "M_PRE_XX", NewCongressCounts, [Next]_vars
  PROVE  NewCongressCounts'
<1>1. ASSUME NEW new \in BOOLEAN, OpenCount(new) PROVE NewCongressCounts'
  BY <1>1 DEF OpenCount, Seated, NewCongressCounts
<1>2. CASE UNCHANGED lameDuck
  BY <1>2 DEF NewCongressCounts
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM NewCongressCountsAlways ==
  ASSUME Mut # "M_PRE_XX"
  PROVE  Spec => []NewCongressCounts
<1>1. NewCongressCounts /\ [Next]_vars => NewCongressCounts'
  BY NextNewCongressCounts
<1>2. Init => NewCongressCounts
  BY DEF Init, NewCongressCounts
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* CountIsCongress [Mut # "M_PRESIDING"]                                    *)

LEMMA NextCountIsCongress ==
  ASSUME Mut # "M_PRESIDING", CountIsCongress, [Next]_vars
  PROVE  CountIsCongress'
<1>1. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
      PROVE  CountIsCongress'
  BY <1>1 DEF Sustain, Concur, CountIsCongress
<1>2. CASE UNCHANGED rejectedAlone
  BY <1>2 DEF CountIsCongress
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM CountIsCongressAlways ==
  ASSUME Mut # "M_PRESIDING"
  PROVE  Spec => []CountIsCongress
<1>1. CountIsCongress /\ [Next]_vars => CountIsCongress'
  BY NextCountIsCongress
<1>2. Init => CountIsCongress
  BY DEF Init, CountIsCongress
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* ElectorsChoose [Mut # "M_PRE_XII", Mut # "M_PLURALITY"]                  *)

LEMMA NextElectorsChoose ==
  ASSUME Mut # "M_PRE_XII", Mut # "M_PLURALITY", ElectorsChoose, [Next]_vars
  PROVE  ElectorsChoose'
<1>1. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE ElectorsChoose'
  <2>1. /\ (p # NoOne => PCarries(p)) /\ (v # NoOne => VCarries(v))
        /\ minorityElect' = (minorityElect \/ (p # NoOne /\ ~PMajority(p))
                                           \/ (v # NoOne /\ ~VMajority(v)))
    BY <1>1 DEF Announce, PResult, VResult
  <2>2. (p # NoOne => PMajority(p)) /\ (v # NoOne => VMajority(v))
    BY <2>1, CarriesIsMajority
  <2> QED
    BY <2>1, <2>2 DEF ElectorsChoose
<1>2. CASE UNCHANGED <<minorityElect, wronglyDevolved>>
  BY <1>2 DEF ElectorsChoose
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM ElectorsChooseAlways ==
  ASSUME Mut # "M_PRE_XII", Mut # "M_PLURALITY"
  PROVE  Spec => []ElectorsChoose
<1>1. ElectorsChoose /\ [Next]_vars => ElectorsChoose'
  BY NextElectorsChoose
<1>2. Init => ElectorsChoose
  BY DEF Init, ElectorsChoose
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* DevolvesOnlyWithoutMajority [Mut # "M_ENTITLED"]                         *)

LEMMA NextDevolvesOnlyWithoutMajority ==
  ASSUME Mut # "M_ENTITLED", DevolvesOnlyWithoutMajority, [Next]_vars
  PROVE  DevolvesOnlyWithoutMajority'
<1>1. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE DevolvesOnlyWithoutMajority'
  <2>1. /\ (p = NoOne => \A c \in Candidates : ~PCarries(c))
        /\ (v = NoOne => \A c \in Candidates : ~VCarries(c))
        /\ wronglyDevolved' = (wronglyDevolved
                                 \/ (p = NoOne /\ \E c \in Candidates : PMajority(c))
                                 \/ (v = NoOne /\ \E c \in Candidates : VMajority(c)))
    BY <1>1 DEF Announce, PResult, VResult
  <2>2. \A c \in Candidates : (PMajority(c) => PCarries(c)) /\ (VMajority(c) => VCarries(c))
    BY MajorityCarries
  <2> QED
    BY <2>1, <2>2 DEF DevolvesOnlyWithoutMajority
<1>2. CASE UNCHANGED <<minorityElect, wronglyDevolved>>
  BY <1>2 DEF DevolvesOnlyWithoutMajority
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM DevolvesOnlyWithoutMajorityAlways ==
  ASSUME Mut # "M_ENTITLED"
  PROVE  Spec => []DevolvesOnlyWithoutMajority
<1>1. DevolvesOnlyWithoutMajority /\ [Next]_vars => DevolvesOnlyWithoutMajority'
  BY NextDevolvesOnlyWithoutMajority
<1>2. Init => DevolvesOnlyWithoutMajority
  BY DEF Init, DevolvesOnlyWithoutMajority
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* CountCanClose [Mut # "M_SAME_NAME", Mut # "M_PRE_XII", Mut # "M_PLURALITY"] *)
(* Valid in every state whose ballots name two persons each; the invariant  *)
(* TwoNamesOnBallots is inductive under Mut # "M_SAME_NAME".                *)

LEMMA InitInvCC == Init => InvCC
BY InitTypeOK DEF Init, InvCC, TwoNamesOnBallots, Blank

LEMMA NextInvCC ==
  ASSUME Mut # "M_SAME_NAME", InvCC, [Next]_vars
  PROVE  InvCC'
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ TwoNamesOnBallots
  BY NextTypeOK DEF InvCC
<1> SUFFICES TwoNamesOnBallots'
  BY <1>0 DEF InvCC
<1>1. ASSUME NEW e \in Electors, NEW c \in Candidates, Appoint(e, c) PROVE TwoNamesOnBallots'
  BY <1>0, <1>1 DEF Appoint, TwoNamesOnBallots
<1>2. ASSUME NEW e \in Electors, NEW p \in Candidates, NEW v \in Candidates, Vote(e, p, v)
      PROVE  TwoNamesOnBallots'
  <2>1. ballot' = [ballot EXCEPT ![e] = [p |-> p, v |-> v]] /\ p # v
    BY <1>2 DEF Vote, TwoNames
  <2> QED
    BY <1>0, <2>1 DEF TwoNamesOnBallots, TypeOK
<1>3. ASSUME NEW e \in Electors, NEW g \in Grounds, NEW both \in BOOLEAN, Sustain(e, g, both)
      PROVE  TwoNamesOnBallots'
  BY <1>0, <1>3 DEF Sustain, TwoNamesOnBallots
<1>4. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE TwoNamesOnBallots'
  BY <1>4 DEF Announce, Blank, TwoNamesOnBallots
<1>5. CASE OpenElection
  BY <1>5 DEF OpenElection, Blank, TwoNamesOnBallots
<1>6. CASE UNCHANGED collegeVars
  BY <1>0, <1>6 DEF TwoNamesOnBallots
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, CollegeFrame

\* Some pair can be announced: whoever carries each list, or NoOne; and the
\* two are two persons, by the pigeonhole over the electors counted.
LEMMA ClosesUnderInv ==
  ASSUME Mut # "M_PRE_XII", Mut # "M_PLURALITY", InvCC
  PROVE  CountCanClose
<1>0. NoOne \in Choice /\ \A c \in Candidates : c \in Choice /\ c # NoOne
  BY NoOneWF, PersonsWF DEF Choice
<1>1. PICK p \in Choice : PResult(p)
  <2>1. CASE \E c \in Candidates : PCarries(c)
    <3>1. PICK c \in Candidates : PCarries(c)
      BY <2>1
    <3> QED
      BY <1>0, <3>1 DEF PResult
  <2>2. CASE ~\E c \in Candidates : PCarries(c)
    BY <1>0, <2>2 DEF PResult
  <2> QED
    BY <2>1, <2>2
<1>2. PICK v \in Choice : VResult(v)
  <2>1. CASE \E c \in Candidates : VCarries(c)
    <3>1. PICK c \in Candidates : VCarries(c)
      BY <2>1
    <3> QED
      BY <1>0, <3>1 DEF VResult
  <2>2. CASE ~\E c \in Candidates : VCarries(c)
    BY <1>0, <2>2 DEF VResult
  <2> QED
    BY <2>1, <2>2
<1>3. TwoPersons(p, v)
  <2>1. CASE p = NoOne \/ v = NoOne \/ p # v
    BY <2>1 DEF TwoPersons
  <2>2. CASE p # NoOne /\ v # NoOne /\ p = v
    <3>1. PCarries(p) /\ VCarries(p)
      BY <1>1, <1>2, <2>2 DEF PResult, VResult
    <3>2. 2 * PVotes(p) > Base /\ 2 * VVotes(p) > Base
      BY <3>1 DEF PCarries, VCarries, PCount
    <3>3. PVotes(p) + VVotes(p) > Cardinality(Counted)
      BY <3>2, Sizes, VoteSizes
    <3>4. PICK e \in Counted : ballot[e].p = p /\ ballot[e].v = p
      BY <3>3, Pigeonhole
    <3>5. e \in Electors /\ ballot[e] # NoBallot
      BY <3>4 DEF Counted, Appointed, Pledged
    <3> QED
      BY <3>4, <3>5 DEF InvCC, TwoNamesOnBallots
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3 DEF CountCanClose

THEOREM CountCanCloseAlways ==
  ASSUME Mut # "M_SAME_NAME", Mut # "M_PRE_XII", Mut # "M_PLURALITY"
  PROVE  Spec => []CountCanClose
<1>1. InvCC /\ [Next]_vars => InvCC'
  BY NextInvCC
<1>2. InvCC => CountCanClose
  BY ClosesUnderInv
<1> QED
  BY InitInvCC, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* ChoiceFromTheList [Mut # "M_OFF_LIST"]                                   *)

LEMMA NextChoiceFromTheList ==
  ASSUME Mut # "M_OFF_LIST", ChoiceFromTheList, [Next]_vars
  PROVE  ChoiceFromTheList'
<1>1. ASSUME NEW c \in Candidates, NEW Q \in SUBSET States, NEW Y \in SUBSET Q, HouseChooses(c, Q, Y)
      PROVE  ChoiceFromTheList'
  BY <1>1 DEF HouseChooses, OnList, ChoiceFromTheList
<1>2. ASSUME NEW c \in Candidates, NEW Q \in SUBSET Senators, NEW Y \in SUBSET Q, SenateChooses(c, Q, Y)
      PROVE  ChoiceFromTheList'
  BY <1>2 DEF SenateChooses, OnList, ChoiceFromTheList
<1>3. CASE UNCHANGED offList
  BY <1>3 DEF ChoiceFromTheList
<1> QED
  BY <1>1, <1>2, <1>3, FlagFrame

THEOREM ChoiceFromTheListAlways ==
  ASSUME Mut # "M_OFF_LIST"
  PROVE  Spec => []ChoiceFromTheList
<1>1. ChoiceFromTheList /\ [Next]_vars => ChoiceFromTheList'
  BY NextChoiceFromTheList
<1>2. Init => ChoiceFromTheList
  BY DEF Init, ChoiceFromTheList
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* HouseVote [Mut # "M_HOUSE_QUORUM", Mut # "M_HOUSE_PRESENT"]              *)

LEMMA NextHouseVote ==
  ASSUME Mut # "M_HOUSE_QUORUM", Mut # "M_HOUSE_PRESENT", HouseVote, [Next]_vars
  PROVE  HouseVote'
<1>1. ASSUME NEW c \in Candidates, NEW Q \in SUBSET States, NEW Y \in SUBSET Q, HouseChooses(c, Q, Y)
      PROVE  HouseVote'
  BY <1>1 DEF HouseChooses, HouseQuorum, HouseCarries, HouseVote
<1>2. CASE UNCHANGED houseShort
  BY <1>2 DEF HouseVote
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM HouseVoteAlways ==
  ASSUME Mut # "M_HOUSE_QUORUM", Mut # "M_HOUSE_PRESENT"
  PROVE  Spec => []HouseVote
<1>1. HouseVote /\ [Next]_vars => HouseVote'
  BY NextHouseVote
<1>2. Init => HouseVote
  BY DEF Init, HouseVote
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* SenateVote [Mut # "M_SENATE_QUORUM", Mut # "M_SENATE_PRESENT"]           *)

LEMMA NextSenateVote ==
  ASSUME Mut # "M_SENATE_QUORUM", Mut # "M_SENATE_PRESENT", SenateVote, [Next]_vars
  PROVE  SenateVote'
<1>1. ASSUME NEW c \in Candidates, NEW Q \in SUBSET Senators, NEW Y \in SUBSET Q, SenateChooses(c, Q, Y)
      PROVE  SenateVote'
  BY <1>1 DEF SenateChooses, SenateQuorum, SenateCarries, SenateVote
<1>2. CASE UNCHANGED senateShort
  BY <1>2 DEF SenateVote
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM SenateVoteAlways ==
  ASSUME Mut # "M_SENATE_QUORUM", Mut # "M_SENATE_PRESENT"
  PROVE  Spec => []SenateVote
<1>1. SenateVote /\ [Next]_vars => SenateVote'
  BY NextSenateVote
<1>2. Init => SenateVote
  BY DEF Init, SenateVote
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* PresidentNotVP [Mut # "M_ONE_PERSON"]                                    *)

LEMMA InitInvPNV == Init => InvPNV
BY InitTypeOK DEF Init, InvPNV, PresidentNotVP

LEMMA NextInvPNV ==
  ASSUME Mut # "M_ONE_PERSON", InvPNV, [Next]_vars
  PROVE  InvPNV'
<1> USE NoOneWF, PersonsWF DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ PresidentNotVP
  BY NextTypeOK DEF InvPNV
<1> SUFFICES PresidentNotVP'
  BY <1>0 DEF InvPNV
<1>1. ASSUME NEW p \in Choice, NEW v \in Choice, Announce(p, v) PROVE PresidentNotVP'
  BY <1>0, <1>1 DEF Announce, TwoPersons, PresidentNotVP
<1>2. ASSUME NEW c \in Candidates, NEW Q \in SUBSET States, NEW Y \in SUBSET Q, HouseChooses(c, Q, Y)
      PROVE  PresidentNotVP'
  BY <1>0, <1>2 DEF HouseChooses, TwoPersons, PresidentNotVP
<1>3. ASSUME NEW c \in Candidates, NEW Q \in SUBSET Senators, NEW Y \in SUBSET Q, SenateChooses(c, Q, Y)
      PROVE  PresidentNotVP'
  BY <1>0, <1>3 DEF SenateChooses, TwoPersons, PresidentNotVP
<1>4. CASE OpenElection
  BY <1>0, <1>4 DEF OpenElection, PresidentNotVP
<1>5. CASE NoonSteps
  <2>1. CASE NoonInaugurates
    <3>1. /\ pElect # NoOne /\ president' = pElect /\ vicePresident' \in {vElect, NoOne}
          /\ UNCHANGED electVars
      BY <2>1 DEF NoonInaugurates, Qualified, VQualified, VPSeat
    <3> QED
      BY <1>0, <3>1 DEF PresidentNotVP
  <2>2. CASE NoonSucceeds
    BY <1>0, <2>2 DEF NoonSucceeds, PresidentNotVP
  <2>3. CASE NoonVacant
    BY <1>0, <2>3 DEF NoonVacant, PresidentNotVP
  <2>4. CASE Qualify
    BY <1>0, <2>4 DEF Qualify, TwoPersons, PresidentNotVP
  <2>5. CASE VPQualify
    BY <1>0, <2>5 DEF VPQualify, TwoPersons, PresidentNotVP
  <2>6. CASE VPActs
    BY <1>0, <2>6 DEF VPActs, PresidentNotVP
  <2>7. CASE SuccessorActs
    BY <1>0, <2>7 DEF SuccessorActs, PresidentNotVP
  <2> QED
    BY <1>5, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF NoonSteps
<1>6. ASSUME NEW x \in Persons, Die(x) PROVE PresidentNotVP'
  <2>1. /\ president' = IF x = president THEN vicePresident ELSE president
        /\ vicePresident' = IF x \in {president, vicePresident} THEN NoOne ELSE vicePresident
        /\ UNCHANGED electVars
    BY <1>6 DEF Die
  <2> QED
    BY <1>0, <2>1 DEF PresidentNotVP
<1>7. CASE UNCHANGED <<electVars, officeVars>>
  BY <1>0, <1>7 DEF PresidentNotVP
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, ElectOfficeFrame

THEOREM PresidentNotVPAlways ==
  ASSUME Mut # "M_ONE_PERSON"
  PROVE  Spec => []PresidentNotVP
<1>1. InvPNV /\ [Next]_vars => InvPNV'
  BY NextInvPNV
<1>2. InvPNV => PresidentNotVP
  BY DEF InvPNV
<1> QED
  BY InitInvPNV, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Qualifications [Mut # "M_UNQUALIFIED"]                                   *)

LEMMA InitInvQ == Init => InvQ
BY InitTypeOK DEF Init, InvQ, Qualifications, InOffice

LEMMA NextInvQ ==
  ASSUME Mut # "M_UNQUALIFIED", InvQ, [Next]_vars
  PROVE  InvQ'
<1> USE NoOneWF, PersonsWF DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ Qualifications
  BY NextTypeOK DEF InvQ
<1> SUFFICES Qualifications'
  BY <1>0 DEF InvQ
<1>a. (VQualified(pElect) => pElect \in Eligible) /\ (VQualified(vElect) => vElect \in Eligible)
  BY DEF VQualified, MeetsArticleII
<1>1. CASE NoonSteps
  <2>1. CASE NoonInaugurates
    BY <1>0, <1>a, <2>1 DEF NoonInaugurates, Qualified, VPSeat, Qualifications, InOffice
  <2>2. CASE NoonSucceeds
    BY <1>0, <1>a, <2>2 DEF NoonSucceeds, Qualifications, InOffice
  <2>3. CASE NoonVacant
    BY <1>0, <1>a, <2>3 DEF NoonVacant, VPSeat, Qualifications, InOffice
  <2>4. CASE Qualify
    BY <1>0, <1>a, <2>4 DEF Qualify, Qualified, Qualifications, InOffice
  <2>5. CASE VPQualify
    BY <1>0, <1>a, <2>5 DEF VPQualify, Qualifications, InOffice
  <2>6. CASE VPActs
    BY <1>0, <2>6 DEF VPActs, Qualifications, InOffice
  <2>7. CASE SuccessorActs
    BY <1>0, <2>7, SuccessorWF DEF SuccessorActs, Qualifications, InOffice
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF NoonSteps
<1>2. ASSUME NEW x \in Persons, Die(x) PROVE Qualifications'
  <2>1. /\ president' = IF x = president THEN vicePresident ELSE president
        /\ vicePresident' = IF x \in {president, vicePresident} THEN NoOne ELSE vicePresident
        /\ acting' = IF x = acting THEN NoOne ELSE acting
    BY <1>2 DEF Die
  <2> QED
    BY <1>0, <2>1 DEF Qualifications, InOffice
<1>3. CASE UNCHANGED officeVars
  BY <1>0, <1>3 DEF Qualifications, InOffice
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, OfficeFrame

THEOREM QualificationsAlways ==
  ASSUME Mut # "M_UNQUALIFIED"
  PROVE  Spec => []Qualifications
<1>1. InvQ /\ [Next]_vars => InvQ'
  BY NextInvQ
<1>2. InvQ => Qualifications
  BY DEF InvQ
<1> QED
  BY InitInvQ, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Disability [Mut # "M_XIV3"]                                              *)

LEMMA InitInvD == Init => InvD
BY InitTypeOK DEF Init, InvD, Disability, InOffice

LEMMA NextInvD ==
  ASSUME Mut # "M_XIV3", InvD, [Next]_vars
  PROVE  InvD'
<1> USE NoOneWF, PersonsWF DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ Disability /\ relieved \subseteq relieved'
  BY NextTypeOK, RelievedGrows DEF InvD
<1> SUFFICES Disability'
  BY <1>0 DEF InvD
<1>a. /\ (VQualified(pElect) => pElect \notin Disabled \/ pElect \in relieved)
      /\ (VQualified(vElect) => vElect \notin Disabled \/ vElect \in relieved)
  BY DEF VQualified, NotDisabled
<1>1. CASE NoonSteps
  <2>1. CASE NoonInaugurates
    BY <1>0, <1>a, <2>1 DEF NoonInaugurates, Qualified, VPSeat, Disability, InOffice
  <2>2. CASE NoonSucceeds
    BY <1>0, <1>a, <2>2 DEF NoonSucceeds, Disability, InOffice
  <2>3. CASE NoonVacant
    BY <1>0, <1>a, <2>3 DEF NoonVacant, VPSeat, Disability, InOffice
  <2>4. CASE Qualify
    BY <1>0, <1>a, <2>4 DEF Qualify, Qualified, Disability, InOffice
  <2>5. CASE VPQualify
    BY <1>0, <1>a, <2>5 DEF VPQualify, Disability, InOffice
  <2>6. CASE VPActs
    BY <1>0, <2>6 DEF VPActs, Disability, InOffice
  <2>7. CASE SuccessorActs
    BY <1>0, <2>7, SuccessorWF DEF SuccessorActs, Disability, InOffice
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF NoonSteps
<1>2. ASSUME NEW x \in Persons, Die(x) PROVE Disability'
  <2>1. /\ president' = IF x = president THEN vicePresident ELSE president
        /\ vicePresident' = IF x \in {president, vicePresident} THEN NoOne ELSE vicePresident
        /\ acting' = IF x = acting THEN NoOne ELSE acting
        /\ UNCHANGED relieved
    BY <1>2 DEF Die
  <2> QED
    BY <1>0, <2>1 DEF Disability, InOffice
<1>3. CASE UNCHANGED officeVars
  BY <1>0, <1>3 DEF Disability, InOffice
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, OfficeFrame

THEOREM DisabilityAlways ==
  ASSUME Mut # "M_XIV3"
  PROVE  Spec => []Disability
<1>1. InvD /\ [Next]_vars => InvD'
  BY NextInvD
<1>2. InvD => Disability
  BY DEF InvD
<1> QED
  BY InitInvD, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* TwoTermLimit [Mut # "M_XXII", Mut # "M_XXII_SERVICE"]                    *)

LEMMA NextTwoTermLimit ==
  ASSUME Mut # "M_XXII", Mut # "M_XXII_SERVICE", TwoTermLimit, [Next]_vars
  PROVE  TwoTermLimit'
<1>0. \A x : TermAllowed(x) = WithinXXII(x)
  BY DEF TermAllowed
<1>1. CASE NoonInaugurates
  BY <1>0, <1>1 DEF NoonInaugurates, Qualified, TwoTermLimit
<1>2. CASE Qualify
  BY <1>0, <1>2 DEF Qualify, Qualified, TwoTermLimit
<1>3. CASE UNCHANGED thirdTerm
  BY <1>3 DEF TwoTermLimit
<1> QED
  BY <1>1, <1>2, <1>3, FlagFrame

THEOREM TwoTermLimitAlways ==
  ASSUME Mut # "M_XXII", Mut # "M_XXII_SERVICE"
  PROVE  Spec => []TwoTermLimit
<1>1. TwoTermLimit /\ [Next]_vars => TwoTermLimit'
  BY NextTwoTermLimit
<1>2. Init => TwoTermLimit
  BY DEF Init, TwoTermLimit
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* VPElectBecomesOnlyOnDeath [Mut # "M_XX3_BECOMES"]                        *)

LEMMA NextVPElectBecomesOnlyOnDeath ==
  ASSUME Mut # "M_XX3_BECOMES", VPElectBecomesOnlyOnDeath, [Next]_vars
  PROVE  VPElectBecomesOnlyOnDeath'
<1>1. CASE NoonSucceeds
  BY <1>1 DEF NoonSucceeds, ElectGone, VPElectBecomesOnlyOnDeath
<1>2. CASE UNCHANGED becameWithoutDeath
  BY <1>2 DEF VPElectBecomesOnlyOnDeath
<1> QED
  BY <1>1, <1>2, FlagFrame

THEOREM VPElectBecomesOnlyOnDeathAlways ==
  ASSUME Mut # "M_XX3_BECOMES"
  PROVE  Spec => []VPElectBecomesOnlyOnDeath
<1>1. VPElectBecomesOnlyOnDeath /\ [Next]_vars => VPElectBecomesOnlyOnDeath'
  BY NextVPElectBecomesOnlyOnDeath
<1>2. Init => VPElectBecomesOnlyOnDeath
  BY DEF Init, VPElectBecomesOnlyOnDeath
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* ActingOrder [Mut # "M_SPEAKER_FIRST"]                                    *)

LEMMA InitInvAO == Init => InvAO
BY InitTypeOK DEF Init, InvAO, ActingOrder

LEMMA NextInvAO ==
  ASSUME Mut # "M_SPEAKER_FIRST", InvAO, [Next]_vars
  PROVE  InvAO'
<1> USE NoOneWF, PersonsWF DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>0. TypeOK /\ TypeOK' /\ ActingOrder
  BY NextTypeOK DEF InvAO
<1> SUFFICES ActingOrder'
  BY <1>0 DEF InvAO
<1>1. CASE NoonSteps
  <2>1. CASE NoonInaugurates \/ NoonSucceeds \/ NoonVacant \/ Qualify \/ VPQualify
    BY <2>1 DEF NoonInaugurates, NoonSucceeds, NoonVacant, Qualify, VPQualify, ActingOrder
  <2>2. CASE VPActs
    BY <2>2 DEF VPActs, ActingOrder
  <2>3. CASE SuccessorActs
    BY <2>3 DEF SuccessorActs, NoVP, ActingOrder
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3 DEF NoonSteps
<1>2. ASSUME NEW x \in Persons, Die(x) PROVE ActingOrder'
  <2>1. /\ president' = IF x = president THEN vicePresident ELSE president
        /\ vicePresident' = IF x \in {president, vicePresident} THEN NoOne ELSE vicePresident
        /\ acting' = IF x = acting THEN NoOne ELSE acting
        /\ x # Successor /\ x # NoOne
    BY <1>2, SuccessorWF DEF Die
  <2> QED
    BY <1>0, <2>1 DEF ActingOrder
<1>3. CASE UNCHANGED officeVars
  BY <1>0, <1>3 DEF ActingOrder
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, OfficeFrame

THEOREM ActingOrderAlways ==
  ASSUME Mut # "M_SPEAKER_FIRST"
  PROVE  Spec => []ActingOrder
<1>1. InvAO /\ [Next]_vars => InvAO'
  BY NextInvAO
<1>2. InvAO => ActingOrder
  BY DEF InvAO
<1> QED
  BY InitInvAO, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Safety, unmutated                                                        *)

THEOREM SafeAlways ==
  ASSUME Mut = "none"
  PROVE  Spec => []Safety
<1>1. Spec => []ElectorsHoldNoOffice
  BY ElectorsHoldNoOfficeAlways
<1>2. Spec => []AppointedOnElectionDay
  BY AppointedOnElectionDayAlways
<1>3. Spec => []SameDay
  BY SameDayAlways
<1>4. Spec => []OneNotAnInhabitant
  BY OneNotAnInhabitantAlways
<1>5. Spec => []PledgesBind
  BY PledgesBindAlways
<1>6. Spec => []NewCongressCounts
  BY NewCongressCountsAlways
<1>7. Spec => []CountIsCongress
  BY CountIsCongressAlways
<1>8. Spec => []ElectorsChoose
  BY ElectorsChooseAlways
<1>9. Spec => []DevolvesOnlyWithoutMajority
  BY DevolvesOnlyWithoutMajorityAlways
<1>10. Spec => []CountCanClose
  BY CountCanCloseAlways
<1>11. Spec => []ChoiceFromTheList
  BY ChoiceFromTheListAlways
<1>12. Spec => []HouseVote
  BY HouseVoteAlways
<1>13. Spec => []SenateVote
  BY SenateVoteAlways
<1>14. Spec => []PresidentNotVP
  BY PresidentNotVPAlways
<1>15. Spec => []Qualifications
  BY QualificationsAlways
<1>16. Spec => []Disability
  BY DisabilityAlways
<1>17. Spec => []TwoTermLimit
  BY TwoTermLimitAlways
<1>18. Spec => []VPElectBecomesOnlyOnDeath
  BY VPElectBecomesOnlyOnDeathAlways
<1>19. Spec => []ActingOrder
  BY ActingOrderAlways
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13,
     <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, PTL
  DEF Safety

-----------------------------------------------------------------------------
(* Liveness: ExecutiveIsFilled [Mut # "M_NO_STATUTE"], under FairSpec. A      *)
(* leads-to with no quantifier, so one WF1 step: while the office is vacant  *)
(* the Vice President or the statute's officer can act, acting changes the  *)
(* state, and no step re-enters the founding.                               *)


\* The founding is left once and never re-entered.
LEMMA ClockLeavesFounding ==
  ASSUME clock # "Founding", [Next]_vars
  PROVE  clock' # "Founding"
<1> USE DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. CASE CollegeSteps
  BY <1>2 DEF CollegeSteps, Appoint, ElectionDayEnds, Vote, ElectorsAdjourn
<1>3. CASE CountSteps
  BY <1>3 DEF CountSteps, OpenCount, Sustain, Announce, HouseChooses, SenateChooses
<1>4. CASE NoonSteps
  BY <1>4 DEF NoonSteps, NoonInaugurates, NoonSucceeds, NoonVacant, Qualify, VPQualify,
                VPActs, SuccessorActs
<1>5. CASE TermSteps
  BY <1>5 DEF TermSteps, Die, RemoveDisability, Midterm, OpenElection
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

\* While the office is vacant, the Vice President or the statute's officer
\* can act, and acting changes the state.
LEMMA SomeoneCanAct ==
  ASSUME Mut # "M_NO_STATUTE", clock # "Founding", Vacant
  PROVE  ENABLED <<VPActs \/ SuccessorActs>>_vars
<1> USE NoOneWF, PersonsWF, SuccessorWF DEF timeVars, collegeVars, electVars, officeVars, personVars, flagVars
<1>1. Successor # NoOne /\ Statute
  BY DEF Statute
<1>2. CASE vicePresident # NoOne
  BY <1>1, <1>2, ExpandENABLED DEF VPActs, SuccessorActs, vars, Vacant
<1>3. CASE vicePresident = NoOne
  BY <1>1, <1>3, ExpandENABLED DEF VPActs, SuccessorActs, NoVP, vars, Vacant
<1> QED
  BY <1>2, <1>3

LEMMA ActingFills ==
  ASSUME <<VPActs \/ SuccessorActs>>_vars
  PROVE  ~Vacant'
BY NoOneWF, PersonsWF, SuccessorWF DEF VPActs, SuccessorActs, Vacant

THEOREM ExecutiveIsFilledAlways ==
  ASSUME Mut # "M_NO_STATUTE"
  PROVE  FairSpec => ExecutiveIsFilled
<1> DEFINE P == clock # "Founding" /\ Vacant
           Q == ~Vacant
<1>1. P /\ [Next]_vars => P' \/ Q'
  BY ClockLeavesFounding
<1>2. P /\ <<Next /\ (VPActs \/ SuccessorActs)>>_vars => Q'
  BY ActingFills
<1>3. P => ENABLED <<VPActs \/ SuccessorActs>>_vars
  BY SomeoneCanAct
<1> QED
  BY <1>1, <1>2, <1>3, PTL DEF FairSpec, Spec, SomeoneActs, ExecutiveIsFilled
========================================================================

-----------------------------------------------------------------------------
(* Why each mutation must fail: what it admits, in the module's terms. The  *)
(* counterexamples are TLC's (results/Elections-results-*.txt).             *)

\* An officer of the United States may be appointed an elector.
LEMMA MutOfficerElectorAdmits ==
  ASSUME Mut = "M_OFFICER_ELECTOR", NEW e \in Officers
  PROVE  MayBeElector(e)
BY DEF MayBeElector

\* A State may appoint after election day.
LEMMA MutFailedChoiceAdmits ==
  ASSUME Mut = "M_FAILED_CHOICE", stage = "Voting"
  PROVE  AppointmentOpen
BY DEF AppointmentOpen

\* An elector may vote after the electors' day.
LEMMA MutLateVoteAdmits ==
  ASSUME Mut = "M_LATE_VOTE", stage = "Voted"
  PROVE  PollsOpen
BY DEF PollsOpen

\* An elector may name two inhabitants of the elector's own State.
LEMMA MutHabitationAdmits ==
  ASSUME Mut = "M_HABITATION", NEW e, NEW p, NEW v
  PROVE  Habitation(e, p, v)
BY DEF Habitation

\* A ballot may name one person for both offices.
LEMMA MutSameNameAdmits ==
  ASSUME Mut = "M_SAME_NAME", NEW p
  PROVE  TwoNames(p, p)
BY DEF TwoNames

\* A bound elector may depart from the pledge.
LEMMA MutFaithlessAdmits ==
  ASSUME Mut = "M_FAITHLESS", NEW e \in Binding, NEW p, p # pledge[e]
  PROVE  Faithful(e, p)
BY DEF Faithful

\* The outgoing Congress may open the count.
LEMMA MutPreXXAdmits ==
  ASSUME Mut = "M_PRE_XX"
  PROVE  Seated(FALSE)
BY DEF Seated

\* A vote may be rejected without both Houses.
LEMMA MutPresidingAdmits ==
  ASSUME Mut = "M_PRESIDING"
  PROVE  Concur(FALSE)
BY DEF Concur

\* Both names on a ballot stand on the list for President.
LEMMA MutPreXIIAdmits ==
  ASSUME Mut = "M_PRE_XII", NEW c
  PROVE  PCount(c) = Cardinality(PFor(c) \cup VFor(c))
BY DEF PCount

\* A plurality carries, majority or not.
LEMMA MutPluralityAdmits ==
  ASSUME Mut = "M_PLURALITY", NEW c \in Candidates, PVotes(c) > 0,
         \A d \in Candidates \ {c} : PVotes(c) > PVotes(d)
  PROVE  PCarries(c)
BY DEF PCarries, PCount

\* The majority is of every seat, filled or not.
LEMMA MutEntitledAdmits ==
  ASSUME Mut = "M_ENTITLED"
  PROVE  Base = Cardinality(Electors)
BY DEF Base

\* A House may choose someone not on its list.
LEMMA MutOffListAdmits ==
  ASSUME Mut = "M_OFF_LIST", NEW c
  PROVE  OnList(c, {})
BY DEF OnList

\* The House may choose with no State present.
LEMMA MutHouseQuorumAdmits ==
  ASSUME Mut = "M_HOUSE_QUORUM"
  PROVE  HouseQuorum({})
BY DEF HouseQuorum

\* A majority of the States present carries.
LEMMA MutHousePresentAdmits ==
  ASSUME Mut = "M_HOUSE_PRESENT", NEW Q, NEW Y, 2 * Cardinality(Y) > Cardinality(Q)
  PROVE  HouseCarries(Q, Y)
BY DEF HouseCarries

\* The Senate may choose with no Senator present.
LEMMA MutSenateQuorumAdmits ==
  ASSUME Mut = "M_SENATE_QUORUM"
  PROVE  SenateQuorum({})
BY DEF SenateQuorum

\* A majority of the Senators present carries.
LEMMA MutSenatePresentAdmits ==
  ASSUME Mut = "M_SENATE_PRESENT", NEW Q, NEW Y, 2 * Cardinality(Y) > Cardinality(Q)
  PROVE  SenateCarries(Q, Y)
BY DEF SenateCarries

\* One person may be announced, chosen or seated for both offices.
LEMMA MutOnePersonAdmits ==
  ASSUME Mut = "M_ONE_PERSON", NEW p
  PROVE  TwoPersons(p, p)
BY DEF TwoPersons

\* A person not eligible to the office passes Art. II s.1 cl.5.
LEMMA MutUnqualifiedAdmits ==
  ASSUME Mut = "M_UNQUALIFIED", NEW x, x \notin Eligible
  PROVE  MeetsArticleII(x)
BY DEF MeetsArticleII

\* A person under the disability passes Amend. XIV s.3.
LEMMA MutXIV3Admits ==
  ASSUME Mut = "M_XIV3", NEW x \in Disabled, x \notin relieved
  PROVE  NotDisabled(x)
BY DEF NotDisabled

\* A person twice elected may take office as elected again.
LEMMA MutXXIIAdmits ==
  ASSUME Mut = "M_XXII", NEW x, elected[x] = 2
  PROVE  TermAllowed(x)
BY DEF TermAllowed

\* A person who served more than two years of another's term, and was then
\* elected once, may be elected again.
LEMMA MutXXIIServiceAdmits ==
  ASSUME Mut = "M_XXII_SERVICE", NEW x \in servedLong, elected[x] = 1
  PROVE  TermAllowed(x) /\ ~WithinXXII(x)
BY DEF TermAllowed, WithinXXII

\* The Vice President elect may become President though the President elect
\* lives.
LEMMA MutXX3BecomesAdmits ==
  ASSUME Mut = "M_XX3_BECOMES", pElect \notin dead
  PROVE  ElectGone
BY DEF ElectGone

\* The statutory successor may act beside a Vice President.
LEMMA MutSpeakerFirstAdmits ==
  ASSUME Mut = "M_SPEAKER_FIRST", vicePresident # NoOne
  PROVE  NoVP
BY DEF NoVP

\* No statute: the successor never acts (ExecutiveIsFilled is what breaks).
LEMMA MutNoStatuteAdmits ==
  ASSUME Mut = "M_NO_STATUTE"
  PROVE  ~Statute
BY DEF Statute

=============================================================================
