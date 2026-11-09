--------------------------- MODULE Judiciary_proof ---------------------------
(***************************************************************************)
(* TLAPS proofs of the invariants Judiciary.tla states, as Spec => []P,    *)
(* for every value of the constants its named assumptions admit. The base *)
(* module is extended, never edited; the proof results file names it by    *)
(* digest. Check with                                                      *)
(*   tools/tlapm --cleanfp --strict --cache-dir /tmp/x Judiciary_proof.tla *)
(* or scripts/proof_results.py Judiciary (which writes the results file).  *)
(*                                                                         *)
(* THEOREMS, each with its hypothesis: exactly the mutations whose rows    *)
(* in results/Judiciary-results-*.txt read COUNTEREXAMPLE for it.          *)
(*   ShapeAlways, TypeOKAlways          [every mutation]                   *)
(*   OneSupremeCourtAlways      [Mut # M_ABOLISH_SC, M_COURT_OF_UNION,     *)
(*                               M_REESTABLISH]                            *)
(*   CourtsAreEstablishedAlways [every mutation]                           *)
(*   BenchFitsSeatsAlways       [Mut # M_REESTABLISH, M_SHRINK,            *)
(*                               M_VACANCY_RECHECK, M_CHIEF_RECHECK]       *)
(*   NoJudgeOnTwoCourtsAlways   [Mut # M_CONFIRM_RECHECK, M_CHIEF_RECHECK] *)
(*   JudgesAreNotInCongressAlways [Mut # M_INCOMPAT]                       *)
(*   DisqualifiedDoNotSitAlways [Mut # M_DISQUAL]                          *)
(*   ChiefJusticeSitsAlways     [Mut # M_ABOLISH_SC, M_REESTABLISH,        *)
(*                               M_TENURE]                                 *)
(*   CompensationClauseAlways   [Mut # M_PAYCUT]                           *)
(*   GoodBehaviourAlways        [Mut # M_TENURE, M_NOIMPEACH, M_CHASE]     *)
(*   OriginalJurisdictionAlways [Mut # M_MARBURY]                          *)
(*   EleventhAmendmentAlways    [Mut # M_CHISHOLM]                         *)
(*   AppealsCourtsAreAppellateAlways [Mut # M_CIRCUIT]                     *)
(*   PublicRightsOnlyAlways     [Mut # M_NORTHERN_PIPELINE]                *)
(*   JuryAndVenueAlways         [Mut # M_NOJURY, M_VENUE]                  *)
(*   TreasonProofAlways         [Mut # M_TREASON]                          *)
(*   NoDoubleJeopardyAlways     [Mut # M_KEPNER]                           *)
(*   ExceptionsHonouredAlways   [Mut # M_EXCEPTIONS]                       *)
(*   ExceptionsBindPendingAlways [Mut # M_MCCARDLE]                        *)
(*   SafeAlways                 [Mut = "none"]: Spec => []Safety           *)
(* and one lemma per mutation saying what it admits (MutAbolishSC...).     *)
(*                                                                         *)
(* THE INDUCTIVE STRENGTHENING, in prose.                                  *)
(*   Shape (every mutation): TypeOK, split into JudgeTypes and CaseTypes   *)
(*   so that a judge-side step never expands the case record set, and a    *)
(*   filed case sits in a court, so Decide records a venue that is a State *)
(*   or "None".                                                            *)
(*   OneSupremeCourt, CourtsAreEstablished, NoJudgeOnTwoCourts, the case   *)
(*   properties and the four flags are inductive with Shape alone: the     *)
(*   one step that could break each is refused by its guard (the flags,    *)
(*   and the case records written once at File or Decide).                 *)
(*   BenchFitsSeats: a court that does not exist has no judge, no nominee  *)
(*   and no seats (EmptyWhenAbsent). Establish then starts from an empty   *)
(*   bench, and a confirmation always lands on a court that exists. The    *)
(*   counting uses only that a bench is a subset of the finite set Persons *)
(*   (PersonsFinite): adding one judge adds at most one, removing one      *)
(*   removes at most one.                                                  *)
(*   JudgesAreNotInCongress, DisqualifiedDoNotSit: every pending nominee   *)
(*   (to any court, and for Chief Justice) passed the test at nomination,  *)
(*   and conviction withdraws the convicted person's nominations. So these *)
(*   two rest on the test in Eligible, not on the re-check at              *)
(*   confirmation: M_CONFIRM_RECHECK and M_CHIEF_RECHECK break neither.    *)
(*   ChiefJusticeSits: the Supreme Court exists and keeps its tier, so no  *)
(*   fixed term reaches it and it is never abolished.                      *)
(*                                                                         *)
(* NOT PROVED, and why.                                                    *)
(*   The witnesses (Never...) and the mutations' counterexamples: they are *)
(*   reachability claims, which the prover cannot make; they stay with     *)
(*   TLC. Nothing about liveness: the module claims none. Nothing about    *)
(*   constants the assumptions exclude (a Supreme Court outside CourtIds,  *)
(*   NoOne a person, infinitely many persons). Nothing about law: the      *)
(*   module is an abstraction of the text, and "proved" is a claim about   *)
(*   the module under its assumptions and this prover.                     *)
(***************************************************************************)

EXTENDS Judiciary, TLAPS, FiniteSetTheorems

(* The base module's named assumptions are the only ones used:             *)
(* SupremeCourtWF, NoOneWF and PersonsFinite. Nothing is assumed of        *)
(* MaxSeats, MaxSalary, House, Senate, States, CourtIds, Cases or Kinds.   *)
-----------------------------------------------------------------------------
(* Definitions: the shape every mutation keeps, and the strengthenings.     *)

\* A filed case sits in a court: Decide reads location[case[x].court].
FiledInCourt ==
  \A y \in Cases : case[y].status # "Unfiled" => case[y].court \in CourtIds

\* TypeOK, split so that a step about judges never expands the case
\* record set and a step about cases never expands the judges' types.
JudgeTypes ==
  /\ courts \subseteq CourtIds
  /\ tier \in [CourtIds -> Tiers]
  /\ location \in [CourtIds -> States \cup {"None"}]
  /\ seats \in [CourtIds -> Nat]
  /\ salary \in [CourtIds -> Nat]
  /\ exceptions \subseteq Kinds
  /\ bench \in [CourtIds -> SUBSET Persons]
  /\ nominee \in [CourtIds -> Seat]
  /\ chiefJustice \in Seat
  /\ chiefNominee \in Seat
  /\ impeached \subseteq Persons
  /\ disqualified \subseteq Persons
  /\ unseated \subseteq Persons
  /\ payCut \in BOOLEAN
  /\ offBenchOtherwise \in BOOLEAN
  /\ exceptedTaken \in BOOLEAN
  /\ exceptedDecided \in BOOLEAN

CaseTypes == case \in [Cases -> CaseRecord]

Shape == JudgeTypes /\ CaseTypes /\ FiledInCourt

\* A court that does not exist has no judge, no nominee and no seat.
EmptyWhenAbsent ==
  \A d \in CourtIds : d \notin courts =>
     /\ bench[d] = {}
     /\ nominee[d] = NoOne
     /\ seats[d] = 0

\* Every pending nominee passed the test at nomination.
NomineesNotInCongress ==
  /\ \A d \in CourtIds : nominee[d] # NoOne => nominee[d] \notin Congress
  /\ chiefNominee # NoOne => chiefNominee \notin Congress

NomineesNotDisqualified ==
  /\ \A d \in CourtIds : nominee[d] # NoOne => nominee[d] \notin disqualified
  /\ chiefNominee # NoOne => chiefNominee \notin disqualified

InvOne      == Shape /\ OneSupremeCourt
InvEstab    == Shape /\ CourtsAreEstablished
InvSeats    == Shape /\ BenchFitsSeats /\ EmptyWhenAbsent
InvTwo      == Shape /\ NoJudgeOnTwoCourts
InvCongress == Shape /\ JudgesAreNotInCongress /\ NomineesNotInCongress
InvDisq     == Shape /\ DisqualifiedDoNotSit /\ NomineesNotDisqualified
InvChief    == Shape /\ ChiefJusticeSits /\ SupremeCourt \in courts
                     /\ tier[SupremeCourt] = "Supreme"
InvPay      == Shape /\ CompensationClause
InvTenure   == Shape /\ GoodBehaviour
InvOrig     == Shape /\ OriginalJurisdiction
InvXI       == Shape /\ EleventhAmendment
InvAppell   == Shape /\ AppealsCourtsAreAppellate
InvPublic   == Shape /\ PublicRightsOnly
InvJury     == Shape /\ JuryAndVenue
InvTreason  == Shape /\ TreasonProof
InvJeopardy == Shape /\ NoDoubleJeopardy
InvExcept   == Shape /\ ExceptionsHonoured
InvPending  == Shape /\ ExceptionsBindPending

\* Next, split by who acts: Congress, the judges' appointment and removal,
\* and the cases.
CongressStep ==
  \/ \E c \in CourtIds, t \in Tiers, st \in States \cup {"None"}, h \in HouseVotes, s \in SenateVotes :
        EstablishCourt(c, t, st, h, s)
  \/ \E c \in CourtIds, h \in HouseVotes, s \in SenateVotes :
        AbolishCourt(c, h, s)
  \/ \E c \in CourtIds, n \in 1..MaxSeats, h \in HouseVotes, s \in SenateVotes :
        SetSeats(c, n, h, s)
  \/ \E c \in CourtIds, n \in 0..MaxSalary, h \in HouseVotes, s \in SenateVotes :
        SetSalary(c, n, h, s)
  \/ \E E \in SUBSET Kinds, h \in HouseVotes, s \in SenateVotes :
        SetExceptions(E, h, s)

JudgeStep ==
  \/ \E c \in CourtIds, p \in Persons :
        NominateJudge(c, p)
  \/ \E c \in CourtIds, n \in SenateVotes :
        ConfirmJudge(c, n)
  \/ \E c \in CourtIds :
        RejectJudge(c)
  \/ \E p \in Persons :
        NominateChief(p)
  \/ \E n \in SenateVotes :
        ConfirmChief(n)
  \/ RejectChief
  \/ \E c \in CourtIds, p \in Persons :
        Resign(c, p)
  \/ \E c \in CourtIds, p \in Persons :
        TermExpires(c, p)
  \/ \E p \in Persons, n \in HouseVotes :
        Impeach(p, n)
  \/ \E p \in Persons, n \in SenateVotes, dq \in BOOLEAN :
        Convict(p, n, dq)
  \/ \E p \in Persons :
        Acquit(p)

CaseStep ==
  \/ \E x \in Cases, k \in Kinds, c \in CourtIds, st \in States \cup {"None"} :
        File(x, k, c, st)
  \/ \E x \in Cases, j \in BOOLEAN, w \in 0..2, conf \in BOOLEAN, v \in Verdicts :
        Decide(x, j, w, conf, v)
  \/ \E x \in Cases, c \in CourtIds :
        Appeal(x, c)
  \/ \E x \in Cases, v \in Verdicts :
        AppellateDecide(x, v)
  \/ \E x \in Cases :
        Dismiss(x)
  \/ \E x \in Cases :
        Close(x)

-----------------------------------------------------------------------------
(* Finite sets: a bench is a subset of the finite set Persons.             *)

LEMMA BenchCard ==
    ASSUME NEW S \in SUBSET Persons
    PROVE  IsFiniteSet(S) /\ Cardinality(S) \in Nat
BY PersonsFinite, FS_Subset, FS_CardinalityType

LEMMA BenchCardAdd ==
    ASSUME NEW S \in SUBSET Persons, NEW q
    PROVE  Cardinality(S \cup {q}) <= Cardinality(S) + 1
<1>1. IsFiniteSet(S) /\ Cardinality(S) \in Nat
    BY BenchCard
<1> QED
    BY <1>1, FS_AddElement

LEMMA BenchCardRemove ==
    ASSUME NEW S \in SUBSET Persons, NEW q
    PROVE  Cardinality(S \ {q}) <= Cardinality(S)
<1>1. IsFiniteSet(S)
    BY BenchCard
<1> QED
    BY <1>1, FS_Subset

-----------------------------------------------------------------------------
(* Next by who acts, and what each kind of step leaves alone.              *)

LEMMA NextSplit == Next <=> CongressStep \/ JudgeStep \/ CaseStep
BY DEF Next, CongressStep, JudgeStep, CaseStep

LEMMA CaseStepFrame ==
    CaseStep => UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee,
                            chiefJustice, chiefNominee, impeached, disqualified, unseated,
                            payCut, offBenchOtherwise>>
<1>1. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee, chiefJustice, chiefNominee, impeached, disqualified, unseated, payCut, offBenchOtherwise>>
    BY <1>1 DEF File, courtVars, judgeVars, impVars, flagVars
<1>2. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee, chiefJustice, chiefNominee, impeached, disqualified, unseated, payCut, offBenchOtherwise>>
    BY <1>2 DEF Decide, courtVars, judgeVars, impVars, flagVars
<1>3. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee, chiefJustice, chiefNominee, impeached, disqualified, unseated, payCut, offBenchOtherwise>>
    BY <1>3 DEF Appeal, courtVars, judgeVars, impVars, flagVars
<1>4. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee, chiefJustice, chiefNominee, impeached, disqualified, unseated, payCut, offBenchOtherwise>>
    BY <1>4 DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars
<1>5. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee, chiefJustice, chiefNominee, impeached, disqualified, unseated, payCut, offBenchOtherwise>>
    BY <1>5 DEF Dismiss, courtVars, judgeVars, impVars, flagVars
<1>6. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  UNCHANGED <<courts, tier, location, seats, salary, exceptions, bench, nominee, chiefJustice, chiefNominee, impeached, disqualified, unseated, payCut, offBenchOtherwise>>
    BY <1>6 DEF Close, courtVars, judgeVars, impVars, flagVars
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF CaseStep

LEMMA NonCaseFrame ==
    CongressStep \/ JudgeStep => UNCHANGED <<case, exceptedTaken, exceptedDecided>>
<1>1. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>1 DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars
<1>2. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>2 DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars
<1>3. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>3 DEF SetSeats, courtVars, judgeVars, impVars, flagVars
<1>4. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>4 DEF SetSalary, courtVars, judgeVars, impVars, flagVars
<1>5. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>5 DEF SetExceptions, courtVars, judgeVars, impVars, flagVars
<1>6. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>6 DEF NominateJudge, courtVars, judgeVars, impVars, flagVars
<1>7. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>7 DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars
<1>8. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>8 DEF RejectJudge, courtVars, judgeVars, impVars, flagVars
<1>9. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>9 DEF NominateChief, courtVars, judgeVars, impVars, flagVars
<1>10. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>10 DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars
<1>11. CASE RejectChief
    BY <1>11 DEF RejectChief, courtVars, judgeVars, impVars, flagVars
<1>12. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>12 DEF Resign, courtVars, judgeVars, impVars, flagVars
<1>13. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>13 DEF TermExpires, courtVars, judgeVars, impVars, flagVars
<1>14. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>14 DEF Impeach, courtVars, judgeVars, impVars, flagVars
<1>15. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>15 DEF Convict, courtVars, judgeVars, impVars, flagVars
<1>16. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  UNCHANGED <<case, exceptedTaken, exceptedDecided>>
    BY <1>16 DEF Acquit, courtVars, judgeVars, impVars, flagVars
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF CongressStep, JudgeStep

-----------------------------------------------------------------------------
(* The shape, under every mutation.                                         *)

LEMMA InitShape == Init => Shape
BY SupremeCourtWF, NoOneWF DEF Init, Shape, JudgeTypes, CaseTypes, FiledInCourt, CaseRecord, NoCase,
   Seat, Tiers, Status, Verdicts

LEMMA NextShape == Shape /\ [Next]_vars => Shape'
<1> SUFFICES ASSUME Shape, [Next]_vars PROVE Shape'
    OBVIOUS
<1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>2. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  Shape'
    BY <1>2, SupremeCourtWF, NoOneWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers, InferiorTiers, EstablishableTiers
<1>3. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  Shape'
    BY <1>3, SupremeCourtWF, NoOneWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>4. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  Shape'
    BY <1>4, SupremeCourtWF, NoOneWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  Shape'
    <2>1. n \in Nat
        BY <1>5
    <2>2. payCut' \in BOOLEAN
        BY <1>5 DEF SetSalary
    <2> QED
        BY <1>5, <2>1, <2>2 DEF SetSalary, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes,
           CaseTypes, FiledInCourt
<1>6. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  Shape'
    BY <1>6, SupremeCourtWF, NoOneWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>7. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  Shape'
    BY <1>7, SupremeCourtWF, NoOneWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>8. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  Shape'
    BY <1>8, SupremeCourtWF, NoOneWF DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>9. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  Shape'
    BY <1>9, SupremeCourtWF, NoOneWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>10. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  Shape'
    BY <1>10, SupremeCourtWF, NoOneWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>11. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  Shape'
    BY <1>11, SupremeCourtWF, NoOneWF DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>12. CASE RejectChief
    BY <1>12, SupremeCourtWF, NoOneWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>13. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  Shape'
    BY <1>13, SupremeCourtWF, NoOneWF DEF Resign, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  Shape'
    BY <1>14, SupremeCourtWF, NoOneWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>15. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  Shape'
    BY <1>15, SupremeCourtWF, NoOneWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>16. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  Shape'
    BY <1>16, SupremeCourtWF, NoOneWF DEF Convict, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>17. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  Shape'
    BY <1>17, SupremeCourtWF, NoOneWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, Shape, JudgeTypes, CaseTypes, FiledInCourt, Seat, Tiers
<1>18. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  Shape'
    <2>1. /\ case[x] \in CaseRecord
          /\ case[x].status # "Unfiled" => case[x].court \in CourtIds
          /\ case \in [Cases -> CaseRecord]
          /\ location \in [CourtIds -> States \cup {"None"}]
          /\ tier \in [CourtIds -> Tiers]
        BY DEF Shape, JudgeTypes, CaseTypes, FiledInCourt
    <2>2. /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise>>
          /\ exceptedTaken' \in BOOLEAN /\ exceptedDecided' \in BOOLEAN
        BY <1>18, <2>1 DEF File, flagVars, Shape, JudgeTypes
    <2>3. case'[x] \in CaseRecord
        BY <1>18, <2>1, SupremeCourtWF DEF File, CaseRecord, Tiers, Status, Verdicts
    <2>4. case'[x].status # "Unfiled" => case'[x].court \in CourtIds
        BY <1>18, <2>1 DEF File
    <2>5. case' \in [Cases -> CaseRecord]
        BY <1>18, <2>1, <2>3 DEF File
    <2>6. FiledInCourt'
        BY <1>18, <2>1, <2>4 DEF File, Shape, FiledInCourt
    <2> QED
        BY <2>2, <2>5, <2>6 DEF Shape, JudgeTypes, CaseTypes, courtVars, judgeVars, impVars
<1>19. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  Shape'
    <2>1. /\ case[x] \in CaseRecord
          /\ case[x].status # "Unfiled" => case[x].court \in CourtIds
          /\ case \in [Cases -> CaseRecord]
          /\ location \in [CourtIds -> States \cup {"None"}]
        BY DEF Shape, JudgeTypes, CaseTypes, FiledInCourt
    <2>0. location[case[x].court] \in States \cup {"None"}
        BY <1>19, <2>1 DEF Decide
    <2>2. /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise>>
          /\ exceptedTaken' \in BOOLEAN /\ exceptedDecided' \in BOOLEAN
          /\ case[x].status # "Unfiled"
        BY <1>19, <2>1 DEF Decide, flagVars, Shape, JudgeTypes
    <2>3. case'[x] = [case[x] EXCEPT !.status = "Decided", !.jury = j, !.venue = location[case[x].court], !.witnesses = w, !.confession = conf, !.trialVerdict = v, !.verdict = v]
        BY <1>19, <2>1 DEF Decide
    <2>4. ASSUME NEW r \in CaseRecord, NEW rj \in BOOLEAN, NEW rw \in 0..2, NEW rconf \in BOOLEAN, NEW rv \in Verdicts, NEW rvn \in States \cup {"None"}
          PROVE  /\ [r EXCEPT !.status = "Decided", !.jury = rj, !.venue = rvn, !.witnesses = rw, !.confession = rconf, !.trialVerdict = rv, !.verdict = rv] \in CaseRecord
                 /\ [r EXCEPT !.status = "Decided", !.jury = rj, !.venue = rvn, !.witnesses = rw, !.confession = rconf, !.trialVerdict = rv, !.verdict = rv].court \in {r.court}
                 /\ [r EXCEPT !.status = "Decided", !.jury = rj, !.venue = rvn, !.witnesses = rw, !.confession = rconf, !.trialVerdict = rv, !.verdict = rv].status # "Unfiled"
        BY DEF CaseRecord, Status, Verdicts
    <2>5. /\ case'[x] \in CaseRecord
          /\ case'[x].status # "Unfiled"
          /\ case'[x].court \in CourtIds
        BY <2>1, <2>2, <2>3, <2>4, <2>0
    <2>6. case' \in [Cases -> CaseRecord]
        BY <1>19, <2>1, <2>5 DEF Decide
    <2>7. FiledInCourt'
        BY <1>19, <2>1, <2>5 DEF Decide, Shape, FiledInCourt
    <2> QED
        BY <2>2, <2>6, <2>7 DEF Shape, JudgeTypes, CaseTypes, courtVars, judgeVars, impVars
<1>20. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  Shape'
    <2>1. /\ case[x] \in CaseRecord
          /\ case[x].status # "Unfiled" => case[x].court \in CourtIds
          /\ case \in [Cases -> CaseRecord]
          /\ location \in [CourtIds -> States \cup {"None"}]
        BY DEF Shape, JudgeTypes, CaseTypes, FiledInCourt
    <2>2. /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise>>
          /\ exceptedTaken' \in BOOLEAN /\ exceptedDecided' \in BOOLEAN
          /\ case[x].status # "Unfiled"
        BY <1>20, <2>1 DEF Appeal, flagVars, Shape, JudgeTypes
    <2>3. case'[x] = [case[x] EXCEPT !.status = "Pending", !.court = c, !.verdict = "None"]
        BY <1>20, <2>1 DEF Appeal
    <2>4. ASSUME NEW r \in CaseRecord, NEW rc \in CourtIds
          PROVE  /\ [r EXCEPT !.status = "Pending", !.court = rc, !.verdict = "None"] \in CaseRecord
                 /\ [r EXCEPT !.status = "Pending", !.court = rc, !.verdict = "None"].court \in {rc}
                 /\ [r EXCEPT !.status = "Pending", !.court = rc, !.verdict = "None"].status # "Unfiled"
        BY DEF CaseRecord, Status, Verdicts
    <2>5. /\ case'[x] \in CaseRecord
          /\ case'[x].status # "Unfiled"
          /\ case'[x].court \in CourtIds
        BY <2>1, <2>2, <2>3, <2>4
    <2>6. case' \in [Cases -> CaseRecord]
        BY <1>20, <2>1, <2>5 DEF Appeal
    <2>7. FiledInCourt'
        BY <1>20, <2>1, <2>5 DEF Appeal, Shape, FiledInCourt
    <2> QED
        BY <2>2, <2>6, <2>7 DEF Shape, JudgeTypes, CaseTypes, courtVars, judgeVars, impVars
<1>21. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  Shape'
    <2>1. /\ case[x] \in CaseRecord
          /\ case[x].status # "Unfiled" => case[x].court \in CourtIds
          /\ case \in [Cases -> CaseRecord]
          /\ location \in [CourtIds -> States \cup {"None"}]
        BY DEF Shape, JudgeTypes, CaseTypes, FiledInCourt
    <2>2. /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise>>
          /\ exceptedTaken' \in BOOLEAN /\ exceptedDecided' \in BOOLEAN
          /\ case[x].status # "Unfiled"
        BY <1>21, <2>1 DEF AppellateDecide, flagVars, Shape, JudgeTypes
    <2>3. case'[x] = [case[x] EXCEPT !.status = "Decided", !.verdict = v]
        BY <1>21, <2>1 DEF AppellateDecide
    <2>4. ASSUME NEW r \in CaseRecord, NEW rv \in Verdicts
          PROVE  /\ [r EXCEPT !.status = "Decided", !.verdict = rv] \in CaseRecord
                 /\ [r EXCEPT !.status = "Decided", !.verdict = rv].court \in {r.court}
                 /\ [r EXCEPT !.status = "Decided", !.verdict = rv].status # "Unfiled"
        BY DEF CaseRecord, Status, Verdicts
    <2>5. /\ case'[x] \in CaseRecord
          /\ case'[x].status # "Unfiled"
          /\ case'[x].court \in CourtIds
        BY <2>1, <2>2, <2>3, <2>4
    <2>6. case' \in [Cases -> CaseRecord]
        BY <1>21, <2>1, <2>5 DEF AppellateDecide
    <2>7. FiledInCourt'
        BY <1>21, <2>1, <2>5 DEF AppellateDecide, Shape, FiledInCourt
    <2> QED
        BY <2>2, <2>6, <2>7 DEF Shape, JudgeTypes, CaseTypes, courtVars, judgeVars, impVars
<1>22. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  Shape'
    <2>1. /\ case[x] \in CaseRecord
          /\ case[x].status # "Unfiled" => case[x].court \in CourtIds
          /\ case \in [Cases -> CaseRecord]
          /\ location \in [CourtIds -> States \cup {"None"}]
        BY DEF Shape, JudgeTypes, CaseTypes, FiledInCourt
    <2>2. /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise>>
          /\ exceptedTaken' \in BOOLEAN /\ exceptedDecided' \in BOOLEAN
          /\ case[x].status # "Unfiled"
        BY <1>22, <2>1 DEF Dismiss, flagVars, Shape, JudgeTypes
    <2>3. case'[x] = [case[x] EXCEPT !.status = "Closed", !.verdict = "Dismissed"]
        BY <1>22, <2>1 DEF Dismiss
    <2>4. ASSUME NEW r \in CaseRecord
          PROVE  /\ [r EXCEPT !.status = "Closed", !.verdict = "Dismissed"] \in CaseRecord
                 /\ [r EXCEPT !.status = "Closed", !.verdict = "Dismissed"].court \in {r.court}
                 /\ [r EXCEPT !.status = "Closed", !.verdict = "Dismissed"].status # "Unfiled"
        BY DEF CaseRecord, Status, Verdicts
    <2>5. /\ case'[x] \in CaseRecord
          /\ case'[x].status # "Unfiled"
          /\ case'[x].court \in CourtIds
        BY <2>1, <2>2, <2>3, <2>4
    <2>6. case' \in [Cases -> CaseRecord]
        BY <1>22, <2>1, <2>5 DEF Dismiss
    <2>7. FiledInCourt'
        BY <1>22, <2>1, <2>5 DEF Dismiss, Shape, FiledInCourt
    <2> QED
        BY <2>2, <2>6, <2>7 DEF Shape, JudgeTypes, CaseTypes, courtVars, judgeVars, impVars
<1>23. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  Shape'
    <2>1. /\ case[x] \in CaseRecord
          /\ case[x].status # "Unfiled" => case[x].court \in CourtIds
          /\ case \in [Cases -> CaseRecord]
          /\ location \in [CourtIds -> States \cup {"None"}]
        BY DEF Shape, JudgeTypes, CaseTypes, FiledInCourt
    <2>2. /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise>>
          /\ exceptedTaken' \in BOOLEAN /\ exceptedDecided' \in BOOLEAN
          /\ case[x].status # "Unfiled"
        BY <1>23, <2>1 DEF Close, flagVars, Shape, JudgeTypes
    <2>3. case'[x] = [case[x] EXCEPT !.status = "Closed"]
        BY <1>23, <2>1 DEF Close
    <2>4. ASSUME NEW r \in CaseRecord
          PROVE  /\ [r EXCEPT !.status = "Closed"] \in CaseRecord
                 /\ [r EXCEPT !.status = "Closed"].court \in {r.court}
                 /\ [r EXCEPT !.status = "Closed"].status # "Unfiled"
        BY DEF CaseRecord, Status, Verdicts
    <2>5. /\ case'[x] \in CaseRecord
          /\ case'[x].status # "Unfiled"
          /\ case'[x].court \in CourtIds
        BY <2>1, <2>2, <2>3, <2>4
    <2>6. case' \in [Cases -> CaseRecord]
        BY <1>23, <2>1, <2>5 DEF Close
    <2>7. FiledInCourt'
        BY <1>23, <2>1, <2>5 DEF Close, Shape, FiledInCourt
    <2> QED
        BY <2>2, <2>6, <2>7 DEF Shape, JudgeTypes, CaseTypes, courtVars, judgeVars, impVars
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM ShapeAlways == Spec => []Shape
<1>1. Shape /\ [Next]_vars => Shape'
    BY NextShape
<1> QED
    BY InitShape, <1>1, PTL DEF Spec

THEOREM TypeOKAlways == Spec => []TypeOK
<1>1. Shape => TypeOK
    BY DEF Shape, JudgeTypes, CaseTypes, TypeOK
<1> QED
    BY ShapeAlways, <1>1, PTL

-----------------------------------------------------------------------------
(* Art. III s.1: one Supreme Court                                         *)

LEMMA InitInvOne == Init => InvOne
BY InitShape, SupremeCourtWF DEF Init, InvOne, OneSupremeCourt

LEMMA NextInvOne ==
    ASSUME Mut # "M_ABOLISH_SC", Mut # "M_COURT_OF_UNION", Mut # "M_REESTABLISH", InvOne, [Next]_vars
    PROVE  InvOne'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvOne
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvOne'
    BY <1>3, <1>0, SMT, SupremeCourtWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvOne'
    BY <1>4, <1>0, SMT, SupremeCourtWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvOne'
    BY <1>5, <1>0, SMT, SupremeCourtWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvOne'
    BY <1>6, <1>0, SMT, SupremeCourtWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvOne'
    BY <1>7, <1>0, SMT, SupremeCourtWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvOne'
    BY <1>8, <1>0, SMT, SupremeCourtWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvOne'
    BY <1>9, <1>0, SMT, SupremeCourtWF DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvOne'
    BY <1>10, <1>0, SMT, SupremeCourtWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvOne'
    BY <1>11, <1>0, SMT, SupremeCourtWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvOne'
    BY <1>12, <1>0, SMT, SupremeCourtWF DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvOne'
    BY <1>14, <1>0, SMT, SupremeCourtWF DEF Resign, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvOne'
    BY <1>15, <1>0, SMT, SupremeCourtWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvOne'
    BY <1>16, <1>0, SMT, SupremeCourtWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvOne'
    BY <1>17, <1>0, SMT, SupremeCourtWF DEF Convict, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvOne'
    BY <1>18, <1>0, SMT, SupremeCourtWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvOne, OneSupremeCourt, Shape, JudgeTypes, NewCourt, Abolishable, EstablishableTiers, InferiorTiers
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM OneSupremeCourtAlways ==
    ASSUME Mut # "M_ABOLISH_SC", Mut # "M_COURT_OF_UNION", Mut # "M_REESTABLISH"
    PROVE  Spec => []OneSupremeCourt
<1>1. InvOne /\ [Next]_vars => InvOne'
    BY NextInvOne
<1>2. InvOne => OneSupremeCourt
    BY DEF InvOne
<1> QED
    BY InitInvOne, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Courts exist exactly when they have a tier (every mutation)             *)

LEMMA InitInvEstab == Init => InvEstab
BY InitShape, SupremeCourtWF DEF Init, InvEstab, CourtsAreEstablished

LEMMA NextInvEstab ==
    ASSUME InvEstab, [Next]_vars
    PROVE  InvEstab'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvEstab
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvEstab'
    BY <1>3, <1>0, SMT, SupremeCourtWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvEstab'
    BY <1>4, <1>0, SMT, SupremeCourtWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvEstab'
    BY <1>5, <1>0, SMT, SupremeCourtWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvEstab'
    BY <1>6, <1>0, SMT, SupremeCourtWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvEstab'
    BY <1>7, <1>0, SMT, SupremeCourtWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvEstab'
    BY <1>8, <1>0, SMT, SupremeCourtWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvEstab'
    BY <1>9, <1>0, SMT, SupremeCourtWF DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvEstab'
    BY <1>10, <1>0, SMT, SupremeCourtWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvEstab'
    BY <1>11, <1>0, SMT, SupremeCourtWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvEstab'
    BY <1>12, <1>0, SMT, SupremeCourtWF DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvEstab'
    BY <1>14, <1>0, SMT, SupremeCourtWF DEF Resign, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvEstab'
    BY <1>15, <1>0, SMT, SupremeCourtWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvEstab'
    BY <1>16, <1>0, SMT, SupremeCourtWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvEstab'
    BY <1>17, <1>0, SMT, SupremeCourtWF DEF Convict, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvEstab'
    BY <1>18, <1>0, SMT, SupremeCourtWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvEstab, CourtsAreEstablished, Shape, JudgeTypes, EstablishableTiers, InferiorTiers
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM CourtsAreEstablishedAlways == Spec => []CourtsAreEstablished
<1>1. InvEstab /\ [Next]_vars => InvEstab'
    BY NextInvEstab
<1>2. InvEstab => CourtsAreEstablished
    BY DEF InvEstab
<1> QED
    BY InitInvEstab, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Seats bound the bench                                                   *)

LEMMA InitInvSeats == Init => InvSeats
BY InitShape, SupremeCourtWF, FS_EmptySet DEF Init, InvSeats, BenchFitsSeats, EmptyWhenAbsent

LEMMA NextInvSeats ==
    ASSUME Mut # "M_REESTABLISH", Mut # "M_SHRINK", Mut # "M_VACANCY_RECHECK", Mut # "M_CHIEF_RECHECK", InvSeats, [Next]_vars
    PROVE  InvSeats'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvSeats
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvSeats'
    <2>1. /\ c \notin courts
          /\ courts' = courts \cup {c}
          /\ seats' = [seats EXCEPT ![c] = 1]
          /\ UNCHANGED <<bench, nominee>>
        BY <1>3, SMT DEF EstablishCourt, NewCourt, judgeVars
    <2>2. Cardinality(bench[c]) = 0
        BY <2>1, FS_EmptySet DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent
    <2>3. BenchFitsSeats'
        BY <1>0, <2>1, <2>2 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2>4. EmptyWhenAbsent'
        BY <1>0, <2>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>3, <2>4 DEF InvSeats
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvSeats'
    <2>1. /\ courts' = courts \ {c}
          /\ seats' = [seats EXCEPT ![c] = 0]
          /\ bench' = [bench EXCEPT ![c] = {}]
          /\ nominee' = [nominee EXCEPT ![c] = NoOne]
        BY <1>4, SMT DEF AbolishCourt
    <2>2. Cardinality({}) = 0
        BY FS_EmptySet
    <2>3. BenchFitsSeats'
        BY <1>0, <2>1, <2>2 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2>4. EmptyWhenAbsent'
        BY <1>0, <2>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>3, <2>4 DEF InvSeats
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvSeats'
    BY <1>5, <1>0, SMT, SupremeCourtWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvSeats'
    BY <1>6, <1>0, SMT, SupremeCourtWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvSeats'
    BY <1>7, <1>0, SMT, SupremeCourtWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvSeats'
    BY <1>8, <1>0, SMT, SupremeCourtWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvSeats'
    <2>1. /\ nominee[c] # NoOne
          /\ HasVacancy(c)
          /\ bench' = [bench EXCEPT ![c] = bench[c] \cup {nominee[c]}]
          /\ nominee' = [nominee EXCEPT ![c] = NoOne]
          /\ UNCHANGED <<courts, seats>>
        BY <1>9, SMT DEF ConfirmJudge, StillVacant, courtVars
    <2>2. c \in courts
        BY <2>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent
    <2>3. /\ bench[c] \in SUBSET Persons
          /\ nominee[c] \in Persons
          /\ seats[c] \in Nat
        BY <1>0, <2>1 DEF Shape, JudgeTypes, Seat
    <2>4. bench[c] \cup {nominee[c]} \in SUBSET Persons
        BY <2>3
    <2>5. Cardinality(bench[c]) \in Nat
        BY <2>3, BenchCard
    <2>6. Cardinality(bench[c] \cup {nominee[c]}) \in Nat
        BY <2>4, BenchCard
    <2>7. Cardinality(bench[c] \cup {nominee[c]}) <= Cardinality(bench[c]) + 1
        BY <2>3, BenchCardAdd
    <2>8. Cardinality(bench'[c]) <= seats'[c]
        BY <1>0, <2>1, <2>3, <2>5, <2>6, <2>7 DEF HasVacancy, Shape, JudgeTypes
    <2>9. BenchFitsSeats'
        BY <1>0, <2>1, <2>8 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2>10. EmptyWhenAbsent'
        BY <1>0, <2>1, <2>2 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>9, <2>10 DEF InvSeats
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvSeats'
    BY <1>10, <1>0, SMT, SupremeCourtWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvSeats'
    BY <1>11, <1>0, SMT, SupremeCourtWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvSeats'
    <2>1. /\ chiefNominee \in bench[SupremeCourt] \/ HasVacancy(SupremeCourt)
          /\ bench' = [bench EXCEPT ![SupremeCourt] = bench[SupremeCourt] \cup {chiefNominee}]
          /\ chiefNominee # NoOne
          /\ UNCHANGED <<courts, seats, nominee>>
        BY <1>12, SMT DEF ConfirmChief, ChiefStillFits, courtVars
    <2>2. /\ bench[SupremeCourt] \in SUBSET Persons
          /\ chiefNominee \in Persons
          /\ seats[SupremeCourt] \in Nat
          /\ bench'[SupremeCourt] = bench[SupremeCourt] \cup {chiefNominee}
          /\ \A d2 \in CourtIds \ {SupremeCourt} : bench'[d2] = bench[d2]
        BY <1>0, <2>1, SupremeCourtWF DEF Shape, JudgeTypes, Seat
    <2>3. CASE chiefNominee \in bench[SupremeCourt]
        <3>1. \A d2 \in CourtIds : bench'[d2] = bench[d2]
            BY <2>2, <2>3
        <3> QED
            BY <1>0, <2>1, <3>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent
    <2>4. CASE HasVacancy(SupremeCourt)
        <3>1. bench[SupremeCourt] \cup {chiefNominee} \in SUBSET Persons
            BY <2>2
        <3>2. Cardinality(bench[SupremeCourt]) \in Nat
            BY <2>2, BenchCard
        <3>3. Cardinality(bench[SupremeCourt] \cup {chiefNominee}) \in Nat
            BY <3>1, BenchCard
        <3>4. Cardinality(bench[SupremeCourt] \cup {chiefNominee}) <= Cardinality(bench[SupremeCourt]) + 1
            BY <2>2, BenchCardAdd
        <3>5. SupremeCourt \in courts
            BY <2>2, <2>4, <3>2, SupremeCourtWF DEF HasVacancy, InvSeats, BenchFitsSeats, EmptyWhenAbsent
        <3>6. Cardinality(bench'[SupremeCourt]) <= seats'[SupremeCourt]
            BY <2>1, <2>2, <2>4, <3>2, <3>3, <3>4 DEF HasVacancy
        <3>7. BenchFitsSeats'
            BY <1>0, <2>1, <2>2, <3>6, SupremeCourtWF DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
        <3>8. EmptyWhenAbsent'
            BY <1>0, <2>1, <2>2, <3>5, SupremeCourtWF DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
        <3> QED
            BY <1>0, <3>7, <3>8 DEF InvSeats
    <2> QED
        BY <2>1, <2>3, <2>4
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvSeats'
    <2>1. /\ bench' = [bench EXCEPT ![c] = bench[c] \ {p}]
          /\ UNCHANGED <<courts, seats, nominee>>
        BY <1>14, SMT DEF Resign, courtVars
    <2>2. /\ Cardinality(bench[c] \ {p}) <= Cardinality(bench[c])
          /\ Cardinality(bench[c]) \in Nat
          /\ Cardinality(bench[c] \ {p}) \in Nat
          /\ seats[c] \in Nat
        BY <1>0, BenchCardRemove, BenchCard DEF Shape, JudgeTypes
    <2>3. BenchFitsSeats'
        BY <1>0, <2>1, <2>2 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2>4. EmptyWhenAbsent'
        BY <1>0, <2>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>3, <2>4 DEF InvSeats
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvSeats'
    <2>1. /\ bench' = [bench EXCEPT ![c] = bench[c] \ {p}]
          /\ UNCHANGED <<courts, seats, nominee>>
        BY <1>15, SMT DEF TermExpires, courtVars
    <2>2. /\ Cardinality(bench[c] \ {p}) <= Cardinality(bench[c])
          /\ Cardinality(bench[c]) \in Nat
          /\ Cardinality(bench[c] \ {p}) \in Nat
          /\ seats[c] \in Nat
        BY <1>0, BenchCardRemove, BenchCard DEF Shape, JudgeTypes
    <2>3. BenchFitsSeats'
        BY <1>0, <2>1, <2>2 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2>4. EmptyWhenAbsent'
        BY <1>0, <2>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>3, <2>4 DEF InvSeats
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvSeats'
    BY <1>16, <1>0, SMT, SupremeCourtWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvSeats'
    <2>1. /\ bench' = [dd \in CourtIds |-> bench[dd] \ {p}]
          /\ nominee' = [dd \in CourtIds |-> IF nominee[dd] = p THEN NoOne ELSE nominee[dd]]
          /\ UNCHANGED <<courts, seats>>
        BY <1>17, SMT DEF Convict, courtVars
    <2>2. ASSUME NEW dd \in CourtIds
          PROVE  /\ Cardinality(bench[dd] \ {p}) <= Cardinality(bench[dd])
                 /\ Cardinality(bench[dd]) \in Nat
                 /\ Cardinality(bench[dd] \ {p}) \in Nat
                 /\ seats[dd] \in Nat
        BY <1>0, BenchCardRemove, BenchCard DEF Shape, JudgeTypes
    <2>3. BenchFitsSeats'
        BY <1>0, <2>1, <2>2 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2>4. EmptyWhenAbsent'
        BY <1>0, <2>1 DEF InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>3, <2>4 DEF InvSeats
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvSeats'
    BY <1>18, <1>0, SMT, SupremeCourtWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvSeats, BenchFitsSeats, EmptyWhenAbsent, Shape, JudgeTypes, NewCourt, ByAttrition, StillVacant, ChiefStillFits, HasVacancy
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM BenchFitsSeatsAlways ==
    ASSUME Mut # "M_REESTABLISH", Mut # "M_SHRINK", Mut # "M_VACANCY_RECHECK", Mut # "M_CHIEF_RECHECK"
    PROVE  Spec => []BenchFitsSeats
<1>1. InvSeats /\ [Next]_vars => InvSeats'
    BY NextInvSeats
<1>2. InvSeats => BenchFitsSeats
    BY DEF InvSeats
<1> QED
    BY InitInvSeats, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* One commission, one court                                               *)

LEMMA InitInvTwo == Init => InvTwo
BY InitShape DEF Init, InvTwo, NoJudgeOnTwoCourts

LEMMA NextInvTwo ==
    ASSUME Mut # "M_CONFIRM_RECHECK", Mut # "M_CHIEF_RECHECK", InvTwo, [Next]_vars
    PROVE  InvTwo'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvTwo
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvTwo'
    BY <1>3, <1>0, SMT, SupremeCourtWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvTwo'
    BY <1>4, <1>0, SMT, SupremeCourtWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvTwo'
    BY <1>5, <1>0, SMT, SupremeCourtWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvTwo'
    BY <1>6, <1>0, SMT, SupremeCourtWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvTwo'
    BY <1>7, <1>0, SMT, SupremeCourtWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvTwo'
    BY <1>8, <1>0, SMT, SupremeCourtWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvTwo'
    <2>1. /\ \A e \in CourtIds : nominee[c] \notin bench[e]
          /\ bench' = [bench EXCEPT ![c] = bench[c] \cup {nominee[c]}]
        BY <1>9, SMT DEF ConfirmJudge, StillEligible, Eligible, IsJudge
    <2>2. ASSUME NEW e1 \in CourtIds, NEW e2 \in CourtIds, e1 # e2
          PROVE  bench'[e1] \cap bench'[e2] = {}
        BY <1>0, <2>1, <2>2 DEF InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes
    <2> QED
        BY <1>0, <2>2 DEF InvTwo, NoJudgeOnTwoCourts
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvTwo'
    BY <1>10, <1>0, SMT, SupremeCourtWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvTwo'
    BY <1>11, <1>0, SMT, SupremeCourtWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvTwo'
    <2>1. /\ chiefNominee \in bench[SupremeCourt] \/ \A e \in CourtIds : chiefNominee \notin bench[e]
          /\ bench' = [bench EXCEPT ![SupremeCourt] = bench[SupremeCourt] \cup {chiefNominee}]
        BY <1>12, SMT DEF ConfirmChief, ChiefStillFits, Eligible, IsJudge
    <2>2. /\ bench'[SupremeCourt] = bench[SupremeCourt] \cup {chiefNominee}
          /\ \A d2 \in CourtIds \ {SupremeCourt} : bench'[d2] = bench[d2]
        BY <1>0, <2>1, SupremeCourtWF DEF Shape, JudgeTypes
    <2>3. ASSUME NEW e1 \in CourtIds, NEW e2 \in CourtIds, e1 # e2
          PROVE  bench'[e1] \cap bench'[e2] = {}
        <3>1. bench[e1] \cap bench[e2] = {}
            BY <2>3 DEF InvTwo, NoJudgeOnTwoCourts
        <3>2. CASE chiefNominee \in bench[SupremeCourt]
            <4>1. bench'[e1] = bench[e1] /\ bench'[e2] = bench[e2]
                BY <2>2, <3>2
            <4> QED
                BY <3>1, <4>1
        <3>3. CASE \A e \in CourtIds : chiefNominee \notin bench[e]
            <4>1. CASE e1 = SupremeCourt
                BY <2>2, <2>3, <3>1, <3>3, <4>1
            <4>2. CASE e2 = SupremeCourt
                BY <2>2, <2>3, <3>1, <3>3, <4>2
            <4>3. CASE e1 # SupremeCourt /\ e2 # SupremeCourt
                BY <2>2, <2>3, <3>1, <4>3
            <4> QED
                BY <4>1, <4>2, <4>3
        <3> QED
            BY <2>1, <3>2, <3>3
    <2> QED
        BY <1>0, <2>3 DEF InvTwo, NoJudgeOnTwoCourts
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvTwo'
    BY <1>14, <1>0, SupremeCourtWF DEF Resign, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvTwo'
    BY <1>15, <1>0, SupremeCourtWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvTwo'
    BY <1>16, <1>0, SMT, SupremeCourtWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvTwo'
    BY <1>17, <1>0, SupremeCourtWF DEF Convict, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvTwo'
    BY <1>18, <1>0, SMT, SupremeCourtWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvTwo, NoJudgeOnTwoCourts, Shape, JudgeTypes, StillEligible, ChiefStillFits, Eligible, IsJudge
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM NoJudgeOnTwoCourtsAlways ==
    ASSUME Mut # "M_CONFIRM_RECHECK", Mut # "M_CHIEF_RECHECK"
    PROVE  Spec => []NoJudgeOnTwoCourts
<1>1. InvTwo /\ [Next]_vars => InvTwo'
    BY NextInvTwo
<1>2. InvTwo => NoJudgeOnTwoCourts
    BY DEF InvTwo
<1> QED
    BY InitInvTwo, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Incompatibility Clause                                                  *)

LEMMA InitInvCongress == Init => InvCongress
BY InitShape, NoOneWF DEF Init, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress

LEMMA NextInvCongress ==
    ASSUME Mut # "M_INCOMPAT", InvCongress, [Next]_vars
    PROVE  InvCongress'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvCongress
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvCongress'
    BY <1>3, <1>0, SMT, SupremeCourtWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvCongress'
    BY <1>4, <1>0, SMT, SupremeCourtWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvCongress'
    BY <1>5, <1>0, SMT, SupremeCourtWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvCongress'
    BY <1>6, <1>0, SMT, SupremeCourtWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvCongress'
    BY <1>7, <1>0, SMT, SupremeCourtWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvCongress'
    BY <1>8, <1>0, SMT, SupremeCourtWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvCongress'
    BY <1>9, <1>0, SMT, SupremeCourtWF DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvCongress'
    BY <1>10, <1>0, SMT, SupremeCourtWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvCongress'
    BY <1>11, <1>0, SMT, SupremeCourtWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvCongress'
    BY <1>12, <1>0, SMT, SupremeCourtWF DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvCongress'
    BY <1>14, <1>0, SMT, SupremeCourtWF DEF Resign, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvCongress'
    BY <1>15, <1>0, SMT, SupremeCourtWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvCongress'
    BY <1>16, <1>0, SMT, SupremeCourtWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvCongress'
    BY <1>17, <1>0, SMT, SupremeCourtWF DEF Convict, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvCongress'
    BY <1>18, <1>0, SMT, SupremeCourtWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvCongress, JudgesAreNotInCongress, NomineesNotInCongress, Shape, JudgeTypes, Eligible, NotInCongress, Seat
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM JudgesAreNotInCongressAlways ==
    ASSUME Mut # "M_INCOMPAT"
    PROVE  Spec => []JudgesAreNotInCongress
<1>1. InvCongress /\ [Next]_vars => InvCongress'
    BY NextInvCongress
<1>2. InvCongress => JudgesAreNotInCongress
    BY DEF InvCongress
<1> QED
    BY InitInvCongress, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Disqualification                                                        *)

LEMMA InitInvDisq == Init => InvDisq
BY InitShape, NoOneWF DEF Init, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified

LEMMA NextInvDisq ==
    ASSUME Mut # "M_DISQUAL", InvDisq, [Next]_vars
    PROVE  InvDisq'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvDisq
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvDisq'
    BY <1>3, <1>0, SMT, SupremeCourtWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvDisq'
    BY <1>4, <1>0, SMT, SupremeCourtWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvDisq'
    BY <1>5, <1>0, SMT, SupremeCourtWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvDisq'
    BY <1>6, <1>0, SMT, SupremeCourtWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvDisq'
    BY <1>7, <1>0, SMT, SupremeCourtWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvDisq'
    BY <1>8, <1>0, SMT, SupremeCourtWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvDisq'
    BY <1>9, <1>0, SMT, SupremeCourtWF DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvDisq'
    BY <1>10, <1>0, SMT, SupremeCourtWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvDisq'
    BY <1>11, <1>0, SMT, SupremeCourtWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvDisq'
    BY <1>12, <1>0, SMT, SupremeCourtWF DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvDisq'
    BY <1>14, <1>0, SMT, SupremeCourtWF DEF Resign, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvDisq'
    BY <1>15, <1>0, SMT, SupremeCourtWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvDisq'
    BY <1>16, <1>0, SMT, SupremeCourtWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvDisq'
    BY <1>17, <1>0, SMT, SupremeCourtWF DEF Convict, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvDisq'
    BY <1>18, <1>0, SMT, SupremeCourtWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvDisq, DisqualifiedDoNotSit, NomineesNotDisqualified, Shape, JudgeTypes, Eligible, NotDisqualified, Seat
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM DisqualifiedDoNotSitAlways ==
    ASSUME Mut # "M_DISQUAL"
    PROVE  Spec => []DisqualifiedDoNotSit
<1>1. InvDisq /\ [Next]_vars => InvDisq'
    BY NextInvDisq
<1>2. InvDisq => DisqualifiedDoNotSit
    BY DEF InvDisq
<1> QED
    BY InitInvDisq, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* The Chief Justice sits                                                  *)

LEMMA InitInvChief == Init => InvChief
BY InitShape, SupremeCourtWF DEF Init, InvChief, ChiefJusticeSits

LEMMA NextInvChief ==
    ASSUME Mut # "M_ABOLISH_SC", Mut # "M_REESTABLISH", Mut # "M_TENURE", InvChief, [Next]_vars
    PROVE  InvChief'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvChief
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvChief'
    BY <1>3, <1>0, SMT, SupremeCourtWF, NoOneWF DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvChief'
    BY <1>4, <1>0, SMT, SupremeCourtWF, NoOneWF DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvChief'
    BY <1>5, <1>0, SMT, SupremeCourtWF, NoOneWF DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvChief'
    BY <1>6, <1>0, SMT, SupremeCourtWF, NoOneWF DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvChief'
    BY <1>7, <1>0, SMT, SupremeCourtWF, NoOneWF DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvChief'
    BY <1>8, <1>0, SMT, SupremeCourtWF, NoOneWF DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvChief'
    BY <1>9, <1>0, SMT, SupremeCourtWF, NoOneWF DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvChief'
    BY <1>10, <1>0, SMT, SupremeCourtWF, NoOneWF DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvChief'
    BY <1>11, <1>0, SMT, SupremeCourtWF, NoOneWF DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvChief'
    BY <1>12, <1>0, SMT, SupremeCourtWF, NoOneWF DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT, SupremeCourtWF, NoOneWF DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvChief'
    BY <1>14, <1>0, SMT, SupremeCourtWF, NoOneWF DEF Resign, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvChief'
    BY <1>15, <1>0, SMT, SupremeCourtWF, NoOneWF DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvChief'
    BY <1>16, <1>0, SMT, SupremeCourtWF, NoOneWF DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvChief'
    BY <1>17, <1>0, SMT, SupremeCourtWF, NoOneWF DEF Convict, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvChief'
    BY <1>18, <1>0, SMT, SupremeCourtWF, NoOneWF DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvChief, ChiefJusticeSits, Shape, JudgeTypes, NewCourt, Abolishable, FixedTerm, Seat
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM ChiefJusticeSitsAlways ==
    ASSUME Mut # "M_ABOLISH_SC", Mut # "M_REESTABLISH", Mut # "M_TENURE"
    PROVE  Spec => []ChiefJusticeSits
<1>1. InvChief /\ [Next]_vars => InvChief'
    BY NextInvChief
<1>2. InvChief => ChiefJusticeSits
    BY DEF InvChief
<1> QED
    BY InitInvChief, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Compensation Clause                                                     *)

LEMMA InitInvPay == Init => InvPay
BY InitShape DEF Init, InvPay, CompensationClause

LEMMA NextInvPay ==
    ASSUME Mut # "M_PAYCUT", InvPay, [Next]_vars
    PROVE  InvPay'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvPay
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvPay'
    BY <1>3, <1>0, SMT DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvPay'
    BY <1>4, <1>0, SMT DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvPay'
    BY <1>5, <1>0, SMT DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvPay'
    BY <1>6, <1>0, SMT DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvPay'
    BY <1>7, <1>0, SMT DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvPay'
    BY <1>8, <1>0, SMT DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvPay'
    BY <1>9, <1>0, SMT DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvPay'
    BY <1>10, <1>0, SMT DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvPay'
    BY <1>11, <1>0, SMT DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvPay'
    BY <1>12, <1>0, SMT DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvPay'
    BY <1>14, <1>0, SMT DEF Resign, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvPay'
    BY <1>15, <1>0, SMT DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvPay'
    BY <1>16, <1>0, SMT DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvPay'
    BY <1>17, <1>0, SMT DEF Convict, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvPay'
    BY <1>18, <1>0, SMT DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvPay, CompensationClause, Shape, JudgeTypes, PayProtected
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM CompensationClauseAlways ==
    ASSUME Mut # "M_PAYCUT"
    PROVE  Spec => []CompensationClause
<1>1. InvPay /\ [Next]_vars => InvPay'
    BY NextInvPay
<1>2. InvPay => CompensationClause
    BY DEF InvPay
<1> QED
    BY InitInvPay, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Good Behaviour                                                          *)

LEMMA InitInvTenure == Init => InvTenure
BY InitShape DEF Init, InvTenure, GoodBehaviour

LEMMA NextInvTenure ==
    ASSUME Mut # "M_TENURE", Mut # "M_NOIMPEACH", Mut # "M_CHASE", InvTenure, [Next]_vars
    PROVE  InvTenure'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvTenure
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>2. CASE CaseStep
    BY <1>0, <1>2, CaseStepFrame DEF InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>3. ASSUME NEW c \in CourtIds, NEW t \in Tiers, NEW st \in States \cup {"None"}, NEW h \in HouseVotes, NEW s \in SenateVotes,
             EstablishCourt(c, t, st, h, s)
      PROVE  InvTenure'
    BY <1>3, <1>0, SMT DEF EstablishCourt, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>4. ASSUME NEW c \in CourtIds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             AbolishCourt(c, h, s)
      PROVE  InvTenure'
    BY <1>4, <1>0, SMT DEF AbolishCourt, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>5. ASSUME NEW c \in CourtIds, NEW n \in 1..MaxSeats, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSeats(c, n, h, s)
      PROVE  InvTenure'
    BY <1>5, <1>0, SMT DEF SetSeats, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>6. ASSUME NEW c \in CourtIds, NEW n \in 0..MaxSalary, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetSalary(c, n, h, s)
      PROVE  InvTenure'
    BY <1>6, <1>0, SMT DEF SetSalary, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>7. ASSUME NEW E \in SUBSET Kinds, NEW h \in HouseVotes, NEW s \in SenateVotes,
             SetExceptions(E, h, s)
      PROVE  InvTenure'
    BY <1>7, <1>0, SMT DEF SetExceptions, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>8. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             NominateJudge(c, p)
      PROVE  InvTenure'
    BY <1>8, <1>0, SMT DEF NominateJudge, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>9. ASSUME NEW c \in CourtIds, NEW n \in SenateVotes,
             ConfirmJudge(c, n)
      PROVE  InvTenure'
    BY <1>9, <1>0, SMT DEF ConfirmJudge, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>10. ASSUME NEW c \in CourtIds,
             RejectJudge(c)
      PROVE  InvTenure'
    BY <1>10, <1>0, SMT DEF RejectJudge, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>11. ASSUME NEW p \in Persons,
             NominateChief(p)
      PROVE  InvTenure'
    BY <1>11, <1>0, SMT DEF NominateChief, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>12. ASSUME NEW n \in SenateVotes,
             ConfirmChief(n)
      PROVE  InvTenure'
    BY <1>12, <1>0, SMT DEF ConfirmChief, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>13. CASE RejectChief
    BY <1>13, <1>0, SMT DEF RejectChief, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>14. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             Resign(c, p)
      PROVE  InvTenure'
    BY <1>14, <1>0, SMT DEF Resign, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>15. ASSUME NEW c \in CourtIds, NEW p \in Persons,
             TermExpires(c, p)
      PROVE  InvTenure'
    BY <1>15, <1>0, SMT DEF TermExpires, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>16. ASSUME NEW p \in Persons, NEW n \in HouseVotes,
             Impeach(p, n)
      PROVE  InvTenure'
    BY <1>16, <1>0, SMT DEF Impeach, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>17. ASSUME NEW p \in Persons, NEW n \in SenateVotes, NEW dq \in BOOLEAN,
             Convict(p, n, dq)
      PROVE  InvTenure'
    BY <1>17, <1>0, SMT DEF Convict, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1>18. ASSUME NEW p \in Persons,
             Acquit(p)
      PROVE  InvTenure'
    BY <1>18, <1>0, SMT DEF Acquit, courtVars, judgeVars, impVars, flagVars, InvTenure, GoodBehaviour, Shape, JudgeTypes, FixedTerm, Impeached, ConvictionVote, ArticleIII
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM GoodBehaviourAlways ==
    ASSUME Mut # "M_TENURE", Mut # "M_NOIMPEACH", Mut # "M_CHASE"
    PROVE  Spec => []GoodBehaviour
<1>1. InvTenure /\ [Next]_vars => InvTenure'
    BY NextInvTenure
<1>2. InvTenure => GoodBehaviour
    BY DEF InvTenure
<1> QED
    BY InitInvTenure, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Original jurisdiction (Marbury)                                         *)

LEMMA InitInvOrig == Init => InvOrig
BY InitShape DEF Init, InvOrig, OriginalJurisdiction, NoCase

LEMMA NextInvOrig ==
    ASSUME Mut # "M_MARBURY", InvOrig, [Next]_vars
    PROVE  InvOrig'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvOrig
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvOrig'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvOrig'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvOrig'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvOrig'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvOrig'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvOrig'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvOrig, OriginalJurisdiction, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SupremeOriginal, OriginalKinds
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM OriginalJurisdictionAlways ==
    ASSUME Mut # "M_MARBURY"
    PROVE  Spec => []OriginalJurisdiction
<1>1. InvOrig /\ [Next]_vars => InvOrig'
    BY NextInvOrig
<1>2. InvOrig => OriginalJurisdiction
    BY DEF InvOrig
<1> QED
    BY InitInvOrig, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Amend. XI                                                               *)

LEMMA InitInvXI == Init => InvXI
BY InitShape DEF Init, InvXI, EleventhAmendment, NoCase

LEMMA NextInvXI ==
    ASSUME Mut # "M_CHISHOLM", InvXI, [Next]_vars
    PROVE  InvXI'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvXI
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvXI'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvXI'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvXI'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvXI'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvXI'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvXI'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvXI, EleventhAmendment, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, SuableState
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM EleventhAmendmentAlways ==
    ASSUME Mut # "M_CHISHOLM"
    PROVE  Spec => []EleventhAmendment
<1>1. InvXI /\ [Next]_vars => InvXI'
    BY NextInvXI
<1>2. InvXI => EleventhAmendment
    BY DEF InvXI
<1> QED
    BY InitInvXI, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Courts of appeals try nothing                                           *)

LEMMA InitInvAppell == Init => InvAppell
BY InitShape DEF Init, InvAppell, AppealsCourtsAreAppellate, NoCase

LEMMA NextInvAppell ==
    ASSUME Mut # "M_CIRCUIT", InvAppell, [Next]_vars
    PROVE  InvAppell'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvAppell
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvAppell'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvAppell'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvAppell'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvAppell'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvAppell'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvAppell'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvAppell, AppealsCourtsAreAppellate, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, AppealsOriginal
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM AppealsCourtsAreAppellateAlways ==
    ASSUME Mut # "M_CIRCUIT"
    PROVE  Spec => []AppealsCourtsAreAppellate
<1>1. InvAppell /\ [Next]_vars => InvAppell'
    BY NextInvAppell
<1>2. InvAppell => AppealsCourtsAreAppellate
    BY DEF InvAppell
<1> QED
    BY InitInvAppell, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Public rights (Northern Pipeline)                                       *)

LEMMA InitInvPublic == Init => InvPublic
BY InitShape DEF Init, InvPublic, PublicRightsOnly, NoCase

LEMMA NextInvPublic ==
    ASSUME Mut # "M_NORTHERN_PIPELINE", InvPublic, [Next]_vars
    PROVE  InvPublic'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvPublic
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvPublic'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvPublic'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvPublic'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvPublic'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvPublic'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvPublic'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvPublic, PublicRightsOnly, Shape, CaseTypes, FiledInCourt, CaseRecord, HasOriginalJurisdiction, PublicRights
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM PublicRightsOnlyAlways ==
    ASSUME Mut # "M_NORTHERN_PIPELINE"
    PROVE  Spec => []PublicRightsOnly
<1>1. InvPublic /\ [Next]_vars => InvPublic'
    BY NextInvPublic
<1>2. InvPublic => PublicRightsOnly
    BY DEF InvPublic
<1> QED
    BY InitInvPublic, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Jury and venue                                                          *)

LEMMA InitInvJury == Init => InvJury
BY InitShape DEF Init, InvJury, JuryAndVenue, NoCase

LEMMA NextInvJury ==
    ASSUME Mut # "M_NOJURY", Mut # "M_VENUE", InvJury, [Next]_vars
    PROVE  InvJury'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvJury
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvJury'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvJury'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvJury'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvJury'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvJury'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvJury'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvJury, JuryAndVenue, Shape, CaseTypes, FiledInCourt, CaseRecord, TrialByJury, TriedWhereCommitted
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM JuryAndVenueAlways ==
    ASSUME Mut # "M_NOJURY", Mut # "M_VENUE"
    PROVE  Spec => []JuryAndVenue
<1>1. InvJury /\ [Next]_vars => InvJury'
    BY NextInvJury
<1>2. InvJury => JuryAndVenue
    BY DEF InvJury
<1> QED
    BY InitInvJury, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Treason                                                                 *)

LEMMA InitInvTreason == Init => InvTreason
BY InitShape DEF Init, InvTreason, TreasonProof, NoCase

LEMMA NextInvTreason ==
    ASSUME Mut # "M_TREASON", InvTreason, [Next]_vars
    PROVE  InvTreason'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvTreason
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvTreason'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvTreason'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvTreason'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvTreason'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvTreason'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvTreason'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvTreason, TreasonProof, Shape, CaseTypes, FiledInCourt, CaseRecord, TreasonProven
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM TreasonProofAlways ==
    ASSUME Mut # "M_TREASON"
    PROVE  Spec => []TreasonProof
<1>1. InvTreason /\ [Next]_vars => InvTreason'
    BY NextInvTreason
<1>2. InvTreason => TreasonProof
    BY DEF InvTreason
<1> QED
    BY InitInvTreason, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Double jeopardy                                                         *)

LEMMA InitInvJeopardy == Init => InvJeopardy
BY InitShape DEF Init, InvJeopardy, NoDoubleJeopardy, NoCase

LEMMA NextInvJeopardy ==
    ASSUME Mut # "M_KEPNER", InvJeopardy, [Next]_vars
    PROVE  InvJeopardy'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvJeopardy
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvJeopardy'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvJeopardy'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvJeopardy'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvJeopardy'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvJeopardy'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvJeopardy'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvJeopardy, NoDoubleJeopardy, Shape, CaseTypes, FiledInCourt, CaseRecord, NotAcquitted
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM NoDoubleJeopardyAlways ==
    ASSUME Mut # "M_KEPNER"
    PROVE  Spec => []NoDoubleJeopardy
<1>1. InvJeopardy /\ [Next]_vars => InvJeopardy'
    BY NextInvJeopardy
<1>2. InvJeopardy => NoDoubleJeopardy
    BY DEF InvJeopardy
<1> QED
    BY InitInvJeopardy, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Exceptions Clause on the way up                                         *)

LEMMA InitInvExcept == Init => InvExcept
BY InitShape DEF Init, InvExcept, ExceptionsHonoured

LEMMA NextInvExcept ==
    ASSUME Mut # "M_EXCEPTIONS", InvExcept, [Next]_vars
    PROVE  InvExcept'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvExcept
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvExcept'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvExcept'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvExcept'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvExcept'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvExcept'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvExcept'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvExcept, ExceptionsHonoured, Shape, CaseTypes, FiledInCourt, CaseRecord, NotExcepted
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM ExceptionsHonouredAlways ==
    ASSUME Mut # "M_EXCEPTIONS"
    PROVE  Spec => []ExceptionsHonoured
<1>1. InvExcept /\ [Next]_vars => InvExcept'
    BY NextInvExcept
<1>2. InvExcept => ExceptionsHonoured
    BY DEF InvExcept
<1> QED
    BY InitInvExcept, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Exceptions Clause at judgment (McCardle)                                *)

LEMMA InitInvPending == Init => InvPending
BY InitShape DEF Init, InvPending, ExceptionsBindPending

LEMMA NextInvPending ==
    ASSUME Mut # "M_MCCARDLE", InvPending, [Next]_vars
    PROVE  InvPending'
<1>0. Shape /\ Shape'
    BY NextShape DEF InvPending
<1>1. CASE UNCHANGED vars
    BY <1>0, <1>1 DEF vars, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>2. CASE CongressStep \/ JudgeStep
    BY <1>0, <1>2, NonCaseFrame DEF InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>3. ASSUME NEW x \in Cases, NEW k \in Kinds, NEW c \in CourtIds, NEW st \in States \cup {"None"},
             File(x, k, c, st)
      PROVE  InvPending'
    BY <1>3, <1>0, SMT DEF File, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>4. ASSUME NEW x \in Cases, NEW j \in BOOLEAN, NEW w \in 0..2, NEW conf \in BOOLEAN, NEW v \in Verdicts,
             Decide(x, j, w, conf, v)
      PROVE  InvPending'
    BY <1>4, <1>0, SMT DEF Decide, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>5. ASSUME NEW x \in Cases, NEW c \in CourtIds,
             Appeal(x, c)
      PROVE  InvPending'
    BY <1>5, <1>0, SMT DEF Appeal, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>6. ASSUME NEW x \in Cases, NEW v \in Verdicts,
             AppellateDecide(x, v)
      PROVE  InvPending'
    BY <1>6, <1>0, SMT DEF AppellateDecide, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>7. ASSUME NEW x \in Cases,
             Dismiss(x)
      PROVE  InvPending'
    BY <1>7, <1>0, SMT DEF Dismiss, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1>8. ASSUME NEW x \in Cases,
             Close(x)
      PROVE  InvPending'
    BY <1>8, <1>0, SMT DEF Close, courtVars, judgeVars, impVars, flagVars, InvPending, ExceptionsBindPending, Shape, CaseTypes, FiledInCourt, CaseRecord, StillHeard
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, NextSplit DEF CongressStep, JudgeStep, CaseStep

THEOREM ExceptionsBindPendingAlways ==
    ASSUME Mut # "M_MCCARDLE"
    PROVE  Spec => []ExceptionsBindPending
<1>1. InvPending /\ [Next]_vars => InvPending'
    BY NextInvPending
<1>2. InvPending => ExceptionsBindPending
    BY DEF InvPending
<1> QED
    BY InitInvPending, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* The text as specified.                                                  *)

THEOREM SafeAlways ==
    ASSUME Mut = "none"
    PROVE  Spec => []Safety
<1>1. Spec => []OneSupremeCourt
    BY OneSupremeCourtAlways
<1>2. Spec => []CourtsAreEstablished
    BY CourtsAreEstablishedAlways
<1>3. Spec => []BenchFitsSeats
    BY BenchFitsSeatsAlways
<1>4. Spec => []NoJudgeOnTwoCourts
    BY NoJudgeOnTwoCourtsAlways
<1>5. Spec => []JudgesAreNotInCongress
    BY JudgesAreNotInCongressAlways
<1>6. Spec => []DisqualifiedDoNotSit
    BY DisqualifiedDoNotSitAlways
<1>7. Spec => []ChiefJusticeSits
    BY ChiefJusticeSitsAlways
<1>8. Spec => []CompensationClause
    BY CompensationClauseAlways
<1>9. Spec => []GoodBehaviour
    BY GoodBehaviourAlways
<1>10. Spec => []OriginalJurisdiction
    BY OriginalJurisdictionAlways
<1>11. Spec => []EleventhAmendment
    BY EleventhAmendmentAlways
<1>12. Spec => []AppealsCourtsAreAppellate
    BY AppealsCourtsAreAppellateAlways
<1>13. Spec => []PublicRightsOnly
    BY PublicRightsOnlyAlways
<1>14. Spec => []JuryAndVenue
    BY JuryAndVenueAlways
<1>15. Spec => []TreasonProof
    BY TreasonProofAlways
<1>16. Spec => []NoDoubleJeopardy
    BY NoDoubleJeopardyAlways
<1>17. Spec => []ExceptionsHonoured
    BY ExceptionsHonouredAlways
<1>18. Spec => []ExceptionsBindPending
    BY ExceptionsBindPendingAlways
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17, <1>18, PTL DEF Safety

-----------------------------------------------------------------------------
(* Why each mutation must fail: what it admits, in the module's            *)
(* vocabulary. The counterexamples are in the TLC results file.           *)

LEMMA MutAbolishSCAbolishesTheCourt ==
    ASSUME Mut = "M_ABOLISH_SC" PROVE Abolishable(SupremeCourt)
BY DEF Abolishable

LEMMA MutCourtOfUnionAddsASupremeTier ==
    ASSUME Mut = "M_COURT_OF_UNION" PROVE "Supreme" \in EstablishableTiers
BY DEF EstablishableTiers

LEMMA MutReestablishRemakesTheCourt ==
    ASSUME Mut = "M_REESTABLISH" PROVE NewCourt(SupremeCourt)
BY DEF NewCourt

LEMMA MutShrinkUnseatsNoOne ==
    ASSUME Mut = "M_SHRINK", NEW c \in CourtIds, NEW n \in Nat PROVE ByAttrition(c, n)
BY DEF ByAttrition

LEMMA MutVacancyRecheckPacks ==
    ASSUME Mut = "M_VACANCY_RECHECK", NEW c \in CourtIds PROVE StillVacant(c)
BY DEF StillVacant

LEMMA MutConfirmRecheckSeatsASittingJudge ==
    ASSUME Mut = "M_CONFIRM_RECHECK", NEW c \in CourtIds PROVE StillEligible(c)
BY DEF StillEligible

LEMMA MutChiefRecheckSeatsAnyNominee ==
    ASSUME Mut = "M_CHIEF_RECHECK" PROVE ChiefStillFits
BY DEF ChiefStillFits

LEMMA MutIncompatAdmitsCongress ==
    ASSUME Mut = "M_INCOMPAT", NEW p \in Congress PROVE NotInCongress(p)
BY DEF NotInCongress

LEMMA MutDisqualAdmitsTheDisqualified ==
    ASSUME Mut = "M_DISQUAL", NEW p \in disqualified PROVE NotDisqualified(p)
BY DEF NotDisqualified

LEMMA MutMarburyEnlargesOriginal ==
    ASSUME Mut = "M_MARBURY" PROVE SupremeOriginal("Federal") /\ "Federal" \notin OriginalKinds
BY DEF SupremeOriginal, OriginalKinds

LEMMA MutChisholmSuesAState ==
    ASSUME Mut = "M_CHISHOLM" PROVE SuableState("AgainstState")
BY DEF SuableState

LEMMA MutCircuitTriesInAppeals ==
    ASSUME Mut = "M_CIRCUIT" PROVE AppealsOriginal
BY DEF AppealsOriginal

LEMMA MutNorthernPipelineTriesPrivateRights ==
    ASSUME Mut = "M_NORTHERN_PIPELINE" PROVE PublicRights("Diversity")
BY DEF PublicRights

LEMMA MutNoJuryTriesWithoutJury ==
    ASSUME Mut = "M_NOJURY" PROVE TrialByJury(FALSE)
BY DEF TrialByJury

LEMMA MutVenueTriesAnywhere ==
    ASSUME Mut = "M_VENUE", NEW c \in CourtIds, NEW st PROVE TriedWhereCommitted(c, st)
BY DEF TriedWhereCommitted

LEMMA MutTreasonConvictsOnOneWitness ==
    ASSUME Mut = "M_TREASON" PROVE TreasonProven(1, FALSE)
BY DEF TreasonProven

LEMMA MutKepnerAppealsAnAcquittal ==
    ASSUME Mut = "M_KEPNER", NEW x \in Cases PROVE NotAcquitted(x)
BY DEF NotAcquitted

LEMMA MutExceptionsIgnoresCongress ==
    ASSUME Mut = "M_EXCEPTIONS", NEW x \in Cases PROVE NotExcepted(x)
BY DEF NotExcepted

LEMMA MutMcCardleDecidesAnyway ==
    ASSUME Mut = "M_MCCARDLE", NEW x \in Cases PROVE StillHeard(x)
BY DEF StillHeard

LEMMA MutPaycutDiminishes ==
    ASSUME Mut = "M_PAYCUT", NEW c \in CourtIds PROVE PayProtected(c, 0)
BY DEF PayProtected

LEMMA MutTenureEndsAnyTerm ==
    ASSUME Mut = "M_TENURE" PROVE FixedTerm(SupremeCourt)
BY DEF FixedTerm

LEMMA MutNoImpeachTriesTheUnimpeached ==
    ASSUME Mut = "M_NOIMPEACH", NEW p \in Persons PROVE Impeached(p)
BY DEF Impeached

\* Samuel Chase, 1805: with five Senators, three convict under M_CHASE and
\* would not under the text.
LEMMA MutChaseConvictsByMajority ==
    ASSUME Mut = "M_CHASE", Cardinality(Senate) = 5
    PROVE  ConvictionVote(3) /\ ~TwoThirds(3, Senate)
BY DEF ConvictionVote, Majority, TwoThirds

=============================================================================
