----------------------------- MODULE Executive -----------------------------
(***************************************************************************)
(* A TLA+ model of the Executive Branch.                                   *)
(*                                                                         *)
(* Companion to Constitution.tla (which already covers presentment, veto,  *)
(* impeachment, recess appointments and the 22nd/25th sec. 1-2) and        *)
(* Judiciary.tla. This module takes up the rest of Article II and the      *)
(* administrative state the text barely mentions.                          *)
(*                                                                         *)
(* A point worth making at the top: THE CONSTITUTION CREATES NO BUREAUS.   *)
(* Art. II refers to "executive Departments" and "the principal Officer in *)
(* each", and the Appointments Clause to officers "which shall be          *)
(* established by Law", but every department, agency, commission, bureau   *)
(* and office is a creature of statute. Init therefore has no agencies.    *)
(* Congress makes them, and the questions the model asks are the ones the  *)
(* cases ask: who appoints their officers, who may remove them, and which  *)
(* branch they belong to.                                                  *)
(*                                                                         *)
(* Provisions modelled:                                                    *)
(*   Art. II sec. 1   vesting of "the executive Power" in one President    *)
(*   Art. II sec. 2   Commander in Chief; opinions in writing; pardons     *)
(*                    (not for impeachment); treaties (2/3 Senate);        *)
(*                    Appointments Clause - principal vs. inferior         *)
(*                    officers, and where Congress may vest the latter     *)
(*   Art. II sec. 3   convening Congress; Take Care Clause (as a liveness  *)
(*                    obligation)                                          *)
(*   Art. I  sec. 8   Congress, not the President, declares war and        *)
(*                    creates departments (Necessary and Proper)           *)
(*   Art. I  sec. 6   Incompatibility Clause                               *)
(*   Amend. XXV sec. 3-4   presidential inability, voluntary and           *)
(*                    involuntary, and the contest procedure               *)
(*   Buckley v. Valeo (1976): Congress may not appoint officers who        *)
(*                    execute the laws                                     *)
(*   Bowsher v. Synar (1986): Congress may not keep removal power over     *)
(*                    an officer who executes the laws, save impeachment   *)
(*   Myers (1926) / Humphrey's Executor (1935) / Seila Law (2020) /        *)
(*   Trump v. Slaughter (2026): for-cause removal protection survives      *)
(*                    only for bodies that exercise no executive power     *)
(*   Federal Vacancies Reform Act (1998): acting officers, time-limited    *)
(*                                                                         *)
(* Abstracted away: elections, the Electoral College, presentment of       *)
(* statutes (a "statute" is a majority of both houses), the Youngstown     *)
(* framework for executive orders, the Senate's role in ambassadors beyond *)
(* consent, and the Federal Reserve, which Slaughter left alone.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Persons, House, Senate,
  Eligible,        \* Persons eligible to be President
  Agencies,        \* Pool of agency identifiers Congress may bring to life
  Treaties,        \* Treaty identifiers
  ActingLimit,     \* Days an acting officer may serve (FVRA: 210)
  NoOne

ASSUME House \subseteq Persons /\ Senate \subseteq Persons /\ House \cap Senate = {}
ASSUME Eligible \subseteq Persons
ASSUME NoOne \notin Persons
ASSUME ActingLimit \in Nat /\ ActingLimit >= 1

-----------------------------------------------------------------------------
(* Helpers *)

Congress == House \cup Senate
Seat     == Persons \cup {NoOne}

Majority(ayes, body)  == 2 * ayes >  Cardinality(body)
TwoThirds(ayes, body) == 3 * ayes >= 2 * Cardinality(body)
HouseVotes  == 0..Cardinality(House)
SenateVotes == 0..Cardinality(Senate)
Statute(h, s) == Majority(h, House) /\ Majority(s, Senate)

Branches == {"Executive", "Legislative", "Judicial"}
Removal  == {"AtWill", "ForCause"}
\* Where Congress may vest appointment of inferior officers, Art. II sec. 2
\* cl. 2: "in the President alone, in the Courts of Law, or in the Heads of
\* Departments". Not in itself (Buckley).
Vestings == {"President", "Head", "Courts"}

Offences == {"Federal", "State", "Impeachment"}

\* Amend. XXV sec. 3-4 inability states
Inability == {"None",              \* President exercises the office
              "SelfDeclared",      \* sec. 3: President wrote to Congress
              "CabinetDeclared",   \* sec. 4: VP + majority of principal officers
              "Contested",         \* President declared no inability exists;
                                   \*   VP + cabinet have four days to re-declare
              "BeforeCongress"}    \* they did; Congress has 21 days, 2/3 each

-----------------------------------------------------------------------------
VARIABLES
  president,
  vicePresident,
  inability,       \* Inability
  inSession,       \* BOOLEAN
  atWar,           \* BOOLEAN - only Congress changes this
  agency,          \* Agencies -> record (see TypeOK)
  treaty,          \* Treaties -> {"None", "Negotiated", "Ratified"}
  pardoned,        \* SUBSET (Persons \X Offences)
  impeached,
  disqualified

AgencyRecord ==
  [exists      : BOOLEAN,
   branch      : Branches,
   executesLaw : BOOLEAN,       \* exercises executive power?
   removal     : Removal,       \* statutory protection for the head
   vesting     : Vestings,      \* who appoints the inferior officer
   head        : Seat,          \* principal officer, Senate-confirmed
   headNominee : Seat,
   acting      : Seat,          \* FVRA acting head while head is vacant
   actingDays  : 0..ActingLimit,
   inferior    : Seat]          \* one inferior officer per agency

TypeOK ==
  /\ president \in Seat
  /\ vicePresident \in Seat
  /\ inability \in Inability
  /\ inSession \in BOOLEAN
  /\ atWar \in BOOLEAN
  /\ agency \in [Agencies -> AgencyRecord]
  /\ treaty \in [Treaties -> {"None", "Negotiated", "Ratified"}]
  /\ pardoned \subseteq (Persons \X Offences)
  /\ impeached \subseteq Persons
  /\ disqualified \subseteq Persons

execVars   == <<president, vicePresident, inability>>
agencyVars == <<agency>>
otherVars  == <<inSession, atWar, treaty, pardoned>>
impVars    == <<impeached, disqualified>>
vars       == <<execVars, agencyVars, otherVars, impVars>>

\* Whoever holds "the executive Power" right now (Amend. XXV: the VP as
\* Acting President has all of it).
Acting    == inability # "None"
Executive == IF Acting THEN vicePresident ELSE president

Live(a)   == agency[a].exists
Heads     == {agency[a].head : a \in {b \in Agencies : Live(b)}} \ {NoOne}
Inferiors == {agency[a].inferior : a \in {b \in Agencies : Live(b)}} \ {NoOne}
Actings   == {agency[a].acting : a \in {b \in Agencies : Live(b)}} \ {NoOne}
Officers  == ({president, vicePresident} \cup Heads \cup Inferiors \cup Actings) \ {NoOne}

\* "the principal officers of the executive departments" who vote under
\* Amend. XXV sec. 4 - heads of agencies in the Executive branch.
Cabinet == {agency[a].head : a \in {b \in Agencies :
              Live(b) /\ agency[b].branch = "Executive"}} \ {NoOne}

Blank == [exists |-> FALSE, branch |-> "Executive", executesLaw |-> FALSE,
          removal |-> "AtWill", vesting |-> "President",
          head |-> NoOne, headNominee |-> NoOne, acting |-> NoOne,
          actingDays |-> 0, inferior |-> NoOne]

-----------------------------------------------------------------------------
Init ==
  /\ president = NoOne
  /\ vicePresident = NoOne
  /\ inability = "None"
  /\ inSession = TRUE
  /\ atWar = FALSE
  /\ agency = [a \in Agencies |-> Blank]     \* the text creates none
  /\ treaty = [t \in Treaties |-> "None"]
  /\ pardoned = {}
  /\ impeached = {}
  /\ disqualified = {}

-----------------------------------------------------------------------------
(* The office - Art. II sec. 1, Amend. XXV                                 *)

Elect(p, v) ==
  /\ p \in Eligible \ disqualified /\ v \in Eligible \ disqualified
  /\ p # v /\ p \notin Congress /\ v \notin Congress
  /\ p \notin Officers /\ v \notin Officers
  /\ president' = p /\ vicePresident' = v /\ inability' = "None"
  /\ UNCHANGED <<agencyVars, otherVars, impVars>>

\* Amend. XXV sec. 3: the President declares in writing that they are unable.
DeclareInability ==
  /\ president # NoOne /\ vicePresident # NoOne
  /\ inability = "None"
  /\ inability' = "SelfDeclared"
  /\ UNCHANGED <<president, vicePresident, agencyVars, otherVars, impVars>>

\* Amend. XXV sec. 4: the VP and a majority of the principal officers declare.
CabinetDeclares(ayes) ==
  /\ president # NoOne /\ vicePresident # NoOne
  /\ inability \in {"None", "Contested"}
  /\ Majority(ayes, Cabinet)
  /\ inability' = IF inability = "None" THEN "CabinetDeclared" ELSE "BeforeCongress"
  /\ UNCHANGED <<president, vicePresident, agencyVars, otherVars, impVars>>

\* The President declares that no inability exists. Under sec. 3 that ends
\* it; under sec. 4 it opens a four-day window for the cabinet to re-declare.
DeclareAble ==
  /\ inability \in {"SelfDeclared", "CabinetDeclared", "Contested"}
  /\ inability' = CASE inability = "SelfDeclared"    -> "None"
                    [] inability = "CabinetDeclared" -> "Contested"
                    [] inability = "Contested"       -> "None"   \* four days passed
  /\ UNCHANGED <<president, vicePresident, agencyVars, otherVars, impVars>>

\* Congress decides within 21 days. Two-thirds of each house keeps the VP
\* acting; anything less, the President resumes.
CongressDecides(h, s) ==
  /\ inability = "BeforeCongress"
  /\ inability' = IF TwoThirds(h, House) /\ TwoThirds(s, Senate)
                    THEN "CabinetDeclared" ELSE "None"
  /\ UNCHANGED <<president, vicePresident, agencyVars, otherVars, impVars>>

\* Death or resignation (Amend. XXV sec. 1). Vacancy-filling is in
\* Constitution.tla; here the VP office simply stays empty.
PresidentVacates ==
  /\ president # NoOne
  /\ president' = vicePresident /\ vicePresident' = NoOne /\ inability' = "None"
  /\ UNCHANGED <<agencyVars, otherVars, impVars>>

-----------------------------------------------------------------------------
(* Congress builds the administrative state - Art. I sec. 8 cl. 18         *)

\* Congress creates an agency, places it in a branch, decides whether it
\* executes the laws, how its inferior officer is appointed, and whether its
\* head is protected from removal.
\*   Buckley:   it may not vest appointment in itself (Vestings has no
\*              "Congress").
\*   Slaughter: for-cause protection only for a body with no executive
\*              power. (From 1935 to 2026 Humphrey's Executor allowed it for
\*              "quasi-legislative, quasi-judicial" bodies too.)
\*   Legislative-branch agencies (GAO, CBO, Library of Congress) and
\*   judicial-branch agencies (Administrative Office, Sentencing Commission)
\*   are real, but Bowsher means they cannot execute the laws.
CreateAgency(a, br, ex, rm, ve, h, s) ==
  /\ Statute(h, s)
  /\ ~Live(a)
  /\ br \in Branches /\ ex \in BOOLEAN /\ rm \in Removal /\ ve \in Vestings
  /\ ex => (br = "Executive")                    \* Bowsher
  /\ (rm = "ForCause") => ~ex                    \* Slaughter
  /\ agency' = [agency EXCEPT ![a] = [Blank EXCEPT !.exists = TRUE, !.branch = br,
                                       !.executesLaw = ex, !.removal = rm,
                                       !.vesting = ve]]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

AbolishAgency(a, h, s) ==
  /\ Statute(h, s)
  /\ Live(a)
  /\ agency' = [agency EXCEPT ![a] = Blank]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

\* Art. I sec. 8 cl. 11
DeclareWar(h, s) ==
  /\ Statute(h, s)
  /\ atWar' = ~atWar
  /\ UNCHANGED <<execVars, agencyVars, inSession, treaty, pardoned, impVars>>

Adjourn == inSession /\ inSession' = FALSE
           /\ UNCHANGED <<execVars, agencyVars, atWar, treaty, pardoned, impVars>>
Convene == ~inSession /\ inSession' = TRUE
           /\ UNCHANGED <<execVars, agencyVars, atWar, treaty, pardoned, impVars>>

\* Art. II sec. 3: the President may convene Congress "on extraordinary
\* Occasions". Same effect as Convene; the point is who may do it.
ConveneByPresident ==
  /\ Executive # NoOne /\ ~inSession
  /\ inSession' = TRUE
  /\ UNCHANGED <<execVars, agencyVars, atWar, treaty, pardoned, impVars>>

-----------------------------------------------------------------------------
(* Appointments - Art. II sec. 2 cl. 2                                     *)

EligibleOfficer(p) ==
  /\ p \notin disqualified
  /\ p \notin Congress                           \* Art. I sec. 6 cl. 2
  /\ p \notin Officers

\* Principal officers: nominated by the President, confirmed by the Senate.
NominateHead(a, p) ==
  /\ Executive # NoOne
  /\ Live(a) /\ agency[a].head = NoOne /\ agency[a].headNominee = NoOne
  /\ EligibleOfficer(p)
  /\ agency' = [agency EXCEPT ![a].headNominee = p]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

ConfirmHead(a, ayes) ==
  /\ agency[a].headNominee # NoOne
  /\ EligibleOfficer(agency[a].headNominee)      \* re-checked at confirmation
  /\ agency[a].head = NoOne
  /\ Majority(ayes, Senate)
  /\ agency' = [agency EXCEPT ![a].head = agency[a].headNominee, ![a].headNominee = NoOne,
                              ![a].acting = NoOne, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

RejectHead(a) ==
  /\ agency[a].headNominee # NoOne
  /\ agency' = [agency EXCEPT ![a].headNominee = NoOne]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

\* Inferior officers: appointed by whoever Congress vested. "Courts" is
\* abstracted as always available.
AppointInferior(a, p) ==
  /\ Live(a) /\ agency[a].inferior = NoOne
  /\ EligibleOfficer(p)
  /\ CASE agency[a].vesting = "President" -> Executive # NoOne
       [] agency[a].vesting = "Head"      -> agency[a].head # NoOne
       [] agency[a].vesting = "Courts"    -> TRUE
  /\ agency' = [agency EXCEPT ![a].inferior = p]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

\* FVRA: when the head is vacant the inferior (first assistant) may act,
\* for a limited time.
ActAsHead(a) ==
  /\ Live(a) /\ agency[a].head = NoOne /\ agency[a].acting = NoOne
  /\ agency[a].inferior # NoOne
  /\ agency' = [agency EXCEPT ![a].acting = agency[a].inferior, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

ActingTick(a) ==
  /\ agency[a].acting # NoOne /\ agency[a].actingDays < ActingLimit
  /\ agency' = [agency EXCEPT ![a].actingDays = @ + 1]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

ActingExpires(a) ==
  /\ agency[a].acting # NoOne /\ agency[a].actingDays = ActingLimit
  /\ agency' = [agency EXCEPT ![a].acting = NoOne, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

-----------------------------------------------------------------------------
(* Removal                                                                 *)

\* The President removes a principal officer. At will for an agency that
\* executes the laws (Myers, Seila Law, Slaughter); only for cause where
\* Congress said so and could; never for an officer of another branch.
PresidentRemovesHead(a, cause) ==
  /\ Executive # NoOne
  /\ Live(a) /\ agency[a].head # NoOne
  /\ agency[a].branch = "Executive"
  /\ (agency[a].removal = "ForCause") => cause
  /\ agency' = [agency EXCEPT ![a].head = NoOne]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

PresidentRemovesInferior(a) ==
  /\ Executive # NoOne
  /\ Live(a) /\ agency[a].inferior # NoOne
  /\ agency[a].branch = "Executive"
  /\ agency' = [agency EXCEPT ![a].inferior = NoOne,
                              ![a].acting = IF agency[a].acting = agency[a].inferior THEN NoOne ELSE agency[a].acting]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

\* Bowsher: Congress may remove, other than by impeachment, only an officer
\* of its own branch, who by construction does not execute the laws.
CongressRemovesHead(a, h, s) ==
  /\ Statute(h, s)
  /\ Live(a) /\ agency[a].head # NoOne
  /\ agency[a].branch = "Legislative"
  /\ agency' = [agency EXCEPT ![a].head = NoOne]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

Resign(a) ==
  /\ Live(a) /\ agency[a].head # NoOne
  /\ agency' = [agency EXCEPT ![a].head = NoOne]
  /\ UNCHANGED <<execVars, otherVars, impVars>>

\* Art. II sec. 4: impeachment reaches every civil officer.
Impeach(p, ayes) ==
  /\ p \in Officers /\ p \notin impeached
  /\ Majority(ayes, House)
  /\ impeached' = impeached \cup {p}
  /\ UNCHANGED <<execVars, agencyVars, otherVars, disqualified>>

Convict(p, ayes, dq) ==
  /\ p \in impeached
  /\ TwoThirds(ayes, Senate)
  /\ impeached' = impeached \ {p}
  /\ disqualified' = IF dq THEN disqualified \cup {p} ELSE disqualified
  /\ IF p = president
       THEN president' = vicePresident /\ vicePresident' = NoOne /\ inability' = "None"
       ELSE IF p = vicePresident
         THEN president' = president /\ vicePresident' = NoOne /\ inability' = "None"
         ELSE UNCHANGED execVars
  /\ agency' = [a \in Agencies |->
                 [agency[a] EXCEPT !.head = IF @ = p THEN NoOne ELSE @,
                                   !.headNominee = IF @ = p THEN NoOne ELSE @,
                                   !.inferior = IF @ = p THEN NoOne ELSE @,
                                   !.acting = IF @ = p THEN NoOne ELSE @]]
  /\ UNCHANGED otherVars

Acquit(p) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ UNCHANGED <<execVars, agencyVars, otherVars, disqualified>>

-----------------------------------------------------------------------------
(* Other Article II powers                                                 *)

\* Art. II sec. 2 cl. 1: "Offences against the United States, except in
\* Cases of Impeachment". State crimes are not the President's to pardon.
Pardon(p, k) ==
  /\ Executive # NoOne
  /\ k = "Federal"
  /\ pardoned' = pardoned \cup {<<p, k>>}
  /\ UNCHANGED <<execVars, agencyVars, inSession, atWar, treaty, impVars>>

\* Art. II sec. 2 cl. 2: treaties need two-thirds of the Senators present.
Negotiate(t) ==
  /\ Executive # NoOne /\ treaty[t] = "None"
  /\ treaty' = [treaty EXCEPT ![t] = "Negotiated"]
  /\ UNCHANGED <<execVars, agencyVars, inSession, atWar, pardoned, impVars>>

RatifyTreaty(t, ayes) ==
  /\ treaty[t] = "Negotiated"
  /\ TwoThirds(ayes, Senate)
  /\ treaty' = [treaty EXCEPT ![t] = "Ratified"]
  /\ UNCHANGED <<execVars, agencyVars, inSession, atWar, pardoned, impVars>>

RejectTreaty(t) ==
  /\ treaty[t] = "Negotiated"
  /\ treaty' = [treaty EXCEPT ![t] = "None"]
  /\ UNCHANGED <<execVars, agencyVars, inSession, atWar, pardoned, impVars>>

-----------------------------------------------------------------------------
Next ==
  \/ \E p, v \in Persons : Elect(p, v)
  \/ DeclareInability \/ DeclareAble \/ PresidentVacates
  \/ \E n \in 0..Cardinality(Persons) : CabinetDeclares(n)
  \/ \E h \in HouseVotes, s \in SenateVotes :
       \/ CongressDecides(h, s)
       \/ DeclareWar(h, s)
       \/ \E a \in Agencies :
            \/ \E br \in Branches, ex \in BOOLEAN, rm \in Removal, ve \in Vestings :
                 CreateAgency(a, br, ex, rm, ve, h, s)
            \/ AbolishAgency(a, h, s)
            \/ CongressRemovesHead(a, h, s)
  \/ Adjourn \/ Convene \/ ConveneByPresident
  \/ \E a \in Agencies :
       \/ \E p \in Persons : NominateHead(a, p) \/ AppointInferior(a, p)
       \/ \E n \in SenateVotes : ConfirmHead(a, n)
       \/ RejectHead(a) \/ ActAsHead(a) \/ ActingTick(a) \/ ActingExpires(a)
       \/ \E c \in BOOLEAN : PresidentRemovesHead(a, c)
       \/ PresidentRemovesInferior(a) \/ Resign(a)
  \/ \E p \in Persons :
       \/ \E n \in HouseVotes : Impeach(p, n)
       \/ \E n \in SenateVotes, dq \in BOOLEAN : Convict(p, n, dq)
       \/ Acquit(p)
       \/ \E k \in Offences : Pardon(p, k)
  \/ \E t \in Treaties :
       \/ Negotiate(t) \/ RejectTreaty(t)
       \/ \E n \in SenateVotes : RatifyTreaty(t, n)

Spec == Init /\ [][Next]_vars
             /\ \A a \in Agencies : WF_vars(ActingTick(a)) /\ WF_vars(ActingExpires(a))

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* Art. II sec. 1: one President. The VP acts only while there is both a
\* President to be unable and a VP to act.
OneExecutive ==
  /\ president = NoOne \/ president # vicePresident
  /\ Acting => (president # NoOne /\ vicePresident # NoOne)

\* Art. I sec. 6 cl. 2 and Art. I sec. 3 cl. 7
Incompatibility == Officers \cap Congress = {}
Disqualification == Officers \cap disqualified = {}

\* Appointments Clause: a principal officer got there by advice and consent
\* (enforced by construction - only ConfirmHead fills head); an acting
\* officer is never counted as the head.
ActingIsNotHead ==
  \A a \in Agencies : Live(a) => (agency[a].acting = NoOne \/ agency[a].head = NoOne)

\* FVRA time limit
ActingIsTemporary ==
  \A a \in Agencies : agency[a].acting # NoOne => agency[a].actingDays <= ActingLimit

\* Buckley: Congress never appoints.  (Vestings excludes it, so this is
\* definitional; stated anyway so a future edit cannot quietly add it.)
NoCongressionalAppointment ==
  \A a \in Agencies : agency[a].vesting \in {"President", "Head", "Courts"}

\* Bowsher: whoever executes the laws sits in the Executive branch.
ExecutionIsExecutive ==
  \A a \in Agencies : (Live(a) /\ agency[a].executesLaw) => agency[a].branch = "Executive"

\* Slaughter: no for-cause protection for an officer wielding executive
\* power. (Under Humphrey's Executor this invariant would have failed.)
UnitaryExecutive ==
  \A a \in Agencies : (Live(a) /\ agency[a].executesLaw) => agency[a].removal = "AtWill"

\* Art. II sec. 2 cl. 1
PardonScope ==
  \A pk \in pardoned : pk[2] = "Federal"

Safety ==
  /\ OneExecutive /\ Incompatibility /\ Disqualification
  /\ ActingIsNotHead /\ ActingIsTemporary /\ NoCongressionalAppointment
  /\ ExecutionIsExecutive /\ UnitaryExecutive /\ PardonScope

-----------------------------------------------------------------------------
(* Action properties                                                       *)

\* Art. I sec. 8 cl. 11: only a statute changes the state of war.
WarIsCongressional ==
  [][atWar' # atWar => \E h \in HouseVotes, s \in SenateVotes : DeclareWar(h, s)]_vars

\* Bowsher: an officer who executes the laws leaves office only by the
\* President's hand, resignation, impeachment, or abolition of the office -
\* never by an act of Congress short of impeachment.
CongressDoesNotRemoveExecutors ==
  [][\A a \in Agencies :
       (Live(a) /\ agency[a].executesLaw /\ agency[a].head # NoOne
        /\ agency'[a].head = NoOne) =>
         \/ \E c \in BOOLEAN : PresidentRemovesHead(a, c)
         \/ Resign(a)
         \/ \E n \in SenateVotes, dq \in BOOLEAN : Convict(agency[a].head, n, dq)
         \/ \E h \in HouseVotes, s \in SenateVotes : AbolishAgency(a, h, s)]_vars

-----------------------------------------------------------------------------
(* Liveness                                                                *)

\* Take Care Clause, read as an obligation: a vacancy filled by an acting
\* officer does not become a permanent end-run around the Senate.
ActingEventuallyEnds ==
  \A a \in Agencies : (agency[a].acting # NoOne) ~> (agency[a].acting = NoOne)

=============================================================================
