----------------------------- MODULE Executive -----------------------------
(****************************************************************************)
(* Article II and the administrative state.                                 *)
(*                                                                          *)
(* THE CONSTITUTION CREATES NO BUREAUS. Art. II refers to "executive        *)
(* Departments" and "the principal Officer in each", and the Appointments   *)
(* Clause to offices "which shall be established by Law", but every         *)
(* department, agency and commission is a creature of statute, so Init has  *)
(* none. Congress creates them, and the model asks what the cases ask: who  *)
(* appoints their officers, who may remove them, and which branch they      *)
(* belong to. Companion to Constitution.tla (presentment, veto, recess      *)
(* appointments, XXII, XXV secs. 1-2) and Judiciary.tla.                    *)
(*                                                                          *)
(* PROPERTIES (safety; each an invariant, local as noted)                   *)
(*   OneExecutive        Art. II s.1, Amend. XXV ss.3-4: President and Vice *)
(*                       President are two people, and the VP acts only     *)
(*                       while there is a President to be unable and a VP   *)
(*                       to act. State predicate decided by Elect's and     *)
(*                       DeclareInability's guards.                         *)
(*   Incompatibility     Art. I s.6 cl.2: no officer sits in Congress.      *)
(*                       State predicate decided by EligibleOfficer at      *)
(*                       every appointment (Elect, ConfirmHead,             *)
(*                       AppointInferior), the only actions that seat       *)
(*                       someone new.                                       *)
(*   Disqualification    Art. I s.3 cl.7: no one disqualified on            *)
(*                       conviction holds office. As above, and Convict     *)
(*                       unseats the convicted from every office.           *)
(*   ActingIsNotHead     FVRA, 5 U.S.C. 3345(a): an acting officer serves   *)
(*                       only in a vacant office. Decided by ActAsHead.     *)
(*   ActingIsTemporary   FVRA, 5 U.S.C. 3346: acting service is limited to  *)
(*                       ActingLimit days (210). Decided by ActingTick.     *)
(*   NoCongressionalAppointment  Buckley v. Valeo (1976): Congress appoints *)
(*                       no officer who executes the laws. Flag set at      *)
(*                       AppointInferior; the guard is at CreateAgency      *)
(*                       (Chartered), which never charters such a body.     *)
(*                       CHANGED: it was "Vestings excludes Congress",      *)
(*                       true by definition; Congress may now be vested     *)
(*                       with appointment (CBO's director is appointed by   *)
(*                       the Speaker and the President pro tempore) and     *)
(*                       the property is about an appointment made.         *)
(*   ExecutionIsExecutive  Bowsher v. Synar (1986): a body that executes    *)
(*                       the laws is in the Executive branch. Decided by    *)
(*                       Chartered.                                         *)
(*   UnitaryExecutive    Trump v. Slaughter (2026): no for-cause removal    *)
(*                       protection for a body that executes the laws.      *)
(*                       Decided by Chartered.                              *)
(*   PardonScope         Art. II s.2 cl.1: pardons for "Offences against    *)
(*                       the United States, except in Cases of              *)
(*                       Impeachment". Over the append-only set pardoned.   *)
(*   WarIsCongressional  Art. I s.8 cl.11: the state of war changes only by *)
(*                       statute. CHANGED from an action property to a flag *)
(*                       set by DeclareWar when no statute passed.          *)
(*   CongressDoesNotRemoveExecutors  Bowsher: Congress removes, short of    *)
(*                       impeachment, no officer who executes the laws.     *)
(*                       CHANGED from an action property to a flag set by   *)
(*                       CongressRemovesHead; the guard (OwnOfficer) lets   *)
(*                       Congress remove only officers of its own branch,   *)
(*                       so the property also rests on ExecutionIsExecutive.*)
(*   TreatiesByTwoThirds Art. II s.2 cl.2: no treaty without two-thirds of  *)
(*                       the Senators present. Flag set by RatifyTreaty.    *)
(*   Safety              the conjunction of the twelve.                     *)
(* LIVENESS                                                                 *)
(*   ActingEventuallyEnds  Take Care Clause read with the FVRA: an acting   *)
(*                       officer's service ends. Under SpecLive only        *)
(*                       (fairness below); Spec has none.                   *)
(*                                                                          *)
(* MUTATIONS (Mut; one guard each; "breaks" is what TLC must show)          *)
(*   M_SAMEPERSON     Elect without p # v: one person President and Vice    *)
(*                    President. Breaks OneExecutive; and Disqualification, *)
(*                    since convicting that person passes the office to     *)
(*                    themself. No earlier text.                            *)
(*   M_NOVP           DeclareInability without a Vice President in office;  *)
(*                    the executive power falls to no one. Breaks           *)
(*                    OneExecutive. No earlier text.                        *)
(*   M_PLACEMEN       EligibleOfficer without the Incompatibility check:    *)
(*                    the British practice of placemen, Crown officers      *)
(*                    sitting in the Commons, that Art. I s.6 cl.2 was      *)
(*                    written against. Breaks Incompatibility.              *)
(*   M_DISQUAL        EligibleOfficer without the disqualification check: a *)
(*                    judgment of disqualification bars nothing. Breaks     *)
(*                    Disqualification. No earlier text.                    *)
(*   M_ACTWHILEFILLED ActAsHead without the vacancy check: an acting        *)
(*                    officer beside a confirmed head. Breaks               *)
(*                    ActingIsNotHead. No earlier text.                     *)
(*   M_PREFVRA        ActingTick without the limit: acting service with no  *)
(*                    end, the reading (organic statutes displace the       *)
(*                    Vacancies Act's limit) that the FVRA of 1998 was      *)
(*                    enacted to end. Breaks ActingIsTemporary.             *)
(*   M_FECA           Chartered without the Buckley check: appointment of   *)
(*                    officers who execute the laws vested in Congress, as  *)
(*                    in the FEC as first constituted (FECA amendments of   *)
(*                    1974). Breaks NoCongressionalAppointment.             *)
(*   M_GRH            Chartered without the Bowsher check: execution of the *)
(*                    laws given to a legislative-branch officer, as the    *)
(*                    Gramm-Rudman-Hollings Act (1985) gave it to the       *)
(*                    Comptroller General. Breaks ExecutionIsExecutive, and *)
(*                    CongressDoesNotRemoveExecutors, since Congress may    *)
(*                    remove its own officers: Bowsher's facts.             *)
(*   M_JOINTRES       CongressRemovesHead without OwnOfficer: Congress      *)
(*                    removes by joint resolution the head of any agency,   *)
(*                    the removal power the Budget and Accounting Act of    *)
(*                    1921 kept over the Comptroller General, not confined  *)
(*                    to Congress's own officers. Breaks                    *)
(*                    CongressDoesNotRemoveExecutors.                       *)
(*   M_HUMPHREY       Chartered without the Slaughter check: for-cause      *)
(*                    protection for a body that executes the laws, the law *)
(*                    from Humphrey's Executor (1935) until Trump v.        *)
(*                    Slaughter (2026). Breaks UnitaryExecutive.            *)
(*   M_DANBY          PardonReaches without the impeachment exception: the  *)
(*                    pardon Charles II gave the Earl of Danby (1679) to    *)
(*                    stop his impeachment, which the Act of Settlement     *)
(*                    (1701) made unpleadable and Art. II excepts. Breaks   *)
(*                    PardonScope.                                          *)
(*   M_STATECRIME     PardonReaches without the federal-offence check: the  *)
(*                    pardon reaches State crimes. No earlier text. Breaks  *)
(*                    PardonScope.                                          *)
(*   M_PREROGATIVE    WarAuthorised lets the President alone declare war,   *)
(*                    the Crown's prerogative of war and peace that Art. I  *)
(*                    s.8 cl.11 gave to Congress. Breaks WarIsCongressional.*)
(*   M_AUG6           TreatyVote is a simple majority, as in the Committee  *)
(*                    of Detail's draft of 6 August 1787 ("The Senate ...   *)
(*                    shall have power to make treaties"); two-thirds came  *)
(*                    in September. Breaks TreatiesByTwoThirds.             *)
(* Every other (mutation, property) pair must HOLD; the TLC results file    *)
(* runs each one, and Executive_proof.tla proves each property under        *)
(* exactly the mutations above that break it.                               *)
(*                                                                          *)
(* DEADLOCK: no state is terminal (Congress can always adjourn or           *)
(* convene), so TLC's -deadlock flag hides nothing; a stall would be a      *)
(* livelock, and the one progress claim the text makes is                   *)
(* ActingEventuallyEnds.                                                    *)
(*                                                                          *)
(* REACHABILITY WITNESSES (Never..., each must be VIOLATED under "none"):   *)
(* an agency created and one abolished, a head confirmed and one removed    *)
(* by the President, Congress removing its own officer, an acting officer   *)
(* serving and timing out, Congress appointing (a non-executing body's      *)
(* officer), a for-cause-protected head, a disqualification, a voluntary    *)
(* and an involuntary inability declaration, a contest before Congress      *)
(* sustained and one lost, the VP succeeding, war declared, a treaty        *)
(* ratified, a pardon, the President convening Congress.                    *)
(*                                                                          *)
(* ABSTRACTED: elections and the Electoral College (Elect picks a ticket);  *)
(* presentment (a statute is the act of Congress passing it); vote counts   *)
(* (a vote is the strongest threshold it meets, Votes; an action that needs *)
(* a vote and has no Votes parameter is the vote that passes); the XXV      *)
(* four- and twenty-one-day windows (nondeterministic choice); who is       *)
(* pardoned (a pardon is recorded by the offence it reaches); treaty        *)
(* negotiation detail; the Senate tries one impeachment at a time; courts   *)
(* and congressional appointers are always available; time, as an acting    *)
(* officer's day count that ActingTick may advance at any moment. The       *)
(* statutes Congress may attempt are the constant Charters; the rows use    *)
(* KnownCharters, six real ones, through `CONSTANT Charters <-              *)
(* KnownCharters`. The Federal Reserve, which Slaughter left alone, and the *)
(* Youngstown framework are not modelled.                                   *)
(****************************************************************************)
EXTENDS Naturals

CONSTANTS
  Mut,             \* "none", or the one mutation in force
  Persons, House, Senate,
  Eligible,        \* Persons eligible to be President
  Agencies,        \* Pool of agency identifiers Congress may bring to life
  Treaties,        \* Treaty identifiers
  Charters,        \* Statutes creating an agency that Congress may attempt
  ActingLimit,     \* Days an acting officer may serve (FVRA: 210)
  NoOne

Mutations ==
  {"none", "M_SAMEPERSON", "M_NOVP", "M_PLACEMEN", "M_DISQUAL",
   "M_ACTWHILEFILLED", "M_PREFVRA", "M_FECA", "M_GRH", "M_JOINTRES",
   "M_HUMPHREY", "M_DANBY", "M_STATECRIME", "M_PREROGATIVE", "M_AUG6"}

Branches == {"Executive", "Legislative", "Judicial"}
Removal  == {"AtWill", "ForCause"}
\* Who appoints the agency's inferior officer. Art. II s.2 cl.2 lets Congress
\* vest it "in the President alone, in the Courts of Law, or in the Heads of
\* Departments"; a statute may also try Congress itself (Buckley).
Vestings == {"President", "Head", "Courts", "Congress"}
CharterRecord ==
  [branch : Branches, executesLaw : BOOLEAN, removal : Removal, vesting : Vestings]

\* Well-formedness of the constants; TLC checks them against each config and
\* the proof cites them by name. ActingLimit is a number of days; nothing
\* needs it positive (0 means acting service ends at once).
ASSUME MutKnown      == Mut \in Mutations
ASSUME CongressWF    == House \subseteq Persons /\ Senate \subseteq Persons
                        /\ House \cap Senate = {}
ASSUME EligibleWF    == Eligible \subseteq Persons
ASSUME NoOneWF       == NoOne \notin Persons
ASSUME ChartersWF    == Charters \subseteq CharterRecord
ASSUME ActingLimitWF == ActingLimit \in Nat

-----------------------------------------------------------------------------
Congress == House \cup Senate
Seat     == Persons \cup {NoOne}

\* A vote, abstracted to the strongest threshold it meets (for a vote of both
\* houses, the threshold met in each).
Votes == {"Fails", "Majority", "TwoThirds"}
Majority(v)  == v \in {"Majority", "TwoThirds"}
TwoThirds(v) == v = "TwoThirds"

Offences == {"Federal", "State", "Impeachment"}

\* Amend. XXV ss.3-4
Inability == {"None",              \* the President exercises the office
              "SelfDeclared",      \* s.3: the President wrote to Congress
              "CabinetDeclared",   \* s.4: VP and a majority of principal officers
              "Contested",         \* the President wrote that no inability
                                   \*   exists; four days to re-declare
              "BeforeCongress"}    \* they did; Congress decides, two-thirds each
TreatyStates == {"None", "Negotiated", "Ratified"}

\* Six statutes, for the rows (CONSTANT Charters <- KnownCharters). The first
\* three are constitutional; each of the last three is refused by one check
\* in Chartered, and admitted by the mutation that removes it.
KnownCharters ==
  { \* an executive department; the Secretary appoints inferior officers
    [branch |-> "Executive",   executesLaw |-> TRUE,  removal |-> "AtWill",   vesting |-> "Head"],
    \* CBO: a legislative-branch body, director chosen by Congress's leaders
    [branch |-> "Legislative", executesLaw |-> FALSE, removal |-> "AtWill",   vesting |-> "Congress"],
    \* the Sentencing Commission: judicial branch, members removable for cause
    [branch |-> "Judicial",    executesLaw |-> FALSE, removal |-> "ForCause", vesting |-> "Courts"],
    \* the FTC of Humphrey's Executor (refused since Slaughter)
    [branch |-> "Executive",   executesLaw |-> TRUE,  removal |-> "ForCause", vesting |-> "President"],
    \* the FEC of 1974 (refused by Buckley)
    [branch |-> "Executive",   executesLaw |-> TRUE,  removal |-> "AtWill",   vesting |-> "Congress"],
    \* the Comptroller General under Gramm-Rudman-Hollings (refused by Bowsher)
    [branch |-> "Legislative", executesLaw |-> TRUE,  removal |-> "AtWill",   vesting |-> "President"] }

-----------------------------------------------------------------------------
VARIABLES
  president,
  vicePresident,
  inability,           \* Inability
  inSession,           \* BOOLEAN
  atWar,               \* BOOLEAN
  agency,              \* Agencies -> AgencyRecord
  treaty,              \* Treaties -> TreatyStates
  pardoned,            \* SUBSET Offences: the offences pardons have reached
  impeached,           \* the officer awaiting trial, if any (at most one)
  disqualified,        \* SUBSET Persons
  congressAppointed,   \* Congress appointed an officer who executes the laws
  congressRemoved,     \* Congress removed, short of impeachment, such an officer
  warWithoutStatute,   \* the state of war changed without a statute
  treatyShort          \* a treaty was ratified with less than two-thirds

execVars == <<president, vicePresident, inability>>
sideVars == <<inSession, atWar, treaty, pardoned>>
impVars  == <<impeached, disqualified>>
flagVars == <<congressAppointed, congressRemoved, warWithoutStatute, treatyShort>>
vars     == <<execVars, agency, sideVars, impVars, flagVars>>

AgencyRecord ==
  [exists      : BOOLEAN,
   branch      : Branches,
   executesLaw : BOOLEAN,       \* exercises executive power?
   removal     : Removal,       \* statutory protection for the head
   vesting     : Vestings,      \* who appoints the inferior officer
   head        : Seat,          \* principal officer, Senate-confirmed
   headNominee : Seat,
   acting      : Seat,          \* FVRA acting head while the head is vacant
   actingDays  : Nat,
   inferior    : Seat]          \* one inferior officer (the first assistant)

Blank == [exists |-> FALSE, branch |-> "Executive", executesLaw |-> FALSE,
          removal |-> "AtWill", vesting |-> "President",
          head |-> NoOne, headNominee |-> NoOne, acting |-> NoOne,
          actingDays |-> 0, inferior |-> NoOne]

TypeOK ==
  /\ president \in Seat
  /\ vicePresident \in Seat
  /\ inability \in Inability
  /\ inSession \in BOOLEAN
  /\ atWar \in BOOLEAN
  /\ agency \in [Agencies -> AgencyRecord]
  /\ treaty \in [Treaties -> TreatyStates]
  /\ pardoned \subseteq Offences
  /\ impeached \subseteq Persons
  /\ disqualified \subseteq Persons
  /\ congressAppointed \in BOOLEAN
  /\ congressRemoved \in BOOLEAN
  /\ warWithoutStatute \in BOOLEAN
  /\ treatyShort \in BOOLEAN

\* Whoever holds "the executive Power" now (Amend. XXV: the VP as Acting
\* President has all of it).
Acting    == inability # "None"
Executive == IF Acting THEN vicePresident ELSE president

Live(a) == agency[a].exists

InOffice(x) ==
  \/ x = president
  \/ x = vicePresident
  \/ \E a \in Agencies : Live(a) /\ x \in {agency[a].head, agency[a].inferior, agency[a].acting}
Officers == {x \in Persons : InOffice(x)}

\* "the principal officers of the executive departments" (Amend. XXV s.4)
Cabinet == {x \in Persons : \E a \in Agencies :
              Live(a) /\ agency[a].branch = "Executive" /\ agency[a].head = x}

-----------------------------------------------------------------------------
(* The checks. Each is one guard, and Mut = <its mutation> removes it.      *)

TwoPeople(p, v)    == IF Mut = "M_SAMEPERSON" THEN TRUE ELSE p # v
VPToAct            == IF Mut = "M_NOVP" THEN TRUE ELSE vicePresident # NoOne
NotMember(p)       == IF Mut = "M_PLACEMEN" THEN TRUE ELSE p \notin Congress
NotDisqualified(p) == IF Mut = "M_DISQUAL" THEN TRUE ELSE p \notin disqualified
OfficeVacant(a)    == IF Mut = "M_ACTWHILEFILLED" THEN TRUE ELSE agency[a].head = NoOne
WithinLimit(a)     == IF Mut = "M_PREFVRA" THEN TRUE ELSE agency[a].actingDays < ActingLimit
\* What a statute creating an agency may say: three checks, three mutations.
Chartered(c) ==
  /\ IF Mut = "M_GRH"      THEN TRUE ELSE (c.executesLaw => c.branch = "Executive")   \* Bowsher
  /\ IF Mut = "M_HUMPHREY" THEN TRUE ELSE (c.removal = "ForCause" => ~c.executesLaw)  \* Slaughter
  /\ IF Mut = "M_FECA"     THEN TRUE ELSE (c.vesting = "Congress" => ~c.executesLaw)  \* Buckley
OwnOfficer(a)      == IF Mut = "M_JOINTRES" THEN TRUE ELSE agency[a].branch = "Legislative"
PardonReaches(k)   ==
  /\ IF Mut = "M_STATECRIME" THEN TRUE ELSE k # "State"
  /\ IF Mut = "M_DANBY"      THEN TRUE ELSE k # "Impeachment"
WarAuthorised(v)   ==
  IF Mut = "M_PREROGATIVE" THEN Majority(v) \/ Executive # NoOne ELSE Majority(v)
TreatyVote(v)      == IF Mut = "M_AUG6" THEN Majority(v) ELSE TwoThirds(v)

\* Who may be seated in an office: not disqualified (Art. I s.3 cl.7), not a
\* member of Congress (Art. I s.6 cl.2), and holding no other office here.
EligibleOfficer(p) == NotDisqualified(p) /\ NotMember(p) /\ p \notin Officers

\* Whoever the statute vested with appointing the inferior officer is there.
Appointer(a) ==
  CASE agency[a].vesting = "President" -> Executive # NoOne
    [] agency[a].vesting = "Head"      -> agency[a].head # NoOne
    [] agency[a].vesting = "Courts"    -> TRUE
    [] agency[a].vesting = "Congress"  -> TRUE

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
  /\ congressAppointed = FALSE
  /\ congressRemoved = FALSE
  /\ warWithoutStatute = FALSE
  /\ treatyShort = FALSE

-----------------------------------------------------------------------------
(* The office - Art. II s.1, Amend. XXV                                     *)

Elect(p, v) ==
  /\ p \in Eligible /\ v \in Eligible /\ TwoPeople(p, v)
  /\ EligibleOfficer(p) /\ EligibleOfficer(v)
  /\ president' = p /\ vicePresident' = v /\ inability' = "None"
  /\ UNCHANGED <<agency, sideVars, impVars, flagVars>>

\* s.3: the President declares in writing that they are unable.
DeclareInability ==
  /\ president # NoOne /\ VPToAct
  /\ inability = "None"
  /\ inability' = "SelfDeclared"
  /\ UNCHANGED <<president, vicePresident, agency, sideVars, impVars, flagVars>>

\* s.4: the VP and a majority of the principal officers declare.
CabinetDeclares ==
  /\ president # NoOne /\ vicePresident # NoOne
  /\ Cabinet # {}
  /\ inability \in {"None", "Contested"}
  /\ inability' = IF inability = "None" THEN "CabinetDeclared" ELSE "BeforeCongress"
  /\ UNCHANGED <<president, vicePresident, agency, sideVars, impVars, flagVars>>

\* The President declares that no inability exists: under s.3 that ends it;
\* under s.4 it opens four days for the VP and cabinet to re-declare; if
\* they let the four days pass, the President resumes.
DeclareAble ==
  /\ inability \in {"SelfDeclared", "CabinetDeclared", "Contested"}
  /\ inability' = IF inability = "CabinetDeclared" THEN "Contested" ELSE "None"
  /\ UNCHANGED <<president, vicePresident, agency, sideVars, impVars, flagVars>>

\* Congress decides within 21 days: two-thirds of each house keeps the VP
\* acting; anything less, the President resumes.
CongressDecides(v) ==
  /\ inability = "BeforeCongress"
  /\ inability' = IF TwoThirds(v) THEN "CabinetDeclared" ELSE "None"
  /\ UNCHANGED <<president, vicePresident, agency, sideVars, impVars, flagVars>>

\* Death or resignation (s.1). Filling the VP vacancy (s.2) is in
\* Constitution.tla; here it stays empty.
PresidentVacates ==
  /\ president # NoOne
  /\ president' = vicePresident /\ vicePresident' = NoOne /\ inability' = "None"
  /\ UNCHANGED <<agency, sideVars, impVars, flagVars>>

-----------------------------------------------------------------------------
(* Congress builds the administrative state - Art. I s.8 cl.18              *)

CreateAgency(a, c) ==
  /\ ~Live(a)
  /\ Chartered(c)
  /\ agency' = [agency EXCEPT ![a] = [Blank EXCEPT !.exists = TRUE, !.branch = c.branch,
                                       !.executesLaw = c.executesLaw,
                                       !.removal = c.removal, !.vesting = c.vesting]]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

AbolishAgency(a) ==
  /\ Live(a)
  /\ agency' = [agency EXCEPT ![a] = Blank]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

-----------------------------------------------------------------------------
(* Appointments - Art. II s.2 cl.2                                          *)

\* Principal officers: nominated by the President, confirmed by the Senate.
NominateHead(a, p) ==
  /\ Executive # NoOne
  /\ Live(a) /\ agency[a].head = NoOne /\ agency[a].headNominee = NoOne
  /\ EligibleOfficer(p)
  /\ agency' = [agency EXCEPT ![a].headNominee = p]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

\* A majority of the Senate consents; eligibility is checked again here.
ConfirmHead(a) ==
  /\ Live(a) /\ agency[a].headNominee # NoOne /\ agency[a].head = NoOne
  /\ EligibleOfficer(agency[a].headNominee)
  /\ agency' = [agency EXCEPT ![a].head = agency[a].headNominee, ![a].headNominee = NoOne,
                              ![a].acting = NoOne, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

RejectHead(a) ==
  /\ agency[a].headNominee # NoOne
  /\ agency' = [agency EXCEPT ![a].headNominee = NoOne]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

\* Inferior officers: appointed by whoever the statute vested.
AppointInferior(a, p) ==
  /\ Live(a) /\ agency[a].inferior = NoOne
  /\ EligibleOfficer(p) /\ Appointer(a)
  /\ agency' = [agency EXCEPT ![a].inferior = p]
  /\ congressAppointed' = (congressAppointed \/
                            (agency[a].vesting = "Congress" /\ agency[a].executesLaw))
  /\ UNCHANGED <<execVars, sideVars, impVars, congressRemoved, warWithoutStatute, treatyShort>>

\* FVRA: while the head is vacant the first assistant acts, for a limited time.
ActAsHead(a) ==
  /\ Live(a) /\ OfficeVacant(a) /\ agency[a].acting = NoOne
  /\ agency[a].inferior # NoOne
  /\ agency' = [agency EXCEPT ![a].acting = agency[a].inferior, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

ActingTick(a) ==
  /\ agency[a].acting # NoOne /\ WithinLimit(a)
  /\ agency' = [agency EXCEPT ![a].actingDays = @ + 1]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

ActingExpires(a) ==
  /\ agency[a].acting # NoOne /\ agency[a].actingDays = ActingLimit
  /\ agency' = [agency EXCEPT ![a].acting = NoOne, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

-----------------------------------------------------------------------------
(* Removal                                                                  *)

\* At will, or for cause where the statute says so; only in the Executive
\* branch (Myers, Seila Law, Slaughter).
PresidentRemovesHead(a, cause) ==
  /\ Executive # NoOne
  /\ Live(a) /\ agency[a].head # NoOne
  /\ agency[a].branch = "Executive"
  /\ (agency[a].removal = "ForCause") => cause
  /\ agency' = [agency EXCEPT ![a].head = NoOne]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

\* Removing the first assistant also ends their acting service.
PresidentRemovesInferior(a) ==
  /\ Executive # NoOne
  /\ Live(a) /\ agency[a].inferior # NoOne
  /\ agency[a].branch = "Executive"
  /\ agency' = [agency EXCEPT ![a].inferior = NoOne, ![a].acting = NoOne, ![a].actingDays = 0]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

\* By statute (joint resolution), short of impeachment: only an officer of
\* Congress's own branch (Bowsher).
CongressRemovesHead(a) ==
  /\ Live(a) /\ agency[a].head # NoOne
  /\ OwnOfficer(a)
  /\ agency' = [agency EXCEPT ![a].head = NoOne]
  /\ congressRemoved' = (congressRemoved \/ agency[a].executesLaw)
  /\ UNCHANGED <<execVars, sideVars, impVars, congressAppointed, warWithoutStatute, treatyShort>>

Resign(a) ==
  /\ Live(a) /\ agency[a].head # NoOne
  /\ agency' = [agency EXCEPT ![a].head = NoOne]
  /\ UNCHANGED <<execVars, sideVars, impVars, flagVars>>

-----------------------------------------------------------------------------
(* Impeachment - Art. I ss.2-3, Art. II s.4: every civil officer            *)

\* An agency record with p taken out of every seat.
Purge(r, p) ==
  [r EXCEPT !.head        = IF r.head = p THEN NoOne ELSE r.head,
            !.headNominee = IF r.headNominee = p THEN NoOne ELSE r.headNominee,
            !.inferior    = IF r.inferior = p THEN NoOne ELSE r.inferior,
            !.acting      = IF r.acting = p THEN NoOne ELSE r.acting,
            !.actingDays  = IF r.acting = p THEN 0 ELSE r.actingDays]

\* A majority of the House impeaches.
Impeach(p) ==
  /\ p \in Officers /\ impeached = {}
  /\ impeached' = {p}
  /\ UNCHANGED <<execVars, agency, sideVars, disqualified, flagVars>>

\* Two-thirds of the Senate convict; removal from every office follows, and
\* the judgment may extend to disqualification (dq).
Convict(p, dq) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ disqualified' = IF dq THEN disqualified \cup {p} ELSE disqualified
  /\ president' = IF p = president THEN vicePresident ELSE president
  /\ vicePresident' = IF p \in {president, vicePresident} THEN NoOne ELSE vicePresident
  /\ inability' = IF p \in {president, vicePresident} THEN "None" ELSE inability
  /\ agency' = [a \in Agencies |-> Purge(agency[a], p)]
  /\ UNCHANGED <<sideVars, flagVars>>

Acquit(p) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ UNCHANGED <<execVars, agency, sideVars, disqualified, flagVars>>

-----------------------------------------------------------------------------
(* Other powers                                                             *)

\* Art. I s.8 cl.11: declaring war (or, by the same route, peace).
DeclareWar(v) ==
  /\ WarAuthorised(v)
  /\ atWar' = ~atWar
  /\ warWithoutStatute' = (warWithoutStatute \/ ~Majority(v))
  /\ UNCHANGED <<execVars, agency, inSession, treaty, pardoned, impVars,
                 congressAppointed, congressRemoved, treatyShort>>

Adjourn == /\ inSession /\ inSession' = FALSE
           /\ UNCHANGED <<execVars, agency, atWar, treaty, pardoned, impVars, flagVars>>
Convene == /\ ~inSession /\ inSession' = TRUE
           /\ UNCHANGED <<execVars, agency, atWar, treaty, pardoned, impVars, flagVars>>

\* Art. II s.3: the President may convene Congress "on extraordinary
\* Occasions". Same effect as Convene; the point is who may do it.
ConveneByPresident ==
  /\ Executive # NoOne /\ ~inSession
  /\ inSession' = TRUE
  /\ UNCHANGED <<execVars, agency, atWar, treaty, pardoned, impVars, flagVars>>

\* Art. II s.2 cl.1
Pardon(k) ==
  /\ Executive # NoOne
  /\ PardonReaches(k)
  /\ pardoned' = pardoned \cup {k}
  /\ UNCHANGED <<execVars, agency, inSession, atWar, treaty, impVars, flagVars>>

\* Art. II s.2 cl.2
Negotiate(t) ==
  /\ Executive # NoOne /\ treaty[t] = "None"
  /\ treaty' = [treaty EXCEPT ![t] = "Negotiated"]
  /\ UNCHANGED <<execVars, agency, inSession, atWar, pardoned, impVars, flagVars>>

RatifyTreaty(t, v) ==
  /\ treaty[t] = "Negotiated"
  /\ TreatyVote(v)
  /\ treaty' = [treaty EXCEPT ![t] = "Ratified"]
  /\ treatyShort' = (treatyShort \/ ~TwoThirds(v))
  /\ UNCHANGED <<execVars, agency, inSession, atWar, pardoned, impVars,
                 congressAppointed, congressRemoved, warWithoutStatute>>

RejectTreaty(t) ==
  /\ treaty[t] = "Negotiated"
  /\ treaty' = [treaty EXCEPT ![t] = "None"]
  /\ UNCHANGED <<execVars, agency, inSession, atWar, pardoned, impVars, flagVars>>

-----------------------------------------------------------------------------
OfficeSteps ==
  \/ \E p, v \in Persons : Elect(p, v)
  \/ DeclareInability
  \/ CabinetDeclares
  \/ DeclareAble
  \/ \E v \in Votes : CongressDecides(v)
  \/ PresidentVacates

AgencySteps ==
  \/ \E a \in Agencies, c \in Charters : CreateAgency(a, c)
  \/ \E a \in Agencies : AbolishAgency(a)
  \/ \E a \in Agencies, p \in Persons : NominateHead(a, p)
  \/ \E a \in Agencies : ConfirmHead(a)
  \/ \E a \in Agencies : RejectHead(a)
  \/ \E a \in Agencies, p \in Persons : AppointInferior(a, p)
  \/ \E a \in Agencies : ActAsHead(a)
  \/ \E a \in Agencies : ActingTick(a)
  \/ \E a \in Agencies : ActingExpires(a)
  \/ \E a \in Agencies, c \in BOOLEAN : PresidentRemovesHead(a, c)
  \/ \E a \in Agencies : PresidentRemovesInferior(a)
  \/ \E a \in Agencies : CongressRemovesHead(a)
  \/ \E a \in Agencies : Resign(a)

TrialSteps ==
  \/ \E p \in Persons : Impeach(p)
  \/ \E p \in Persons, dq \in BOOLEAN : Convict(p, dq)
  \/ \E p \in Persons : Acquit(p)

OtherSteps ==
  \/ \E v \in Votes : DeclareWar(v)
  \/ Adjourn
  \/ Convene
  \/ ConveneByPresident
  \/ \E k \in Offences : Pardon(k)
  \/ \E t \in Treaties : Negotiate(t)
  \/ \E t \in Treaties, v \in Votes : RatifyTreaty(t, v)
  \/ \E t \in Treaties : RejectTreaty(t)

Next == OfficeSteps \/ AgencySteps \/ TrialSteps \/ OtherSteps

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                        *)

OneExecutive ==
  /\ president = NoOne \/ president # vicePresident
  /\ Acting => (president # NoOne /\ vicePresident # NoOne)

Incompatibility  == Officers \cap Congress = {}
Disqualification == Officers \cap disqualified = {}

ActingIsNotHead ==
  \A a \in Agencies : Live(a) => (agency[a].acting = NoOne \/ agency[a].head = NoOne)

ActingIsTemporary ==
  \A a \in Agencies : agency[a].acting # NoOne => agency[a].actingDays <= ActingLimit

NoCongressionalAppointment == ~congressAppointed

ExecutionIsExecutive ==
  \A a \in Agencies : (Live(a) /\ agency[a].executesLaw) => agency[a].branch = "Executive"

UnitaryExecutive ==
  \A a \in Agencies : (Live(a) /\ agency[a].executesLaw) => agency[a].removal = "AtWill"

PardonScope == \A k \in pardoned : k = "Federal"

WarIsCongressional == ~warWithoutStatute

CongressDoesNotRemoveExecutors == ~congressRemoved

TreatiesByTwoThirds == ~treatyShort

Safety ==
  /\ OneExecutive /\ Incompatibility /\ Disqualification
  /\ ActingIsNotHead /\ ActingIsTemporary /\ NoCongressionalAppointment
  /\ ExecutionIsExecutive /\ UnitaryExecutive /\ PardonScope
  /\ WarIsCongressional /\ CongressDoesNotRemoveExecutors /\ TreatiesByTwoThirds

-----------------------------------------------------------------------------
(* Reachability witnesses: each must be VIOLATED under Mut = "none".        *)
(* State predicates are INVARIANT rows; [][...]_vars ones, which name a     *)
(* step, are PROPERTY rows.                                                 *)

NeverAgency          == \A a \in Agencies : ~Live(a)
NeverAbolished       == [][\A a \in Agencies : ~AbolishAgency(a)]_vars
NeverHead            == \A a \in Agencies : agency[a].head = NoOne
NeverPresidentRemoves == [][\A a \in Agencies, c \in BOOLEAN : ~PresidentRemovesHead(a, c)]_vars
NeverCongressRemoves == [][\A a \in Agencies : ~CongressRemovesHead(a)]_vars
NeverActing          == \A a \in Agencies : agency[a].acting = NoOne
NeverActingExpires   == [][\A a \in Agencies : ~ActingExpires(a)]_vars
NeverCongressAppoints ==
  \A a \in Agencies : ~(Live(a) /\ agency[a].vesting = "Congress" /\ agency[a].inferior # NoOne)
NeverProtectedHead   ==
  \A a \in Agencies : ~(Live(a) /\ agency[a].removal = "ForCause" /\ agency[a].head # NoOne)
NeverDisqualified    == disqualified = {}
NeverSelfDeclared    == inability # "SelfDeclared"
NeverCabinetDeclared == inability # "CabinetDeclared"
NeverCongressSustains == [][~(inability = "BeforeCongress" /\ inability' = "CabinetDeclared")]_vars
NeverCongressRestores == [][~(inability = "BeforeCongress" /\ inability' = "None")]_vars
NeverSuccession      == [][~PresidentVacates]_vars
NeverWar             == ~atWar
NeverTreaty          == \A t \in Treaties : treaty[t] # "Ratified"
NeverPardon          == pardoned = {}
NeverPresidentConvenes == [][~ConveneByPresident]_vars

-----------------------------------------------------------------------------
(* Liveness - claimed only for acting service                               *)

\* Take Care Clause, read with the FVRA: an acting officer's service ends.
ActingEventuallyEnds ==
  \A a \in Agencies : (agency[a].acting # NoOne) ~> (agency[a].acting = NoOne)

\* Fairness, each an action of Next, named for whose obligation it is. Weak
\* fairness suffices for both: once enabled, each stays enabled until it
\* fires or the acting service ends some other way.
ClockRuns  == \A a \in Agencies : WF_vars(ActingTick(a))     \* the calendar: days pass
LimitBinds == \A a \in Agencies : WF_vars(ActingExpires(a))  \* the Executive ends acting
                                                              \* service at the limit
SpecLive    == Spec /\ ClockRuns /\ LimitBinds
SpecNoClock == Spec /\ LimitBinds        \* drops ClockRuns
SpecNoLimit == Spec /\ ClockRuns         \* drops LimitBinds

\* Violated exactly when the spec has a fair behaviour at all.
NoBehaviour == <>FALSE

\* A space-cutting bound for TLC under M_PREFVRA, whose day count is
\* otherwise unbounded (used as constraint=DaysBound on those rows). Not an
\* assumption: nothing in the proof uses it.
DaysBound == \A a \in Agencies : agency[a].actingDays <= ActingLimit + 1
=============================================================================
