---------------------------- MODULE Constitution ----------------------------
(***************************************************************************)
(* The procedural core of Articles I, II and V of the U.S. Constitution,  *)
(* with Amendments XXII and XXV. An exercise, not law: the state machines *)
(* the text specifies, and the invariants the text guarantees, written so *)
(* that each invariant can be broken by removing one check.                *)
(*                                                                         *)
(* PROPERTIES (each a state predicate over the state below; a "flag" is a *)
(* variable the one violating action would set, and never clears)         *)
(*   Bicameralism      Art. I s.7 cl.2  no bill is presented to the       *)
(*                     President, so none becomes law, unless both Houses *)
(*                     passed it. (Strengthened: it used to say only that *)
(*                     a law passed both Houses; it now says it of every  *)
(*                     presented, returned or enacted bill, which makes   *)
(*                     it inductive. It implies the old statement.)       *)
(*   Origination       Art. I s.7 cl.1  bills for raising revenue          *)
(*                     originate in the House.                             *)
(*   Presentment       Art. I s.7 cl.2  every law was signed, or became   *)
(*                     law unreturned, or was repassed over the veto by   *)
(*                     both Houses, each by two-thirds (flag              *)
(*                     shortOverride: an override vote below two-thirds   *)
(*                     was counted). The two-thirds is new to the         *)
(*                     property; the old one checked only both Houses.    *)
(*   TenDayRule        Art. I s.7 cl.2, last sentence  an unreturned bill *)
(*                     is law if Congress sits when the ten days run out, *)
(*                     and dies only if adjournment prevents its return   *)
(*                     (flag tenDayBreach). New.                          *)
(*   Incompatibility   Art. I s.6 cl.2  no member of Congress holds an    *)
(*                     office of the United States.                       *)
(*   CongressNotImpeachable  Art. II s.4, Blount (1799)  no member of     *)
(*                     Congress is impeached.                             *)
(*   ConvictionTwoThirds  Art. I s.3 cl.6  no conviction without two-     *)
(*                     thirds of the Senate (flag shortConviction). New.  *)
(*   TwoTermLimit      Amend. XXII  no one is elected President more than *)
(*                     twice. (No longer implied by TypeOK: terms is now  *)
(*                     a function into Nat, not into 0..2.)               *)
(*   Disqualification  Art. I s.3 cl.7  no one disqualified on            *)
(*                     conviction holds office.                           *)
(*   PresidentNotVP    Art. II s.1, Amend. XII, XXV  the President and    *)
(*                     the Vice President are two persons.                *)
(*   ArticleV          Art. V  every ratified amendment was ratified by   *)
(*                     three-fourths of the States, and one touching the  *)
(*                     Senate's equal suffrage by every State.            *)
(*   XXVBothHouses     Amend. XXV s.2  no Vice President takes office on  *)
(*                     nomination without a majority of the House as well *)
(*                     as of the Senate (flag vpWithoutHouse). New.       *)
(*   RecessAppointmentsInRecess  Art. II s.2 cl.3  the President fills    *)
(*                     vacancies alone only during the Recess of the      *)
(*                     Senate (flag recessWhileSitting). New.             *)
(*   Safety            the conjunction of the thirteen.                   *)
(*   PresentedBillsResolve (liveness, the only progress the text claims)  *)
(*                     a bill presented to the President is eventually    *)
(*                     law, returned, or dead: the ten-day rule.          *)
(*                                                                         *)
(* MUTATIONS. Mut = "none" is the text. Each other value removes one      *)
(* check, written at the check, and must break the properties named.      *)
(*   M_UNICAMERAL      PassChamber presents a bill once one House passes  *)
(*                     it: the single-chamber Congress of the Articles of *)
(*                     Confederation. Breaks Bicameralism.                *)
(*   M_ORIGIN          Introduce lets a revenue bill start in the Senate: *)
(*                     the Virginia Plan, before the Great Compromise     *)
(*                     added the Origination Clause. Breaks Origination.  *)
(*   M_OVR_ONE_HOUSE   Override makes a vetoed bill law once the House of *)
(*                     origin repasses it. Breaks Presentment.            *)
(*   M_OVR_VOTE        Override counts a House's vote without two-thirds  *)
(*                     (with one member per House, a vote of none; a      *)
(*                     simple-majority override, as in several state      *)
(*                     constitutions, needs a House of five to show).     *)
(*                     Breaks Presentment.                                *)
(*   M_NO_POCKET       BecomeLawUnsigned ignores adjournment: no pocket   *)
(*                     veto. Breaks TenDayRule.                           *)
(*   M_POCKET_SITTING  PocketVeto while Congress sits and can receive the *)
(*                     return: the claim Wright v. United States (1938)   *)
(*                     and Kennedy v. Sampson (D.C. Cir. 1974) rejected.  *)
(*                     Breaks TenDayRule.                                 *)
(*   M_INCOMPAT        Compatible() admits members of Congress to office: *)
(*                     the British practice of ministers sitting in       *)
(*                     Parliament, which the clause excludes. Breaks      *)
(*                     Incompatibility and CongressNotImpeachable (an     *)
(*                     officeholder is impeachable, and is now a member). *)
(*   M_BLOUNT          Impeach reaches members of Congress: the House's   *)
(*                     impeachment of Senator Blount (1797), which the    *)
(*                     Senate dismissed in 1799. Breaks                   *)
(*                     CongressNotImpeachable.                            *)
(*   M_CONVICT_VOTE    Convict without two-thirds of the Senate (here a   *)
(*                     vote of none; a majority rule, under which Johnson *)
(*                     (1868, 35-19) would have been removed, needs a     *)
(*                     Senate of five to show). Breaks                    *)
(*                     ConvictionTwoThirds.                               *)
(*   M_XXII            Elect without the two-term limit: the text before  *)
(*                     the Twenty-second Amendment (1951). Breaks         *)
(*                     TwoTermLimit.                                      *)
(*   M_DQ              Qualified() ignores disqualification when a person *)
(*                     is elected, nominated or recess-appointed. Breaks  *)
(*                     Disqualification.                                  *)
(*   M_VP_RECHECK      ConfirmVP does not re-check disqualification: this *)
(*                     module's own text before commit fe3ce28, which TLC *)
(*                     refuted (a nominee impeached, convicted and        *)
(*                     disqualified while pending was then confirmed).    *)
(*                     Breaks Disqualification.                           *)
(*   M_CONSENT_RECHECK Consent does not re-check disqualification (the    *)
(*                     same check for officers; the module has had it     *)
(*                     from its first version). Breaks Disqualification.  *)
(*   M_NO_REMOVAL      Conviction does not remove from office (Art. II    *)
(*                     s.4: "shall be removed"). Breaks Disqualification. *)
(*   M_ONE_PERSON      TwoPersons() lets one person be elected to both    *)
(*                     offices, or nominated Vice President by himself.   *)
(*                     Breaks PresidentNotVP.                             *)
(*   M_RATIFY_VOTE     Ratify without three-fourths of the States (here   *)
(*                     with none). Breaks ArticleV.                       *)
(*   M_SUFFRAGE        Ratify without the equal-suffrage proviso: the     *)
(*                     text of Article V before Gouverneur Morris's       *)
(*                     motion of 15 September 1787. Breaks ArticleV.      *)
(*   M_XXV_SENATE      ConfirmVP on the Senate's vote alone, as Art. II   *)
(*                     s.2 has it for officers; XXV s.2 adds the House.   *)
(*                     Breaks XXVBothHouses.                              *)
(*   M_PRO_FORMA       RecessAppoint while the Senate sits: the January   *)
(*                     2012 NLRB appointments made during pro forma       *)
(*                     sessions, held invalid by NLRB v. Noel Canning     *)
(*                     (2014). Breaks RecessAppointmentsInRecess.         *)
(* No mutation breaks a property it is not listed against; the results    *)
(* file runs every pair (rows/Constitution-rows.txt).                     *)
(*                                                                         *)
(* WITNESSES (Never..., each must be VIOLATED under Mut = "none"): law by *)
(* signature, by lapse and over a veto; a pocket veto; conviction with    *)
(* disqualification; a pending nominee (VP and officer) disqualified, the *)
(* state the two re-checks exist for; a recess appointment; a President   *)
(* elected twice; succession of the Vice President; a Vice President      *)
(* confirmed under XXV s.2; ratification after each proposal route; an    *)
(* amendment ratified by fewer than every State.                          *)
(*                                                                         *)
(* LIVENESS. FairSpec = Spec /\ TimeRuns, where TimeRuns is weak fairness *)
(* on Lapse(b), the ten days running out: no one's obligation, the        *)
(* clause executes itself. Under Spec alone (TimeRuns dropped)            *)
(* PresentedBillsResolve fails; so it does under SpecPresidentActs, weak  *)
(* fairness on the President's signing or returning in place of the      *)
(* clock, because the Presidency can be vacant. NoBehaviour is violated   *)
(* under FairSpec, so FairSpec has a behaviour.                           *)
(*                                                                         *)
(* DEADLOCK. Convene or Adjourn is always enabled, so no state is         *)
(* terminal; a stall is a livelock that only the leads-to sees.           *)
(*                                                                         *)
(* ABSTRACTED: quorum, Sundays, elections themselves (one Elect step),    *)
(* judicial review, the age/residency/natural-born tests (the constant    *)
(* Eligible), the "more than two years of another's term" nuance of XXII, *)
(* presidential succession beyond the Vice President. Time is             *)
(* nondeterminism: the ten days run out by a Lapse step at any moment     *)
(* after presentment, and the outcome is fixed by whether Congress then   *)
(* sits. Votes are counts of ayes, of members or of States; which States  *)
(* ratify or apply is abstracted to how many. Ratification and a          *)
(* convention's call are each one step at the moment the count suffices.  *)
(* A bill passes its House of origin first; one that never passes the     *)
(* other House stays pending (no step kills it); a veto not overridden    *)
(* dies by FailOverride.                                                  *)
(* Sessions: Congress sits and adjourns as one body (one House adjourning *)
(* without the other, Art. I s.5 cl.4, is not expressed), and inSession   *)
(* is read only where the text turns on a sitting: whether a bill can be  *)
(* returned (Veto, BecomeLawUnsigned, PocketVeto) and whether the Senate  *)
(* is in Recess (RecessAppoint). Every other act of Congress (Introduce,  *)
(* PassChamber, Override, the votes on nominations, Impeach, Convict,     *)
(* ProposeByCongress) may happen while it is adjourned. Government.tla    *)
(* gates Pass and Override on its own inSession; the two modules differ   *)
(* there.                                                                 *)
(*                                                                         *)
(* CONSTANTS are unconstrained beyond the named well-formedness ASSUMEs.  *)
(* ElectionsBound is a state constraint for TLC only: it binds only under *)
(* M_XXII, whose state space is otherwise infinite; no property or proof  *)
(* uses it. The proof is Constitution_proof.tla.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Mut,                 \* "none", or the one check removed (see above)
  Persons,             \* everyone who might hold an office
  House,               \* members of the House of Representatives
  Senate,              \* members of the Senate
  Eligible,            \* persons eligible to be President (Art. II s.1)
  States,              \* the several States
  Bills,               \* bill identifiers
  RevenueBills,        \* bills "for raising Revenue" (Art. I s.7 cl.1)
  Offices,             \* offices filled with advice and consent (Art. II s.2)
  Amendments,          \* amendment identifiers
  SuffrageAmendments,  \* amendments that would alter equal suffrage in the Senate
  NoOne                \* vacancy marker

Mutations ==
  {"none", "M_UNICAMERAL", "M_ORIGIN", "M_OVR_ONE_HOUSE", "M_OVR_VOTE",
   "M_NO_POCKET", "M_POCKET_SITTING", "M_INCOMPAT", "M_BLOUNT",
   "M_CONVICT_VOTE", "M_XXII", "M_DQ", "M_VP_RECHECK", "M_CONSENT_RECHECK",
   "M_NO_REMOVAL", "M_ONE_PERSON", "M_RATIFY_VOTE", "M_SUFFRAGE",
   "M_XXV_SENATE", "M_PRO_FORMA"}

ASSUME MutKnown       == Mut \in Mutations
ASSUME CongressPersons == House \subseteq Persons /\ Senate \subseteq Persons
ASSUME OneChamberEach == House \cap Senate = {}
ASSUME EligiblePersons == Eligible \subseteq Persons
ASSUME RevenueAreBills == RevenueBills \subseteq Bills
ASSUME SuffrageAreAmendments == SuffrageAmendments \subseteq Amendments
ASSUME NoOneIsNoPerson == NoOne \notin Persons
ASSUME FiniteBodies   == IsFiniteSet(House) /\ IsFiniteSet(Senate) /\ IsFiniteSet(States)

-----------------------------------------------------------------------------
(* Helpers *)

Chambers   == {"House", "Senate"}
Members(c) == IF c = "House" THEN House ELSE Senate
Seat       == Persons \cup {NoOne}
Congress   == House \cup Senate

Majority(ayes, body)      == 2 * ayes >  Cardinality(body)
TwoThirds(ayes, body)     == 3 * ayes >= 2 * Cardinality(body)
ThreeQuarters(ayes, body) == 4 * ayes >= 3 * Cardinality(body)

VotesIn(c)  == 0..Cardinality(Members(c))
StateVotes  == 0..Cardinality(States)

-----------------------------------------------------------------------------
VARIABLES
  (* Art. I s.7 *)
  bill,              \* Bills -> BillRec
  inSession,         \* Congress sitting, both Houses as one; gates only a
                     \* bill's return and recess appointments
  (* Art. II s.1, Amend. XXII, XXV *)
  president,
  vicePresident,
  terms,             \* Persons -> number of times elected President
  vpNominee,         \* Amend. XXV s.2 nominee for a vacant Vice Presidency
  (* Art. II s.2 *)
  officer,           \* Offices -> who holds it
  nominee,           \* Offices -> pending nomination
  recess,            \* Offices -> is the holder a recess appointee?
  (* Art. I s.2-3, Art. II s.4 *)
  impeached,         \* impeached by the House, awaiting trial
  disqualified,      \* convicted and barred from office
  (* Art. V *)
  amend,             \* Amendments -> AmendRec
  (* flags, each set only by the action that would break its property *)
  shortOverride,     \* an override vote below two-thirds was counted
  tenDayBreach,      \* the ten days ran out and the outcome ignored the session
  shortConviction,   \* a conviction below two-thirds of the Senate
  vpWithoutHouse,    \* a Vice President confirmed without a House majority
  recessWhileSitting \* a recess appointment while the Senate sat

billVars  == <<bill, inSession>>
execVars  == <<president, vicePresident, terms, vpNominee>>
apptVars  == <<officer, nominee, recess>>
impVars   == <<impeached, disqualified>>
flagVars  == <<shortOverride, tenDayBreach, shortConviction, vpWithoutHouse, recessWhileSitting>>
vars      == <<billVars, execVars, apptVars, impVars, amend, flagVars>>

BillStatus == {"Unintroduced", "Pending", "Presented", "Vetoed", "Law", "Dead"}
Hows       == {"None", "Signed", "Unsigned", "Override", "Pocket"}
BillRec    == [status : BillStatus, origin : Chambers \cup {"None"},
               passed : SUBSET Chambers, overridden : SUBSET Chambers,
               how : Hows]
AmendRec   == [status : {"None", "Proposed", "Ratified"},
               route  : {"None", "Congress", "Convention"},
               ratifications : Nat]

TypeOK ==
  /\ bill \in [Bills -> BillRec]
  /\ inSession \in BOOLEAN
  /\ president \in Seat
  /\ vicePresident \in Seat
  /\ terms \in [Persons -> Nat]
  /\ vpNominee \in Seat
  /\ officer \in [Offices -> Seat]
  /\ nominee \in [Offices -> Seat]
  /\ recess \in [Offices -> BOOLEAN]
  /\ impeached \subseteq Persons
  /\ disqualified \subseteq Persons
  /\ amend \in [Amendments -> AmendRec]
  /\ shortOverride \in BOOLEAN
  /\ tenDayBreach \in BOOLEAN
  /\ shortConviction \in BOOLEAN
  /\ vpWithoutHouse \in BOOLEAN
  /\ recessWhileSitting \in BOOLEAN

Officeholders ==
  ({president, vicePresident} \cup {officer[o] : o \in Offices}) \ {NoOne}

-----------------------------------------------------------------------------
(* The checks each mutation removes, one definition per check where the   *)
(* check is used by several actions.                                      *)

BothHouses(ps)       == Mut = "M_UNICAMERAL" \/ ps = Chambers
MayOriginate(b, c)   == Mut = "M_ORIGIN" \/ b \notin RevenueBills \/ c = "House"
OverrideCarries(n, c) == Mut = "M_OVR_VOTE" \/ TwoThirds(n, Members(c))
OverrideComplete(ov) == Mut = "M_OVR_ONE_HOUSE" \/ ov = Chambers
Compatible(p)        == Mut = "M_INCOMPAT" \/ p \notin Congress
Qualified(p)         == Mut = "M_DQ" \/ p \notin disqualified
TwoPersons(p, q)     == Mut = "M_ONE_PERSON" \/ p # q
TermAllowed(p)       == Mut = "M_XXII" \/ terms[p] < 2
Impeachable(p)       == p \in Officeholders \/ (Mut = "M_BLOUNT" /\ p \in Congress)
ConvictionCarries(n) == Mut = "M_CONVICT_VOTE" \/ TwoThirds(n, Senate)
RemovedBy(p, x)      == Mut # "M_NO_REMOVAL" /\ x = p
HouseConfirms(n)     == Mut = "M_XXV_SENATE" \/ Majority(n, House)
SenateInRecess       == Mut = "M_PRO_FORMA" \/ ~inSession
Ratifies(a, n)       == /\ Mut = "M_RATIFY_VOTE" \/ ThreeQuarters(n, States)
                        /\ Mut = "M_SUFFRAGE" \/ a \notin SuffrageAmendments
                                              \/ n = Cardinality(States)

-----------------------------------------------------------------------------
Init ==
  /\ bill = [b \in Bills |-> [status |-> "Unintroduced", origin |-> "None",
                              passed |-> {}, overridden |-> {}, how |-> "None"]]
  /\ inSession = TRUE
  /\ president = NoOne
  /\ vicePresident = NoOne
  /\ terms = [p \in Persons |-> 0]
  /\ vpNominee = NoOne
  /\ officer = [o \in Offices |-> NoOne]
  /\ nominee = [o \in Offices |-> NoOne]
  /\ recess = [o \in Offices |-> FALSE]
  /\ impeached = {}
  /\ disqualified = {}
  /\ amend = [a \in Amendments |-> [status |-> "None", route |-> "None", ratifications |-> 0]]
  /\ shortOverride = FALSE
  /\ tenDayBreach = FALSE
  /\ shortConviction = FALSE
  /\ vpWithoutHouse = FALSE
  /\ recessWhileSitting = FALSE

-----------------------------------------------------------------------------
(* Art. I s.5 cl.4, s.7 cl.2 - Congress sits and adjourns. Adjournment    *)
(* ends recess commissions (Art. II s.2 cl.3: they "expire at the End of  *)
(* their next Session"; a recess appointment is made out of session, so   *)
(* the next adjournment ends the next session).                           *)

Convene ==
  /\ ~inSession
  /\ inSession' = TRUE
  /\ UNCHANGED <<bill, execVars, apptVars, impVars, amend, flagVars>>

Adjourn ==
  /\ inSession
  /\ inSession' = FALSE
  /\ officer' = [o \in Offices |-> IF recess[o] THEN NoOne ELSE officer[o]]
  /\ recess'  = [o \in Offices |-> FALSE]
  /\ UNCHANGED <<bill, nominee, execVars, impVars, amend, flagVars>>

-----------------------------------------------------------------------------
(* Art. I s.7 - Legislation                                               *)

\* cl. 1: revenue bills originate in the House.
Introduce(b, c) ==
  /\ bill[b].status = "Unintroduced"
  /\ MayOriginate(b, c)
  /\ bill' = [bill EXCEPT ![b].status = "Pending", ![b].origin = c]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend, flagVars>>

\* cl. 2: passed by both Houses, the House of origin first, then presented
\* to the President.
PassChamber(b, c, ayes) ==
  /\ bill[b].status = "Pending"
  /\ c \notin bill[b].passed
  /\ bill[b].passed = {} => c = bill[b].origin
  /\ Majority(ayes, Members(c))
  /\ bill' = [bill EXCEPT ![b].passed = @ \cup {c},
                          ![b].status = IF BothHouses(bill[b].passed \cup {c})
                                          THEN "Presented" ELSE "Pending"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend, flagVars>>

Sign(b) ==
  /\ bill[b].status = "Presented"
  /\ president # NoOne
  /\ bill' = [bill EXCEPT ![b].status = "Law", ![b].how = "Signed"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend, flagVars>>

\* Returned with objections; possible only while Congress can receive it.
Veto(b) ==
  /\ bill[b].status = "Presented"
  /\ president # NoOne
  /\ inSession
  /\ bill' = [bill EXCEPT ![b].status = "Vetoed"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend, flagVars>>

\* The ten days (Sundays excepted) run out with Congress sitting: law.
BecomeLawUnsigned(b) ==
  /\ bill[b].status = "Presented"
  /\ Mut = "M_NO_POCKET" \/ inSession
  /\ bill' = [bill EXCEPT ![b].status = "Law", ![b].how = "Unsigned"]
  /\ tenDayBreach' = (tenDayBreach \/ ~inSession)
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend,
                 shortOverride, shortConviction, vpWithoutHouse, recessWhileSitting>>

\* The ten days run out with Congress adjourned: the pocket veto.
PocketVeto(b) ==
  /\ bill[b].status = "Presented"
  /\ Mut = "M_POCKET_SITTING" \/ ~inSession
  /\ bill' = [bill EXCEPT ![b].status = "Dead", ![b].how = "Pocket"]
  /\ tenDayBreach' = (tenDayBreach \/ inSession)
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend,
                 shortOverride, shortConviction, vpWithoutHouse, recessWhileSitting>>

\* The House of origin reconsiders first, then the other; two-thirds of each.
Override(b, c, ayes) ==
  /\ bill[b].status = "Vetoed"
  /\ c \notin bill[b].overridden
  /\ bill[b].overridden = {} => c = bill[b].origin
  /\ OverrideCarries(ayes, c)
  /\ bill' = [bill EXCEPT ![b].overridden = @ \cup {c},
                          ![b].status = IF OverrideComplete(bill[b].overridden \cup {c})
                                          THEN "Law" ELSE "Vetoed",
                          ![b].how    = IF OverrideComplete(bill[b].overridden \cup {c})
                                          THEN "Override" ELSE @]
  /\ shortOverride' = (shortOverride \/ ~TwoThirds(ayes, Members(c)))
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend,
                 tenDayBreach, shortConviction, vpWithoutHouse, recessWhileSitting>>

FailOverride(b) ==
  /\ bill[b].status = "Vetoed"
  /\ bill' = [bill EXCEPT ![b].status = "Dead"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amend, flagVars>>

-----------------------------------------------------------------------------
(* Art. II s.1, Amend. XII, XXII, XXV - the Executive                      *)

\* The whole electoral process in one step.
Elect(p, v) ==
  /\ p \in Eligible /\ v \in Eligible
  /\ Qualified(p) /\ Qualified(v)
  /\ Compatible(p) /\ Compatible(v)
  /\ TwoPersons(p, v)
  /\ TermAllowed(p)                                  \* Amend. XXII
  /\ president' = p
  /\ vicePresident' = v
  /\ terms' = [terms EXCEPT ![p] = @ + 1]
  /\ vpNominee' = NoOne
  /\ UNCHANGED <<billVars, apptVars, impVars, amend, flagVars>>

\* Death or resignation: the Vice President becomes President (XXV s.1).
PresidentVacates ==
  /\ president # NoOne
  /\ president' = vicePresident
  /\ vicePresident' = NoOne
  /\ UNCHANGED <<terms, vpNominee, billVars, apptVars, impVars, amend, flagVars>>

VicePresidentVacates ==
  /\ vicePresident # NoOne
  /\ vicePresident' = NoOne
  /\ UNCHANGED <<president, terms, vpNominee, billVars, apptVars, impVars, amend, flagVars>>

\* Amend. XXV s.2: the President nominates; a majority of both Houses confirms.
NominateVP(p) ==
  /\ vicePresident = NoOne
  /\ president # NoOne
  /\ vpNominee = NoOne
  /\ p \in Eligible
  /\ Qualified(p)
  /\ Compatible(p)
  /\ TwoPersons(p, president)
  /\ vpNominee' = p
  /\ UNCHANGED <<president, vicePresident, terms, billVars, apptVars, impVars, amend, flagVars>>

ConfirmVP(hAyes, sAyes) ==
  /\ vpNominee # NoOne
  /\ Mut = "M_VP_RECHECK" \/ vpNominee \notin disqualified   \* re-checked: TLC found this
  /\ HouseConfirms(hAyes)
  /\ Majority(sAyes, Senate)
  /\ vicePresident' = vpNominee
  /\ vpNominee' = NoOne
  /\ vpWithoutHouse' = (vpWithoutHouse \/ ~Majority(hAyes, House))
  /\ UNCHANGED <<president, terms, billVars, apptVars, impVars, amend,
                 shortOverride, tenDayBreach, shortConviction, recessWhileSitting>>

RejectVP ==
  /\ vpNominee # NoOne
  /\ vpNominee' = NoOne
  /\ UNCHANGED <<president, vicePresident, terms, billVars, apptVars, impVars, amend, flagVars>>

-----------------------------------------------------------------------------
(* Art. II s.2 cl.2-3 - Appointments                                      *)

Nominate(o, p) ==
  /\ president # NoOne
  /\ officer[o] = NoOne \/ recess[o]       \* may nominate to regularize a recess appointee
  /\ nominee[o] = NoOne
  /\ Qualified(p)
  /\ Compatible(p)                         \* Art. I s.6 cl.2
  /\ nominee' = [nominee EXCEPT ![o] = p]
  /\ UNCHANGED <<officer, recess, billVars, execVars, impVars, amend, flagVars>>

Consent(o, ayes) ==
  /\ nominee[o] # NoOne
  /\ Mut = "M_CONSENT_RECHECK" \/ nominee[o] \notin disqualified  \* convicted since nomination?
  /\ Majority(ayes, Senate)
  /\ officer' = [officer EXCEPT ![o] = nominee[o]]
  /\ nominee' = [nominee EXCEPT ![o] = NoOne]
  /\ recess'  = [recess  EXCEPT ![o] = FALSE]
  /\ UNCHANGED <<billVars, execVars, impVars, amend, flagVars>>

Reject(o) ==
  /\ nominee[o] # NoOne
  /\ nominee' = [nominee EXCEPT ![o] = NoOne]
  /\ UNCHANGED <<officer, recess, billVars, execVars, impVars, amend, flagVars>>

\* cl. 3: vacancies during the Recess of the Senate, filled without it.
RecessAppoint(o, p) ==
  /\ SenateInRecess
  /\ president # NoOne
  /\ officer[o] = NoOne
  /\ Qualified(p)
  /\ Compatible(p)
  /\ officer' = [officer EXCEPT ![o] = p]
  /\ recess'  = [recess  EXCEPT ![o] = TRUE]
  /\ recessWhileSitting' = (recessWhileSitting \/ inSession)
  /\ UNCHANGED <<nominee, billVars, execVars, impVars, amend,
                 shortOverride, tenDayBreach, shortConviction, vpWithoutHouse>>

OfficerResigns(o) ==
  /\ officer[o] # NoOne
  /\ officer' = [officer EXCEPT ![o] = NoOne]
  /\ recess'  = [recess  EXCEPT ![o] = FALSE]
  /\ UNCHANGED <<nominee, billVars, execVars, impVars, amend, flagVars>>

-----------------------------------------------------------------------------
(* Art. I s.2 cl.5, s.3 cl.6-7, Art. II s.4 - Impeachment                 *)

\* The House has the sole power of impeachment; a majority suffices.
Impeach(p, ayes) ==
  /\ Impeachable(p)
  /\ p \notin impeached
  /\ Majority(ayes, House)
  /\ impeached' = impeached \cup {p}
  /\ UNCHANGED <<disqualified, billVars, execVars, apptVars, amend, flagVars>>

\* The Senate tries; two-thirds convict; judgment is removal from every
\* office (a removed President is succeeded by the Vice President, XXV s.1)
\* and, if the Senate so votes, disqualification - nothing more.
Convict(p, ayes, dq) ==
  /\ p \in impeached
  /\ ConvictionCarries(ayes)
  /\ impeached' = impeached \ {p}
  /\ disqualified' = IF dq THEN disqualified \cup {p} ELSE disqualified
  /\ LET vp == IF RemovedBy(p, vicePresident) THEN NoOne ELSE vicePresident
     IN  /\ president'     = IF RemovedBy(p, president) THEN vp ELSE president
         /\ vicePresident' = IF RemovedBy(p, president) THEN NoOne ELSE vp
  /\ officer' = [o \in Offices |-> IF RemovedBy(p, officer[o]) THEN NoOne ELSE officer[o]]
  /\ recess'  = [o \in Offices |-> IF RemovedBy(p, officer[o]) THEN FALSE ELSE recess[o]]
  /\ shortConviction' = (shortConviction \/ ~TwoThirds(ayes, Senate))
  /\ UNCHANGED <<terms, vpNominee, nominee, billVars, amend,
                 shortOverride, tenDayBreach, vpWithoutHouse, recessWhileSitting>>

Acquit(p) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ UNCHANGED <<disqualified, billVars, execVars, apptVars, amend, flagVars>>

-----------------------------------------------------------------------------
(* Art. V - Amendment                                                      *)

\* Route 1: two-thirds of both Houses propose.
ProposeByCongress(a, hAyes, sAyes) ==
  /\ amend[a].status = "None"
  /\ TwoThirds(hAyes, House)
  /\ TwoThirds(sAyes, Senate)
  /\ amend' = [amend EXCEPT ![a].status = "Proposed", ![a].route = "Congress"]
  /\ UNCHANGED <<billVars, execVars, apptVars, impVars, flagVars>>

\* Route 2: on the application of two-thirds of the States, a convention.
ProposeByConvention(a, n) ==
  /\ amend[a].status = "None"
  /\ TwoThirds(n, States)
  /\ amend' = [amend EXCEPT ![a].status = "Proposed", ![a].route = "Convention"]
  /\ UNCHANGED <<billVars, execVars, apptVars, impVars, flagVars>>

\* Ratified when n States have ratified: three-fourths, and every State for
\* an amendment touching the Senate's equal suffrage.
Ratify(a, n) ==
  /\ amend[a].status = "Proposed"
  /\ Ratifies(a, n)
  /\ amend' = [amend EXCEPT ![a].status = "Ratified", ![a].ratifications = n]
  /\ UNCHANGED <<billVars, execVars, apptVars, impVars, flagVars>>

-----------------------------------------------------------------------------
Next ==
  \/ Convene \/ Adjourn
  \/ \E b \in Bills :
       \/ \E c \in Chambers : Introduce(b, c)
       \/ \E c \in Chambers : \E n \in VotesIn(c) : PassChamber(b, c, n)
       \/ Sign(b) \/ Veto(b)
       \/ BecomeLawUnsigned(b) \/ PocketVeto(b) \/ FailOverride(b)
       \/ \E c \in Chambers : \E n \in VotesIn(c) : Override(b, c, n)
  \/ \E p, v \in Persons : Elect(p, v)
  \/ PresidentVacates \/ VicePresidentVacates \/ RejectVP
  \/ \E p \in Persons : NominateVP(p)
  \/ \E h \in VotesIn("House"), s \in VotesIn("Senate") : ConfirmVP(h, s)
  \/ \E o \in Offices :
       \/ \E p \in Persons : Nominate(o, p) \/ RecessAppoint(o, p)
       \/ \E n \in VotesIn("Senate") : Consent(o, n)
       \/ Reject(o) \/ OfficerResigns(o)
  \/ \E p \in Persons :
       \/ \E n \in VotesIn("House") : Impeach(p, n)
       \/ \E n \in VotesIn("Senate"), dq \in BOOLEAN : Convict(p, n, dq)
       \/ Acquit(p)
  \/ \E a \in Amendments :
       \/ \E h \in VotesIn("House"), s \in VotesIn("Senate") : ProposeByCongress(a, h, s)
       \/ \E n \in StateVotes : ProposeByConvention(a, n)
       \/ \E n \in StateVotes : Ratify(a, n)

Spec == Init /\ [][Next]_vars

\* A bound for TLC only: it binds only under M_XXII. Not a property; unused
\* by the proof.
ElectionsBound == \A p \in Persons : terms[p] <= 3

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* Art. I s.7 cl.2: no bill reaches the President, or becomes law, unless
\* both Houses passed it.
Bicameralism ==
  \A b \in Bills :
    bill[b].status \in {"Presented", "Vetoed", "Law"} => bill[b].passed = Chambers

\* Art. I s.7 cl.1
Origination ==
  \A b \in RevenueBills : bill[b].origin \in {"None", "House"}

\* Art. I s.7 cl.2: every law was signed, became law unreturned, or was
\* repassed by both Houses, each by two-thirds.
Presentment ==
  /\ \A b \in Bills :
       bill[b].status = "Law" =>
         \/ bill[b].how \in {"Signed", "Unsigned"}
         \/ bill[b].how = "Override" /\ bill[b].overridden = Chambers
  /\ ~shortOverride

\* Art. I s.7 cl.2, last sentence.
TenDayRule == ~tenDayBreach

\* Art. I s.6 cl.2
Incompatibility == Officeholders \cap Congress = {}

\* Art. II s.4 and the Blount precedent (1799)
CongressNotImpeachable == impeached \cap Congress = {}

\* Art. I s.3 cl.6
ConvictionTwoThirds == ~shortConviction

\* Amend. XXII
TwoTermLimit == \A p \in Persons : terms[p] <= 2

\* Art. I s.3 cl.7
Disqualification == disqualified \cap Officeholders = {}

\* Art. II s.1, Amend. XII, XXV
PresidentNotVP == president = NoOne \/ president # vicePresident

\* Art. V
ArticleV ==
  \A a \in Amendments :
    amend[a].status = "Ratified" =>
      /\ ThreeQuarters(amend[a].ratifications, States)
      /\ a \in SuffrageAmendments => amend[a].ratifications = Cardinality(States)

\* Amend. XXV s.2
XXVBothHouses == ~vpWithoutHouse

\* Art. II s.2 cl.3
RecessAppointmentsInRecess == ~recessWhileSitting

Safety ==
  /\ Bicameralism /\ Origination /\ Presentment /\ TenDayRule
  /\ Incompatibility /\ CongressNotImpeachable /\ ConvictionTwoThirds
  /\ TwoTermLimit /\ Disqualification /\ PresidentNotVP /\ ArticleV
  /\ XXVBothHouses /\ RecessAppointmentsInRecess

-----------------------------------------------------------------------------
(* Witnesses: each must be VIOLATED under Mut = "none".                    *)

NeverLawBySignature   == \A b \in Bills : ~(bill[b].status = "Law" /\ bill[b].how = "Signed")
NeverLawByLapse       == \A b \in Bills : ~(bill[b].status = "Law" /\ bill[b].how = "Unsigned")
NeverLawByOverride    == \A b \in Bills : ~(bill[b].status = "Law" /\ bill[b].how = "Override")
NeverPocketVeto       == \A b \in Bills : bill[b].how # "Pocket"
NeverDisqualified     == disqualified = {}
NeverVPNomineeDisqualified == vpNominee \notin disqualified
NeverNomineeDisqualified   == \A o \in Offices : nominee[o] \notin disqualified
NeverRecessAppointment == \A o \in Offices : ~recess[o]
NeverReelected        == \A p \in Persons : terms[p] < 2
NeverRatifiedFromCongress ==
  \A a \in Amendments : ~(amend[a].status = "Ratified" /\ amend[a].route = "Congress")
NeverRatifiedFromConvention ==
  \A a \in Amendments : ~(amend[a].status = "Ratified" /\ amend[a].route = "Convention")
NeverRatifiedByFewerThanAll ==
  \A a \in Amendments : amend[a].status = "Ratified" => amend[a].ratifications = Cardinality(States)
\* Action properties (PROPERTY rows): a step that must be possible.
NeverSuccession ==
  [][~(president # NoOne /\ vicePresident # NoOne /\ president' = vicePresident)]_vars
NeverXXVConfirmation ==
  [][~(\E h \in VotesIn("House"), s \in VotesIn("Senate") : ConfirmVP(h, s))]_vars

-----------------------------------------------------------------------------
(* Liveness: the ten-day rule. A presented bill is eventually law,         *)
(* returned, or dead.                                                      *)

Lapse(b) == BecomeLawUnsigned(b) \/ PocketVeto(b)

\* The ten days run out: no one's obligation; the clause executes itself.
TimeRuns == \A b \in Bills : WF_vars(Lapse(b))

\* The President's signing or returning: an obligation the text does not
\* impose, stated to show it would not suffice in the clock's place.
PresidentActs == \A b \in Bills : WF_vars(Sign(b) \/ Veto(b))

FairSpec          == Spec /\ TimeRuns
SpecPresidentActs == Spec /\ PresidentActs

PresentedBillsResolve ==
  \A b \in Bills :
    (bill[b].status = "Presented") ~> (bill[b].status \in {"Law", "Vetoed", "Dead"})

\* Satisfied by no behaviour: violated under a spec exactly when the spec,
\* fairness included, has a behaviour.
NoBehaviour == <>(inSession /\ ~inSession)

=============================================================================
