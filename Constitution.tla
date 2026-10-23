---------------------------- MODULE Constitution ----------------------------
(***************************************************************************)
(* A TLA+ model of the *procedural* core of the U.S. Constitution.         *)
(*                                                                         *)
(* This is an exercise, not law. It models the state machines the text     *)
(* actually specifies and the invariants the text actually guarantees:     *)
(*                                                                         *)
(*   Art. I  sec. 6   Incompatibility Clause                               *)
(*   Art. I  sec. 7   Origination, bicameralism, presentment, veto,        *)
(*                    pocket veto, ten-day rule, override                  *)
(*   Art. I  sec. 2-3 Impeachment (House) and trial (Senate)               *)
(*   Art. II sec. 1   Eligibility, succession                              *)
(*   Art. II sec. 2   Advice and consent, recess appointments              *)
(*   Art. II sec. 4   Who may be impeached                                 *)
(*   Art. V           Amendment (both proposal routes, equal-suffrage      *)
(*                    entrenchment)                                        *)
(*   Amend. XXII      Two-term limit                                       *)
(*   Amend. XXV       VP succession and VP vacancy                         *)
(*                                                                         *)
(* Deliberately abstracted away: quorum, Sundays, elections themselves,    *)
(* judicial review, the 14-year/35-year/natural-born tests (folded into    *)
(* the constant Eligible), and the "more than two years of another's      *)
(* term" nuance in the 22nd Amendment.                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Persons,             \* Everyone who might hold an office
  House,               \* Members of the House of Representatives
  Senate,              \* Members of the Senate
  Eligible,            \* Persons eligible to be President (Art. II sec. 1)
  States,              \* The several States
  Bills,               \* Bill identifiers
  RevenueBills,        \* Bills "for raising Revenue" (Art. I sec. 7 cl. 1)
  Offices,             \* Offices requiring advice and consent (Art. II sec. 2)
  Amendments,          \* Proposed amendment identifiers
  SuffrageAmendments,  \* Amendments that would alter equal suffrage in the Senate
  NoOne                \* Vacancy marker

ASSUME House \subseteq Persons /\ Senate \subseteq Persons
ASSUME House \cap Senate = {}              \* nobody sits in both chambers
ASSUME Eligible \subseteq Persons
ASSUME RevenueBills \subseteq Bills
ASSUME SuffrageAmendments \subseteq Amendments
ASSUME NoOne \notin Persons

-----------------------------------------------------------------------------
(* Helpers *)

Chambers   == {"House", "Senate"}
Members(c) == IF c = "House" THEN House ELSE Senate
Seat       == Persons \cup {NoOne}
Congress   == House \cup Senate

Majority(ayes, body)      == 2 * ayes >  Cardinality(body)
TwoThirds(ayes, body)     == 3 * ayes >= 2 * Cardinality(body)
ThreeQuarters(ayes, body) == 4 * ayes >= 3 * Cardinality(body)

VotesIn(c) == 0..Cardinality(Members(c))

-----------------------------------------------------------------------------
VARIABLES
  (* Art. I sec. 7 *)
  bill,            \* Bills -> record (see TypeOK)
  inSession,       \* BOOLEAN: is Congress sitting?

  (* Art. II sec. 1, Amend. XXII, XXV *)
  president,
  vicePresident,
  terms,           \* Persons -> number of times elected President
  vpNominee,       \* Amend. XXV sec. 2 nominee for a vacant VP office

  (* Art. II sec. 2 *)
  officer,         \* Offices -> who holds it
  nominee,         \* Offices -> pending nomination
  recess,          \* Offices -> was this a recess appointment?

  (* Art. I sec. 2-3, Art. II sec. 4 *)
  impeached,       \* impeached by the House, awaiting Senate trial
  disqualified,    \* convicted and barred from future office

  (* Art. V *)
  amend,           \* Amendments -> record (see TypeOK)
  conventionCalls  \* States that have applied for a convention

billVars  == <<bill, inSession>>
execVars  == <<president, vicePresident, terms, vpNominee>>
apptVars  == <<officer, nominee, recess>>
impVars   == <<impeached, disqualified>>
amendVars == <<amend, conventionCalls>>
vars      == <<billVars, execVars, apptVars, impVars, amendVars>>

BillStatus == {"Unintroduced", "Pending", "Presented", "Law", "Vetoed", "Dead"}
Enactment  == {"None", "Signed", "Unsigned", "Override"}

TypeOK ==
  /\ bill \in [Bills -> [status     : BillStatus,
                         origin     : Chambers \cup {"None"},
                         passed     : SUBSET Chambers,
                         overridden : SUBSET Chambers,
                         days       : 0..10,
                         enacted    : Enactment]]
  /\ inSession \in BOOLEAN
  /\ president \in Seat
  /\ vicePresident \in Seat
  /\ terms \in [Persons -> 0..2]
  /\ vpNominee \in Seat
  /\ officer \in [Offices -> Seat]
  /\ nominee \in [Offices -> Seat]
  /\ recess \in [Offices -> BOOLEAN]
  /\ impeached \subseteq Persons
  /\ disqualified \subseteq Persons
  /\ amend \in [Amendments -> [status     : {"None", "Proposed", "Ratified"},
                               ratifiedBy : SUBSET States]]
  /\ conventionCalls \subseteq States

Officeholders ==
  ({president, vicePresident} \cup {officer[o] : o \in Offices}) \ {NoOne}

-----------------------------------------------------------------------------
Init ==
  /\ bill = [b \in Bills |-> [status |-> "Unintroduced", origin |-> "None",
                              passed |-> {}, overridden |-> {},
                              days |-> 0, enacted |-> "None"]]
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
  /\ amend = [a \in Amendments |-> [status |-> "None", ratifiedBy |-> {}]]
  /\ conventionCalls = {}

-----------------------------------------------------------------------------
(* Art. I sec. 5 cl. 4 / sec. 7 cl. 2 - Congress sits and adjourns.        *)
(* Adjournment also ends recess appointments (Art. II sec. 2 cl. 3:        *)
(* commissions "expire at the End of their next Session").                 *)

Convene ==
  /\ ~inSession
  /\ inSession' = TRUE
  /\ UNCHANGED <<bill, execVars, apptVars, impVars, amendVars>>

Adjourn ==
  /\ inSession
  /\ inSession' = FALSE
  /\ officer' = [o \in Offices |-> IF recess[o] THEN NoOne ELSE officer[o]]
  /\ recess'  = [o \in Offices |-> FALSE]
  /\ UNCHANGED <<bill, nominee, execVars, impVars, amendVars>>

-----------------------------------------------------------------------------
(* Art. I sec. 7 - Legislation                                             *)

\* cl. 1: revenue bills originate in the House
Introduce(b, c) ==
  /\ bill[b].status = "Unintroduced"
  /\ (b \in RevenueBills) => (c = "House")
  /\ bill' = [bill EXCEPT ![b].status = "Pending", ![b].origin = c]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

\* cl. 2: must pass both chambers; then presented to the President
PassChamber(b, c, ayes) ==
  /\ bill[b].status = "Pending"
  /\ c \notin bill[b].passed
  /\ Majority(ayes, Members(c))
  /\ LET passed == bill[b].passed \cup {c}
     IN bill' = [bill EXCEPT ![b].passed = passed,
                             ![b].status = IF passed = Chambers
                                             THEN "Presented" ELSE "Pending",
                             ![b].days = 0]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

FailChamber(b) ==
  /\ bill[b].status = "Pending"
  /\ bill' = [bill EXCEPT ![b].status = "Dead"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

Sign(b) ==
  /\ bill[b].status = "Presented"
  /\ president # NoOne
  /\ bill' = [bill EXCEPT ![b].status = "Law", ![b].enacted = "Signed"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

\* Returned with objections. Only possible if Congress can receive it.
Veto(b) ==
  /\ bill[b].status = "Presented"
  /\ president # NoOne
  /\ inSession
  /\ bill' = [bill EXCEPT ![b].status = "Vetoed"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

\* A day passes with the bill on the President's desk (Sundays excepted).
Tick(b) ==
  /\ bill[b].status = "Presented"
  /\ bill[b].days < 10
  /\ bill' = [bill EXCEPT ![b].days = @ + 1]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

\* Ten days, Congress sitting: becomes law without signature.
BecomeLawUnsigned(b) ==
  /\ bill[b].status = "Presented"
  /\ bill[b].days = 10
  /\ inSession
  /\ bill' = [bill EXCEPT ![b].status = "Law", ![b].enacted = "Unsigned"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

\* Ten days, Congress adjourned: pocket veto.
PocketVeto(b) ==
  /\ bill[b].status = "Presented"
  /\ bill[b].days = 10
  /\ ~inSession
  /\ bill' = [bill EXCEPT ![b].status = "Dead"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

\* Override: the originating house reconsiders first, then the other.
\* Two-thirds of each.
Override(b, c, ayes) ==
  /\ bill[b].status = "Vetoed"
  /\ c \notin bill[b].overridden
  /\ (bill[b].overridden = {}) => (c = bill[b].origin)
  /\ TwoThirds(ayes, Members(c))
  /\ LET ov == bill[b].overridden \cup {c}
     IN bill' = [bill EXCEPT ![b].overridden = ov,
                             ![b].status  = IF ov = Chambers THEN "Law" ELSE "Vetoed",
                             ![b].enacted = IF ov = Chambers THEN "Override" ELSE @]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

FailOverride(b) ==
  /\ bill[b].status = "Vetoed"
  /\ bill' = [bill EXCEPT ![b].status = "Dead"]
  /\ UNCHANGED <<inSession, execVars, apptVars, impVars, amendVars>>

-----------------------------------------------------------------------------
(* Art. II sec. 1, Amend. XII, XXII - The Executive                        *)

\* Abstracts the whole electoral process to one step.
Elect(p, v) ==
  /\ p \in Eligible \ disqualified
  /\ v \in Eligible \ disqualified
  /\ p # v
  /\ p \notin Congress /\ v \notin Congress
  /\ terms[p] < 2                                   \* Amend. XXII
  /\ president' = p
  /\ vicePresident' = v
  /\ terms' = [terms EXCEPT ![p] = @ + 1]
  /\ vpNominee' = NoOne
  /\ UNCHANGED <<billVars, apptVars, impVars, amendVars>>

\* Death or resignation of the President: VP becomes President (XXV sec. 1).
PresidentVacates ==
  /\ president # NoOne
  /\ president' = vicePresident
  /\ vicePresident' = NoOne
  /\ UNCHANGED <<terms, vpNominee, billVars, apptVars, impVars, amendVars>>

VicePresidentVacates ==
  /\ vicePresident # NoOne
  /\ vicePresident' = NoOne
  /\ UNCHANGED <<president, terms, vpNominee, billVars, apptVars, impVars, amendVars>>

\* Amend. XXV sec. 2: President nominates; majority of BOTH houses confirms.
NominateVP(p) ==
  /\ vicePresident = NoOne
  /\ president # NoOne
  /\ vpNominee = NoOne
  /\ p \in Eligible \ disqualified
  /\ p \notin Congress
  /\ p # president
  /\ vpNominee' = p
  /\ UNCHANGED <<president, vicePresident, terms, billVars, apptVars, impVars, amendVars>>

ConfirmVP(hAyes, sAyes) ==
  /\ vpNominee # NoOne
  /\ Majority(hAyes, House)
  /\ Majority(sAyes, Senate)
  /\ vicePresident' = vpNominee
  /\ vpNominee' = NoOne
  /\ UNCHANGED <<president, terms, billVars, apptVars, impVars, amendVars>>

RejectVP ==
  /\ vpNominee # NoOne
  /\ vpNominee' = NoOne
  /\ UNCHANGED <<president, vicePresident, terms, billVars, apptVars, impVars, amendVars>>

-----------------------------------------------------------------------------
(* Art. II sec. 2 cl. 2-3 - Appointments                                   *)

Nominate(o, p) ==
  /\ president # NoOne
  /\ officer[o] = NoOne \/ recess[o]        \* may nominate to regularize a recess appointee
  /\ nominee[o] = NoOne
  /\ p \notin disqualified
  /\ p \notin Congress                      \* Art. I sec. 6 cl. 2
  /\ nominee' = [nominee EXCEPT ![o] = p]
  /\ UNCHANGED <<officer, recess, billVars, execVars, impVars, amendVars>>

Consent(o, ayes) ==
  /\ nominee[o] # NoOne
  /\ nominee[o] \notin disqualified         \* could have been convicted since nomination
  /\ Majority(ayes, Senate)
  /\ officer' = [officer EXCEPT ![o] = nominee[o]]
  /\ nominee' = [nominee EXCEPT ![o] = NoOne]
  /\ recess'  = [recess  EXCEPT ![o] = FALSE]
  /\ UNCHANGED <<billVars, execVars, impVars, amendVars>>

Reject(o) ==
  /\ nominee[o] # NoOne
  /\ nominee' = [nominee EXCEPT ![o] = NoOne]
  /\ UNCHANGED <<officer, recess, billVars, execVars, impVars, amendVars>>

\* cl. 3: vacancies during the recess may be filled without the Senate.
RecessAppoint(o, p) ==
  /\ ~inSession
  /\ president # NoOne
  /\ officer[o] = NoOne
  /\ p \notin disqualified
  /\ p \notin Congress
  /\ officer' = [officer EXCEPT ![o] = p]
  /\ recess'  = [recess  EXCEPT ![o] = TRUE]
  /\ UNCHANGED <<nominee, billVars, execVars, impVars, amendVars>>

OfficerResigns(o) ==
  /\ officer[o] # NoOne
  /\ officer' = [officer EXCEPT ![o] = NoOne]
  /\ recess'  = [recess  EXCEPT ![o] = FALSE]
  /\ UNCHANGED <<nominee, billVars, execVars, impVars, amendVars>>

-----------------------------------------------------------------------------
(* Art. I sec. 2 cl. 5, sec. 3 cl. 6-7, Art. II sec. 4 - Impeachment       *)

\* The House has the sole power of impeachment; a simple majority suffices.
Impeach(p, ayes) ==
  /\ p \in Officeholders
  /\ p \notin impeached
  /\ Majority(ayes, House)
  /\ impeached' = impeached \cup {p}
  /\ UNCHANGED <<disqualified, billVars, execVars, apptVars, amendVars>>

\* The Senate tries; two-thirds to convict; judgment is removal and,
\* optionally, disqualification - nothing more.
Convict(p, ayes, dq) ==
  /\ p \in impeached
  /\ TwoThirds(ayes, Senate)
  /\ impeached' = impeached \ {p}
  /\ disqualified' = IF dq THEN disqualified \cup {p} ELSE disqualified
  /\ IF p = president
       THEN president' = vicePresident /\ vicePresident' = NoOne   \* XXV sec. 1
       ELSE IF p = vicePresident
         THEN president' = president /\ vicePresident' = NoOne
         ELSE UNCHANGED <<president, vicePresident>>
  /\ officer' = [o \in Offices |-> IF officer[o] = p THEN NoOne ELSE officer[o]]
  /\ recess'  = [o \in Offices |-> IF officer[o] = p THEN FALSE ELSE recess[o]]
  /\ UNCHANGED <<terms, vpNominee, nominee, billVars, amendVars>>

Acquit(p) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ UNCHANGED <<disqualified, billVars, execVars, apptVars, amendVars>>

-----------------------------------------------------------------------------
(* Art. V - Amendment                                                      *)

\* Route 1: two-thirds of both houses propose.
ProposeByCongress(a, hAyes, sAyes) ==
  /\ amend[a].status = "None"
  /\ TwoThirds(hAyes, House)
  /\ TwoThirds(sAyes, Senate)
  /\ amend' = [amend EXCEPT ![a].status = "Proposed"]
  /\ UNCHANGED <<conventionCalls, billVars, execVars, apptVars, impVars>>

\* Route 2: two-thirds of the States apply; a convention proposes.
ApplyForConvention(s) ==
  /\ s \notin conventionCalls
  /\ conventionCalls' = conventionCalls \cup {s}
  /\ UNCHANGED <<amend, billVars, execVars, apptVars, impVars>>

ProposeByConvention(a) ==
  /\ amend[a].status = "None"
  /\ TwoThirds(Cardinality(conventionCalls), States)
  /\ amend' = [amend EXCEPT ![a].status = "Proposed"]
  /\ UNCHANGED <<conventionCalls, billVars, execVars, apptVars, impVars>>

\* Ratification by three-fourths of the States. An amendment touching equal
\* suffrage in the Senate additionally needs the consent of every State
\* (modelled as: every State must ratify).
Ratify(a, s) ==
  /\ amend[a].status = "Proposed"
  /\ s \notin amend[a].ratifiedBy
  /\ LET r == amend[a].ratifiedBy \cup {s}
         done == /\ ThreeQuarters(Cardinality(r), States)
                 /\ (a \in SuffrageAmendments) => (r = States)
     IN amend' = [amend EXCEPT ![a].ratifiedBy = r,
                               ![a].status = IF done THEN "Ratified" ELSE "Proposed"]
  /\ UNCHANGED <<conventionCalls, billVars, execVars, apptVars, impVars>>

-----------------------------------------------------------------------------
Next ==
  \/ Convene \/ Adjourn
  \/ \E b \in Bills :
       \/ \E c \in Chambers : Introduce(b, c)
       \/ \E c \in Chambers, n \in VotesIn(c) : PassChamber(b, c, n)
       \/ FailChamber(b) \/ Sign(b) \/ Veto(b) \/ Tick(b)
       \/ BecomeLawUnsigned(b) \/ PocketVeto(b) \/ FailOverride(b)
       \/ \E c \in Chambers, n \in VotesIn(c) : Override(b, c, n)
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
       \/ ProposeByConvention(a)
       \/ \E s \in States : Ratify(a, s)
  \/ \E s \in States : ApplyForConvention(s)

Resolve(b) == Sign(b) \/ Veto(b) \/ BecomeLawUnsigned(b) \/ PocketVeto(b)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A b \in Bills : WF_vars(Tick(b)) /\ WF_vars(Resolve(b))

-----------------------------------------------------------------------------
(* Safety properties - what the text guarantees                            *)

\* Art. I sec. 7 cl. 2: no law without both chambers.
Bicameralism ==
  \A b \in Bills : bill[b].status = "Law" => bill[b].passed = Chambers

\* Art. I sec. 7 cl. 1: revenue bills originate in the House.
Origination ==
  \A b \in RevenueBills : bill[b].origin \in {"None", "House"}

\* Art. I sec. 7 cl. 2: every law was signed, lapsed into law, or overridden
\* by two-thirds of both houses.
Presentment ==
  \A b \in Bills :
    bill[b].status = "Law" =>
      /\ bill[b].enacted \in {"Signed", "Unsigned", "Override"}
      /\ (bill[b].enacted = "Override") => (bill[b].overridden = Chambers)

\* Art. I sec. 6 cl. 2: no one holds office under the United States while
\* sitting in Congress.
Incompatibility ==
  Officeholders \cap Congress = {}

\* Art. II sec. 4 (and the Blount precedent, 1799): members of Congress are
\* not civil officers and are not subject to impeachment.
CongressNotImpeachable ==
  impeached \cap Congress = {}

\* Amend. XXII
TwoTermLimit ==
  \A p \in Persons : terms[p] <= 2

\* Art. I sec. 3 cl. 7: disqualification bars any office.
Disqualification ==
  disqualified \cap Officeholders = {}

PresidentNotVP ==
  president = NoOne \/ president # vicePresident

\* Art. V
ArticleV ==
  \A a \in Amendments :
    amend[a].status = "Ratified" =>
      /\ ThreeQuarters(Cardinality(amend[a].ratifiedBy), States)
      /\ (a \in SuffrageAmendments) => (amend[a].ratifiedBy = States)

Safety ==
  /\ Bicameralism /\ Origination /\ Presentment /\ Incompatibility
  /\ CongressNotImpeachable /\ TwoTermLimit /\ Disqualification
  /\ PresidentNotVP /\ ArticleV

-----------------------------------------------------------------------------
(* Liveness - the ten-day rule means a presented bill cannot sit forever.  *)

PresentedBillsResolve ==
  \A b \in Bills :
    (bill[b].status = "Presented") ~> (bill[b].status \in {"Law", "Vetoed", "Dead"})

=============================================================================
