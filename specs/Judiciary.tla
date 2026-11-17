----------------------------- MODULE Judiciary -----------------------------
(***************************************************************************)
(* A TLA+ model of the federal judiciary: the one Supreme Court, the       *)
(* inferior Article III courts Congress ordains and establishes, and       *)
(* Article I tribunals. Companion to Constitution.tla.                     *)
(*                                                                         *)
(* PROPERTIES (each an invariant; each local, see "How each is local")     *)
(*   OneSupremeCourt        Art. III s.1 "one supreme Court": the Supreme  *)
(*                          Court always exists, and is the only court of  *)
(*                          that tier                                      *)
(*   CourtsAreEstablished   representation: a court exists iff it has a    *)
(*                          tier (holds under every mutation)              *)
(*   BenchFitsSeats         Art. III s.1, Art. I s.8 cl.9: no court has    *)
(*                          more judges than the seats Congress gave it    *)
(*   NoJudgeOnTwoCourts     one commission, one court                      *)
(*   JudgesAreNotInCongress Art. I s.6 cl.2, Incompatibility Clause        *)
(*   DisqualifiedDoNotSit   Art. I s.3 cl.7, disqualification on conviction *)
(*   ChiefJusticeSits       Art. I s.3 cl.6, Art. II s.2: the Chief        *)
(*                          Justice is one of the Justices                 *)
(*   OriginalJurisdiction   Art. III s.2 cl.2 and Marbury v. Madison       *)
(*                          (1803): the Supreme Court tries only the heads *)
(*                          the text gives it                              *)
(*   EleventhAmendment      Amend. XI: no suit against a State by a        *)
(*                          citizen of another State or a foreigner        *)
(*   AppealsCourtsAreAppellate  courts of appeals try nothing (Evarts Act  *)
(*                          1891, Judicial Code 1911)                      *)
(*   PublicRightsOnly       Northern Pipeline v. Marathon (1982): an       *)
(*                          Article I court tries only public-rights       *)
(*                          ("Federal") matters                            *)
(*   JuryAndVenue           Art. III s.2 cl.3: crimes tried by jury in the *)
(*                          State where committed                          *)
(*   TreasonProof           Art. III s.3 cl.1: two witnesses to the same   *)
(*                          overt act, or confession in open court         *)
(*   NoDoubleJeopardy       Amend. V: no appeal from an acquittal          *)
(*   ExceptionsHonoured     Art. III s.2 cl.2, Exceptions Clause: the      *)
(*                          Supreme Court takes no appeal Congress has     *)
(*                          excepted                                       *)
(*   ExceptionsBindPending  Ex parte McCardle (1869): an exception made    *)
(*                          while an appeal is pending binds it; the Court *)
(*                          dismisses rather than decides                  *)
(*   CompensationClause     Art. III s.1: a sitting Article III judge's    *)
(*                          pay is never diminished                        *)
(*   GoodBehaviour          Art. III s.1, Art. II s.4, Art. I s.2-3: an    *)
(*                          Article III judge leaves the bench only by     *)
(*                          resignation or death, conviction on a House    *)
(*                          impeachment by two-thirds of the Senate, or    *)
(*                          the abolition of the court (Stuart v. Laird)   *)
(*   Safety                 the conjunction of the above                   *)
(*                                                                         *)
(* Changes of meaning from the module's earlier text (README "Bugs TLC     *)
(* found"): ExceptionsHonoured was a state predicate, "a case pending in   *)
(* the Supreme Court on appeal is of a kind not excepted"; TLC refutes it  *)
(* there, because Congress may except a head while the appeal is pending,  *)
(* which is McCardle itself. It is now the claim at the step that takes    *)
(* the appeal, and ExceptionsBindPending is the claim at the step that     *)
(* decides it (a new guard on AppellateDecide and a new Dismiss action).   *)
(* AppealsCourtsAreAppellate read tier[origCourt] in the current state;    *)
(* TLC refutes that too, because a district court may be abolished after   *)
(* its case moved up and its identifier re-used for a court of appeals.    *)
(* It now reads trialTier, the tier recorded when the case was filed, and  *)
(* OriginalJurisdiction reads it too (it read origCourt = SupremeCourt,    *)
(* which names an identifier, not a tier).                                 *)
(* CompensationClause and GoodBehaviour were action properties; each is    *)
(* now a flag set at the step that would violate it (payCut,               *)
(* offBenchOtherwise), so it is an invariant a mutation can break. The     *)
(* flag for GoodBehaviour is raised by every step that removes an Article  *)
(* III judge other than Resign, Convict after a House impeachment and a    *)
(* two-thirds vote, and AbolishCourt: TermExpires reaching an Article III  *)
(* court, and Convict without impeachment or without two-thirds. The       *)
(* other names keep their meaning.                                         *)
(*                                                                         *)
(* MUTATIONS (Mut = "none" is the text; each other value removes one       *)
(* guard, written where the guard is)                                      *)
(*   M_ABOLISH_SC      AbolishCourt loses c # SupremeCourt. No earlier     *)
(*                     text (the Repeal Act of 1802 only cancelled two     *)
(*                     Terms). Breaks OneSupremeCourt, ChiefJusticeSits.   *)
(*   M_COURT_OF_UNION  EstablishCourt may create a second court of the     *)
(*                     Supreme tier: the "Court of the Union" the Council  *)
(*                     of State Governments proposed in 1962. Breaks       *)
(*                     OneSupremeCourt.                                    *)
(*   M_REESTABLISH     EstablishCourt loses c \notin courts: Congress      *)
(*                     re-makes a sitting court, the Supreme Court         *)
(*                     included. Breaks OneSupremeCourt, ChiefJusticeSits. *)
(*   M_SHRINK          SetSeats loses n >= the sitting bench: a reduction  *)
(*                     with immediate effect, where the Acts of 1801 and   *)
(*                     1866 reduced the Court only as seats fell vacant.   *)
(*                     Breaks BenchFitsSeats.                              *)
(*   M_VACANCY_RECHECK ConfirmJudge does not re-check the vacancy it was   *)
(*                     nominated to. Breaks BenchFitsSeats.                *)
(*   M_CONFIRM_RECHECK ConfirmJudge does not re-check eligibility at       *)
(*                     confirmation. Breaks NoJudgeOnTwoCourts.            *)
(*   M_CHIEF_RECHECK   ConfirmChief does not re-check, at confirmation,    *)
(*                     the seat or the eligibility and vacancy checked at  *)
(*                     nomination: this module's own earlier text, which   *)
(*                     TLC refuted (README). Breaks NoJudgeOnTwoCourts,    *)
(*                     BenchFitsSeats.                                     *)
(*   M_INCOMPAT        a member of Congress may be appointed: the English  *)
(*                     practice in which the Law Lords sat in Parliament   *)
(*                     until 2009. Breaks JudgesAreNotInCongress.          *)
(*   M_DISQUAL         a judgment of disqualification is not honoured at   *)
(*                     appointment. Breaks DisqualifiedDoNotSit.           *)
(*   M_MARBURY         the Supreme Court may try any head: s.13 of the     *)
(*                     Judiciary Act of 1789 as Marbury read it (original  *)
(*                     mandamus). Breaks OriginalJurisdiction.             *)
(*   M_CHISHOLM        a State may be sued by an outsider: Chisholm v.     *)
(*                     Georgia (1793), before Amend. XI (1795). Breaks     *)
(*                     EleventhAmendment.                                  *)
(*   M_CIRCUIT         a court of appeals may try cases: the circuit       *)
(*                     courts of the Judiciary Act of 1789 (abolished      *)
(*                     1911). Breaks AppealsCourtsAreAppellate.            *)
(*   M_NORTHERN_PIPELINE an Article I court may try any head: the          *)
(*                     Bankruptcy Act of 1978 struck down in Northern      *)
(*                     Pipeline. Breaks PublicRightsOnly.                  *)
(*   M_NOJURY          a crime may be tried without a jury: the            *)
(*                     vice-admiralty courts of the Declaration of         *)
(*                     Independence's grievances. Breaks JuryAndVenue.     *)
(*   M_VENUE           a crime may be tried outside the State where        *)
(*                     committed: "transporting us beyond Seas to be       *)
(*                     tried" (the Dockyards Act 1772). Breaks             *)
(*                     JuryAndVenue.                                       *)
(*   M_TREASON         a treason conviction without two witnesses or a     *)
(*                     confession: English law before the Treason Act      *)
(*                     1696. Breaks TreasonProof.                          *)
(*   M_KEPNER          the prosecution may appeal an acquittal: the        *)
(*                     Spanish-derived procedure of Kepner v. United       *)
(*                     States (1904), and the state statute of Palko v.    *)
(*                     Connecticut (1937). Breaks NoDoubleJeopardy.        *)
(*   M_EXCEPTIONS      Appeal ignores Congress's exceptions. Breaks        *)
(*                     ExceptionsHonoured.                                 *)
(*   M_MCCARDLE        AppellateDecide does not re-check the exceptions:   *)
(*                     this module's own earlier text, which checked them  *)
(*                     only when the appeal was taken, and the course      *)
(*                     McCardle refused. Breaks ExceptionsBindPending.     *)
(*   M_PAYCUT          Congress may cut a sitting Article III judge's pay: *)
(*                     "dependent on his Will alone, for ... the amount    *)
(*                     and payment of their salaries" (Declaration of      *)
(*                     Independence). Breaks CompensationClause.           *)
(*   M_TENURE          fixed terms reach Article III judges: tenure at     *)
(*                     pleasure, as English judges held office before the  *)
(*                     Act of Settlement 1701. Breaks GoodBehaviour,       *)
(*                     ChiefJusticeSits.                                   *)
(*   M_NOIMPEACH       the Senate may convict without a House impeachment  *)
(*                     (Art. I s.2 cl.5 gives the House the sole power).   *)
(*                     Breaks GoodBehaviour.                               *)
(*   M_CHASE           a simple majority of the Senate convicts: Samuel    *)
(*                     Chase (1805) would have been removed, 19 of 34 on   *)
(*                     the eighth article. Breaks GoodBehaviour.           *)
(* The checks at nomination (NominateJudge, NominateChief) carry no        *)
(* property alone: the re-checks at confirmation do, so the confirmation   *)
(* checks are the ones mutated. The column "Breaks" above is what the TLC  *)
(* results file shows and what Judiciary_proof.tla's hypotheses restate.   *)
(*                                                                         *)
(* WITNESSES (Never... operators; each must be VIOLATED under Mut = none)  *)
(*   NeverUnseatedByAbolition  a court established, staffed, abolished     *)
(*   NeverDisqualified         a judge convicted and disqualified          *)
(*   NeverChiefJustice         a Chief Justice confirmed                   *)
(*   NeverEnlarged             Congress enlarges a court (MaxSeats >= 2)   *)
(*   NeverOriginalAction       an original action in the Supreme Court     *)
(*   NeverArticleITrial        an Article I court tries a case             *)
(*   NeverTreasonConviction    a treason conviction                        *)
(*   NeverAcquittal            a criminal acquittal                        *)
(*   NeverReachesSupremeCourt  an appeal reaches the Supreme Court         *)
(*   NeverStrippedWhilePending Congress excepts the head of a pending      *)
(*                             appeal (McCardle's facts)                   *)
(*   NeverDismissed            the Court dismisses for want of             *)
(*                             jurisdiction                                *)
(*   NeverSalaryRaised         Congress raises a court's pay               *)
(*                                                                         *)
(* HOW EACH IS LOCAL. ExceptionsHonoured, ExceptionsBindPending,           *)
(* CompensationClause and GoodBehaviour are flags raised by the one step   *)
(* that would violate them, against that step's guard. JuryAndVenue,      *)
(* TreasonProof, OriginalJurisdiction, EleventhAmendment,                  *)
(* AppealsCourtsAreAppellate and PublicRightsOnly read fields of the case  *)
(* record written once, at File or Decide, against that step's guard.      *)
(* The others are state predicates whose step is decided by the guard of   *)
(* each action that grows a bench, a seat count or the set of courts.      *)
(* BenchFitsSeats counts: seats are a number Congress sets (six in 1789,   *)
(* nine since 1869), and the claim is that the bench never outnumbers      *)
(* them, so Cardinality is the design here, not a convenience.             *)
(*                                                                         *)
(* ABSTRACTED. The President (nominations just happen); presentment (a     *)
(* "statute" is a majority of both houses: compose with Constitution.tla); *)
(* who the members of Congress are (a constant, so nobody is elected to    *)
(* Congress while a judge or nominee); judicial review as a holding;       *)
(* Amend. VI-VII (speedy trial, civil juries: a civil trial records no     *)
(* jury); remand; senior status; death (folded into Resign); the evidence  *)
(* at a trial other than treason (recorded as none). The heads of          *)
(* jurisdiction a run includes are the constant Kinds, a subset of the     *)
(* seven heads AllKinds. Time is the order of steps. Who sits on a case:   *)
(* a court decides whether or not its bench is full. The earlier text      *)
(* required a sitting judge at Decide and AppellateDecide; no property     *)
(* read that guard, and it was the only place a case read a judge          *)
(* variable. Without it the cases read only the courts, the tiers, the     *)
(* locations and the exceptions, and the judges read the cases only in     *)
(* AbolishCourt's "no live case" guard, which a run without cases relaxes. *)
(* So a run with no cases reaches every judge-side state a run with cases  *)
(* reaches, and a run with no persons every case-side state; the row list  *)
(* checks each property at the profile its own variables need.            *)
(*                                                                         *)
(* LIVENESS. None: the text promises no progress for anything modelled     *)
(* here (the speedy-trial right of Amend. VI is not modelled), so Spec has *)
(* no fairness. Congress may always legislate, so no state is terminal;    *)
(* the DEADLOCK row in rows/Judiciary-rows.txt audits that.                *)
(*                                                                         *)
(* CONSTANTS. Well-formedness conditions are the named ASSUMEs below.      *)
(* MaxSeats and MaxSalary only bound the model for TLC and are assumed     *)
(* nothing; Judiciary_proof.tla proves every invariant for every value.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Mut,            \* "none", or the mutation in force (see the header)
  Persons,        \* everyone who might be a judge
  House,          \* members of the House: their number decides a vote, and
  Senate,         \* members of the Senate: none of them may be a judge
  States,         \* the several States (venue for criminal trials)
  CourtIds,       \* pool of court identifiers
  SupremeCourt,   \* the distinguished member of CourtIds
  Cases,          \* case identifiers
  Kinds,          \* the heads of jurisdiction this run includes
  MaxSeats,       \* bound on seats per court (TLC only)
  MaxSalary,      \* bound on judicial salary (TLC only)
  NoOne           \* vacancy marker

\* Heads of jurisdiction, Art. III sec. 2 cl. 1
AllKinds == {"Federal",       \* arising under the Constitution, laws, treaties
             "Diversity",     \* between citizens of different States
             "Ambassador",    \* affecting ambassadors, ministers, consuls
             "StateIsParty",  \* a State is a party (and consents or sues)
             "AgainstState",  \* a State sued by a citizen of another State
                              \* or a foreigner - withdrawn by Amend. XI
             "Crime",
             "Treason"}

ASSUME SupremeCourtWF == SupremeCourt \in CourtIds
ASSUME NoOneWF        == NoOne \notin Persons
ASSUME PersonsFinite  == IsFiniteSet(Persons)
ASSUME CongressWF     == House \cap Senate = {}
ASSUME KindsWF        == Kinds \subseteq AllKinds

-----------------------------------------------------------------------------
(* Helpers *)

Congress == House \cup Senate
Seat     == Persons \cup {NoOne}

Majority(ayes, body)  == 2 * ayes >  Cardinality(body)
TwoThirds(ayes, body) == 3 * ayes >= 2 * Cardinality(body)
HouseVotes  == 0..Cardinality(House)
SenateVotes == 0..Cardinality(Senate)

\* Art. I sec. 7, abstracted: a statute is a majority of both houses.
Statute(h, s) == Majority(h, House) /\ Majority(s, Senate)

Tiers         == {"None", "Supreme", "Appeals", "District", "ArticleI"}
InferiorTiers == {"Appeals", "District", "ArticleI"}

\* Art. III sec. 2 cl. 2: "affecting Ambassadors, other public Ministers
\* and Consuls, and those in which a State shall be Party".
OriginalKinds == {"Ambassador", "StateIsParty", "AgainstState"}
Criminal      == {"Crime", "Treason"}

Verdicts == {"None", "Guilty", "NotGuilty", "Judgment", "Affirmed",
             "Reversed", "Dismissed"}
Status   == {"Unfiled", "Pending", "Decided", "Closed"}

-----------------------------------------------------------------------------
VARIABLES
  (* Courts - Art. III sec. 1, Art. I sec. 8 cl. 9 *)
  courts,          \* SUBSET CourtIds currently established
  tier,            \* CourtIds -> Tiers
  location,        \* CourtIds -> States \cup {"None"}; district courts sit in a State
  seats,           \* CourtIds -> Nat, set by Congress
  salary,          \* CourtIds -> Nat, set by Congress
  exceptions,      \* SUBSET Kinds stripped from Supreme Court appellate review

  (* Judges - Art. II sec. 2, Art. III sec. 1 *)
  bench,           \* CourtIds -> SUBSET Persons sitting on that court
  nominee,         \* CourtIds -> Seat
  chiefJustice,    \* Seat
  chiefNominee,    \* Seat

  (* Removal - Art. II sec. 4 *)
  impeached,       \* SUBSET Persons awaiting trial in the Senate
  disqualified,    \* SUBSET Persons disqualified on conviction
  unseated,        \* SUBSET Persons who lost a seat when their court was
                   \* abolished (witness record; nothing reads it)

  (* Cases - Art. III sec. 2-3 *)
  case,            \* Cases -> CaseRecord

  (* Flags, each raised only by the step that would violate a property *)
  payCut,            \* CompensationClause
  offBenchOtherwise, \* GoodBehaviour
  exceptedTaken,     \* ExceptionsHonoured
  exceptedDecided    \* ExceptionsBindPending

courtVars == <<courts, tier, location, seats, salary, exceptions>>
judgeVars == <<bench, nominee, chiefJustice, chiefNominee>>
impVars   == <<impeached, disqualified, unseated>>
flagVars  == <<payCut, offBenchOtherwise, exceptedTaken, exceptedDecided>>
vars      == <<courtVars, judgeVars, impVars, case, flagVars>>

CaseRecord ==
  [kind         : Kinds \cup {"None"},     \* "None" until filed
   status       : Status,
   court        : CourtIds \cup {"None"},   \* where it sits now
   origCourt    : CourtIds \cup {"None"},   \* where it was filed and tried
   trialTier    : Tiers,                    \* that court's tier at filing
   crimeState   : States \cup {"None"},     \* where the crime was committed
   venue        : States \cup {"None"},     \* where it was actually tried
   jury         : BOOLEAN,
   witnesses    : 0..2,                     \* witnesses to the same overt act
   confession   : BOOLEAN,                  \* confession in open court
   trialVerdict : Verdicts,
   verdict      : Verdicts]

NoCase ==
  [kind |-> "None", status |-> "Unfiled", court |-> "None", origCourt |-> "None",
   trialTier |-> "None", crimeState |-> "None", venue |-> "None",
   jury |-> FALSE, witnesses |-> 0, confession |-> FALSE,
   trialVerdict |-> "None", verdict |-> "None"]

TypeOK ==
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
  /\ case \in [Cases -> CaseRecord]
  /\ payCut \in BOOLEAN
  /\ offBenchOtherwise \in BOOLEAN
  /\ exceptedTaken \in BOOLEAN
  /\ exceptedDecided \in BOOLEAN

IsJudge(p)    == \E cj \in CourtIds : p \in bench[cj]
ArticleIII(c) == tier[c] \in {"Supreme", "Appeals", "District"}
OnArticleIIIBench(p) == \E ca \in CourtIds : ArticleIII(ca) /\ p \in bench[ca]
HasVacancy(c) == Cardinality(bench[c]) < seats[c]

-----------------------------------------------------------------------------
(* The guards a mutation removes. Each is one check, written once.         *)

\* Art. III sec. 1: "one supreme Court". Congress establishes only
\* inferior courts, never a second court of the Supreme tier ...
EstablishableTiers ==
  IF Mut = "M_COURT_OF_UNION" THEN InferiorTiers \cup {"Supreme"} ELSE InferiorTiers
\* ... only courts that do not exist yet ...
NewCourt(c) == IF Mut = "M_REESTABLISH" THEN TRUE ELSE c \notin courts
\* ... and abolishes any court but the Supreme Court.
Abolishable(c) == IF Mut = "M_ABOLISH_SC" THEN TRUE ELSE c # SupremeCourt

\* A reduction in seats takes effect by attrition (Acts of 1801, 1866).
ByAttrition(c, n) == IF Mut = "M_SHRINK" THEN TRUE ELSE n >= Cardinality(bench[c])

\* Compensation Clause, Art. III sec. 1.
PayProtected(c, n) ==
  IF Mut = "M_PAYCUT" THEN TRUE
  ELSE (ArticleIII(c) /\ bench[c] # {}) => n >= salary[c]

\* Art. I sec. 6 cl. 2 and Art. I sec. 3 cl. 7, tested at nomination and
\* again at confirmation.
NotInCongress(p)   == IF Mut = "M_INCOMPAT" THEN TRUE ELSE p \notin Congress
NotDisqualified(p) == IF Mut = "M_DISQUAL" THEN TRUE ELSE p \notin disqualified
Eligible(p) == NotDisqualified(p) /\ NotInCongress(p) /\ ~IsJudge(p)

\* The re-checks at confirmation: the nominee may since have been seated
\* elsewhere, convicted, or the vacancy filled.
StillEligible(c) == IF Mut = "M_CONFIRM_RECHECK" THEN TRUE ELSE Eligible(nominee[c])
StillVacant(c)   == IF Mut = "M_VACANCY_RECHECK" THEN TRUE ELSE HasVacancy(c)
ChiefStillFits ==
  IF Mut = "M_CHIEF_RECHECK" THEN TRUE
  ELSE \/ chiefNominee \in bench[SupremeCourt]
       \/ Eligible(chiefNominee) /\ HasVacancy(SupremeCourt)

\* Good Behaviour: only Article I judges serve fixed terms.
FixedTerm(c) == IF Mut = "M_TENURE" THEN TRUE ELSE tier[c] = "ArticleI"
\* Art. I sec. 2 cl. 5 and sec. 3 cl. 6.
Impeached(p) == IF Mut = "M_NOIMPEACH" THEN TRUE ELSE p \in impeached
ConvictionVote(ayes) ==
  IF Mut = "M_CHASE" THEN Majority(ayes, Senate) ELSE TwoThirds(ayes, Senate)

\* Art. III sec. 2 cl. 2 and Amend. XI: where a case may be filed in the
\* first instance. Fixed by the Constitution; no action of Congress
\* changes it.
SuableState(k)     == IF Mut = "M_CHISHOLM" THEN TRUE ELSE k # "AgainstState"
SupremeOriginal(k) == IF Mut = "M_MARBURY" THEN TRUE ELSE k \in OriginalKinds
AppealsOriginal    == Mut = "M_CIRCUIT"
PublicRights(k)    == IF Mut = "M_NORTHERN_PIPELINE" THEN TRUE ELSE k = "Federal"

HasOriginalJurisdiction(k, c) ==
  /\ c \in courts
  /\ SuableState(k)
  /\ \/ tier[c] = "Supreme"  /\ SupremeOriginal(k)
     \/ tier[c] = "District"
     \/ tier[c] = "ArticleI" /\ PublicRights(k)
     \/ tier[c] = "Appeals"  /\ AppealsOriginal

\* Art. III sec. 2 cl. 3 and sec. 3 cl. 1.
TrialByJury(j)             == IF Mut = "M_NOJURY" THEN TRUE ELSE j
TriedWhereCommitted(c, st) == IF Mut = "M_VENUE" THEN TRUE ELSE location[c] = st
TreasonProven(w, conf)     == IF Mut = "M_TREASON" THEN TRUE ELSE w = 2 \/ conf

\* Amend. V, and the Exceptions Clause on the way up and at judgment.
NotAcquitted(x) == IF Mut = "M_KEPNER" THEN TRUE ELSE case[x].trialVerdict # "NotGuilty"
NotExcepted(x)  == IF Mut = "M_EXCEPTIONS" THEN TRUE ELSE case[x].kind \notin exceptions
StillHeard(x)   == IF Mut = "M_MCCARDLE" THEN TRUE ELSE case[x].kind \notin exceptions

-----------------------------------------------------------------------------
Init ==
  /\ courts = {SupremeCourt}
  /\ tier = [c \in CourtIds |-> IF c = SupremeCourt THEN "Supreme" ELSE "None"]
  /\ location = [c \in CourtIds |-> "None"]
  /\ seats = [c \in CourtIds |-> IF c = SupremeCourt THEN 1 ELSE 0]
  /\ salary = [c \in CourtIds |-> 0]
  /\ exceptions = {}
  /\ bench = [c \in CourtIds |-> {}]
  /\ nominee = [c \in CourtIds |-> NoOne]
  /\ chiefJustice = NoOne
  /\ chiefNominee = NoOne
  /\ impeached = {}
  /\ disqualified = {}
  /\ unseated = {}
  /\ case = [x \in Cases |-> NoCase]
  /\ payCut = FALSE
  /\ offBenchOtherwise = FALSE
  /\ exceptedTaken = FALSE
  /\ exceptedDecided = FALSE

-----------------------------------------------------------------------------
(* Congress and the courts - Art. III sec. 1, Art. I sec. 8 cl. 9         *)

\* Congress ordains and establishes an inferior court.
EstablishCourt(c, t, st, h, s) ==
  /\ Statute(h, s)
  /\ NewCourt(c)
  /\ t \in EstablishableTiers
  /\ (t = "District") <=> (st \in States)      \* trial courts sit somewhere
  /\ courts' = courts \cup {c}
  /\ tier' = [tier EXCEPT ![c] = t]
  /\ location' = [location EXCEPT ![c] = st]
  /\ seats' = [seats EXCEPT ![c] = 1]
  /\ UNCHANGED <<salary, exceptions, judgeVars, impVars, case, flagVars>>

\* Congress abolishes an inferior court. Its judges lose their seats
\* (Repeal Act of 1802; Stuart v. Laird). Not while it holds a live case.
AbolishCourt(c, h, s) ==
  /\ Statute(h, s)
  /\ c \in courts
  /\ Abolishable(c)
  /\ \A xa \in Cases : case[xa].court # c \/ case[xa].status \in {"Unfiled", "Closed"}
  /\ courts' = courts \ {c}
  /\ tier' = [tier EXCEPT ![c] = "None"]
  /\ location' = [location EXCEPT ![c] = "None"]
  /\ seats' = [seats EXCEPT ![c] = 0]
  /\ bench' = [bench EXCEPT ![c] = {}]
  /\ nominee' = [nominee EXCEPT ![c] = NoOne]
  /\ unseated' = unseated \cup bench[c]
  /\ UNCHANGED <<salary, exceptions, chiefJustice, chiefNominee, impeached,
                 disqualified, case, flagVars>>

\* Congress sets the size of a court, the Supreme Court included (it has
\* been 5, 6, 7, 9 and 10).
SetSeats(c, n, h, s) ==
  /\ Statute(h, s)
  /\ c \in courts
  /\ n \in 1..MaxSeats
  /\ ByAttrition(c, n)
  /\ seats' = [seats EXCEPT ![c] = n]
  /\ UNCHANGED <<courts, tier, location, salary, exceptions, judgeVars, impVars,
                 case, flagVars>>

\* Congress sets compensation. An Article I judge or an empty court has
\* no protection.
SetSalary(c, n, h, s) ==
  /\ Statute(h, s)
  /\ c \in courts
  /\ n \in 0..MaxSalary
  /\ PayProtected(c, n)
  /\ salary' = [salary EXCEPT ![c] = n]
  /\ payCut' = (payCut \/ (ArticleIII(c) /\ bench[c] # {} /\ n < salary[c]))
  /\ UNCHANGED <<courts, tier, location, seats, exceptions, judgeVars, impVars,
                 case, offBenchOtherwise, exceptedTaken, exceptedDecided>>

\* Exceptions Clause, Art. III sec. 2 cl. 2: Congress may strip heads of
\* jurisdiction from the Supreme Court's appellate docket (McCardle),
\* even while an appeal in that head is pending. It cannot touch original
\* jurisdiction (Marbury): see HasOriginalJurisdiction.
SetExceptions(E, h, s) ==
  /\ Statute(h, s)
  /\ E \subseteq Kinds
  /\ exceptions' = E
  /\ UNCHANGED <<courts, tier, location, seats, salary, judgeVars, impVars,
                 case, flagVars>>

-----------------------------------------------------------------------------
(* Judges - Art. II sec. 2 cl. 2, Art. III sec. 1                          *)

NominateJudge(c, p) ==
  /\ c \in courts
  /\ HasVacancy(c)
  /\ nominee[c] = NoOne
  /\ Eligible(p)
  /\ nominee' = [nominee EXCEPT ![c] = p]
  /\ UNCHANGED <<courtVars, bench, chiefJustice, chiefNominee, impVars, case,
                 flagVars>>

ConfirmJudge(c, ayes) ==
  /\ nominee[c] # NoOne
  /\ Majority(ayes, Senate)
  /\ StillEligible(c)
  /\ StillVacant(c)
  /\ bench' = [bench EXCEPT ![c] = @ \cup {nominee[c]}]
  /\ nominee' = [nominee EXCEPT ![c] = NoOne]
  /\ UNCHANGED <<courtVars, chiefJustice, chiefNominee, impVars, case, flagVars>>

RejectJudge(c) ==
  /\ nominee[c] # NoOne
  /\ nominee' = [nominee EXCEPT ![c] = NoOne]
  /\ UNCHANGED <<courtVars, bench, chiefJustice, chiefNominee, impVars, case,
                 flagVars>>

\* The Chief Justice is a separately confirmed office. The nominee may
\* already be an Associate Justice (White 1910, Stone 1941, Rehnquist 1986)
\* or an outsider who needs a vacant seat.
NominateChief(p) ==
  /\ chiefJustice = NoOne
  /\ chiefNominee = NoOne
  /\ NotDisqualified(p) /\ NotInCongress(p)
  /\ p \in bench[SupremeCourt] \/ ~IsJudge(p)
  /\ chiefNominee' = p
  /\ UNCHANGED <<courtVars, bench, nominee, chiefJustice, impVars, case, flagVars>>

ConfirmChief(ayes) ==
  /\ chiefNominee # NoOne
  /\ Majority(ayes, Senate)
  /\ ChiefStillFits
  /\ bench' = [bench EXCEPT ![SupremeCourt] = @ \cup {chiefNominee}]
  /\ chiefJustice' = chiefNominee
  /\ chiefNominee' = NoOne
  /\ UNCHANGED <<courtVars, nominee, impVars, case, flagVars>>

RejectChief ==
  /\ chiefNominee # NoOne
  /\ chiefNominee' = NoOne
  /\ UNCHANGED <<courtVars, bench, nominee, chiefJustice, impVars, case, flagVars>>

\* Death or resignation.
Resign(c, p) ==
  /\ p \in bench[c]
  /\ bench' = [bench EXCEPT ![c] = @ \ {p}]
  /\ chiefJustice' = IF p = chiefJustice THEN NoOne ELSE chiefJustice
  /\ UNCHANGED <<courtVars, nominee, chiefNominee, impVars, case, flagVars>>

\* Article I judges serve fixed terms; "good Behaviour" does not reach them.
TermExpires(c, p) ==
  /\ FixedTerm(c)
  /\ p \in bench[c]
  /\ bench' = [bench EXCEPT ![c] = @ \ {p}]
  /\ offBenchOtherwise' = (offBenchOtherwise \/ ArticleIII(c))
  /\ UNCHANGED <<courtVars, nominee, chiefJustice, chiefNominee, impVars, case,
                 payCut, exceptedTaken, exceptedDecided>>

-----------------------------------------------------------------------------
(* Removal - Art. I sec. 2-3, Art. II sec. 4                               *)
(* Judges are civil officers: Pickering (1804), Chase (acquitted 1805),    *)
(* and thirteen others since.                                              *)

Impeach(p, ayes) ==
  /\ IsJudge(p)
  /\ p \notin impeached
  /\ Majority(ayes, House)
  /\ impeached' = impeached \cup {p}
  /\ UNCHANGED <<courtVars, judgeVars, disqualified, unseated, case, flagVars>>

Convict(p, ayes, dq) ==
  /\ Impeached(p)
  /\ ConvictionVote(ayes)
  /\ offBenchOtherwise' =
       (offBenchOtherwise \/
          (OnArticleIIIBench(p) /\ ~(p \in impeached /\ TwoThirds(ayes, Senate))))
  /\ impeached' = impeached \ {p}
  /\ disqualified' = IF dq THEN disqualified \cup {p} ELSE disqualified
  /\ bench' = [cv \in CourtIds |-> bench[cv] \ {p}]
  /\ chiefJustice' = IF p = chiefJustice THEN NoOne ELSE chiefJustice
  /\ nominee' = [cv \in CourtIds |-> IF nominee[cv] = p THEN NoOne ELSE nominee[cv]]
  /\ chiefNominee' = IF chiefNominee = p THEN NoOne ELSE chiefNominee
  /\ UNCHANGED <<courtVars, unseated, case, payCut, exceptedTaken, exceptedDecided>>

Acquit(p) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ UNCHANGED <<courtVars, judgeVars, disqualified, unseated, case, flagVars>>

-----------------------------------------------------------------------------
(* Cases - Art. III sec. 2-3                                               *)

File(x, k, c, st) ==
  /\ case[x].status = "Unfiled"
  /\ k \in Kinds
  /\ HasOriginalJurisdiction(k, c)
  /\ (k \in Criminal) <=> (st \in States)
  /\ case' = [case EXCEPT ![x] =
                [kind |-> k, status |-> "Pending", court |-> c, origCourt |-> c,
                 trialTier |-> tier[c], crimeState |-> st, venue |-> "None",
                 jury |-> FALSE, witnesses |-> 0, confession |-> FALSE,
                 trialVerdict |-> "None", verdict |-> "None"]]
  /\ UNCHANGED <<courtVars, judgeVars, impVars, flagVars>>

\* Trial-court decision. A civil trial records no jury (Amend. VII is not
\* modelled) and a trial other than for treason records no evidence.
Decide(x, jury, w, conf, v) ==
  /\ case[x].status = "Pending"
  /\ case[x].court = case[x].origCourt
  /\ (case[x].kind \in Criminal) => TrialByJury(jury)
  /\ (case[x].kind \in Criminal) => TriedWhereCommitted(case[x].court, case[x].crimeState)
  /\ (case[x].kind \notin Criminal) => ~jury
  /\ (case[x].kind # "Treason") => (w = 0 /\ ~conf)
  /\ v \in (IF case[x].kind \in Criminal THEN {"Guilty", "NotGuilty"} ELSE {"Judgment"})
  /\ (case[x].kind = "Treason" /\ v = "Guilty") => TreasonProven(w, conf)
  /\ case' = [case EXCEPT ![x].status = "Decided", ![x].jury = jury,
                          ![x].venue = location[case[x].court],
                          ![x].witnesses = w, ![x].confession = conf,
                          ![x].trialVerdict = v, ![x].verdict = v]
  /\ UNCHANGED <<courtVars, judgeVars, impVars, flagVars>>

\* Appeal to the next tier. Article I and district decisions go to a court
\* of appeals; a court of appeals goes to the Supreme Court unless Congress
\* has excepted that head. Nothing lies from the Supreme Court.
Appeal(x, c) ==
  /\ case[x].status = "Decided"
  /\ c \in courts
  /\ NotAcquitted(x)
  /\ \/ tier[case[x].court] \in {"District", "ArticleI"} /\ tier[c] = "Appeals"
     \/ tier[case[x].court] = "Appeals" /\ c = SupremeCourt /\ NotExcepted(x)
  /\ exceptedTaken' =
       (exceptedTaken \/ (tier[case[x].court] = "Appeals" /\ c = SupremeCourt
                          /\ case[x].kind \in exceptions))
  /\ case' = [case EXCEPT ![x].status = "Pending", ![x].court = c,
                          ![x].verdict = "None"]
  /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise,
                 exceptedDecided>>

AppellateDecide(x, v) ==
  /\ case[x].status = "Pending"
  /\ case[x].court # case[x].origCourt
  /\ v \in {"Affirmed", "Reversed"}
  /\ (case[x].court = SupremeCourt) => StillHeard(x)
  /\ exceptedDecided' =
       (exceptedDecided \/ (case[x].court = SupremeCourt /\ case[x].kind \in exceptions))
  /\ case' = [case EXCEPT ![x].status = "Decided", ![x].verdict = v]
  /\ UNCHANGED <<courtVars, judgeVars, impVars, payCut, offBenchOtherwise,
                 exceptedTaken>>

\* Ex parte McCardle (1869): jurisdiction withdrawn while the appeal is
\* pending; the Court "can only ... announc[e] the fact and dismiss[] the
\* cause". The judgment below stands.
Dismiss(x) ==
  /\ case[x].status = "Pending"
  /\ case[x].court = SupremeCourt
  /\ case[x].court # case[x].origCourt
  /\ case[x].kind \in exceptions
  /\ case' = [case EXCEPT ![x].status = "Closed", ![x].verdict = "Dismissed"]
  /\ UNCHANGED <<courtVars, judgeVars, impVars, flagVars>>

\* No further review sought, or certiorari denied.
Close(x) ==
  /\ case[x].status = "Decided"
  /\ case' = [case EXCEPT ![x].status = "Closed"]
  /\ UNCHANGED <<courtVars, judgeVars, impVars, flagVars>>

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in CourtIds, t \in Tiers, st \in States \cup {"None"},
        h \in HouseVotes, s \in SenateVotes : EstablishCourt(c, t, st, h, s)
  \/ \E c \in CourtIds, h \in HouseVotes, s \in SenateVotes : AbolishCourt(c, h, s)
  \/ \E c \in CourtIds, n \in 1..MaxSeats, h \in HouseVotes, s \in SenateVotes :
        SetSeats(c, n, h, s)
  \/ \E c \in CourtIds, n \in 0..MaxSalary, h \in HouseVotes, s \in SenateVotes :
        SetSalary(c, n, h, s)
  \/ \E E \in SUBSET Kinds, h \in HouseVotes, s \in SenateVotes : SetExceptions(E, h, s)
  \/ \E c \in CourtIds, p \in Persons : NominateJudge(c, p)
  \/ \E c \in CourtIds, n \in SenateVotes : ConfirmJudge(c, n)
  \/ \E c \in CourtIds : RejectJudge(c)
  \/ \E p \in Persons : NominateChief(p)
  \/ \E n \in SenateVotes : ConfirmChief(n)
  \/ RejectChief
  \/ \E c \in CourtIds, p \in Persons : Resign(c, p)
  \/ \E c \in CourtIds, p \in Persons : TermExpires(c, p)
  \/ \E p \in Persons, n \in HouseVotes : Impeach(p, n)
  \/ \E p \in Persons, n \in SenateVotes, dq \in BOOLEAN : Convict(p, n, dq)
  \/ \E p \in Persons : Acquit(p)
  \/ \E x \in Cases, k \in Kinds, c \in CourtIds, st \in States \cup {"None"} :
        File(x, k, c, st)
  \/ \E x \in Cases, j \in BOOLEAN, w \in 0..2, conf \in BOOLEAN, v \in Verdicts :
        Decide(x, j, w, conf, v)
  \/ \E x \in Cases, c \in CourtIds : Appeal(x, c)
  \/ \E x \in Cases, v \in Verdicts : AppellateDecide(x, v)
  \/ \E x \in Cases : Dismiss(x)
  \/ \E x \in Cases : Close(x)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* Art. III sec. 1: "one supreme Court" - exactly one, and always.
OneSupremeCourt ==
  /\ SupremeCourt \in courts
  /\ \A c \in CourtIds : tier[c] = "Supreme" <=> c = SupremeCourt

CourtsAreEstablished ==
  \A c \in CourtIds : (c \in courts) <=> (tier[c] # "None")

BenchFitsSeats ==
  \A c \in CourtIds : Cardinality(bench[c]) <= seats[c]

NoJudgeOnTwoCourts ==
  \A c1, c2 \in CourtIds : c1 # c2 => bench[c1] \cap bench[c2] = {}

\* Art. I sec. 6 cl. 2 and Art. I sec. 3 cl. 7
JudgesAreNotInCongress == \A c \in CourtIds : bench[c] \cap Congress = {}
DisqualifiedDoNotSit   == \A c \in CourtIds : bench[c] \cap disqualified = {}

ChiefJusticeSits ==
  chiefJustice = NoOne \/ chiefJustice \in bench[SupremeCourt]

\* Marbury: the Supreme Court's original docket is what Art. III sec. 2
\* cl. 2 says it is.
OriginalJurisdiction ==
  \A x \in Cases :
    case[x].trialTier = "Supreme" => case[x].kind \in OriginalKinds

\* Amend. XI
EleventhAmendment ==
  \A x \in Cases : case[x].status # "Unfiled" => case[x].kind # "AgainstState"

\* Courts of appeals hear only appeals.
AppealsCourtsAreAppellate ==
  \A x \in Cases : case[x].trialTier # "Appeals"

\* Article I courts try only public-rights matters.
PublicRightsOnly ==
  \A x \in Cases : case[x].trialTier = "ArticleI" => case[x].kind = "Federal"

\* Art. III sec. 2 cl. 3
JuryAndVenue ==
  \A x \in Cases :
    (case[x].kind \in Criminal /\ case[x].trialVerdict # "None") =>
      /\ case[x].jury
      /\ case[x].venue = case[x].crimeState   \* recorded at trial; the court
                                              \* may since have been abolished

\* Art. III sec. 3 cl. 1
TreasonProof ==
  \A x \in Cases :
    (case[x].kind = "Treason" /\ case[x].trialVerdict = "Guilty") =>
      (case[x].witnesses = 2 \/ case[x].confession)

\* Amend. V: once acquitted, a defendant never faces an appellate court.
NoDoubleJeopardy ==
  \A x \in Cases :
    case[x].trialVerdict = "NotGuilty" => case[x].court = case[x].origCourt

\* Exceptions Clause honoured on the way up, and at judgment (McCardle).
ExceptionsHonoured    == ~exceptedTaken
ExceptionsBindPending == ~exceptedDecided

\* Compensation Clause, Art. III sec. 1.
CompensationClause == ~payCut

\* Good Behaviour, Art. III sec. 1.
GoodBehaviour == ~offBenchOtherwise

Safety ==
  /\ OneSupremeCourt /\ CourtsAreEstablished /\ BenchFitsSeats
  /\ NoJudgeOnTwoCourts /\ JudgesAreNotInCongress /\ DisqualifiedDoNotSit
  /\ ChiefJusticeSits /\ OriginalJurisdiction /\ EleventhAmendment
  /\ AppealsCourtsAreAppellate /\ PublicRightsOnly /\ JuryAndVenue
  /\ TreasonProof /\ NoDoubleJeopardy /\ ExceptionsHonoured
  /\ ExceptionsBindPending /\ CompensationClause /\ GoodBehaviour

-----------------------------------------------------------------------------
(* Reachability witnesses: each must be VIOLATED under Mut = "none".       *)

NeverUnseatedByAbolition == unseated = {}
NeverDisqualified        == disqualified = {}
NeverChiefJustice        == chiefJustice = NoOne
NeverEnlarged            == \A c \in CourtIds : seats[c] <= 1
NeverOriginalAction      == \A x \in Cases : case[x].trialTier # "Supreme"
NeverArticleITrial       == \A x \in Cases : case[x].trialTier # "ArticleI"
NeverTreasonConviction   ==
  \A x \in Cases : ~(case[x].kind = "Treason" /\ case[x].trialVerdict = "Guilty")
NeverAcquittal           == \A x \in Cases : case[x].trialVerdict # "NotGuilty"
NeverReachesSupremeCourt ==
  \A x \in Cases : ~(case[x].court = SupremeCourt /\ case[x].origCourt # SupremeCourt)
NeverStrippedWhilePending ==
  \A x \in Cases : ~(/\ case[x].status = "Pending"
                     /\ case[x].court = SupremeCourt
                     /\ case[x].origCourt # SupremeCourt
                     /\ case[x].kind \in exceptions)
NeverDismissed           == \A x \in Cases : case[x].verdict # "Dismissed"
NeverSalaryRaised        == \A c \in CourtIds : salary[c] = 0

=============================================================================
