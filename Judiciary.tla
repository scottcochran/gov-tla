----------------------------- MODULE Judiciary -----------------------------
(***************************************************************************)
(* A TLA+ model of the federal judiciary.                                  *)
(*                                                                         *)
(* Companion to Constitution.tla. Covers every federal court the           *)
(* Constitution contemplates:                                              *)
(*                                                                         *)
(*   - the one Supreme Court (Art. III sec. 1), which Congress cannot      *)
(*     abolish but whose size it sets;                                     *)
(*   - inferior Article III courts (district courts, courts of appeals)    *)
(*     that Congress "may from time to time ordain and establish"          *)
(*     (Art. III sec. 1, Art. I sec. 8 cl. 9);                             *)
(*   - Article I "legislative" tribunals (bankruptcy, tax, claims,         *)
(*     military, territorial courts) whose judges lack life tenure.        *)
(*                                                                         *)
(* Provisions modelled:                                                    *)
(*   Art. III sec. 1   one Supreme Court; inferior courts by statute;      *)
(*                     tenure during good behaviour; Compensation Clause   *)
(*   Art. III sec. 2   original vs. appellate jurisdiction; the            *)
(*                     Exceptions Clause; jury and venue for crimes        *)
(*   Art. III sec. 3   treason: two witnesses or open-court confession     *)
(*   Art. I  sec. 8    Congress constitutes inferior tribunals             *)
(*   Art. II sec. 2    judges appointed with advice and consent            *)
(*   Art. II sec. 4    judges are civil officers; removable only by        *)
(*                     impeachment                                         *)
(*   Amend. V          double jeopardy: no appeal from an acquittal        *)
(*   Amend. XI         no federal suit against a State by an outsider      *)
(*   Marbury v. Madison (1803): Congress cannot enlarge the Supreme        *)
(*                     Court's original jurisdiction                       *)
(*   Ex parte McCardle (1869): Congress may strip appellate jurisdiction   *)
(*   Stuart v. Laird (1803): abolishing a court unseats its judges         *)
(*                                                                         *)
(* Abstracted away: the President (nominations just happen), presentment  *)
(* of statutes (a "statute" is a majority of both houses - compose with   *)
(* Constitution.tla for the full path), judicial review as a holding,     *)
(* Amend. VII's civil-jury and re-examination rules, and senior status.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Persons,        \* Everyone who might be a judge
  House,          \* Members of the House
  Senate,         \* Members of the Senate
  States,         \* The several States (venue for criminal trials)
  CourtIds,       \* Pool of court identifiers
  SupremeCourt,   \* The distinguished member of CourtIds
  Cases,          \* Case identifiers
  MaxSeats,       \* Upper bound on seats per court (for finite checking)
  MaxSalary,      \* Upper bound on judicial salary (for finite checking)
  NoOne           \* Vacancy marker

ASSUME House \subseteq Persons /\ Senate \subseteq Persons /\ House \cap Senate = {}
ASSUME SupremeCourt \in CourtIds
ASSUME NoOne \notin Persons
ASSUME MaxSeats \in Nat /\ MaxSeats >= 1
ASSUME MaxSalary \in Nat

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

Tiers == {"None", "Supreme", "Appeals", "District", "ArticleI"}

\* Heads of jurisdiction, Art. III sec. 2 cl. 1
Kinds == {"Federal",       \* arising under the Constitution, laws, treaties
          "Diversity",     \* between citizens of different States
          "Ambassador",    \* affecting ambassadors, ministers, consuls
          "StateIsParty",  \* a State is a party
          "AgainstState",  \* a State sued by a citizen of another State
                           \* or a foreigner - barred by Amend. XI
          "Crime",
          "Treason"}

OriginalKinds == {"Ambassador", "StateIsParty"}   \* Art. III sec. 2 cl. 2
Criminal      == {"Crime", "Treason"}

Verdicts == {"None", "Guilty", "NotGuilty", "Judgment", "Affirmed", "Reversed"}
Status   == {"Unfiled", "Pending", "Decided", "Closed"}

-----------------------------------------------------------------------------
VARIABLES
  (* Courts - Art. III sec. 1, Art. I sec. 8 cl. 9 *)
  courts,          \* SUBSET CourtIds currently established
  tier,            \* CourtIds -> Tiers
  location,        \* CourtIds -> States \cup {"None"}; district courts sit in a State
  seats,           \* CourtIds -> 0..MaxSeats, set by Congress
  salary,          \* CourtIds -> 0..MaxSalary, set by Congress
  exceptions,      \* SUBSET Kinds stripped from Supreme Court appellate review

  (* Judges - Art. II sec. 2, Art. III sec. 1 *)
  bench,           \* CourtIds -> SUBSET Persons sitting on that court
  nominee,         \* CourtIds -> Seat
  chiefJustice,    \* Seat
  chiefNominee,    \* Seat

  (* Removal - Art. II sec. 4 *)
  impeached,
  disqualified,

  (* Cases - Art. III sec. 2-3 *)
  case             \* Cases -> record (see TypeOK)

courtVars == <<courts, tier, location, seats, salary, exceptions>>
judgeVars == <<bench, nominee, chiefJustice, chiefNominee>>
impVars   == <<impeached, disqualified>>
vars      == <<courtVars, judgeVars, impVars, case>>

CaseRecord ==
  [kind         : Kinds,
   status       : Status,
   court        : CourtIds \cup {"None"},   \* where it sits now
   origCourt    : CourtIds \cup {"None"},   \* where it was tried
   crimeState   : States \cup {"None"},     \* where the crime was committed
   venue        : States \cup {"None"},     \* where it was actually tried
   jury         : BOOLEAN,
   witnesses    : 0..2,                     \* witnesses to the same overt act
   confession   : BOOLEAN,                  \* confession in open court
   trialVerdict : Verdicts,
   verdict      : Verdicts]

TypeOK ==
  /\ courts \subseteq CourtIds
  /\ tier \in [CourtIds -> Tiers]
  /\ location \in [CourtIds -> States \cup {"None"}]
  /\ seats \in [CourtIds -> 0..MaxSeats]
  /\ salary \in [CourtIds -> 0..MaxSalary]
  /\ exceptions \subseteq Kinds
  /\ bench \in [CourtIds -> SUBSET Persons]
  /\ nominee \in [CourtIds -> Seat]
  /\ chiefJustice \in Seat
  /\ chiefNominee \in Seat
  /\ impeached \subseteq Persons
  /\ disqualified \subseteq Persons
  /\ case \in [Cases -> CaseRecord]

AllJudges     == UNION {bench[c] : c \in CourtIds}
ArticleIII(c) == tier[c] \in {"Supreme", "Appeals", "District"}
Vacancies(c)  == seats[c] - Cardinality(bench[c])

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
  /\ case = [x \in Cases |-> [kind |-> "Federal", status |-> "Unfiled",
                              court |-> "None", origCourt |-> "None",
                              crimeState |-> "None", venue |-> "None", jury |-> FALSE,
                              witnesses |-> 0, confession |-> FALSE,
                              trialVerdict |-> "None", verdict |-> "None"]]

-----------------------------------------------------------------------------
(* Congress and the courts - Art. III sec. 1, Art. I sec. 8 cl. 9         *)

\* Congress ordains and establishes an inferior court. Never a second
\* Supreme Court.
EstablishCourt(c, t, st, h, s) ==
  /\ Statute(h, s)
  /\ c \notin courts
  /\ t \in {"Appeals", "District", "ArticleI"}
  /\ (t = "District") <=> (st \in States)      \* trial courts sit somewhere
  /\ courts' = courts \cup {c}
  /\ tier' = [tier EXCEPT ![c] = t]
  /\ location' = [location EXCEPT ![c] = st]
  /\ seats' = [seats EXCEPT ![c] = 1]
  /\ UNCHANGED <<salary, exceptions, judgeVars, impVars, case>>

\* Congress abolishes an inferior court. Its judges lose their seats
\* (Judiciary Act of 1802; Stuart v. Laird). Not while cases are pending.
AbolishCourt(c, h, s) ==
  /\ Statute(h, s)
  /\ c \in courts
  /\ c # SupremeCourt
  /\ \A x \in Cases : case[x].court # c \/ case[x].status \in {"Unfiled", "Closed"}
  /\ courts' = courts \ {c}
  /\ tier' = [tier EXCEPT ![c] = "None"]
  /\ location' = [location EXCEPT ![c] = "None"]
  /\ seats' = [seats EXCEPT ![c] = 0]
  /\ bench' = [bench EXCEPT ![c] = {}]
  /\ nominee' = [nominee EXCEPT ![c] = NoOne]
  /\ UNCHANGED <<salary, exceptions, chiefJustice, chiefNominee, impVars, case>>

\* Congress sets the size of a court, the Supreme Court included (it has
\* been 5, 6, 7, 9 and 10). Reductions take effect by attrition, so a
\* court is never shrunk below its sitting bench.
SetSeats(c, n, h, s) ==
  /\ Statute(h, s)
  /\ c \in courts
  /\ n \in 1..MaxSeats
  /\ n >= Cardinality(bench[c])
  /\ seats' = [seats EXCEPT ![c] = n]
  /\ UNCHANGED <<courts, tier, location, salary, exceptions, judgeVars, impVars, case>>

\* Congress sets compensation. The Compensation Clause (Art. III sec. 1)
\* bars diminishing a sitting Article III judge's pay; an Article I judge
\* or an empty court enjoys no such protection. Checked again as the
\* action property CompensationClause below.
SetSalary(c, n, h, s) ==
  /\ Statute(h, s)
  /\ c \in courts
  /\ n \in 0..MaxSalary
  /\ (ArticleIII(c) /\ bench[c] # {}) => n >= salary[c]
  /\ salary' = [salary EXCEPT ![c] = n]
  /\ UNCHANGED <<courts, tier, location, seats, exceptions, judgeVars, impVars, case>>

\* Exceptions Clause, Art. III sec. 2 cl. 2: Congress may strip heads of
\* jurisdiction from the Supreme Court's appellate docket (McCardle).
\* It may not touch original jurisdiction (Marbury) - see
\* HasOriginalJurisdiction, which Congress cannot change.
SetExceptions(E, h, s) ==
  /\ Statute(h, s)
  /\ E \subseteq Kinds
  /\ exceptions' = E
  /\ UNCHANGED <<courts, tier, location, seats, salary, judgeVars, impVars, case>>

-----------------------------------------------------------------------------
(* Judges - Art. II sec. 2 cl. 2, Art. III sec. 1                          *)

Eligible(p) ==
  /\ p \notin disqualified
  /\ p \notin Congress            \* Art. I sec. 6 cl. 2
  /\ p \notin AllJudges

NominateJudge(c, p) ==
  /\ c \in courts
  /\ Vacancies(c) > 0
  /\ nominee[c] = NoOne
  /\ Eligible(p)
  /\ nominee' = [nominee EXCEPT ![c] = p]
  /\ UNCHANGED <<courtVars, bench, chiefJustice, chiefNominee, impVars, case>>

ConfirmJudge(c, ayes) ==
  /\ nominee[c] # NoOne
  /\ Eligible(nominee[c])          \* may have been convicted since nomination
  /\ Vacancies(c) > 0
  /\ Majority(ayes, Senate)
  /\ bench' = [bench EXCEPT ![c] = @ \cup {nominee[c]}]
  /\ nominee' = [nominee EXCEPT ![c] = NoOne]
  /\ UNCHANGED <<courtVars, chiefJustice, chiefNominee, impVars, case>>

RejectJudge(c) ==
  /\ nominee[c] # NoOne
  /\ nominee' = [nominee EXCEPT ![c] = NoOne]
  /\ UNCHANGED <<courtVars, bench, chiefJustice, chiefNominee, impVars, case>>

\* The Chief Justice is a separately confirmed office. The nominee may
\* already be an Associate Justice (White 1910, Stone 1941, Rehnquist 1986)
\* or an outsider who needs a vacant seat.
NominateChief(p) ==
  /\ chiefJustice = NoOne
  /\ chiefNominee = NoOne
  /\ p \notin disqualified /\ p \notin Congress
  /\ p \in bench[SupremeCourt] \/ Eligible(p)
  /\ chiefNominee' = p
  /\ UNCHANGED <<courtVars, bench, nominee, chiefJustice, impVars, case>>

ConfirmChief(ayes) ==
  /\ chiefNominee # NoOne
  /\ Majority(ayes, Senate)
  \* Re-checked at confirmation: the nominee may since have been seated on
  \* another court, convicted, or elected to Congress. (TLC found this one.)
  /\ \/ chiefNominee \in bench[SupremeCourt]
     \/ Eligible(chiefNominee) /\ Vacancies(SupremeCourt) > 0
  /\ bench' = [bench EXCEPT ![SupremeCourt] = @ \cup {chiefNominee}]
  /\ chiefJustice' = chiefNominee
  /\ chiefNominee' = NoOne
  /\ UNCHANGED <<courtVars, nominee, impVars, case>>

RejectChief ==
  /\ chiefNominee # NoOne
  /\ chiefNominee' = NoOne
  /\ UNCHANGED <<courtVars, bench, nominee, chiefJustice, impVars, case>>

\* Death or resignation. Article III judges leave no other way, save
\* impeachment.
Resign(c, p) ==
  /\ p \in bench[c]
  /\ bench' = [bench EXCEPT ![c] = @ \ {p}]
  /\ chiefJustice' = IF p = chiefJustice THEN NoOne ELSE chiefJustice
  /\ UNCHANGED <<courtVars, nominee, chiefNominee, impVars, case>>

\* Article I judges serve fixed terms; "good Behaviour" does not reach them.
TermExpires(c, p) ==
  /\ tier[c] = "ArticleI"
  /\ p \in bench[c]
  /\ bench' = [bench EXCEPT ![c] = @ \ {p}]
  /\ UNCHANGED <<courtVars, nominee, chiefJustice, chiefNominee, impVars, case>>

-----------------------------------------------------------------------------
(* Removal - Art. I sec. 2-3, Art. II sec. 4                               *)
(* Judges are civil officers: Pickering (1804), Chase (acquitted 1805),    *)
(* and thirteen others since.                                              *)

Impeach(p, ayes) ==
  /\ p \in AllJudges
  /\ p \notin impeached
  /\ Majority(ayes, House)
  /\ impeached' = impeached \cup {p}
  /\ UNCHANGED <<courtVars, judgeVars, disqualified, case>>

Convict(p, ayes, dq) ==
  /\ p \in impeached
  /\ TwoThirds(ayes, Senate)
  /\ impeached' = impeached \ {p}
  /\ disqualified' = IF dq THEN disqualified \cup {p} ELSE disqualified
  /\ bench' = [c \in CourtIds |-> bench[c] \ {p}]
  /\ chiefJustice' = IF p = chiefJustice THEN NoOne ELSE chiefJustice
  /\ nominee' = [c \in CourtIds |-> IF nominee[c] = p THEN NoOne ELSE nominee[c]]
  /\ chiefNominee' = IF chiefNominee = p THEN NoOne ELSE chiefNominee
  /\ UNCHANGED <<courtVars, case>>

Acquit(p) ==
  /\ p \in impeached
  /\ impeached' = impeached \ {p}
  /\ UNCHANGED <<courtVars, judgeVars, disqualified, case>>

-----------------------------------------------------------------------------
(* Cases - Art. III sec. 2-3                                               *)

\* Where a case may be filed in the first instance. Fixed by the
\* Constitution; no action of Congress changes this predicate.
HasOriginalJurisdiction(k, c) ==
  /\ c \in courts
  /\ k # "AgainstState"                              \* Amend. XI
  /\ CASE tier[c] = "Supreme"  -> k \in OriginalKinds  \* Marbury
       [] tier[c] = "District" -> TRUE
       [] tier[c] = "ArticleI" -> k = "Federal"       \* public-rights matters
       [] tier[c] = "Appeals"  -> FALSE
       [] OTHER                -> FALSE

File(x, k, c, st) ==
  /\ case[x].status = "Unfiled"
  /\ HasOriginalJurisdiction(k, c)
  /\ (k \in Criminal) <=> (st \in States)
  /\ case' = [case EXCEPT ![x].kind = k, ![x].status = "Pending",
                          ![x].court = c, ![x].origCourt = c,
                          ![x].crimeState = st]
  /\ UNCHANGED <<courtVars, judgeVars, impVars>>

\* Trial-court decision.
\*   Art. III sec. 2 cl. 3: crimes are tried by jury in the State where
\*   committed.
\*   Art. III sec. 3 cl. 1: no treason conviction without two witnesses to
\*   the same overt act, or confession in open court.
Decide(x, jury, w, conf, v) ==
  /\ case[x].status = "Pending"
  /\ case[x].court = case[x].origCourt
  /\ bench[case[x].court] # {}                       \* somebody must sit
  /\ LET k == case[x].kind
         c == case[x].court
     IN /\ (k \in Criminal) => (jury /\ location[c] = case[x].crimeState)
        /\ v \in (IF k \in Criminal THEN {"Guilty", "NotGuilty"} ELSE {"Judgment"})
        /\ (k = "Treason" /\ v = "Guilty") => (w = 2 \/ conf)
  /\ case' = [case EXCEPT ![x].status = "Decided", ![x].jury = jury,
                          ![x].venue = location[case[x].court],
                          ![x].witnesses = w, ![x].confession = conf,
                          ![x].trialVerdict = v, ![x].verdict = v]
  /\ UNCHANGED <<courtVars, judgeVars, impVars>>

\* Appeal to the next tier. Article I and district decisions go to a court
\* of appeals; a court of appeals goes to the Supreme Court unless Congress
\* has excepted that head of jurisdiction. Nothing lies from the Supreme
\* Court. Amend. V: an acquittal cannot be appealed.
Appeal(x, c) ==
  /\ case[x].status = "Decided"
  /\ c \in courts
  /\ case[x].trialVerdict # "NotGuilty"
  /\ LET from == tier[case[x].court]
     IN CASE from \in {"District", "ArticleI"} -> tier[c] = "Appeals"
          [] from = "Appeals" -> c = SupremeCourt /\ case[x].kind \notin exceptions
          [] OTHER -> FALSE
  /\ case' = [case EXCEPT ![x].status = "Pending", ![x].court = c,
                          ![x].verdict = "None"]
  /\ UNCHANGED <<courtVars, judgeVars, impVars>>

AppellateDecide(x, v) ==
  /\ case[x].status = "Pending"
  /\ case[x].court # case[x].origCourt
  /\ bench[case[x].court] # {}
  /\ v \in {"Affirmed", "Reversed"}
  /\ case' = [case EXCEPT ![x].status = "Decided", ![x].verdict = v]
  /\ UNCHANGED <<courtVars, judgeVars, impVars>>

\* No further review sought, or certiorari denied.
Close(x) ==
  /\ case[x].status = "Decided"
  /\ case' = [case EXCEPT ![x].status = "Closed"]
  /\ UNCHANGED <<courtVars, judgeVars, impVars>>

-----------------------------------------------------------------------------
Next ==
  \/ \E h \in HouseVotes, s \in SenateVotes :
       \/ \E c \in CourtIds, t \in Tiers, st \in States \cup {"None"} :
            EstablishCourt(c, t, st, h, s)
       \/ \E c \in CourtIds : AbolishCourt(c, h, s)
       \/ \E c \in CourtIds, n \in 1..MaxSeats : SetSeats(c, n, h, s)
       \/ \E c \in CourtIds, n \in 0..MaxSalary : SetSalary(c, n, h, s)
       \/ \E E \in SUBSET Kinds : SetExceptions(E, h, s)
  \/ \E c \in CourtIds :
       \/ \E p \in Persons : NominateJudge(c, p) \/ Resign(c, p) \/ TermExpires(c, p)
       \/ \E n \in SenateVotes : ConfirmJudge(c, n)
       \/ RejectJudge(c)
  \/ \E p \in Persons : NominateChief(p)
  \/ \E n \in SenateVotes : ConfirmChief(n)
  \/ RejectChief
  \/ \E p \in Persons :
       \/ \E n \in HouseVotes : Impeach(p, n)
       \/ \E n \in SenateVotes, dq \in BOOLEAN : Convict(p, n, dq)
       \/ Acquit(p)
  \/ \E x \in Cases :
       \/ \E k \in Kinds, c \in CourtIds, st \in States \cup {"None"} : File(x, k, c, st)
       \/ \E j \in BOOLEAN, w \in 0..2, conf \in BOOLEAN, v \in Verdicts :
            Decide(x, j, w, conf, v)
       \/ \E c \in CourtIds : Appeal(x, c)
       \/ \E v \in Verdicts : AppellateDecide(x, v)
       \/ Close(x)

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
JudgesAreNotInCongress == AllJudges \cap Congress = {}
DisqualifiedDoNotSit   == AllJudges \cap disqualified = {}

ChiefJusticeSits ==
  chiefJustice = NoOne \/ chiefJustice \in bench[SupremeCourt]

\* Marbury: the Supreme Court's original docket is exactly what Art. III
\* sec. 2 cl. 2 says it is.
OriginalJurisdiction ==
  \A x \in Cases :
    case[x].origCourt = SupremeCourt => case[x].kind \in OriginalKinds

\* Amend. XI
EleventhAmendment ==
  \A x \in Cases : case[x].status # "Unfiled" => case[x].kind # "AgainstState"

\* Courts of appeals hear only appeals.
AppealsCourtsAreAppellate ==
  \A x \in Cases :
    case[x].origCourt # "None" => tier[case[x].origCourt] # "Appeals"

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

\* Exceptions Clause honoured on the way up.
ExceptionsHonoured ==
  \A x \in Cases :
    (case[x].court = SupremeCourt /\ case[x].origCourt # SupremeCourt) =>
      case[x].kind \notin exceptions

Safety ==
  /\ OneSupremeCourt /\ CourtsAreEstablished /\ BenchFitsSeats
  /\ NoJudgeOnTwoCourts /\ JudgesAreNotInCongress /\ DisqualifiedDoNotSit
  /\ ChiefJusticeSits /\ OriginalJurisdiction /\ EleventhAmendment
  /\ AppealsCourtsAreAppellate /\ JuryAndVenue /\ TreasonProof
  /\ NoDoubleJeopardy /\ ExceptionsHonoured

-----------------------------------------------------------------------------
(* Action properties - what may happen between one state and the next     *)

\* Compensation Clause, Art. III sec. 1: the pay of a sitting Article III
\* judge is never diminished. Congress may cut the salary of an empty
\* court or an Article I tribunal.
CompensationClause ==
  [][\A c \in CourtIds :
       (ArticleIII(c) /\ bench[c] \cap bench'[c] # {}) => salary'[c] >= salary[c]]_vars

\* Good Behaviour, Art. III sec. 1: an Article III judge leaves the bench
\* only by resignation or death, conviction on impeachment, or the
\* abolition of the court itself.
GoodBehaviour ==
  [][\A c \in CourtIds, p \in Persons :
       (ArticleIII(c) /\ p \in bench[c] /\ p \notin bench'[c]) =>
         \/ Resign(c, p)
         \/ \E n \in SenateVotes, dq \in BOOLEAN : Convict(p, n, dq)
         \/ \E h \in HouseVotes, s \in SenateVotes : AbolishCourt(c, h, s)]_vars

=============================================================================
