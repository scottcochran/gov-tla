----------------------------- MODULE Elections -----------------------------
(****************************************************************************)
(* The presidential cycle: Article II s.1, Amendments XII, XX and XXII.     *)
(*                                                                          *)
(* ONE ELECTION, THEN THE NEXT. The States appoint electors; the electors   *)
(* vote on one day; Congress counts; if the electors made no choice the     *)
(* House chooses the President and the Senate the Vice President; at noon   *)
(* on 20 January the old term ends whether or not anyone was chosen. The    *)
(* module asks what the text asks at each step - who may be an elector, what*)
(* a ballot may say, what a majority is a majority of, who chooses when the *)
(* electors do not - and who holds the executive power when the choice is   *)
(* late, dead or disqualified. Constitution.tla and Executive.tla take all  *)
(* of this in one Elect step; this module is that step.                     *)
(*                                                                          *)
(* PROPERTIES (safety; each an invariant, local as noted)                   *)
(*   ElectorsHoldNoOffice  Art. II s.1 cl.2: no Senator, Representative or  *)
(*                       officer of the United States is appointed an       *)
(*                       elector. State predicate decided by Appoint.       *)
(*   AppointedOnElectionDay  Art. II s.1 cl.4, 3 U.S.C. 1: electors are     *)
(*                       appointed on the day Congress fixed. Flag set by   *)
(*                       Appoint.                                           *)
(*   SameDay             Art. II s.1 cl.4: the electors vote on one day,    *)
(*                       "the same throughout the United States". Flag set  *)
(*                       by Vote.                                           *)
(*   OneNotAnInhabitant  Amend. XII: of the two persons an elector names,   *)
(*                       one at least is not an inhabitant of the elector's *)
(*                       State. Over the ballots, written once by Vote.     *)
(*   PledgesBind         Chiafalo v. Washington (2020): a State may hold its*)
(*                       electors to their pledge. Over the ballots of the  *)
(*                       electors in Binding.                               *)
(*   NewCongressCounts   Amend. XX ss.1-2: the Congress that assembles on   *)
(*                       3 January counts the votes (and so its House and   *)
(*                       Senate hold any contingent election). Flag set by  *)
(*                       OpenCount.                                         *)
(*   CountIsCongress     3 U.S.C. 15: no elector's vote is rejected but by  *)
(*                       both Houses, each sustaining the objection. Flag   *)
(*                       set by Sustain.                                    *)
(*   ElectorsChoose      Amend. XII: no one is announced President or Vice  *)
(*                       President without a majority of the whole number   *)
(*                       of electors appointed, on the list for that office.*)
(*                       Flag set by Announce.                              *)
(*   DevolvesOnlyWithoutMajority  Amend. XII: the choice passes to the House*)
(*                       or the Senate only "if no person have such         *)
(*                       majority". Flag set by Announce.                   *)
(*   CountCanClose       Amend. XII: whatever the ballots say, some result  *)
(*                       can be announced. A consequence, not a rule, and   *)
(*                       no one guard decides it: two majorities of the     *)
(*                       same electors share an elector, and that elector's *)
(*                       ballot names two persons, so the two lists never   *)
(*                       give one person both offices. State predicate.     *)
(*   ChoiceFromTheList   Amend. XII: the House chooses from the three       *)
(*                       highest on the list of those voted for as          *)
(*                       President, the Senate from the two highest for     *)
(*                       Vice President. Flag set by HouseChooses and       *)
(*                       SenateChooses.                                     *)
(*   HouseVote           Amend. XII: by States, each one vote; a quorum of  *)
(*                       two-thirds of the States; a majority of all the    *)
(*                       States to choose. Flag set by HouseChooses.        *)
(*   SenateVote          Amend. XII: a quorum of two-thirds of the whole    *)
(*                       number of Senators; a majority of the whole number *)
(*                       to choose. Flag set by SenateChooses.              *)
(*   PresidentNotVP      Art. II s.1: President and Vice President, elect   *)
(*                       and in office, are two persons. State predicate    *)
(*                       decided by TwoPersons wherever either is chosen or *)
(*                       seated.                                            *)
(*   Qualifications      Art. II s.1 cl.5, Amend. XII (last sentence): only *)
(*                       a person eligible to the office of President holds *)
(*                       it, acts in it, or is Vice President. State        *)
(*                       predicate decided by VQualified at every seating.  *)
(*   Disability          Amend. XIV s.3: no one under its disability holds  *)
(*                       either office unless Congress removed it. As above.*)
(*   TwoTermLimit        Amend. XXII: no one takes office as an elected     *)
(*                       President a third time, or a second time having    *)
(*                       held the office for more than two years of a term  *)
(*                       to which another was elected. Flag set by          *)
(*                       NoonInaugurates and Qualify.                       *)
(*   VPElectBecomesOnlyOnDeath  Amend. XX s.3: the Vice President elect     *)
(*                       becomes President only if the President elect has  *)
(*                       died; otherwise the Vice President elect acts      *)
(*                       "until a President shall have qualified". Flag set *)
(*                       by NoonSucceeds.                                   *)
(*   ActingOrder         Amend. XX s.3, 3 U.S.C. 19: no one acts as         *)
(*                       President while there is a President; the Vice     *)
(*                       President acts before anyone the statute names.    *)
(*                       State predicate decided by VPActs, SuccessorActs,  *)
(*                       Qualify and VPQualify.                             *)
(*   Safety              the conjunction of the nineteen.                   *)
(* LIVENESS                                                                 *)
(*   ExecutiveIsFilled   Amend. XX s.3 read with 3 U.S.C. 19: once the first*)
(*                       term has begun, a vacancy in the executive power   *)
(*                       ends. Under FairSpec only (fairness below).        *)
(*                                                                          *)
(* MUTATIONS (Mut; one check each; "breaks" is what TLC must show)          *)
(*   M_OFFICER_ELECTOR  Appoint without the officer check. Oregon, 1876: the*)
(*                      elector Watts was a postmaster. Breaks              *)
(*                      ElectorsHoldNoOffice.                               *)
(*   M_FAILED_CHOICE    Appoint after election day: 3 U.S.C. 2 as it stood  *)
(*                      until 2022, under which a State that "failed to make*)
(*                      a choice" could appoint "on a subsequent day in such*)
(*                      a manner as the legislature ... may direct". Breaks *)
(*                      AppointedOnElectionDay.                             *)
(*   M_LATE_VOTE        Vote after the electors' day. Wisconsin, 1856: a    *)
(*                      snowstorm, and the electors met a day late. Breaks  *)
(*                      SameDay.                                            *)
(*   M_HABITATION       Vote without the inhabitant rule. No earlier text   *)
(*                      (Art. II s.1 cl.3 had it too). Breaks               *)
(*                      OneNotAnInhabitant.                                 *)
(*   M_SAME_NAME        Vote lets an elector name one person on both        *)
(*                      ballots. Art. II s.1 cl.3 said "two Persons";       *)
(*                      Amend. XII does not say so again. Breaks            *)
(*                      CountCanClose: a person with a majority on both     *)
(*                      lists can be announced for neither office.          *)
(*   M_FAITHLESS        Vote without the pledge: Baca v. Colorado Department*)
(*                      of State (10th Cir. 2019), reversed with Chiafalo.  *)
(*                      Breaks PledgesBind.                                 *)
(*   M_PRE_XX           OpenCount by the outgoing Congress: the text before *)
(*                      1933, under which the outgoing House chose between  *)
(*                      Jefferson and Burr in 1801. Breaks                  *)
(*                      NewCongressCounts.                                  *)
(*   M_PRESIDING        Sustain without both Houses: the presiding officer  *)
(*                      rejects a vote alone, the reading 3 U.S.C. 15(b)    *)
(*                      (2022) forecloses. Breaks CountIsCongress.          *)
(*   M_PRE_XII          The list for President counts both names on each    *)
(*                      ballot: Art. II s.1 cl.3 before 1804, under which   *)
(*                      Jefferson and Burr each had a majority in 1800.     *)
(*                      Breaks ElectorsChoose; and CountCanClose once three *)
(*                      persons are voted for.                              *)
(*   M_PLURALITY        The most votes carry, majority or not. No earlier   *)
(*                      text. Breaks ElectorsChoose; and CountCanClose once *)
(*                      three persons are voted for, since one person can   *)
(*                      then lead both lists.                               *)
(*   M_ENTITLED         The majority is of the electors the States are      *)
(*                      entitled to, not of those appointed. New York       *)
(*                      appointed none in 1789, and no vote of the eleven   *)
(*                      States of the Confederacy was counted in 1865.      *)
(*                      Breaks DevolvesOnlyWithoutMajority.                 *)
(*   M_OFF_LIST         The House and the Senate choose anyone. No earlier  *)
(*                      text (Art. II s.1 cl.3 had five highest). Breaks    *)
(*                      ChoiceFromTheList.                                  *)
(*   M_HOUSE_QUORUM     HouseChooses without a quorum of the States. Breaks *)
(*                      HouseVote. No earlier text.                         *)
(*   M_HOUSE_PRESENT    A majority of the States present chooses. Breaks    *)
(*                      HouseVote. No earlier text.                         *)
(*   M_SENATE_QUORUM    SenateChooses without a quorum. Breaks SenateVote.  *)
(*                      No earlier text.                                    *)
(*   M_SENATE_PRESENT   A majority of the Senators present chooses. Breaks  *)
(*                      SenateVote. No earlier text.                        *)
(*   M_ONE_PERSON       TwoPersons lets one person be announced, chosen and *)
(*                      seated for both offices (the ballot's own check is  *)
(*                      M_SAME_NAME). Breaks PresidentNotVP. No earlier     *)
(*                      text.                                               *)
(*   M_UNQUALIFIED      VQualified without Art. II s.1 cl.5. Breaks         *)
(*                      Qualifications. No earlier text.                    *)
(*   M_XIV3             VQualified without Amend. XIV s.3: the text before  *)
(*                      1868. Breaks Disability.                            *)
(*   M_XXII             Qualified without the term limit: the text before   *)
(*                      1951. Breaks TwoTermLimit.                          *)
(*   M_XXII_SERVICE     The term limit counts elections only, as            *)
(*                      Constitution.tla's TermAllowed does. Breaks         *)
(*                      TwoTermLimit.                                       *)
(*   M_XX3_BECOMES      NoonSucceeds without the death of the President     *)
(*                      elect: the Vice President elect becomes President   *)
(*                      whenever no President elect qualifies. Breaks       *)
(*                      VPElectBecomesOnlyOnDeath. No earlier text (Amend.  *)
(*                      XII had the Vice President act).                    *)
(*   M_SPEAKER_FIRST    SuccessorActs although there is a Vice President.   *)
(*                      Breaks ActingOrder. No earlier text.                *)
(*   M_NO_STATUTE       SuccessorActs never: Amend. XX s.3 without the law  *)
(*                      it invites ("Congress may by law provide"). It adds *)
(*                      no state, so it breaks no safety property and no    *)
(*                      witness; it breaks ExecutiveIsFilled.               *)
(* Every other (mutation, property) pair must HOLD; the TLC results file    *)
(* runs each one.                                                           *)
(*                                                                          *)
(* DEADLOCK: no state is terminal. Each stage of an election can be closed  *)
(* (ElectionDayEnds, ElectorsAdjourn, OpenCount), noon comes once the count *)
(* is open, and Midterm and OpenElection follow, so TLC's -deadlock flag    *)
(* hides nothing. An election that never produces a President is a livelock *)
(* the text allows; the one progress claim is ExecutiveIsFilled.            *)
(*                                                                          *)
(* REACHABILITY WITNESSES (Never..., each must be VIOLATED under "none"): a *)
(* President; a seat no State filled; an appointed elector who casts no     *)
(* vote; an unbound elector departing from the pledge; a vote rejected; a   *)
(* President elect who lacks a majority of the electors the States          *)
(* appointed, made by rejecting electors; a person voted for as Vice        *)
(* President and left off the Senate's list; the House and the Senate each  *)
(* choosing; noon with no President after a finished count; the Vice        *)
(* President elect becoming President; the Vice President acting; the       *)
(* statutory successor acting; a President elect and a Vice President elect *)
(* each qualifying after noon; the count announced after noon; a disability *)
(* removed; a President elect dead; succession within a term; a person      *)
(* elected President twice; service of more than two years of another's     *)
(* term; a President elect barred by the term limit; a person twice elected *)
(* President becoming President again by succession; the next election      *)
(* opening.                                                                 *)
(*                                                                          *)
(* ABSTRACTED: the States, on the electors' side (an elector is a seat some *)
(* State fills, pledged to a candidate for President; winner-take-all,      *)
(* districts and the popular vote are whatever pledges the seats get; who   *)
(* shares a State with whom is the constant Inhabitants); the House's       *)
(* delegations (a State's vote is given, not built from its members, so     *)
(* voting by member instead of by State cannot be expressed); the calendar  *)
(* (stages in order through the opening of the count; a term in two halves; *)
(* noon may strike while the count is open or after); the joint session     *)
(* (objections are sustained elector by elector, then one announcement,     *)
(* after which the certificates are spent and the ballots cleared); one-    *)
(* fifth of each House to object, and the grounds beyond the two that       *)
(* differ in effect (3 U.S.C. 15(e)(2): an elector "not lawfully certified" *)
(* leaves the whole number appointed, a vote "not regularly given" does     *)
(* not); competing slates; who checks a qualification (it is checked where  *)
(* the office is taken; Trump v. Anderson (2024) leaves the States out of   *)
(* Amend. XIV s.3 for federal office); the two-thirds vote that removes a   *)
(* disability; death is the only way an office falls vacant in a term       *)
(* (resignation, removal and Amend. XXV ss.2-4 are in Constitution.tla and  *)
(* Executive.tla); the statutory line is one person, Successor, who never   *)
(* dies and is never a candidate; Amend. XX s.4 (a candidate's death        *)
(* before the House or Senate chooses), on which Congress has not           *)
(* legislated, so the lists stand as announced.                             *)
(* Three readings are fixed, each stated where it is used: a tie for the    *)
(* last place on a list admits everyone tied (and the rows cannot tell the  *)
(* House's three highest from four, which needs seven electors); the term   *)
(* limit is a qualification checked at noon, so a President elect it bars   *)
(* has "failed to qualify"; and Amend. XII's last sentence is read as Art.  *)
(* II s.1 cl.5 and Amend. XIV s.3, not Amend. XXII                          *)
(* (NeverThirdTermBySuccession shows what that reading admits). Service as  *)
(* Acting President is not counted toward Amend. XXII's two years, the      *)
(* halves being too coarse to time it.                                      *)
(****************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Mut,           \* "none", or the one mutation in force
  Persons,
  Electors,      \* one per seat in the college: whom a State would appoint
  Candidates,    \* whom an elector may be pledged to, or name on a ballot
  Eligible,      \* Art. II s.1 cl.5: natural born, thirty-five, fourteen years
  Disabled,      \* under the disability of Amend. XIV s.3
  Officers,      \* Senators, Representatives, officers of the United States
  Mortal,        \* the persons whose death the model follows
  Inhabitants,   \* sets of persons who are inhabitants of one State
  Binding,       \* the electors whose State holds them to their pledge
  Contestable,   \* the electors whose votes may be objected to at the count
  States,        \* the States, as they vote in the House
  Senators,
  Successor,     \* whom 3 U.S.C. 19 names to act (the Speaker)
  NoOne

Mutations ==
  {"none", "M_OFFICER_ELECTOR", "M_FAILED_CHOICE", "M_LATE_VOTE",
   "M_HABITATION", "M_SAME_NAME", "M_FAITHLESS", "M_PRE_XX", "M_PRESIDING", "M_PRE_XII",
   "M_PLURALITY", "M_ENTITLED", "M_OFF_LIST", "M_HOUSE_QUORUM",
   "M_HOUSE_PRESENT", "M_SENATE_QUORUM", "M_SENATE_PRESENT", "M_ONE_PERSON",
   "M_UNQUALIFIED", "M_XIV3", "M_XXII", "M_XXII_SERVICE", "M_XX3_BECOMES",
   "M_SPEAKER_FIRST", "M_NO_STATUTE"}

\* Well-formedness of the constants; TLC checks them against each config and
\* a proof would cite them by name. Mortal, Contestable and Candidates may be
\* as small as a row likes: they bound what the model follows, not the law.
ASSUME MutKnown      == Mut \in Mutations
ASSUME PersonsWF     == /\ Electors \subseteq Persons /\ Candidates \subseteq Persons
                        /\ Eligible \subseteq Persons /\ Disabled \subseteq Persons
                        /\ Officers \subseteq Persons /\ Mortal \subseteq Persons
ASSUME NoOneWF       == NoOne \notin Persons
ASSUME InhabitantsWF == Inhabitants \subseteq SUBSET Persons
ASSUME CollegeWF     == Binding \subseteq Electors /\ Contestable \subseteq Electors
\* The statute's line never runs out, and is not on the ballot.
ASSUME SuccessorWF   == /\ Successor \in Eligible
                        /\ Successor \notin Mortal \cup Disabled \cup Candidates
ASSUME FiniteWF      == /\ IsFiniteSet(Electors) /\ IsFiniteSet(Candidates)
                        /\ IsFiniteSet(States) /\ IsFiniteSet(Senators)

-----------------------------------------------------------------------------
Seat    == Persons \cup {NoOne}
Choice  == Candidates \cup {NoOne}

\* Amend. XII: "they shall name in their ballots the person voted for as
\* President, and in distinct ballots the person voted for as
\* Vice-President".
Ballots  == [p : Candidates, v : Candidates]
NoBallot == [p |-> NoOne, v |-> NoOne]

\* What the two Houses may hold of an elector's vote (3 U.S.C. 15(d)(2)(B)).
Grounds == {"NotAppointed",    \* the elector was not lawfully certified
            "NotRegular"}      \* the vote was not regularly given
Rulings == {"None"} \cup Grounds

\* Where the election stands.
Stages == {"Appointing",   \* election day: the States appoint
           "Voting",       \* the electors' day
           "Voted",        \* the certificates are on their way to Congress
           "Counting",     \* the joint session is open
           "Counted"}      \* the result is announced; House and Senate may
                           \*   still have a choice to make
\* Where the term stands.
Clocks == {"Founding",     \* before the first term (1789)
           "BeforeNoon",   \* from election day to noon on 20 January
           "FirstHalf",    \* the first two years of a term
           "SecondHalf"}   \* the rest, until the next election day

-----------------------------------------------------------------------------
VARIABLES
  stage,               \* Stages
  clock,               \* Clocks
  pledge,              \* Electors -> Choice: appointed, and pledged to whom
  ballot,              \* Electors -> Ballots \cup {NoBallot}
  objection,           \* Electors -> Rulings
  pElect,              \* the President elect, by the electors or the House
  vElect,              \* the Vice President elect, by the electors or the Senate
  pList,               \* from whom the House may choose (set by Announce)
  vList,               \* from whom the Senate may choose
  president,
  vicePresident,
  acting,              \* who acts as President, if anyone
  dead,                \* SUBSET Persons
  relieved,            \* whose disability Congress has removed
  elected,             \* Persons -> times taken office as elected President
  servedLong,          \* held the office over two years of another's term
  lateAppointment,     \* an elector was appointed after election day
  lateVote,            \* an elector voted after the electors' day
  lameDuck,            \* the outgoing Congress opened the count
  rejectedAlone,       \* a vote was rejected without both Houses
  minorityElect,       \* someone was announced without a majority
  wronglyDevolved,     \* a choice went to a House though someone had one
  offList,             \* a House chose someone not on its list
  houseShort,          \* the House chose without quorum or majority
  senateShort,         \* the Senate chose without quorum or majority
  thirdTerm,           \* someone took office as elected past Amend. XXII
  becameWithoutDeath   \* a VP elect became President, the President elect alive

timeVars    == <<stage, clock>>
collegeVars == <<pledge, ballot, objection>>
electVars   == <<pElect, vElect, pList, vList>>
officeVars  == <<president, vicePresident, acting>>
personVars  == <<dead, relieved, elected, servedLong>>
flagVars    == <<lateAppointment, lateVote, lameDuck, rejectedAlone,
                 minorityElect, wronglyDevolved, offList, houseShort,
                 senateShort, thirdTerm, becameWithoutDeath>>
vars == <<timeVars, collegeVars, electVars, officeVars, personVars, flagVars>>

TypeOK ==
  /\ stage \in Stages
  /\ clock \in Clocks
  /\ pledge \in [Electors -> Choice]
  /\ ballot \in [Electors -> Ballots \cup {NoBallot}]
  /\ objection \in [Electors -> Rulings]
  /\ pElect \in Choice
  /\ vElect \in Choice
  /\ pList \subseteq Candidates
  /\ vList \subseteq Candidates
  /\ president \in Seat
  /\ vicePresident \in Seat
  /\ acting \in Seat
  /\ dead \subseteq Persons
  /\ relieved \subseteq Persons
  /\ elected \in [Persons -> Nat]
  /\ servedLong \subseteq Persons
  /\ lateAppointment \in BOOLEAN
  /\ lateVote \in BOOLEAN
  /\ lameDuck \in BOOLEAN
  /\ rejectedAlone \in BOOLEAN
  /\ minorityElect \in BOOLEAN
  /\ wronglyDevolved \in BOOLEAN
  /\ offList \in BOOLEAN
  /\ houseShort \in BOOLEAN
  /\ senateShort \in BOOLEAN
  /\ thirdTerm \in BOOLEAN
  /\ becameWithoutDeath \in BOOLEAN

-----------------------------------------------------------------------------
(* The college, as the text counts it.                                      *)

\* The seats the States filled; those of them Congress has not held unlawfully
\* certified ("the whole number of Electors appointed", 3 U.S.C. 15(e)(2));
\* and those of them whose votes are counted.
Pledged   == {e \in Electors : pledge[e] # NoOne}
Appointed == {e \in Pledged : objection[e] # "NotAppointed"}
Counted   == {e \in Appointed : objection[e] = "None" /\ ballot[e] # NoBallot}

PFor(c)   == {e \in Counted : ballot[e].p = c}
VFor(c)   == {e \in Counted : ballot[e].v = c}
PVotes(c) == Cardinality(PFor(c))
VVotes(c) == Cardinality(VFor(c))
Whole     == Cardinality(Appointed)

PMajority(c) == 2 * PVotes(c) > Whole
VMajority(c) == 2 * VVotes(c) > Whole

\* "the persons having the highest numbers not exceeding three on the list of
\* those voted for as President", and "the two highest numbers on the list"
\* for Vice President. A tie for the last place admits everyone tied.
PTop == {c \in Candidates :
           PVotes(c) > 0 /\ Cardinality({d \in Candidates : PVotes(d) > PVotes(c)}) < 3}
VTop == {c \in Candidates :
           VVotes(c) > 0 /\ Cardinality({d \in Candidates : VVotes(d) > VVotes(c)}) < 2}

SameState(x, y) == \E g \in Inhabitants : x \in g /\ y \in g

-----------------------------------------------------------------------------
(* The checks. Each is one guard, and Mut = <its mutation> removes it.      *)

MayBeElector(e)  == IF Mut = "M_OFFICER_ELECTOR" THEN TRUE ELSE e \notin Officers
AppointmentOpen  == IF Mut = "M_FAILED_CHOICE"
                    THEN stage \in {"Appointing", "Voting"} ELSE stage = "Appointing"
PollsOpen        == IF Mut = "M_LATE_VOTE"
                    THEN stage \in {"Voting", "Voted"} ELSE stage = "Voting"
Habitation(e, p, v) ==
  IF Mut = "M_HABITATION" THEN TRUE ELSE ~(SameState(e, p) /\ SameState(e, v))
TwoNames(p, v)   == IF Mut = "M_SAME_NAME" THEN TRUE ELSE p # v
Faithful(e, p)   == IF Mut = "M_FAITHLESS" THEN TRUE ELSE (e \in Binding => p = pledge[e])
Seated(new)      == IF Mut = "M_PRE_XX" THEN TRUE ELSE new
Concur(both)     == IF Mut = "M_PRESIDING" THEN TRUE ELSE both

\* The count. Under M_PRE_XII an elector's two names both stand on the list
\* for President; under M_ENTITLED the majority is of every seat; under
\* M_PLURALITY the most votes carry.
PCount(c) == IF Mut = "M_PRE_XII" THEN Cardinality(PFor(c) \cup VFor(c)) ELSE PVotes(c)
Base      == IF Mut = "M_ENTITLED" THEN Cardinality(Electors) ELSE Whole
PCarries(c) ==
  IF Mut = "M_PLURALITY"
  THEN PCount(c) > 0 /\ \A d \in Candidates \ {c} : PCount(c) > PCount(d)
  ELSE 2 * PCount(c) > Base
VCarries(c) ==
  IF Mut = "M_PLURALITY"
  THEN VVotes(c) > 0 /\ \A d \in Candidates \ {c} : VVotes(c) > VVotes(d)
  ELSE 2 * VVotes(c) > Base
\* What may be announced: the person who carries, or no one if no one does.
PResult(p) == IF p = NoOne THEN \A c \in Candidates : ~PCarries(c) ELSE PCarries(p)
VResult(v) == IF v = NoOne THEN \A c \in Candidates : ~VCarries(c) ELSE VCarries(v)

\* The contingent elections.
OnList(c, L)    == IF Mut = "M_OFF_LIST" THEN TRUE ELSE c \in L
HouseQuorum(Q)  == IF Mut = "M_HOUSE_QUORUM" THEN TRUE
                   ELSE 3 * Cardinality(Q) >= 2 * Cardinality(States)
HouseCarries(Q, Y) ==
  IF Mut = "M_HOUSE_PRESENT" THEN 2 * Cardinality(Y) > Cardinality(Q)
  ELSE 2 * Cardinality(Y) > Cardinality(States)
SenateQuorum(Q) == IF Mut = "M_SENATE_QUORUM" THEN TRUE
                   ELSE 3 * Cardinality(Q) >= 2 * Cardinality(Senators)
SenateCarries(Q, Y) ==
  IF Mut = "M_SENATE_PRESENT" THEN 2 * Cardinality(Y) > Cardinality(Q)
  ELSE 2 * Cardinality(Y) > Cardinality(Senators)

\* Two offices, two persons: at the announcement, in each House's choice and
\* at every seating. (On a ballot it is TwoNames.)
TwoPersons(x, y) ==
  IF Mut = "M_ONE_PERSON" THEN TRUE ELSE (x = NoOne \/ y = NoOne \/ x # y)

\* Who may take an office. The Vice President needs what the President needs
\* (Amend. XII), read here without Amend. XXII, which speaks of being elected
\* President. The term limit is checked where the elected President takes
\* office: one it bars has "failed to qualify" (Amend. XX s.3).
MeetsArticleII(x) == IF Mut = "M_UNQUALIFIED" THEN TRUE ELSE x \in Eligible
NotDisabled(x)    == IF Mut = "M_XIV3" THEN TRUE ELSE (x \notin Disabled \/ x \in relieved)
WithinXXII(x)     == elected[x] < (IF x \in servedLong THEN 1 ELSE 2)
TermAllowed(x)    == CASE Mut = "M_XXII"         -> TRUE
                       [] Mut = "M_XXII_SERVICE" -> elected[x] < 2
                       [] OTHER                  -> WithinXXII(x)
VQualified(x) == x # NoOne /\ x \notin dead /\ MeetsArticleII(x) /\ NotDisabled(x)
Qualified(x)  == VQualified(x) /\ TermAllowed(x)

\* Amend. XX s.3, first sentence: "the President elect shall have died".
ElectGone == IF Mut = "M_XX3_BECOMES" THEN TRUE ELSE (pElect # NoOne /\ pElect \in dead)
\* 3 U.S.C. 19: "neither a President nor Vice President".
NoVP      == IF Mut = "M_SPEAKER_FIRST" THEN TRUE ELSE vicePresident = NoOne
Statute   == Mut # "M_NO_STATUTE"

-----------------------------------------------------------------------------
Blank(S, x) == [e \in S |-> x]

Init ==
  /\ stage = "Appointing"
  /\ clock = "Founding"
  /\ pledge = Blank(Electors, NoOne)
  /\ ballot = Blank(Electors, NoBallot)
  /\ objection = Blank(Electors, "None")
  /\ pElect = NoOne /\ vElect = NoOne
  /\ pList = {} /\ vList = {}
  /\ president = NoOne /\ vicePresident = NoOne /\ acting = NoOne
  /\ dead = {}
  /\ relieved = {}
  /\ elected = Blank(Persons, 0)
  /\ servedLong = {}
  /\ lateAppointment = FALSE /\ lateVote = FALSE /\ lameDuck = FALSE
  /\ rejectedAlone = FALSE /\ minorityElect = FALSE /\ wronglyDevolved = FALSE
  /\ offList = FALSE /\ houseShort = FALSE /\ senateShort = FALSE
  /\ thirdTerm = FALSE /\ becameWithoutDeath = FALSE

-----------------------------------------------------------------------------
(* The States appoint - Art. II s.1 cl.2, cl.4                              *)

\* A State fills one of its seats, "in such Manner as the Legislature thereof
\* may direct", with an elector pledged to c.
Appoint(e, c) ==
  /\ AppointmentOpen
  /\ pledge[e] = NoOne
  /\ MayBeElector(e)
  /\ pledge' = [pledge EXCEPT ![e] = c]
  /\ lateAppointment' = (lateAppointment \/ stage # "Appointing")
  /\ UNCHANGED <<timeVars, ballot, objection, electVars, officeVars, personVars,
                 lateVote, lameDuck, rejectedAlone, minorityElect, wronglyDevolved,
                 offList, houseShort, senateShort, thirdTerm, becameWithoutDeath>>

\* A seat not filled by now stays empty (New York, 1789).
ElectionDayEnds ==
  /\ stage = "Appointing"
  /\ stage' = "Voting"
  /\ UNCHANGED <<clock, collegeVars, electVars, officeVars, personVars, flagVars>>

-----------------------------------------------------------------------------
(* The electors vote - Amend. XII                                           *)

Vote(e, p, v) ==
  /\ PollsOpen
  /\ pledge[e] # NoOne
  /\ ballot[e] = NoBallot
  /\ TwoNames(p, v)
  /\ Habitation(e, p, v)
  /\ Faithful(e, p)
  /\ ballot' = [ballot EXCEPT ![e] = [p |-> p, v |-> v]]
  /\ lateVote' = (lateVote \/ stage # "Voting")
  /\ UNCHANGED <<timeVars, pledge, objection, electVars, officeVars, personVars,
                 lateAppointment, lameDuck, rejectedAlone, minorityElect,
                 wronglyDevolved, offList, houseShort, senateShort, thirdTerm,
                 becameWithoutDeath>>

\* An elector who has not voted by now has cast no vote.
ElectorsAdjourn ==
  /\ stage = "Voting"
  /\ stage' = "Voted"
  /\ UNCHANGED <<clock, collegeVars, electVars, officeVars, personVars, flagVars>>

-----------------------------------------------------------------------------
(* Congress counts - Amend. XII, Amend. XX ss.1-2, 3 U.S.C. 15              *)

\* The joint session opens; new says whether it is the Congress that
\* assembled on 3 January.
OpenCount(new) ==
  /\ stage = "Voted"
  /\ Seated(new)
  /\ stage' = "Counting"
  /\ lameDuck' = (lameDuck \/ ~new)
  /\ UNCHANGED <<clock, collegeVars, electVars, officeVars, personVars,
                 lateAppointment, lateVote, rejectedAlone, minorityElect,
                 wronglyDevolved, offList, houseShort, senateShort, thirdTerm,
                 becameWithoutDeath>>

\* An objection to elector e's vote on ground g is sustained; both says
\* whether each House sustained it.
Sustain(e, g, both) ==
  /\ stage = "Counting"
  /\ e \in Contestable
  /\ pledge[e] # NoOne
  /\ objection[e] = "None"
  /\ Concur(both)
  /\ objection' = [objection EXCEPT ![e] = g]
  /\ rejectedAlone' = (rejectedAlone \/ ~both)
  /\ UNCHANGED <<timeVars, pledge, ballot, electVars, officeVars, personVars,
                 lateAppointment, lateVote, lameDuck, minorityElect,
                 wronglyDevolved, offList, houseShort, senateShort, thirdTerm,
                 becameWithoutDeath>>

\* "The votes shall then be counted": p and v are announced elected, or no
\* one is and the choice passes to the House or the Senate with its list.
\* The certificates are then spent.
Announce(p, v) ==
  /\ stage = "Counting"
  /\ PResult(p)
  /\ VResult(v)
  /\ TwoPersons(p, v)
  /\ stage' = "Counted"
  /\ pElect' = p
  /\ vElect' = v
  /\ pList' = IF p = NoOne THEN PTop ELSE {}
  /\ vList' = IF v = NoOne THEN VTop ELSE {}
  /\ minorityElect' = (minorityElect \/ (p # NoOne /\ ~PMajority(p))
                                     \/ (v # NoOne /\ ~VMajority(v)))
  /\ wronglyDevolved' = (wronglyDevolved
                           \/ (p = NoOne /\ \E c \in Candidates : PMajority(c))
                           \/ (v = NoOne /\ \E c \in Candidates : VMajority(c)))
  /\ pledge' = Blank(Electors, NoOne)
  /\ ballot' = Blank(Electors, NoBallot)
  /\ objection' = Blank(Electors, "None")
  /\ UNCHANGED <<clock, officeVars, personVars, lateAppointment, lateVote,
                 lameDuck, rejectedAlone, offList, houseShort, senateShort,
                 thirdTerm, becameWithoutDeath>>

-----------------------------------------------------------------------------
(* The House and the Senate choose - Amend. XII                             *)

\* One ballot of the House that chooses: the States in Q are present, those
\* in Y vote for c. A ballot that chooses no one is a stuttering step (there
\* were thirty-five of them in 1801). Before noon or after it.
HouseChooses(c, Q, Y) ==
  /\ stage = "Counted"
  /\ pElect = NoOne
  /\ OnList(c, pList)
  /\ HouseQuorum(Q)
  /\ HouseCarries(Q, Y)
  /\ TwoPersons(c, vElect)
  /\ pElect' = c
  /\ pList' = {}
  /\ offList' = (offList \/ c \notin pList)
  /\ houseShort' = (houseShort \/ ~(3 * Cardinality(Q) >= 2 * Cardinality(States))
                               \/ ~(2 * Cardinality(Y) > Cardinality(States)))
  /\ UNCHANGED <<timeVars, collegeVars, vElect, vList, officeVars, personVars,
                 lateAppointment, lateVote, lameDuck, rejectedAlone, minorityElect,
                 wronglyDevolved, senateShort, thirdTerm, becameWithoutDeath>>

SenateChooses(c, Q, Y) ==
  /\ stage = "Counted"
  /\ vElect = NoOne
  /\ OnList(c, vList)
  /\ SenateQuorum(Q)
  /\ SenateCarries(Q, Y)
  /\ TwoPersons(pElect, c)
  /\ vElect' = c
  /\ vList' = {}
  /\ offList' = (offList \/ c \notin vList)
  /\ senateShort' = (senateShort \/ ~(3 * Cardinality(Q) >= 2 * Cardinality(Senators))
                                 \/ ~(2 * Cardinality(Y) > Cardinality(Senators)))
  /\ UNCHANGED <<timeVars, collegeVars, pElect, pList, officeVars, personVars,
                 lateAppointment, lateVote, lameDuck, rejectedAlone, minorityElect,
                 wronglyDevolved, houseShort, thirdTerm, becameWithoutDeath>>

-----------------------------------------------------------------------------
(* Noon on 20 January - Amend. XX ss.1, 3; Amend. XXII                      *)

\* The old term ends once the count is open, finished or not. Exactly one of
\* the three steps below is then enabled.
TermEnds == clock \in {"Founding", "BeforeNoon"} /\ stage \in {"Counting", "Counted"}
InTerm   == clock \in {"FirstHalf", "SecondHalf"}
\* The Vice President elect takes that office if qualified for it.
VPSeat   == IF VQualified(vElect) THEN vElect ELSE NoOne

\* The President elect qualifies.
NoonInaugurates ==
  /\ TermEnds
  /\ Qualified(pElect)
  /\ clock' = "FirstHalf"
  /\ president' = pElect
  /\ vicePresident' = VPSeat
  /\ acting' = NoOne
  /\ elected' = [elected EXCEPT ![pElect] = @ + 1]
  /\ thirdTerm' = (thirdTerm \/ ~WithinXXII(pElect))
  /\ UNCHANGED <<stage, collegeVars, electVars, dead, relieved, servedLong,
                 lateAppointment, lateVote, lameDuck, rejectedAlone, minorityElect,
                 wronglyDevolved, offList, houseShort, senateShort,
                 becameWithoutDeath>>

\* "If ... the President elect shall have died, the Vice President elect
\* shall become President": for the whole of a term to which another was
\* elected.
NoonSucceeds ==
  /\ TermEnds
  /\ ~Qualified(pElect)
  /\ ElectGone
  /\ VQualified(vElect)
  /\ clock' = "FirstHalf"
  /\ president' = vElect
  /\ vicePresident' = NoOne
  /\ acting' = NoOne
  /\ servedLong' = IF pElect # NoOne THEN servedLong \cup {vElect} ELSE servedLong
  /\ becameWithoutDeath' = (becameWithoutDeath \/ pElect = NoOne \/ pElect \notin dead)
  /\ UNCHANGED <<stage, collegeVars, electVars, dead, relieved, elected,
                 lateAppointment, lateVote, lameDuck, rejectedAlone, minorityElect,
                 wronglyDevolved, offList, houseShort, senateShort, thirdTerm>>

\* No President: none chosen, or the one chosen has failed to qualify, or
\* is dead with no Vice President elect to take the office.
NoonVacant ==
  /\ TermEnds
  /\ ~Qualified(pElect)
  /\ ~(ElectGone /\ VQualified(vElect))
  /\ clock' = "FirstHalf"
  /\ president' = NoOne
  /\ vicePresident' = VPSeat
  /\ acting' = NoOne
  /\ UNCHANGED <<stage, collegeVars, electVars, personVars, flagVars>>

\* "... until a President shall have qualified": the House chooses late, the
\* count ends late, or a disability is removed.
Qualify ==
  /\ InTerm
  /\ president = NoOne
  /\ Qualified(pElect)
  /\ TwoPersons(pElect, vicePresident)
  /\ president' = pElect
  /\ acting' = NoOne
  /\ elected' = [elected EXCEPT ![pElect] = @ + 1]
  /\ thirdTerm' = (thirdTerm \/ ~WithinXXII(pElect))
  /\ UNCHANGED <<timeVars, collegeVars, electVars, vicePresident, dead, relieved,
                 servedLong, lateAppointment, lateVote, lameDuck, rejectedAlone,
                 minorityElect, wronglyDevolved, offList, houseShort, senateShort,
                 becameWithoutDeath>>

\* The same for the Vice President elect; whoever the statute had acting
\* gives way (3 U.S.C. 19(c)).
VPQualify ==
  /\ InTerm
  /\ vicePresident = NoOne
  /\ VQualified(vElect)
  /\ TwoPersons(president, vElect)
  /\ vicePresident' = vElect
  /\ acting' = NoOne
  /\ UNCHANGED <<timeVars, collegeVars, electVars, president, personVars, flagVars>>

-----------------------------------------------------------------------------
(* Acting as President - Amend. XX s.3, 3 U.S.C. 19                         *)

VPActs ==
  /\ clock # "Founding"
  /\ president = NoOne /\ acting = NoOne
  /\ vicePresident # NoOne
  /\ acting' = vicePresident
  /\ UNCHANGED <<timeVars, collegeVars, electVars, president, vicePresident,
                 personVars, flagVars>>

SuccessorActs ==
  /\ clock # "Founding"
  /\ Statute
  /\ president = NoOne /\ acting = NoOne
  /\ NoVP
  /\ acting' = Successor
  /\ UNCHANGED <<timeVars, collegeVars, electVars, president, vicePresident,
                 personVars, flagVars>>

-----------------------------------------------------------------------------
(* The term, and the people in it                                           *)

\* Death, of a candidate or of whoever holds an office. The Vice President
\* becomes President (Amend. XXV s.1); if more than two years of the term
\* remain, that is service Amend. XXII counts.
Die(x) ==
  /\ x \in Mortal /\ x \notin dead
  /\ dead' = dead \cup {x}
  /\ president' = IF x = president THEN vicePresident ELSE president
  /\ vicePresident' = IF x \in {president, vicePresident} THEN NoOne ELSE vicePresident
  /\ acting' = IF x = acting THEN NoOne ELSE acting
  /\ servedLong' = IF x = president /\ vicePresident # NoOne /\ clock = "FirstHalf"
                   THEN servedLong \cup {vicePresident} ELSE servedLong
  /\ UNCHANGED <<timeVars, collegeVars, electVars, relieved, elected, flagVars>>

\* Amend. XIV s.3: "Congress may by a vote of two-thirds of each House,
\* remove such disability."
RemoveDisability(x) ==
  /\ x \in Disabled /\ x \notin relieved
  /\ relieved' = relieved \cup {x}
  /\ UNCHANGED <<timeVars, collegeVars, electVars, officeVars, dead, elected,
                 servedLong, flagVars>>

Midterm ==
  /\ clock = "FirstHalf"
  /\ clock' = "SecondHalf"
  /\ UNCHANGED <<stage, collegeVars, electVars, officeVars, personVars, flagVars>>

\* Election day again. Whatever the last election left undecided is moot.
OpenElection ==
  /\ clock = "SecondHalf"
  /\ clock' = "BeforeNoon"
  /\ stage' = "Appointing"
  /\ pledge' = Blank(Electors, NoOne)
  /\ ballot' = Blank(Electors, NoBallot)
  /\ objection' = Blank(Electors, "None")
  /\ pElect' = NoOne /\ vElect' = NoOne
  /\ pList' = {} /\ vList' = {}
  /\ UNCHANGED <<officeVars, personVars, flagVars>>

-----------------------------------------------------------------------------
CollegeSteps ==
  \/ \E e \in Electors, c \in Candidates : Appoint(e, c)
  \/ ElectionDayEnds
  \/ \E e \in Electors, p, v \in Candidates : Vote(e, p, v)
  \/ ElectorsAdjourn

CountSteps ==
  \/ \E new \in BOOLEAN : OpenCount(new)
  \/ \E e \in Electors, g \in Grounds, both \in BOOLEAN : Sustain(e, g, both)
  \/ \E p, v \in Choice : Announce(p, v)
  \/ \E c \in Candidates, Q \in SUBSET States : \E Y \in SUBSET Q : HouseChooses(c, Q, Y)
  \/ \E c \in Candidates, Q \in SUBSET Senators : \E Y \in SUBSET Q : SenateChooses(c, Q, Y)

NoonSteps ==
  \/ NoonInaugurates
  \/ NoonSucceeds
  \/ NoonVacant
  \/ Qualify
  \/ VPQualify
  \/ VPActs
  \/ SuccessorActs

TermSteps ==
  \/ \E x \in Persons : Die(x)
  \/ \E x \in Persons : RemoveDisability(x)
  \/ Midterm
  \/ OpenElection

Next == CollegeSteps \/ CountSteps \/ NoonSteps \/ TermSteps

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                        *)

ElectorsHoldNoOffice   == Pledged \cap Officers = {}
AppointedOnElectionDay == ~lateAppointment
SameDay                == ~lateVote

OneNotAnInhabitant ==
  \A e \in Electors :
    ballot[e] = NoBallot \/ ~(SameState(e, ballot[e].p) /\ SameState(e, ballot[e].v))

PledgesBind ==
  \A e \in Binding : ballot[e] = NoBallot \/ ballot[e].p = pledge[e]

NewCongressCounts == ~lameDuck
CountIsCongress   == ~rejectedAlone
ElectorsChoose    == ~minorityElect
DevolvesOnlyWithoutMajority == ~wronglyDevolved
ChoiceFromTheList == ~offList

\* Announce is enabled whenever the count is open.
CountCanClose ==
  stage = "Counting" =>
    \E p, v \in Choice : PResult(p) /\ VResult(v) /\ TwoPersons(p, v)
HouseVote         == ~houseShort
SenateVote        == ~senateShort

PresidentNotVP ==
  /\ pElect = NoOne \/ pElect # vElect
  /\ president = NoOne \/ president # vicePresident

InOffice == {president, vicePresident, acting} \ {NoOne}

Qualifications == InOffice \subseteq Eligible
Disability     == \A x \in InOffice : x \notin Disabled \/ x \in relieved

TwoTermLimit == ~thirdTerm
VPElectBecomesOnlyOnDeath == ~becameWithoutDeath

ActingOrder ==
  acting # NoOne =>
    /\ president = NoOne
    /\ acting = vicePresident \/ (vicePresident = NoOne /\ acting = Successor)

Safety ==
  /\ ElectorsHoldNoOffice /\ AppointedOnElectionDay /\ SameDay
  /\ OneNotAnInhabitant /\ PledgesBind /\ NewCongressCounts /\ CountIsCongress
  /\ ElectorsChoose /\ DevolvesOnlyWithoutMajority /\ CountCanClose
  /\ ChoiceFromTheList /\ HouseVote /\ SenateVote
  /\ PresidentNotVP /\ Qualifications /\ Disability
  /\ TwoTermLimit /\ VPElectBecomesOnlyOnDeath /\ ActingOrder

-----------------------------------------------------------------------------
(* Reachability witnesses: each must be VIOLATED under Mut = "none".        *)
(* State predicates are INVARIANT rows; [][...]_vars ones, which name a     *)
(* step, are PROPERTY rows.                                                 *)

NeverPresident      == president = NoOne
NeverUnfilledSeat   == ~(stage = "Voted" /\ Pledged # Electors)
NeverAbstention     == ~(stage = "Voted" /\ \E e \in Pledged : ballot[e] = NoBallot)
NeverDepartsFromPledge ==
  \A e \in Electors : ballot[e] = NoBallot \/ ballot[e].p = pledge[e]
NeverRejected       == \A e \in Electors : objection[e] = "None"
\* Announced President with a majority of the electors appointed (as it must
\* be) but not of the electors the States appointed: the difference is the
\* electors Congress held not lawfully certified.
NeverElectedByRejection ==
  [][\A p, v \in Choice :
       Announce(p, v) => (p = NoOne \/ 2 * PVotes(p) > Cardinality(Pledged))]_vars
\* Voted for as Vice President, and not one of the two highest on the list.
NeverOffTheSenateList ==
  [][\A p, v \in Choice :
       Announce(p, v) =>
         (v # NoOne \/ \A c \in Candidates : VVotes(c) > 0 => c \in VTop)]_vars
NeverHouseChooses ==
  [][\A c \in Candidates, Q, Y \in SUBSET States : ~HouseChooses(c, Q, Y)]_vars
NeverSenateChooses ==
  [][\A c \in Candidates, Q, Y \in SUBSET Senators : ~SenateChooses(c, Q, Y)]_vars
NeverNoonWithoutPresident == [][~(NoonVacant /\ stage = "Counted")]_vars
NeverVPElectBecomes == [][~NoonSucceeds]_vars
NeverVPActs         == acting = NoOne \/ acting # vicePresident
NeverSuccessorActs  == acting # Successor
NeverQualifiesLate  == [][~Qualify]_vars
NeverVPQualifiesLate == [][~VPQualify]_vars
NeverCountAfterNoon == [][\A p, v \in Choice : ~(Announce(p, v) /\ InTerm)]_vars
NeverRelieved       == relieved = {}
NeverDeadElect      == pElect = NoOne \/ pElect \notin dead
NeverSuccession     ==
  [][\A x \in Persons : ~(Die(x) /\ x = president /\ vicePresident # NoOne)]_vars
NeverReelected      == \A x \in Persons : elected[x] < 2
NeverServedLong     == servedLong = {}
NeverTermLimited    ==
  [][~(NoonVacant /\ pElect # NoOne /\ pElect \notin dead /\ ~WithinXXII(pElect))]_vars
\* What reading Amend. XII's last sentence without Amend. XXII admits: twice
\* elected President, then Vice President, then President again.
NeverThirdTermBySuccession ==
  [][\A x \in Persons : ~(/\ Die(x) /\ x = president /\ vicePresident # NoOne
                          /\ elected[vicePresident] = 2)]_vars
NeverSecondElection == [][~OpenElection]_vars

-----------------------------------------------------------------------------
(* Liveness - claimed only for the executive power                          *)

Vacant == president = NoOne /\ acting = NoOne

\* Amend. XX s.3 with 3 U.S.C. 19: someone holds the executive power.
ExecutiveIsFilled == (clock # "Founding" /\ Vacant) ~> ~Vacant

\* Fairness, on actions of Next, named for whose obligation it is: the Vice
\* President, or failing one the officer the statute names, takes up the
\* powers and duties. Weak fairness on the two together: while the vacancy
\* lasts one of them is enabled, but which one changes with each Vice
\* President elect who qualifies or dies.
SomeoneActs == WF_vars(VPActs \/ SuccessorActs)

FairSpec          == Spec /\ SomeoneActs
SpecVPOnly        == Spec /\ WF_vars(VPActs)          \* drops the statute's officer
SpecSuccessorOnly == Spec /\ WF_vars(SuccessorActs)   \* drops the Vice President
\* Weak fairness on each alone: not enough (see above).
SpecEachAlone     == Spec /\ WF_vars(VPActs) /\ WF_vars(SuccessorActs)

\* Violated exactly when the spec has a fair behaviour at all.
NoBehaviour == <>FALSE

\* A space-cutting bound for TLC under M_XXII, whose count of elections is
\* otherwise unbounded (used as constraint=ElectionsBound on those rows).
\* Not an assumption.
ElectionsBound == \A x \in Persons : elected[x] <= 3
=============================================================================
