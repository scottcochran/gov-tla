---------------------------- MODULE Government ----------------------------
(***************************************************************************)
(* The authority graph of the federal government.                          *)
(*                                                                         *)
(* Constitution.tla, Executive.tla and Judiciary.tla model what each       *)
(* branch does. This module models how authority runs between them, as a   *)
(* directed, labelled multigraph whose shape changes as the system runs.   *)
(*                                                                         *)
(* Nodes: the People, the States, the Constitution, the three branches,    *)
(* the Vice President, and the creatures of statute (agencies, inferior    *)
(* courts) that Congress brings into being and may abolish.                *)
(*                                                                         *)
(* Edges come in two layers. GRANT says where authority comes from: Power  *)
(* (vesting clauses, enabling acts), Select (elections, nomination,        *)
(* consent), Amend (Art. V, Art. VII). CONTROL is one holder acting on     *)
(* another's exercise of power (veto, override, purse, impeachment,        *)
(* removal, review, pardon ...). Every exercise of authority is the firing *)
(* of one edge in the graph, by its holder, under the edge's condition;    *)
(* firing may change the graph: statutes add and remove edges and nodes,   *)
(* amendments rewrite text edges, courts sever statutory edges.            *)
(*                                                                         *)
(* PROPERTIES. Each is local - one action could break it, and that        *)
(* action's guard decides in the current state whether it would - or it   *)
(* is a global reachability claim kept under its old name and checked by   *)
(* TLC, with the local property it follows from named beside it.           *)
(*                                                                         *)
(*  Shape of the graph                                                     *)
(*   EdgesConnectLiveNodes     no edge touches an abolished or unmade body *)
(*   OfficesAreLive            only an existing office is filled or        *)
(*                             pending; abolition unseats (Stuart v. Laird)*)
(*   TextFollowsArticleV       the text layer is the 1789 text as amended  *)
(*                             by the ratified amendments, nothing else.   *)
(*                             Local form of TextChangesOnlyByArticleV.    *)
(*   ArticleVStands            the Art. V edges (propose, apply for a      *)
(*                             convention, ratify) are always in the graph *)
(*   ConstitutionWrittenByPeopleAndStates   Preamble, Arts. V and VII:     *)
(*                             every edge into the text is theirs          *)
(*   OnlyStatutesOverstep      no text edge is one a doctrine forbids      *)
(*  Grant layer (the refuted claims are below)                             *)
(*   GrantFollowsChainExceptXXV   local: every inner grant edge (People    *)
(*                             and States set aside) climbs the rank       *)
(*                             Constitution < Congress < VP < Executive    *)
(*                             < Judiciary < statute, except XXV sec. 2's  *)
(*                             NominateVP                                  *)
(*   GrantCyclesPassThroughPeopleStatesOrVP  global, checked: with the VP  *)
(*                             also set aside the inner grant layer is     *)
(*                             acyclic. Follows from the local form: no    *)
(*                             edge left descends the rank.                *)
(*   NominationLoopIffXXV      local: NominateVP is in the graph exactly   *)
(*                             while XXV is ratified, Succession always    *)
(*   OnlyGrantCycleIsXXV       global, checked: the Executive-VP loop is   *)
(*                             the only inner grant cycle, present exactly *)
(*                             under XXV. Follows from the two local forms.*)
(*   NamedPathsFromPeople      local: People -ElectHouse-> Congress, and   *)
(*                             from Congress one named edge to every       *)
(*                             branch, the VP and every live body          *)
(*   EveryBodyIsCreatedByLaw   every agency and inferior court has its     *)
(*                             Power edge from Congress (Art. I sec. 8)    *)
(*   PowerTracesToPeople       global, checked; follows from the two above *)
(*   PeoplePowerGoesThroughConstitution  local: every Power or Amend edge  *)
(*                             out of the People goes into the text        *)
(*   ConstitutionIsTheOnlyDoor global, checked; follows from the above     *)
(*  Control layer                                                          *)
(*   MutualChecks              every branch has a control edge onto each   *)
(*                             other branch (the text layer never loses    *)
(*                             one, and no statute joins two branches)     *)
(*   ControlLayerIsCyclic      global, checked; follows from MutualChecks  *)
(*   LegislativePrimacy        Congress has more control edges onto each   *)
(*                             branch than it has onto Congress            *)
(*  Doctrine: a court that hears a challenge to a forbidden statutory edge *)
(*  severs it. Each is a record of what a court upheld.                    *)
(*   BuckleyHonoured           Buckley v. Valeo (1976): Congress appoints  *)
(*                             no officer                                  *)
(*   SeilaLawHonoured          Seila Law (2020), Trump v. Slaughter (2026):*)
(*                             no for-cause tenure for an officer who      *)
(*                             executes the laws                           *)
(*   BowsherHonoured           Bowsher v. Synar (1986): Congress removes   *)
(*                             no officer who executes the laws            *)
(*   ChadhaHonoured            INS v. Chadha (1983): no legislative veto   *)
(*   WillHonoured              Compensation Clause, U.S. v. Will (1980)    *)
(*   ExecutorsAreRemovable     whatever a court severs, an officer who     *)
(*                             executes the laws stays removable by        *)
(*                             someone (Seila Law: at will; Bowsher: by    *)
(*                             Congress, once the executive power is gone) *)
(*  Acts                                                                   *)
(*   ActsFollowEdges, ActsByHolders (together EveryActIsAnEdge)  every act *)
(*                             fires an edge in the graph, by its holder   *)
(*   GoodBehaviour             Art. III sec. 1: an inferior-court judge is *)
(*                             never removed by the President or Congress  *)
(*                             (resignation, conviction, abolition only)   *)
(*   PocketVetoHonoured        Art. I sec. 7 cl. 2: a bill never becomes   *)
(*                             law unsigned while an adjournment prevents  *)
(*                             its return                                  *)
(*  Action properties (proved; no mutation breaks them)                    *)
(*   TextChangesOnlyByArticleV, StatutesChangeOnlyByLawOrCourt             *)
(*  Liveness                                                               *)
(*   UnconstitutionalEdgesAreStruck  Marbury as a process: under FairSpec  *)
(*                             a statutory edge the doctrines forbid does  *)
(*                             not last. Fairness: LitigantsSue (the       *)
(*                             People's: someone injured eventually sues)  *)
(*                             and CourtsDecide (the Judiciary's: a        *)
(*                             pending case is eventually decided), both   *)
(*                             weak: neither action is disabled by another *)
(*                             while the edge stands. SpecNoSuit and       *)
(*                             SpecNoRuling each drop one; NoBehaviour     *)
(*                             shows a fair spec has a behaviour.          *)
(*                                                                         *)
(* REFUTED CLAIMS, kept unchanged: GrantCyclesPassThroughPeopleOrStates    *)
(* and GrantFollowsChain. Both held while the Vice President was folded    *)
(* into the Executive; with the VP as a node TLC refutes both under        *)
(* Mut = "none" in two steps (propose XXV, ratify it). See the comment at  *)
(* their definitions.                                                      *)
(*                                                                         *)
(* MUTATIONS. Mut = "none" is the module as specified. Each other value    *)
(* removes one guard or rule, and names the property that must fail.      *)
(*   M_OFFEDGE    Fire does not require the edge to be in the graph.       *)
(*                ActsFollowEdges and GoodBehaviour must fail.             *)
(*   M_INACTIVE   Fire does not require the edge's holder to be seated.    *)
(*                ActsByHolders must fail.                                 *)
(*   M_APPLICABLE a bill's precondition (the body exists, or not yet; the  *)
(*                edge is new) is checked neither at passage nor at        *)
(*                enactment. EdgesConnectLiveNodes must fail.              *)
(*   M_RECHECK    the precondition is checked at passage only. Nothing     *)
(*                between passage and enactment changes it (one bill is in *)
(*                flight), so this reaches exactly the states of none and  *)
(*                no property may fail: the re-check is redundant here.    *)
(*   M_NOSTUART   abolishing a court leaves its judge in office: the       *)
(*                Federalist reading Stuart v. Laird (1803) rejected.      *)
(*                OfficesAreLive must fail.                                *)
(*   M_NOPOCKET   a bill lapses into law although Congress is adjourned:   *)
(*                no pocket veto. PocketVetoHonoured must fail.            *)
(*   M_UPHOLD     a court upholds every edge it reviews: no judicial       *)
(*                review. All five doctrine properties must fail.          *)
(*   M_HUMPHREY   for-cause tenure is upheld for an executing officer:     *)
(*                Humphrey's Executor (1935). SeilaLawHonoured must fail.  *)
(*   M_PRECHADHA  the legislative veto is upheld, as before 1983.          *)
(*                ChadhaHonoured must fail.                                *)
(*   M_PREBUCKLEY Congress's appointment of officers is upheld, as for the *)
(*                FEC before 1976. BuckleyHonoured must fail.              *)
(*   M_PREBOWSHER Congress's removal of an executing officer is upheld, as *)
(*                for the Comptroller General before 1986.                 *)
(*                BowsherHonoured must fail.                               *)
(*   M_SEVER_PLAIN a court strikes the offending edge and nothing else:    *)
(*                no at-will removal in place of struck tenure (Seila      *)
(*                Law), no loss of executive power in place of Congress's  *)
(*                removal (Bowsher). ExecutorsAreRemovable must fail.      *)
(*   M_CONGRESS_AMENDS (a constant, not a guard) XXV also gives Congress   *)
(*                an Amend edge into the text.                             *)
(*                ConstitutionWrittenByPeopleAndStates,                    *)
(*                GrantFollowsChainExceptXXV, and with them                *)
(*                GrantCyclesPassThroughPeopleStatesOrVP and               *)
(*                OnlyGrantCycleIsXXV must fail.                           *)
(*   M_NO_ARTV    (a constant, not a guard) XXV also repeals Article V.    *)
(*                ArticleVStands must fail.                                *)
(* The two constant mutations are the amendments the old module's ASSUME   *)
(* comment imagined: they show the properties above are facts about the    *)
(* current text, not necessary truths.                                     *)
(*                                                                         *)
(* WITNESSES. Each Never... property must be VIOLATED under "none": an     *)
(* agency created and abolished, a court established, a forbidden edge     *)
(* enacted, an edge of each doctrine struck, XVII and XXV ratified, a Vice *)
(* President seated by nomination, a contested inability, a court          *)
(* abolished under a sitting judge, a bill on the desk while Congress is   *)
(* adjourned.                                                              *)
(*                                                                         *)
(* ABSTRACTED: vote counts (see the other modules), persons, State         *)
(* governments' internal structure, the Youngstown framework, standing     *)
(* (any statutory edge whose label is in Standing may be challenged), and  *)
(* an agency's internal head-to-inferior delegation, which does not cross  *)
(* between bodies. Initial graph: the Constitution of 1789 with the Bill   *)
(* of Rights. Two later amendments that change the graph's shape are       *)
(* modelled: XVII (the Senate chosen by the People) and XXV (the President *)
(* nominates a Vice President whom Congress confirms; inability).          *)
(*                                                                         *)
(* CONSTANTS beyond the pools only bound the state space for TLC: which    *)
(* amendments may be proposed (Proposable), which statutory edges may be   *)
(* challenged (Standing), and which enabling acts Congress may pass        *)
(* (ExecOptions, RemoverOptions, VestingOptions). Government.cfg sets each *)
(* to everything; the rows set them small. No proof assumes them.          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Agencies,       \* Pool of agency identifiers Congress may create
  Courts,         \* Pool of inferior-court identifiers Congress may establish
  Mut,            \* "none", or the one guard removed (see the header)
  Proposable,     \* amendments that may be proposed
  Standing,       \* labels of the statutory edges that may be challenged
  ExecOptions,    \* enabling acts Congress may pass: executive power or not,
  RemoverOptions, \*   who removes the head,
  VestingOptions  \*   who appoints inferior officers

Mutations ==
  {"none", "M_OFFEDGE", "M_INACTIVE", "M_APPLICABLE", "M_RECHECK", "M_NOSTUART",
   "M_NOPOCKET", "M_UPHOLD", "M_HUMPHREY", "M_PRECHADHA", "M_PREBUCKLEY",
   "M_PREBOWSHER", "M_SEVER_PLAIN", "M_CONGRESS_AMENDS", "M_NO_ARTV"}

-----------------------------------------------------------------------------
(* Nodes and edges                                                         *)

Fixed    == {"People", "States", "Constitution", "Congress", "Executive", "Judiciary",
             "VicePresident"}
Branches == {"Congress", "Executive", "Judiciary"}
Nodes    == Fixed \cup Agencies \cup Courts

\* Nodes that are vacant unless someone holds the office. The Supreme Court
\* is treated as an institution that never lapses; impeaching one justice
\* does not empty it.
Offices  == {"Executive", "VicePresident"} \cup Agencies \cup Courts

Kinds      == {"Power", "Select", "Amend", "Control"}
GrantKinds == {"Power", "Select", "Amend"}
Bases      == {"Text", "Statute"}

Labels ==
  { \* constituent
    "Ordain", "Ratify", "Propose", "ApplyForConvention",
    \* vesting
    "ArtI", "ArtII", "ArtIII",
    \* selection
    "ElectHouse", "ElectSenate", "AppointElectors", "ContingentElection",
    "Nominate", "Consent", "ConfirmVP", "NominateVP", "Succession",
    \* control between the branches
    "Presentment", "Veto", "Override", "Appropriate", "Impeach",
    "AdviseTreaties", "DeclareWar", "Convene", "Adjourn", "Exceptions",
    "Organize", "Pardon", "Review", "PresideTrial", "Sue", "DecideInability",
    "PresideSenate", "DeclareInability",
    \* statutory
    "Enable", "ExecutivePower", "Direct", "NominateHead", "ConsentHead",
    "Remove", "RemoveForCause", "AppointInferior", "Establish",
    "Jurisdiction", "Appeal", "LegislativeVeto", "DiminishPay" }

Edge(f, t, k, l, b) == [from |-> f, to |-> t, kind |-> k, label |-> l, basis |-> b]
Txt(f, t, k, l)     == Edge(f, t, k, l, "Text")       \* put there by the Constitution
Law(f, t, k, l)     == Edge(f, t, k, l, "Statute")    \* put there by an Act of Congress
NoEdge              == Edge("None", "None", "None", "None", "None")

EdgeType == [from : Nodes, to : Nodes, kind : Kinds, label : Labels, basis : Bases]

\* The pools are disjoint, and no pool member is a fixed node (or "None").
ASSUME PoolsDisjoint == Agencies \cap Courts = {}
ASSUME PoolsAreNew   == (Agencies \cup Courts) \cap (Fixed \cup {"None"}) = {}
ASSUME MutIsKnown    == Mut \in Mutations

-----------------------------------------------------------------------------
(* The graph of 1789                                                       *)

Founding ==
  { \* -- Who may write the Constitution: Preamble, Art. V, Art. VII
    Txt("People",   "Constitution", "Amend",   "Ordain"),
    Txt("States",   "Constitution", "Amend",   "Ratify"),        \* 3/4 of the States
    Txt("Congress", "States",       "Amend",   "Propose"),       \* 2/3 of each house
    Txt("States",   "Congress",     "Control", "ApplyForConvention"),
                                    \* 2/3 of the States; Congress "shall call"
    \* -- The three vesting clauses
    Txt("Constitution", "Congress",  "Power", "ArtI"),
    Txt("Constitution", "Executive", "Power", "ArtII"),
    Txt("Constitution", "Judiciary", "Power", "ArtIII"),
    \* -- Who fills the offices
    Txt("People",    "Congress",  "Select", "ElectHouse"),         \* Art. I sec. 2
    Txt("States",    "Congress",  "Select", "ElectSenate"),        \* Art. I sec. 3 (to 1913)
    Txt("States",    "Executive", "Select", "AppointElectors"),    \* Art. II sec. 1 cl. 2
    Txt("Congress",  "Executive", "Select", "ContingentElection"), \* Art. II sec. 1 cl. 3; Amend. XII
    Txt("Executive", "Judiciary", "Select", "Nominate"),           \* Art. II sec. 2 cl. 2
    Txt("Congress",  "Judiciary", "Select", "Consent"),            \* Senate majority
    \* -- Congress onto the Executive
    Txt("Congress", "Executive", "Control", "Presentment"),    \* Art. I sec. 7 cl. 2
    Txt("Congress", "Executive", "Control", "Override"),       \* 2/3 of each house
    Txt("Congress", "Executive", "Control", "Appropriate"),    \* Art. I sec. 9 cl. 7
    Txt("Congress", "Executive", "Control", "Impeach"),        \* House majority, Senate 2/3
    Txt("Congress", "Executive", "Control", "AdviseTreaties"), \* Senate 2/3
    Txt("Congress", "Executive", "Control", "DeclareWar"),     \* Art. I sec. 8 cl. 11
    \* -- The Executive onto Congress
    Txt("Executive", "Congress", "Control", "Veto"),           \* within ten days
    Txt("Executive", "Congress", "Control", "Convene"),        \* Art. II sec. 3
    Txt("Executive", "Congress", "Control", "Adjourn"),        \* Art. II sec. 3; never used
    \* -- Congress onto the Judiciary
    Txt("Congress", "Judiciary", "Control", "Impeach"),
    Txt("Congress", "Judiciary", "Control", "Exceptions"),     \* Art. III sec. 2 cl. 2
    Txt("Congress", "Judiciary", "Control", "Organize"),       \* Art. I sec. 8 cl. 9: size, pay, courts
    \* -- The Judiciary onto the others. Review is not in the text; it is
    \* -- Marbury's reading of Arts. III and VI, and treated here as fixed.
    Txt("Judiciary", "Congress",  "Control", "Review"),
    Txt("Judiciary", "Executive", "Control", "Review"),
    Txt("Judiciary", "Congress",  "Control", "PresideTrial"),  \* Art. I sec. 3 cl. 6
    \* -- The Executive onto the Judiciary
    Txt("Executive", "Judiciary", "Control", "Pardon"),        \* not in cases of impeachment
    \* -- The People onto the Judiciary: Art. III acts only on a case
    Txt("People", "Judiciary", "Control", "Sue"),
    \* -- The Vice President
    Txt("Constitution",  "VicePresident", "Power",   "ArtI"),     \* Art. I sec. 3 cl. 4
    Txt("States",        "VicePresident", "Select",  "AppointElectors"),
                                              \* Art. II sec. 1 cl. 2; Amend. XII
    Txt("Congress",      "VicePresident", "Select",  "ContingentElection"),
                                              \* Amend. XII: the Senate chooses
    Txt("VicePresident", "Executive",     "Select",  "Succession"), \* Art. II sec. 1 cl. 6
    Txt("VicePresident", "Congress",      "Control", "PresideSenate"),
                                              \* Art. I sec. 3 cl. 4: the tie vote
    Txt("Congress",      "VicePresident", "Control", "Impeach") }  \* Art. II sec. 4

\* The three edges of Article V.
ArticleV ==
  { Txt("Congress", "States",       "Amend",   "Propose"),
    Txt("States",   "Congress",     "Control", "ApplyForConvention"),
    Txt("States",   "Constitution", "Amend",   "Ratify") }

-----------------------------------------------------------------------------
(* Amendments that reshape the graph                                       *)

AmendIds == {"XVII", "XXV"}

\* What ratifying each amendment adds to and drops from the text. The two
\* constant mutations change these: M_CONGRESS_AMENDS has XXV also give
\* Congress an Amend edge into the text; M_NO_ARTV has XXV also repeal
\* Article V.
Adds(x) ==
  CASE x = "XVII" -> {Txt("People", "Congress", "Select", "ElectSenate")}
    [] x = "XXV"  -> {Txt("Executive", "VicePresident", "Select", "NominateVP"),    \* sec. 2
                      Txt("Congress", "VicePresident", "Select", "ConfirmVP"),       \* sec. 2
                      Txt("VicePresident", "Executive", "Control", "DeclareInability"),
                                                                             \* sec. 4
                      Txt("Congress", "Executive", "Control", "DecideInability")}    \* sec. 4
                     \cup (IF Mut = "M_CONGRESS_AMENDS"
                             THEN {Txt("Congress", "Constitution", "Amend", "Ratify")}
                             ELSE {})

Drops(x) ==
  CASE x = "XVII" -> {Txt("States", "Congress", "Select", "ElectSenate")}
    [] x = "XXV"  -> IF Mut = "M_NO_ARTV" THEN ArticleV ELSE {}

\* Every amendment rewrites the text among the fixed nodes, under every
\* mutation. (That none lets a branch write the text and none repeals
\* Article V is not assumed: those are the properties the two constant
\* mutations break.)
ASSUME AmendmentsRewriteText ==
  \A x \in AmendIds : \A e \in Adds(x) \cup Drops(x) :
    e.basis = "Text" /\ e.from \in Fixed /\ e.to \in Fixed

\* The text as amended: the founding text, less what the ratified
\* amendments drop, plus what they add. a is a value of `amendment`.
Applied(a, x, S) == IF a[x] = "Ratified" THEN S ELSE {}
TextFor(a) ==
  (Founding \ (Applied(a, "XVII", Drops("XVII")) \cup Applied(a, "XXV", Drops("XXV"))))
  \cup Applied(a, "XVII", Adds("XVII")) \cup Applied(a, "XXV", Adds("XXV"))

-----------------------------------------------------------------------------
(* Statutes                                                                *)

\* How the head of an agency may be removed, and who appoints its inferior
\* officer. "Congress" is on both lists because Congress has tried both;
\* see Forbidden.
Removers == {"President", "PresidentForCause", "Congress"}
Vesters  == {"President", "Head", "Courts", "Congress"}

Op(n, t, x, r, v) == [name |-> n, target |-> t, exec |-> x, remover |-> r, vesting |-> v]
NoOp == Op("None", "None", FALSE, "President", "Head")

\* Every bill Congress may pass, as Op records. (Record sets, each mapped
\* through a one-variable comprehension: the prover cannot unfold a set
\* comprehension over several variables, and the mapping keeps the order in
\* which TLC enumerates the bills, so seeded simulations are unchanged.)
Ops ==
  {o : o \in [name : {"CreateAgency"}, target : Agencies, exec : BOOLEAN,
              remover : Removers, vesting : Vesters]}
  \cup {o : o \in [name : {"AbolishAgency", "LegislativeVeto"}, target : Agencies,
                   exec : {FALSE}, remover : {"President"}, vesting : {"Head"}]}
  \cup {o : o \in [name : {"EstablishCourt", "AbolishCourt", "StripJurisdiction", "CutPay"},
                   target : Courts, exec : {FALSE}, remover : {"President"}, vesting : {"Head"}]}

\* Bills this run lets Congress pass (a bound for TLC; see the header).
InScope(op) ==
  op.name = "CreateAgency" =>
    op.exec \in ExecOptions /\ op.remover \in RemoverOptions /\ op.vesting \in VestingOptions

ASSUME BoundsWellFormed ==
  /\ Proposable \subseteq AmendIds /\ Standing \subseteq Labels
  /\ ExecOptions \subseteq BOOLEAN /\ RemoverOptions \subseteq Removers
  /\ VestingOptions \subseteq Vesters

\* The edges an enabling act creates. "exec" says whether the agency
\* exercises executive power.
AgencyEdges(a, x, r, v) ==
  { Law("Congress",  a, "Power",   "Enable"),
    Law("Executive", a, "Select",  "NominateHead"),
    Law("Congress",  a, "Select",  "ConsentHead"),
    Law("Congress",  a, "Control", "Appropriate"),
    Law("Congress",  a, "Control", "Impeach"),
    Law("Judiciary", a, "Control", "Review") }
  \cup (IF x THEN {Law("Executive", a, "Power",   "ExecutivePower"),
                   Law("Executive", a, "Control", "Direct")}
             ELSE {})
  \cup (CASE r = "President"         -> {Law("Executive", a, "Control", "Remove")}
          [] r = "PresidentForCause" -> {Law("Executive", a, "Control", "RemoveForCause")}
          [] r = "Congress"          -> {Law("Congress",  a, "Control", "Remove")})
  \cup (CASE v = "President" -> {Law("Executive", a, "Select", "AppointInferior")}
          [] v = "Courts"    -> {Law("Judiciary", a, "Select", "AppointInferior")}
          [] v = "Congress"  -> {Law("Congress",  a, "Select", "AppointInferior")}
          [] v = "Head"      -> {})

\* Art. III sec. 1: the court's judicial power is Art. III's, but it exists
\* only because Congress ordained it - two grant edges in.
CourtEdges(c) ==
  { Law("Congress",     c, "Power",   "Establish"),
    Law("Constitution", c, "Power",   "ArtIII"),
    Law("Executive",    c, "Select",  "Nominate"),
    Law("Congress",     c, "Select",  "Consent"),
    Law("Congress",     c, "Control", "Jurisdiction"),
    Law("Congress",     c, "Control", "Impeach"),
    Law("Judiciary",    c, "Control", "Appeal") }

\* The edges by which the head of n may be removed.
RemovalEdges(n) ==
  { Law("Executive", n, "Control", "Remove"),
    Law("Executive", n, "Control", "RemoveForCause"),
    Law("Congress",  n, "Control", "Remove") }

\* Labels of the statutory edges an enabling act or a later statute can draw.
StatutoryLabels ==
  {"Enable", "NominateHead", "ConsentHead", "Appropriate", "Impeach", "Review",
   "ExecutivePower", "Direct", "Remove", "RemoveForCause", "AppointInferior",
   "Establish", "ArtIII", "Nominate", "Consent", "Jurisdiction", "Appeal",
   "LegislativeVeto", "DiminishPay"}

-----------------------------------------------------------------------------
VARIABLES
  edges,       \* the authority graph: a set of edge records
  live,        \* agencies and inferior courts currently in existence
  seated,      \* offices currently filled
  nominated,   \* offices with a nomination before the Senate
  trial,       \* who the Senate is trying, or "None"
  bill,        \* the bill in flight: [stage, op]
  inSession,   \* is Congress sitting?
  amendment,   \* AmendIds -> {"None", "Proposed", "Ratified"}
  challenged,  \* statutory edges under challenge in court
  last,        \* the edge whose firing produced this state (NoEdge if none)
  stray,       \* how an act strayed from the graph: "OffGraph", "Vacant"
  breaches     \* provisions some act breached (each is a property below)

vars == <<edges, live, seated, nominated, trial, bill, inSession, amendment,
          challenged, last, stray, breaches>>

graphVars  == <<edges, live, challenged>>
officeVars == <<seated, nominated, trial>>
lawVars    == <<bill, inSession>>

NoBill == [stage |-> "None", op |-> NoOp]

Doctrines == {"Buckley", "SeilaLaw", "Bowsher", "Chadha", "Will"}
Breaches  == Doctrines \cup {"GoodBehaviour", "PocketVeto"}

TypeOK ==
  /\ edges \subseteq EdgeType
  /\ live \subseteq Agencies \cup Courts
  /\ seated \subseteq Offices
  /\ nominated \subseteq Agencies \cup Courts \cup {"VicePresident"}
  /\ trial \in Offices \cup {"Judiciary", "None"}
  /\ bill \in [stage : {"None", "Presented", "Vetoed"}, op : Ops \cup {NoOp}]
  /\ inSession \in BOOLEAN
  /\ amendment \in [AmendIds -> {"None", "Proposed", "Ratified"}]
  /\ challenged \subseteq edges
  /\ last \in EdgeType \cup {NoEdge}
  /\ stray \subseteq {"OffGraph", "Vacant"}
  /\ breaches \subseteq Breaches

-----------------------------------------------------------------------------
(* Graph helpers                                                           *)

LiveNodes == Fixed \cup live
GovNodes  == Branches \cup {"VicePresident"} \cup live

OfKind(E, K)     == {e \in E : e.kind \in K}
GrantEdges       == OfKind(edges, GrantKinds)
ControlEdges     == OfKind(edges, {"Control"})
Between(E, f, t) == {e \in E : e.from = f /\ e.to = t}
Among(E, N)      == {e \in E : e.from \in N /\ e.to \in N}
Touching(n)      == {e \in edges : e.from = n \/ e.to = n}
TextOf(E)        == {e \in E : e.basis = "Text"}
StatuteOf(E)     == {e \in E : e.basis = "Statute"}

\* Nodes reachable from n in one or more steps along E. A shortest path
\* from n passes through distinct targets of E, so as many rounds as E has
\* targets reach every node there is to reach. (A recursive function, not
\* a RECURSIVE operator: the prover refuses a module that has one.)
Reach(E, n) ==
  LET Succ(S) == {e.to : e \in {f \in E : f.from \in S}}
      grow[k \in Nat] == IF k = 0 THEN Succ({n})
                         ELSE LET p == grow[k - 1] IN p \cup Succ(p)
  IN  grow[Cardinality({e.to : e \in E})]

Acyclic(E) == \A e \in E : e.from # e.to /\ e.from \notin Reach(E, e.to)

\* The order the grant layer follows once the People and the States are
\* set aside.
Rank(n) ==
  CASE n = "Constitution"  -> 1
    [] n = "Congress"      -> 2
    [] n = "VicePresident" -> 3
    [] n = "Executive"     -> 4
    [] n = "Judiciary"     -> 5
    [] OTHER               -> 6      \* creatures of statute

\* An office acts only while someone holds it.
Active(n) == n \notin Offices \/ n \in seated

ExecPower(n) == Law("Executive", n, "Power", "ExecutivePower") \in edges

\* What each doctrine forbids a statutory edge to be.
Violates(d, e) ==
  CASE d = "Buckley"  -> e.label = "AppointInferior" /\ e.from = "Congress"
    [] d = "SeilaLaw" -> e.label = "RemoveForCause" /\ ExecPower(e.to)
    [] d = "Bowsher"  -> e.label = "Remove" /\ e.from = "Congress" /\ ExecPower(e.to)
    [] d = "Chadha"   -> e.label = "LegislativeVeto"
    [] d = "Will"     -> e.label = "DiminishPay"

Unconstitutional(e) == \E d \in Doctrines : Violates(d, e)

\* Which doctrines the courts apply. Each doctrinal mutation reverts one.
InForce(d) ==
  CASE d = "Buckley"  -> Mut # "M_PREBUCKLEY"
    [] d = "SeilaLaw" -> Mut # "M_HUMPHREY"
    [] d = "Bowsher"  -> Mut # "M_PREBOWSHER"
    [] d = "Chadha"   -> Mut # "M_PRECHADHA"
    [] d = "Will"     -> TRUE

\* Statutory edges a court will strike.
Forbidden(e) == \E d \in Doctrines : InForce(d) /\ Violates(d, e)

\* What a court leaves standing when it strikes e. Courts sever the
\* offending provision and keep the rest of the Act.
Sever(e) ==
  LET a == e.to IN
  IF Mut = "M_SEVER_PLAIN" THEN edges \ {e} ELSE
  CASE e.label = "RemoveForCause" ->
         \* Seila Law: strike the protection; the head serves at will.
         (edges \ {e}) \cup {Law("Executive", a, "Control", "Remove")}
    [] e.label = "Remove" /\ e.from = "Congress" ->
         \* Bowsher: Congress keeps its removal power; the officer loses
         \* the executive functions.
         edges \ {Law("Executive", a, "Power", "ExecutivePower"),
                  Law("Executive", a, "Control", "Direct")}
    [] OTHER -> edges \ {e}

\* Every statutory edge that might be forbidden. Fairness is attached to
\* these so that the liveness property has something to work with.
Challengeable ==
  UNION {{Law("Congress",  a, "Select",  "AppointInferior"),
          Law("Executive", a, "Control", "RemoveForCause"),
          Law("Congress",  a, "Control", "Remove"),
          Law("Congress",  a, "Control", "LegislativeVeto")} : a \in Agencies}
  \cup {Law("Congress", c, "Control", "DiminishPay") : c \in Courts}

-----------------------------------------------------------------------------
Init ==
  /\ edges = Founding
  /\ live = {}                    \* the text creates no agency and no inferior court
  /\ seated = {}
  /\ nominated = {}
  /\ trial = "None"
  /\ bill = NoBill
  /\ inSession = TRUE
  /\ amendment = [x \in AmendIds |-> "None"]
  /\ challenged = {}
  /\ last = NoEdge
  /\ stray = {}
  /\ breaches = {}

\* The one way anything happens: an edge in the graph, held by an active
\* node, fires. stray records an act that was neither (a mutation's).
OnGraph(e) == Mut = "M_OFFEDGE" \/ e \in edges
Held(e)    == Mut = "M_INACTIVE" \/ Active(e.from)
StrayOf(e) == (IF e \in edges THEN {} ELSE {"OffGraph"})
              \cup (IF Active(e.from) THEN {} ELSE {"Vacant"})

Fire(e) ==
  /\ OnGraph(e)
  /\ Held(e)
  /\ last' = e
  /\ stray' = stray \cup StrayOf(e)

SetEdges(new) ==
  /\ edges' = new
  /\ challenged' = challenged \cap new

-----------------------------------------------------------------------------
(* The flow of law: Art. I sec. 7                                          *)

\* The edge a bill draws its authority from.
AuthorityFor(op) ==
  CASE op.name = "StripJurisdiction" ->
         Txt("Congress", "Judiciary", "Control", "Exceptions")
    [] op.name \in {"EstablishCourt", "AbolishCourt", "CutPay"} ->
         Txt("Congress", "Judiciary", "Control", "Organize")
    [] OTHER ->
         Txt("Constitution", "Congress", "Power", "ArtI")   \* Necessary and Proper

\* What must be true for a bill to make sense: the body exists (or does
\* not yet), the edge it adds is not already there.
Precondition(op) ==
  LET t == op.target IN
  CASE op.name \in {"CreateAgency", "EstablishCourt"} -> t \notin live
    [] op.name \in {"AbolishAgency", "AbolishCourt"}  -> t \in live
    [] op.name = "LegislativeVeto" ->
         t \in live /\ Law("Congress", t, "Control", "LegislativeVeto") \notin edges
    [] op.name = "CutPay" ->
         t \in live /\ Law("Congress", t, "Control", "DiminishPay") \notin edges
    [] op.name = "StripJurisdiction" ->
         Law("Judiciary", t, "Control", "Appeal") \in edges

\* Checked at passage, and re-checked at enactment.
Applicable(op) == Mut = "M_APPLICABLE" \/ Precondition(op)
Rechecked(op)  == Mut = "M_RECHECK" \/ Applicable(op)

EdgesAfter(op) ==
  LET t == op.target IN
  CASE op.name = "CreateAgency" ->
         edges \cup AgencyEdges(t, op.exec, op.remover, op.vesting)
    [] op.name = "EstablishCourt"  -> edges \cup CourtEdges(t)
    [] op.name \in {"AbolishAgency", "AbolishCourt"} -> edges \ Touching(t)
    [] op.name = "LegislativeVeto" ->
         edges \cup {Law("Congress", t, "Control", "LegislativeVeto")}
    [] op.name = "CutPay" ->
         edges \cup {Law("Congress", t, "Control", "DiminishPay")}
    [] op.name = "StripJurisdiction" ->
         edges \ {Law("Judiciary", t, "Control", "Appeal")}   \* McCardle

LiveAfter(op) ==
  CASE op.name \in {"CreateAgency", "EstablishCourt"} -> live \cup {op.target}
    [] op.name \in {"AbolishAgency", "AbolishCourt"}  -> live \ {op.target}
    [] OTHER                                          -> live

\* Stuart v. Laird: abolishing an office unseats its holder.
Unseat(s, l) ==
  IF Mut = "M_NOSTUART" THEN s ELSE s \cap ({"Executive", "VicePresident"} \cup l)

\* A bill becomes law. Abolition also ends any pending nomination or trial.
Enact(op) ==
  /\ live' = LiveAfter(op)
  /\ SetEdges(EdgesAfter(op))
  /\ seated' = Unseat(seated, live')
  /\ nominated' = nominated \cap (live' \cup {"VicePresident"})
  /\ trial' = IF trial \in (Agencies \cup Courts) \ live' THEN "None" ELSE trial

\* Both houses pass a bill; it is presented to the President.
Pass(op) ==
  /\ InScope(op)
  /\ inSession
  /\ bill.stage = "None"
  /\ Applicable(op)
  /\ Fire(AuthorityFor(op))
  /\ bill' = [stage |-> "Presented", op |-> op]
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment, breaches>>

\* Signed: presentment completes. Applicability is re-checked at enactment,
\* not only at passage.
Sign ==
  /\ bill.stage = "Presented"
  /\ "Executive" \in seated
  /\ Rechecked(bill.op)
  /\ Fire(Txt("Congress", "Executive", "Control", "Presentment"))
  /\ Enact(bill.op)
  /\ bill' = NoBill
  /\ UNCHANGED <<inSession, amendment, breaches>>

\* Ten days (Sundays excepted), Congress sitting, not returned: law
\* without signature. An adjournment that prevents the return is a pocket
\* veto, so Congress must be sitting.
CanReturn == Mut = "M_NOPOCKET" \/ inSession

Lapse ==
  /\ bill.stage = "Presented"
  /\ CanReturn
  /\ Rechecked(bill.op)
  /\ Fire(Txt("Congress", "Executive", "Control", "Presentment"))
  /\ Enact(bill.op)
  /\ bill' = NoBill
  /\ breaches' = IF inSession THEN breaches ELSE breaches \cup {"PocketVeto"}
  /\ UNCHANGED <<inSession, amendment>>

\* Returned with objections - only to a Congress that can receive it.
Veto ==
  /\ bill.stage = "Presented"
  /\ inSession
  /\ Fire(Txt("Executive", "Congress", "Control", "Veto"))
  /\ bill' = [bill EXCEPT !.stage = "Vetoed"]
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment, breaches>>

\* Congress has adjourned and prevented the return.
PocketVeto ==
  /\ bill.stage = "Presented"
  /\ ~inSession
  /\ Fire(Txt("Executive", "Congress", "Control", "Veto"))
  /\ bill' = NoBill
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment, breaches>>

\* Two-thirds of each house.
Override ==
  /\ bill.stage = "Vetoed"
  /\ inSession
  /\ Rechecked(bill.op)
  /\ Fire(Txt("Congress", "Executive", "Control", "Override"))
  /\ Enact(bill.op)
  /\ bill' = NoBill
  /\ UNCHANGED <<inSession, amendment, breaches>>

\* A chamber votes it down, or an override fails.
BillFails ==
  /\ bill.stage # "None"
  /\ bill' = NoBill
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment, stray, breaches>>

-----------------------------------------------------------------------------
(* Sessions                                                                *)

\* Congress sits and adjourns under its own Article I power.
Adjourn ==
  /\ inSession
  /\ Fire(Txt("Constitution", "Congress", "Power", "ArtI"))
  /\ inSession' = FALSE
  /\ UNCHANGED <<graphVars, officeVars, bill, amendment, breaches>>

Convene ==
  /\ ~inSession
  /\ Fire(Txt("Constitution", "Congress", "Power", "ArtI"))
  /\ inSession' = TRUE
  /\ UNCHANGED <<graphVars, officeVars, bill, amendment, breaches>>

\* Art. II sec. 3, "on extraordinary Occasions".
ConveneByPresident ==
  /\ ~inSession
  /\ Fire(Txt("Executive", "Congress", "Control", "Convene"))
  /\ inSession' = TRUE
  /\ UNCHANGED <<graphVars, officeVars, bill, amendment, breaches>>

\* The President's power to adjourn Congress "in Case of Disagreement
\* between them" is an edge that no action fires: the model does not track
\* the houses disagreeing, and no President has ever used it.

-----------------------------------------------------------------------------
(* Offices                                                                 *)

\* The Electoral College, or - when it produces no majority - the House.
\* Which one applies is left to nondeterminism.
ElectPresident ==
  /\ "Executive" \notin seated
  /\ Fire(Txt("States", "Executive", "Select", "AppointElectors"))
  /\ seated' = seated \cup {"Executive"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, breaches>>

ContingentElection ==
  /\ "Executive" \notin seated
  /\ Fire(Txt("Congress", "Executive", "Select", "ContingentElection"))
  /\ seated' = seated \cup {"Executive"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, breaches>>

\* The electors choose a Vice President too; if none has a majority, the
\* Senate chooses (Amend. XII).
ElectVicePresident ==
  /\ "VicePresident" \notin seated
  /\ Fire(Txt("States", "VicePresident", "Select", "AppointElectors"))
  /\ seated' = seated \cup {"VicePresident"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, breaches>>

ContingentElectionVP ==
  /\ "VicePresident" \notin seated
  /\ Fire(Txt("Congress", "VicePresident", "Select", "ContingentElection"))
  /\ seated' = seated \cup {"VicePresident"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, breaches>>

\* Art. II sec. 1 cl. 6, Amend. XXV sec. 1: the presidency devolves on the
\* Vice President, whose own office falls vacant.
Succeed ==
  /\ "Executive" \notin seated
  /\ Fire(Txt("VicePresident", "Executive", "Select", "Succession"))
  /\ seated' = (seated \ {"VicePresident"}) \cup {"Executive"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, breaches>>

\* Amend. XXV sec. 2: the President nominates, a majority of both houses
\* confirms. Before XXV these edges do not exist and a vacancy stays open.
NominateVP ==
  /\ "VicePresident" \notin seated \cup nominated
  /\ Fire(Txt("Executive", "VicePresident", "Select", "NominateVP"))
  /\ nominated' = nominated \cup {"VicePresident"}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment, breaches>>

ConfirmVP ==
  /\ "VicePresident" \in nominated
  /\ "VicePresident" \notin seated               \* re-checked at confirmation
  /\ Fire(Txt("Congress", "VicePresident", "Select", "ConfirmVP"))
  /\ seated' = seated \cup {"VicePresident"}
  /\ nominated' = nominated \ {"VicePresident"}
  /\ UNCHANGED <<graphVars, trial, lawVars, amendment, breaches>>

RejectVP ==
  /\ "VicePresident" \in nominated
  /\ Fire(Txt("Congress", "VicePresident", "Select", "ConfirmVP"))
  /\ nominated' = nominated \ {"VicePresident"}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment, breaches>>

VicePresidentLeaves ==
  /\ "VicePresident" \in seated
  /\ seated' = seated \ {"VicePresident"}
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, stray, breaches>>

\* Death, resignation, end of term. Not an exercise of anyone's authority.
PresidentLeaves ==
  /\ "Executive" \in seated
  /\ seated' = seated \ {"Executive"}
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, stray, breaches>>

NominateLabel(n) == IF n \in Agencies THEN "NominateHead" ELSE "Nominate"
ConsentLabel(n)  == IF n \in Agencies THEN "ConsentHead"  ELSE "Consent"

\* Only an office Congress has created can be filled: the Select edges
\* into it exist only while the enabling act does.
Nominate(n) ==
  /\ n \in live
  /\ n \notin seated \cup nominated
  /\ Fire(Law("Executive", n, "Select", NominateLabel(n)))
  /\ nominated' = nominated \cup {n}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment, breaches>>

Consent(n) ==
  /\ n \in nominated
  /\ n \notin seated                        \* re-checked at confirmation
  /\ Fire(Law("Congress", n, "Select", ConsentLabel(n)))
  /\ seated' = seated \cup {n}
  /\ nominated' = nominated \ {n}
  /\ UNCHANGED <<graphVars, trial, lawVars, amendment, breaches>>

Reject(n) ==
  /\ n \in nominated
  /\ Fire(Law("Congress", n, "Select", ConsentLabel(n)))
  /\ nominated' = nominated \ {n}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment, breaches>>

\* Removal follows whichever edge the enabling act drew (and the courts
\* left standing). For-cause removal needs cause, which is abstracted.
\* Inferior courts have no removal edge at all: good behaviour. A removal
\* of a judge is recorded as a breach of it.
Remove(n) ==
  /\ n \in seated
  /\ \E e \in RemovalEdges(n) : Fire(e)
  /\ seated' = seated \ {n}
  /\ breaches' = IF n \in Courts THEN breaches \cup {"GoodBehaviour"} ELSE breaches
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

Resign(n) ==
  /\ n \in seated \ {"Executive"}
  /\ seated' = seated \ {n}
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment, stray, breaches>>

-----------------------------------------------------------------------------
(* Impeachment: the House impeaches, the Senate tries                      *)

ImpeachEdge(n) ==
  IF n \in {"Executive", "VicePresident", "Judiciary"}
    THEN Txt("Congress", n, "Control", "Impeach")
    ELSE Law("Congress", n, "Control", "Impeach")

Impeach(n) ==
  /\ trial = "None"
  /\ n \in seated \/ n = "Judiciary"
  /\ Fire(ImpeachEdge(n))
  /\ trial' = n
  /\ UNCHANGED <<graphVars, seated, nominated, lawVars, amendment, breaches>>

Convict ==
  /\ trial # "None"
  /\ Fire(ImpeachEdge(trial))
  /\ seated' = seated \ {trial}
  /\ trial' = "None"
  /\ UNCHANGED <<graphVars, nominated, lawVars, amendment, breaches>>

Acquit ==
  /\ trial # "None"
  /\ Fire(ImpeachEdge(trial))
  /\ trial' = "None"
  /\ UNCHANGED <<graphVars, seated, nominated, lawVars, amendment, breaches>>

-----------------------------------------------------------------------------
(* Courts: Art. III acts only on a case                                    *)

\* Someone affected by a statutory edge brings a case. (Standing is
\* abstracted: any statutory edge whose label is in Standing.)
Sue(e) ==
  /\ e \in edges
  /\ e.basis = "Statute"
  /\ e.label \in Standing
  /\ e \notin challenged
  /\ Fire(Txt("People", "Judiciary", "Control", "Sue"))
  /\ challenged' = challenged \cup {e}
  /\ UNCHANGED <<edges, live, officeVars, lawVars, amendment, breaches>>

\* The court rules. A forbidden edge is severed; anything else is upheld,
\* and an upheld edge a doctrine forbids is recorded as a breach of it.
\* Either way the review is the Judiciary acting on Congress's Act.
Strikes(e)    == Mut # "M_UPHOLD" /\ Forbidden(e)
Ruling(e)     == IF Strikes(e) THEN Sever(e) ELSE edges
ViolatedBy(e) == {d \in Doctrines : Violates(d, e)}

Review(e) ==
  /\ e \in challenged
  /\ Fire(Txt("Judiciary", "Congress", "Control", "Review"))
  /\ edges' = Ruling(e)
  /\ challenged' = (challenged \ {e}) \cap Ruling(e)
  /\ breaches' = IF Strikes(e) THEN breaches ELSE breaches \cup ViolatedBy(e)
  /\ UNCHANGED <<live, officeVars, lawVars, amendment>>

-----------------------------------------------------------------------------
(* Article V                                                               *)

\* By two-thirds of each house, or by a convention Congress must call on
\* the application of two-thirds of the States.
Propose(x) ==
  /\ x \in Proposable
  /\ amendment[x] = "None"
  /\ \/ Fire(Txt("Congress", "States", "Amend", "Propose"))
     \/ Fire(Txt("States", "Congress", "Control", "ApplyForConvention"))
  /\ amendment' = [amendment EXCEPT ![x] = "Proposed"]
  /\ UNCHANGED <<graphVars, officeVars, lawVars, breaches>>

\* Three-fourths of the States. The graph is rewritten.
Ratify(x) ==
  /\ amendment[x] = "Proposed"
  /\ Fire(Txt("States", "Constitution", "Amend", "Ratify"))
  /\ amendment' = [amendment EXCEPT ![x] = "Ratified"]
  /\ SetEdges((edges \ Drops(x)) \cup Adds(x))
  /\ UNCHANGED <<live, officeVars, lawVars, breaches>>

-----------------------------------------------------------------------------
(* Exercises of power whose effects other modules model                    *)

IsInert(e) ==
  \/ e.label \in {"Appropriate", "AdviseTreaties", "DeclareWar", "Pardon",
                  "Direct", "AppointInferior", "Jurisdiction", "Appeal",
                  "LegislativeVeto", "DiminishPay", "DecideInability",
                  "DeclareInability", "PresideTrial", "PresideSenate"}
  \/ e.label = "Review" /\ e.to # "Congress"
  \/ e.label \in {"Nominate", "Consent"} /\ e.to = "Judiciary"

\* Conditional edges whose condition is visible at this level.
Guard(e) ==
  /\ e.label = "PresideTrial" => trial = "Executive"     \* only the President's trial
  /\ e.label \in {"DecideInability", "DeclareInability"} => "Executive" \in seated
  /\ e.label = "PresideSenate" => inSession

Exercise(e) ==
  /\ IsInert(e)
  /\ Guard(e)
  /\ Fire(e)
  /\ UNCHANGED <<graphVars, officeVars, lawVars, amendment, breaches>>

-----------------------------------------------------------------------------
Next ==
  \/ \E op \in Ops : Pass(op)
  \/ Sign \/ Lapse \/ Veto \/ PocketVeto \/ Override \/ BillFails
  \/ Adjourn \/ Convene \/ ConveneByPresident
  \/ ElectPresident \/ ContingentElection \/ PresidentLeaves
  \/ ElectVicePresident \/ ContingentElectionVP \/ VicePresidentLeaves \/ Succeed
  \/ NominateVP \/ ConfirmVP \/ RejectVP
  \/ \E n \in Agencies \cup Courts :
       Nominate(n) \/ Consent(n) \/ Reject(n) \/ Remove(n) \/ Resign(n)
  \/ \E n \in Offices \cup {"Judiciary"} : Impeach(n)
  \/ Convict \/ Acquit
  \/ \E e \in edges : Sue(e) \/ Exercise(e)
  \/ \E e \in challenged : Review(e)
  \/ \E x \in AmendIds : Propose(x) \/ Ratify(x)

Spec == Init /\ [][Next]_vars

\* Fairness, each named for whose obligation it is. Both are weak: while a
\* challengeable edge stands unchallenged nothing but its suit or its
\* removal changes that, and while it is challenged nothing but its review
\* or its removal ends the case.
LitigantsSue == \A e \in Challengeable : WF_vars(Sue(e))      \* the People's
CourtsDecide == \A e \in Challengeable : WF_vars(Review(e))   \* the Judiciary's

FairSpec     == Spec /\ LitigantsSue /\ CourtsDecide
SpecNoSuit   == Spec /\ CourtsDecide     \* drops the litigants' obligation
SpecNoRuling == Spec /\ LitigantsSue     \* drops the courts' obligation

-----------------------------------------------------------------------------
(* Safety: the shape of the graph                                          *)

EdgesConnectLiveNodes ==
  \A e \in edges : e.from \in LiveNodes /\ e.to \in LiveNodes

OfficesAreLive ==
  /\ seated \subseteq {"Executive", "VicePresident"} \cup live
  /\ nominated \subseteq live \cup {"VicePresident"}

\* The text layer is the founding text as amended, and nothing else: the
\* state form of TextChangesOnlyByArticleV.
TextFollowsArticleV == TextOf(edges) = TextFor(amendment)

ArticleVStands == ArticleV \subseteq edges

\* Only the People and the States write the Constitution. Nothing in any
\* layer runs from a branch into it.
ConstitutionWrittenByPeopleAndStates ==
  \A e \in edges : e.to = "Constitution" => e.from \in {"People", "States"}

\* The text never oversteps itself; only statutes do.
OnlyStatutesOverstep ==
  \A e \in edges : Unconstitutional(e) => e.basis = "Statute"

\* The grant layer with the People and the States set aside.
InnerGrant == Among(GrantEdges, LiveNodes \ {"People", "States"})

\* As first written, these two claimed that the inner grant layer is
\* acyclic - every grant cycle closes through the People or the States -
\* and that it runs forward along one chain:
\*   Constitution -> Congress -> Vice President -> Executive -> Judiciary
\*     -> creatures of statute
\* Both held while the Vice President was folded into the Executive. With
\* the Vice President as a node, TLC refutes both in two steps: propose
\* XXV, ratify it. Section 2 lets the President nominate a Vice President,
\* who may succeed the President, so Executive -> VicePresident ->
\* Executive is a grant cycle that touches neither the People nor the
\* States (Ford, nominated 1973 and President 1974; Rockefeller,
\* nominated by Ford). They are kept, unchanged, as refuted claims: rows
\* that expect COUNTEREXAMPLE under Mut = "none" reproduce it.
GrantCyclesPassThroughPeopleOrStates == Acyclic(InnerGrant)

GrantFollowsChain == \A e \in InnerGrant : Rank(e.from) < Rank(e.to)

\* What does hold. Every grant edge but the President's nomination of a
\* Vice President runs forward along the chain (local) ...
GrantFollowsChainExceptXXV ==
  \A e \in InnerGrant : e.label # "NominateVP" => Rank(e.from) < Rank(e.to)

\* ... so with the Vice Presidency also set aside no grant edge descends,
\* and every grant cycle closes through the People, the States, or the
\* Vice Presidency (global, checked) ...
GrantCyclesPassThroughPeopleStatesOrVP ==
  Acyclic(Among(GrantEdges, LiveNodes \ {"People", "States", "VicePresident"}))

\* ... the one descending edge is in the graph exactly while XXV is, and
\* the edge back up is always there (local) ...
NominationLoopIffXXV ==
  /\ Txt("Executive", "VicePresident", "Select", "NominateVP") \in edges
       <=> amendment["XXV"] = "Ratified"
  /\ Txt("VicePresident", "Executive", "Select", "Succession") \in edges

\* ... so the President-Vice President loop is the only inner grant cycle
\* there is, present exactly when XXV is in force (global, checked).
OnlyGrantCycleIsXXV ==
  /\ ~Acyclic(InnerGrant) <=> amendment["XXV"] = "Ratified"
  /\ \A e \in InnerGrant :
       e.from \in Reach(InnerGrant, e.to) => {e.from, e.to} = {"Executive", "VicePresident"}

\* Every agency and inferior court exists because Congress enacted it.
EveryBodyIsCreatedByLaw ==
  \A n \in live : \E e \in Between(edges, "Congress", n) : e.kind = "Power"

\* A named path from the People to each part of the government: the House
\* election, then one edge from Congress (local).
FromCongress(n) ==
  CASE n = "Congress"      -> {}
    [] n = "Executive"     -> {Txt("Congress", "Executive", "Select", "ContingentElection")}
    [] n = "VicePresident" -> {Txt("Congress", "VicePresident", "Select", "ContingentElection")}
    [] n = "Judiciary"     -> {Txt("Congress", "Judiciary", "Select", "Consent")}
    [] n \in Agencies      -> {Law("Congress", n, "Power", "Enable")}
    [] OTHER               -> {Law("Congress", n, "Power", "Establish")}

NamedPathsFromPeople ==
  \A n \in GovNodes :
    {Txt("People", "Congress", "Select", "ElectHouse")} \cup FromCongress(n) \subseteq edges

\* Every branch, agency and court traces its authority back to the People
\* (global, checked).
PowerTracesToPeople ==
  \A n \in GovNodes : n \in Reach(GrantEdges, "People")

\* Every Power or Amend edge out of the People goes into the text (local).
PeoplePowerGoesThroughConstitution ==
  \A e \in edges : e.from = "People" /\ e.kind \in {"Power", "Amend"} => e.to = "Constitution"

\* Elections choose who holds power; only the Constitution confers it.
\* Remove the Constitution and no Power or Amend path from the People
\* reaches any part of the government (global, checked).
ConstitutionIsTheOnlyDoor ==
  \A n \in GovNodes :
    n \notin Reach(Among(OfKind(edges, {"Power", "Amend"}),
                            Nodes \ {"Constitution"}),
                   "People")

\* The control layer is complete among the branches ...
MutualChecks ==
  \A x, y \in Branches : x # y => Between(ControlEdges, x, y) # {}

\* ... and therefore cyclic (global, checked) ...
ControlLayerIsCyclic ==
  "Congress" \in Reach(Among(ControlEdges, Branches), "Congress")

\* ... and asymmetric: Congress has more control edges onto each branch
\* than that branch has onto Congress.
LegislativePrimacy ==
  \A x \in Branches \ {"Congress"} :
    Cardinality(Between(ControlEdges, "Congress", x))
      > Cardinality(Between(ControlEdges, x, "Congress"))

-----------------------------------------------------------------------------
(* Safety: doctrine, removal, acts                                         *)

BuckleyHonoured  == "Buckley" \notin breaches
SeilaLawHonoured == "SeilaLaw" \notin breaches
BowsherHonoured  == "Bowsher" \notin breaches
ChadhaHonoured   == "Chadha" \notin breaches
WillHonoured     == "Will" \notin breaches

\* An officer who executes the laws can always be removed by someone.
ExecutorsAreRemovable ==
  \A a \in Agencies : ExecPower(a) => RemovalEdges(a) \cap edges # {}

ActsFollowEdges  == "OffGraph" \notin stray
ActsByHolders    == "Vacant" \notin stray
EveryActIsAnEdge == ActsFollowEdges /\ ActsByHolders

GoodBehaviour      == "GoodBehaviour" \notin breaches
PocketVetoHonoured == "PocketVeto" \notin breaches

Safety ==
  /\ EdgesConnectLiveNodes /\ OfficesAreLive
  /\ TextFollowsArticleV /\ ArticleVStands
  /\ ConstitutionWrittenByPeopleAndStates /\ OnlyStatutesOverstep
  /\ GrantFollowsChainExceptXXV /\ GrantCyclesPassThroughPeopleStatesOrVP
  /\ NominationLoopIffXXV /\ OnlyGrantCycleIsXXV
  /\ EveryBodyIsCreatedByLaw /\ NamedPathsFromPeople /\ PowerTracesToPeople
  /\ PeoplePowerGoesThroughConstitution /\ ConstitutionIsTheOnlyDoor
  /\ MutualChecks /\ ControlLayerIsCyclic /\ LegislativePrimacy
  /\ BuckleyHonoured /\ SeilaLawHonoured /\ BowsherHonoured
  /\ ChadhaHonoured /\ WillHonoured /\ ExecutorsAreRemovable
  /\ EveryActIsAnEdge /\ GoodBehaviour /\ PocketVetoHonoured

-----------------------------------------------------------------------------
(* Action properties: how the graph may change                             *)

\* Text edges change only by ratification of an amendment.
TextChangesOnlyByArticleV ==
  [][TextOf(edges') # TextOf(edges) => last'.label = "Ratify"]_vars

\* Statutory edges change only by the flow of law - presentment or
\* override - or by a court striking them.
StatutesChangeOnlyByLawOrCourt ==
  [][StatuteOf(edges') # StatuteOf(edges) =>
       last'.label \in {"Presentment", "Override", "Review"}]_vars

-----------------------------------------------------------------------------
(* Liveness                                                                *)

\* Marbury, as a process: an unconstitutional statutory edge can exist,
\* but it does not last once someone sues. Unconstitutional is what the
\* doctrines forbid, whether or not the courts (under a mutation) apply
\* them.
UnconstitutionalEdgesAreStruck ==
  \A e \in Challengeable :
    (e \in edges /\ Unconstitutional(e)) ~> ~(e \in edges /\ Unconstitutional(e))

\* Violated by every behaviour: a fair spec has at least one.
NoBehaviour == <>FALSE

-----------------------------------------------------------------------------
(* Witnesses: each must be VIOLATED under Mut = "none"                     *)

NeverAgencyCreated    == live \cap Agencies = {}
NeverCourtEstablished == live \cap Courts = {}
NeverForbiddenEnacted == \A e \in edges : ~Unconstitutional(e)
NeverXVII             == amendment["XVII"] # "Ratified"
NeverXXV              == amendment["XXV"] # "Ratified"
NeverBillOnDeskInRecess == ~(bill.stage = "Presented" /\ ~inSession)

NeverAgencyAbolished ==
  [][\A a \in Agencies : a \in live => a \in live']_vars

NeverCourtAbolishedUnderAJudge ==
  [][~(\E c \in Courts : c \in seated /\ c \in live /\ c \notin live')]_vars

NeverVPByNomination ==
  [][~(last'.label = "ConfirmVP" /\ "VicePresident" \in seated' \ seated)]_vars

NeverInabilityContested == [][last'.label # "DecideInability"]_vars

\* A court reviews an edge doctrine d forbids and the graph changes: struck.
Struck(d) ==
  /\ last'.label = "Review" /\ edges' # edges
  /\ \E e \in challenged : Violates(d, e) /\ e \notin challenged'

NeverStruckBuckley  == [][~Struck("Buckley")]_vars
NeverStruckSeilaLaw == [][~Struck("SeilaLaw")]_vars
NeverStruckBowsher  == [][~Struck("Bowsher")]_vars
NeverStruckChadha   == [][~Struck("Chadha")]_vars
NeverStruckWill     == [][~Struck("Will")]_vars

-----------------------------------------------------------------------------
(* Bounds for TLC (named in rows/Government-rows.txt; never in a spec)     *)

\* `last` records which edge fired and no action reads it, so states that
\* differ only in `last` have the same successors. The rows check with this
\* VIEW, which identifies them; every property in the rows reads `last`, if
\* at all, only primed, in an action property checked on each transition.
Unrecorded == <<edges, live, seated, nominated, trial, bill, inSession, amendment,
                challenged, stray, breaches>>

\* The agency rows under a mutation explore no impeachment trial, no Vice
\* President and no nomination: the mutations they check act on statutes
\* and courts' rulings, and the office rows (no agency, no court, every
\* amendment) and the court rows explore those machines.
LawRowsBound == trial = "None" /\ "VicePresident" \notin seated /\ nominated = {}

=============================================================================
