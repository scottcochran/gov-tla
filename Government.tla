---------------------------- MODULE Government ----------------------------
(***************************************************************************)
(* The authority graph of the federal government.                          *)
(*                                                                         *)
(* Constitution.tla, Executive.tla and Judiciary.tla model what each       *)
(* branch does. This module models how authority runs between them, as a   *)
(* directed, labelled multigraph whose shape changes as the system runs.   *)
(*                                                                         *)
(* Nodes: the People, the States, the Constitution, the three branches,    *)
(* and the creatures of statute (agencies, inferior courts) that Congress  *)
(* brings into being and may abolish.                                      *)
(*                                                                         *)
(* Edges come in two layers.                                               *)
(*                                                                         *)
(*   GRANT - where authority comes from:                                   *)
(*     Power    confers power        (vesting clauses, enabling acts)      *)
(*     Select   fills an office      (elections, nomination, consent)      *)
(*     Amend    writes the text      (Art. V, Art. VII)                    *)
(*   CONTROL - how one holder acts on another's exercise of power          *)
(*     (veto, override, purse, impeachment, removal, review, pardon ...)   *)
(*                                                                         *)
(* Every exercise of authority below is the firing of one edge that is in  *)
(* the graph at that moment, under that edge's condition (death,           *)
(* resignation and failed votes fire nothing). Thresholds are abstracted;  *)
(* state conditions - a sitting Congress, a seated President, a pending    *)
(* case, a trial of the President - are real guards. Firing an edge may    *)
(* change the graph itself: statutes add and remove edges and nodes,       *)
(* amendments rewrite text edges, and courts strike statutory edges.       *)
(*                                                                         *)
(* What TLC is asked to confirm:                                           *)
(*                                                                         *)
(*   - The grant layer is partially linear. With the People and the States *)
(*     set aside it is acyclic, and every grant edge runs forward along    *)
(*         Constitution -> Congress -> Executive -> Judiciary -> statute   *)
(*     (GrantFollowsChain). Every grant cycle closes through the People    *)
(*     or the States, by election or by Article V.                         *)
(*   - The control layer is cyclic: every branch has an edge to each       *)
(*     other branch (MutualChecks), and it is asymmetric: Congress has     *)
(*     more edges onto each branch than that branch has onto Congress      *)
(*     (LegislativePrimacy).                                               *)
(*   - Only the People and the States write the Constitution, and no       *)
(*     power reaches a branch from the People except through it.           *)
(*   - Text edges change only by Article V; statutory edges change only by *)
(*     presentment, override, or judicial review.                          *)
(*   - An unconstitutional statutory edge may exist - nothing stops        *)
(*     Congress passing one - but once someone sues it is struck.          *)
(*                                                                         *)
(* Initial graph: the Constitution of 1789 with the Bill of Rights. Two    *)
(* later amendments that change the graph's shape are modelled: XVII       *)
(* (the Senate chosen by the People, not the States) and XXV (Congress     *)
(* confirms a VP and decides a contested inability).                       *)
(*                                                                         *)
(* The Vice President is a node of its own: chosen with the President,    *)
(* presiding over the Senate, succeeding to the presidency, and (since     *)
(* XXV) nominated by the President.                                        *)
(*                                                                         *)
(* Abstracted away: vote counts (see the other modules), persons, State    *)
(* governments' internal structure, the Youngstown framework, and standing *)
(* doctrine (any statutory edge may be challenged). Agencies' internal head-to-inferior delegation is not an   *)
(* edge, since it does not cross between bodies.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Agencies,       \* Pool of agency identifiers Congress may create
  Courts          \* Pool of inferior-court identifiers Congress may establish

ASSUME Agencies \cap Courts = {}

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

-----------------------------------------------------------------------------
(* Amendments that reshape the graph                                       *)

AmendIds == {"XVII", "XXV"}

Adds(x) ==
  CASE x = "XVII" -> {Txt("People", "Congress", "Select", "ElectSenate")}
    [] x = "XXV"  -> {Txt("Executive", "VicePresident", "Select", "NominateVP"),    \* sec. 2
                      Txt("Congress", "VicePresident", "Select", "ConfirmVP"),       \* sec. 2
                      Txt("VicePresident", "Executive", "Control", "DeclareInability"),
                                                                             \* sec. 4
                      Txt("Congress", "Executive", "Control", "DecideInability")}    \* sec. 4

Drops(x) ==
  CASE x = "XVII" -> {Txt("States", "Congress", "Select", "ElectSenate")}
    [] x = "XXV"  -> {}

\* Modelling assumptions about these amendments, not limits Article V
\* imposes: none lets a branch write the Constitution, and none repeals
\* Article V. (Drop the second conjunct, add an amendment giving Congress
\* an Amend edge into the Constitution, and TLC shows the invariants
\* below are facts about the current text rather than necessary truths.)
ASSUME \A x \in AmendIds :
  /\ \A e \in Adds(x) : e.basis = "Text" /\ e.from \in Fixed /\ e.to \in Fixed
  /\ \A e \in Adds(x) : e.to = "Constitution" => e.from \in {"People", "States"}
  /\ \A e \in Drops(x) : e.kind # "Amend"

-----------------------------------------------------------------------------
(* Statutes                                                                *)

\* How the head of an agency may be removed, and who appoints its inferior
\* officer. "Congress" is on both lists because Congress has tried both;
\* see Forbidden.
Removers == {"President", "PresidentForCause", "Congress"}
Vesters  == {"President", "Head", "Courts", "Congress"}

Op(n, t, x, r, v) == [name |-> n, target |-> t, exec |-> x, remover |-> r, vesting |-> v]
NoOp == Op("None", "None", FALSE, "President", "Head")

Ops ==
  {Op("CreateAgency", a, x, r, v) :
     a \in Agencies, x \in BOOLEAN, r \in Removers, v \in Vesters}
  \cup {Op(n, a, FALSE, "President", "Head") :
          n \in {"AbolishAgency", "LegislativeVeto"}, a \in Agencies}
  \cup {Op(n, c, FALSE, "President", "Head") :
          n \in {"EstablishCourt", "AbolishCourt", "StripJurisdiction", "CutPay"},
          c \in Courts}

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
  last         \* the edge whose firing produced this state (NoEdge if none)

vars == <<edges, live, seated, nominated, trial, bill, inSession, amendment,
          challenged, last>>

graphVars  == <<edges, live, challenged>>
officeVars == <<seated, nominated, trial>>
lawVars    == <<bill, inSession>>

NoBill == [stage |-> "None", op |-> NoOp]

TypeOK ==
  /\ \A e \in edges : e \in EdgeType
  /\ live \subseteq Agencies \cup Courts
  /\ seated \subseteq Offices
  /\ nominated \subseteq Agencies \cup Courts \cup {"VicePresident"}
  /\ trial \in Offices \cup {"Judiciary", "None"}
  /\ bill \in [stage : {"None", "Presented", "Vetoed"}, op : Ops \cup {NoOp}]
  /\ inSession \in BOOLEAN
  /\ amendment \in [AmendIds -> {"None", "Proposed", "Ratified"}]
  /\ challenged \subseteq edges
  /\ last \in EdgeType \cup {NoEdge}

-----------------------------------------------------------------------------
(* Graph helpers                                                           *)

LiveNodes == Fixed \cup live
GovNodes  == Branches \cup {"VicePresident"} \cup live

OfKind(E, K)     == {e \in E : e.kind \in K}
GrantEdges       == OfKind(edges, GrantKinds)
ControlEdges     == OfKind(edges, {"Control"})
Between(E, f, t) == {e \in E : e.from = f /\ e.to = t}
Restrict(E, N)   == {e \in E : e.from \in N /\ e.to \in N}
Touching(n)      == {e \in edges : e.from = n \/ e.to = n}
TextOf(E)        == {e \in E : e.basis = "Text"}
StatuteOf(E)     == {e \in E : e.basis = "Statute"}

\* Nodes reachable from n in one or more steps along E.
RECURSIVE Closure(_, _)
Closure(E, R) ==
  LET grown == R \cup {e.to : e \in {f \in E : f.from \in R}}
  IN  IF grown = R THEN R ELSE Closure(E, grown)

Reach(E, n) == Closure(E, {e.to : e \in {f \in E : f.from = n}})

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

\* Statutory edges the Constitution does not allow.
Forbidden(e) ==
  \/ e.label = "AppointInferior" /\ e.from = "Congress"               \* Buckley v. Valeo (1976)
  \/ e.label = "RemoveForCause" /\ ExecPower(e.to)                     \* Seila Law (2020), Trump v. Slaughter (2026)
  \/ e.label = "Remove" /\ e.from = "Congress" /\ ExecPower(e.to)      \* Bowsher v. Synar (1986)
  \/ e.label = "LegislativeVeto"                                       \* INS v. Chadha (1983)
  \/ e.label = "DiminishPay"                                           \* Compensation Clause; U.S. v. Will (1980)

\* What a court leaves standing when it strikes e. Courts sever the
\* offending provision and keep the rest of the Act.
Sever(e) ==
  LET a == e.to IN
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

\* The one way anything happens: an edge in the graph, held by an active
\* node, fires.
Fire(e) ==
  /\ e \in edges
  /\ Active(e.from)
  /\ last' = e

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

Applicable(op) ==
  LET t == op.target IN
  CASE op.name \in {"CreateAgency", "EstablishCourt"} -> t \notin live
    [] op.name \in {"AbolishAgency", "AbolishCourt"}  -> t \in live
    [] op.name = "LegislativeVeto" ->
         t \in live /\ Law("Congress", t, "Control", "LegislativeVeto") \notin edges
    [] op.name = "CutPay" ->
         t \in live /\ Law("Congress", t, "Control", "DiminishPay") \notin edges
    [] op.name = "StripJurisdiction" ->
         Law("Judiciary", t, "Control", "Appeal") \in edges

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

\* A bill becomes law. Abolishing an office unseats its holder (Stuart v.
\* Laird) and ends any pending nomination or trial.
Enact(op) ==
  /\ live' = LiveAfter(op)
  /\ SetEdges(EdgesAfter(op))
  /\ seated' = seated \cap ({"Executive", "VicePresident"} \cup live')
  /\ nominated' = nominated \cap (live' \cup {"VicePresident"})
  /\ trial' = IF trial \in (Agencies \cup Courts) \ live' THEN "None" ELSE trial

\* Both houses pass a bill; it is presented to the President.
Pass(op) ==
  /\ inSession
  /\ bill.stage = "None"
  /\ Applicable(op)
  /\ Fire(AuthorityFor(op))
  /\ bill' = [stage |-> "Presented", op |-> op]
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment>>

\* Signed: presentment completes. Applicability is re-checked at enactment,
\* not only at passage.
Sign ==
  /\ bill.stage = "Presented"
  /\ "Executive" \in seated
  /\ Applicable(bill.op)
  /\ Fire(Txt("Congress", "Executive", "Control", "Presentment"))
  /\ Enact(bill.op)
  /\ bill' = NoBill
  /\ UNCHANGED <<inSession, amendment>>

\* Ten days (Sundays excepted), Congress sitting, not returned: law
\* without signature.
Lapse ==
  /\ bill.stage = "Presented"
  /\ inSession
  /\ Applicable(bill.op)
  /\ Fire(Txt("Congress", "Executive", "Control", "Presentment"))
  /\ Enact(bill.op)
  /\ bill' = NoBill
  /\ UNCHANGED <<inSession, amendment>>

\* Returned with objections - only to a Congress that can receive it.
Veto ==
  /\ bill.stage = "Presented"
  /\ inSession
  /\ Fire(Txt("Executive", "Congress", "Control", "Veto"))
  /\ bill' = [bill EXCEPT !.stage = "Vetoed"]
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment>>

\* Congress has adjourned and prevented the return.
PocketVeto ==
  /\ bill.stage = "Presented"
  /\ ~inSession
  /\ Fire(Txt("Executive", "Congress", "Control", "Veto"))
  /\ bill' = NoBill
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment>>

\* Two-thirds of each house.
Override ==
  /\ bill.stage = "Vetoed"
  /\ inSession
  /\ Applicable(bill.op)
  /\ Fire(Txt("Congress", "Executive", "Control", "Override"))
  /\ Enact(bill.op)
  /\ bill' = NoBill
  /\ UNCHANGED <<inSession, amendment>>

\* A chamber votes it down, or an override fails.
BillFails ==
  /\ bill.stage # "None"
  /\ bill' = NoBill
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, officeVars, inSession, amendment>>

-----------------------------------------------------------------------------
(* Sessions                                                                *)

\* Congress sits and adjourns under its own Article I power.
Adjourn ==
  /\ inSession
  /\ Fire(Txt("Constitution", "Congress", "Power", "ArtI"))
  /\ inSession' = FALSE
  /\ UNCHANGED <<graphVars, officeVars, bill, amendment>>

Convene ==
  /\ ~inSession
  /\ Fire(Txt("Constitution", "Congress", "Power", "ArtI"))
  /\ inSession' = TRUE
  /\ UNCHANGED <<graphVars, officeVars, bill, amendment>>

\* Art. II sec. 3, "on extraordinary Occasions".
ConveneByPresident ==
  /\ ~inSession
  /\ Fire(Txt("Executive", "Congress", "Control", "Convene"))
  /\ inSession' = TRUE
  /\ UNCHANGED <<graphVars, officeVars, bill, amendment>>

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
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

ContingentElection ==
  /\ "Executive" \notin seated
  /\ Fire(Txt("Congress", "Executive", "Select", "ContingentElection"))
  /\ seated' = seated \cup {"Executive"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

\* The electors choose a Vice President too; if none has a majority, the
\* Senate chooses (Amend. XII).
ElectVicePresident ==
  /\ "VicePresident" \notin seated
  /\ Fire(Txt("States", "VicePresident", "Select", "AppointElectors"))
  /\ seated' = seated \cup {"VicePresident"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

ContingentElectionVP ==
  /\ "VicePresident" \notin seated
  /\ Fire(Txt("Congress", "VicePresident", "Select", "ContingentElection"))
  /\ seated' = seated \cup {"VicePresident"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

\* Art. II sec. 1 cl. 6, Amend. XXV sec. 1: the presidency devolves on the
\* Vice President, whose own office falls vacant.
Succeed ==
  /\ "Executive" \notin seated
  /\ Fire(Txt("VicePresident", "Executive", "Select", "Succession"))
  /\ seated' = (seated \ {"VicePresident"}) \cup {"Executive"}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

\* Amend. XXV sec. 2: the President nominates, a majority of both houses
\* confirms. Before XXV these edges do not exist and a vacancy stays open.
NominateVP ==
  /\ "VicePresident" \notin seated \cup nominated
  /\ Fire(Txt("Executive", "VicePresident", "Select", "NominateVP"))
  /\ nominated' = nominated \cup {"VicePresident"}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment>>

ConfirmVP ==
  /\ "VicePresident" \in nominated
  /\ "VicePresident" \notin seated               \* re-checked at confirmation
  /\ Fire(Txt("Congress", "VicePresident", "Select", "ConfirmVP"))
  /\ seated' = seated \cup {"VicePresident"}
  /\ nominated' = nominated \ {"VicePresident"}
  /\ UNCHANGED <<graphVars, trial, lawVars, amendment>>

RejectVP ==
  /\ "VicePresident" \in nominated
  /\ Fire(Txt("Congress", "VicePresident", "Select", "ConfirmVP"))
  /\ nominated' = nominated \ {"VicePresident"}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment>>

VicePresidentLeaves ==
  /\ "VicePresident" \in seated
  /\ seated' = seated \ {"VicePresident"}
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

\* Death, resignation, end of term. Not an exercise of anyone's authority.
PresidentLeaves ==
  /\ "Executive" \in seated
  /\ seated' = seated \ {"Executive"}
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

NominateLabel(n) == IF n \in Agencies THEN "NominateHead" ELSE "Nominate"
ConsentLabel(n)  == IF n \in Agencies THEN "ConsentHead"  ELSE "Consent"

\* Only an office Congress has created can be filled: the Select edges
\* into it exist only while the enabling act does.
Nominate(n) ==
  /\ n \in live
  /\ n \notin seated \cup nominated
  /\ Fire(Law("Executive", n, "Select", NominateLabel(n)))
  /\ nominated' = nominated \cup {n}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment>>

Consent(n) ==
  /\ n \in nominated
  /\ n \notin seated                        \* re-checked at confirmation
  /\ Fire(Law("Congress", n, "Select", ConsentLabel(n)))
  /\ seated' = seated \cup {n}
  /\ nominated' = nominated \ {n}
  /\ UNCHANGED <<graphVars, trial, lawVars, amendment>>

Reject(n) ==
  /\ n \in nominated
  /\ Fire(Law("Congress", n, "Select", ConsentLabel(n)))
  /\ nominated' = nominated \ {n}
  /\ UNCHANGED <<graphVars, seated, trial, lawVars, amendment>>

\* Removal follows whichever edge the enabling act drew (and the courts
\* left standing). For-cause removal needs cause, which is abstracted.
\* Inferior courts have no removal edge at all: good behaviour.
Remove(n) ==
  /\ n \in seated
  /\ \E e \in {Law("Executive", n, "Control", "Remove"),
               Law("Executive", n, "Control", "RemoveForCause"),
               Law("Congress",  n, "Control", "Remove")} : Fire(e)
  /\ seated' = seated \ {n}
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

Resign(n) ==
  /\ n \in seated \ {"Executive"}
  /\ seated' = seated \ {n}
  /\ last' = NoEdge
  /\ UNCHANGED <<graphVars, nominated, trial, lawVars, amendment>>

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
  /\ UNCHANGED <<graphVars, seated, nominated, lawVars, amendment>>

Convict ==
  /\ trial # "None"
  /\ Fire(ImpeachEdge(trial))
  /\ seated' = seated \ {trial}
  /\ trial' = "None"
  /\ UNCHANGED <<graphVars, nominated, lawVars, amendment>>

Acquit ==
  /\ trial # "None"
  /\ Fire(ImpeachEdge(trial))
  /\ trial' = "None"
  /\ UNCHANGED <<graphVars, seated, nominated, lawVars, amendment>>

-----------------------------------------------------------------------------
(* Courts: Art. III acts only on a case                                    *)

\* Someone affected by a statutory edge brings a case. (Standing is
\* abstracted: any statutory edge can be challenged.)
Sue(e) ==
  /\ e \in edges
  /\ e.basis = "Statute"
  /\ e \notin challenged
  /\ Fire(Txt("People", "Judiciary", "Control", "Sue"))
  /\ challenged' = challenged \cup {e}
  /\ UNCHANGED <<edges, live, officeVars, lawVars, amendment>>

\* The court rules. A forbidden edge is severed; anything else is upheld.
\* Either way the review is the Judiciary acting on Congress's Act.
Review(e) ==
  /\ e \in challenged
  /\ Fire(Txt("Judiciary", "Congress", "Control", "Review"))
  /\ LET new == IF Forbidden(e) THEN Sever(e) ELSE edges
     IN  /\ edges' = new
         /\ challenged' = (challenged \ {e}) \cap new
  /\ UNCHANGED <<live, officeVars, lawVars, amendment>>

-----------------------------------------------------------------------------
(* Article V                                                               *)

\* By two-thirds of each house, or by a convention Congress must call on
\* the application of two-thirds of the States.
Propose(x) ==
  /\ amendment[x] = "None"
  /\ \/ Fire(Txt("Congress", "States", "Amend", "Propose"))
     \/ Fire(Txt("States", "Congress", "Control", "ApplyForConvention"))
  /\ amendment' = [amendment EXCEPT ![x] = "Proposed"]
  /\ UNCHANGED <<graphVars, officeVars, lawVars>>

\* Three-fourths of the States. The graph is rewritten.
Ratify(x) ==
  /\ amendment[x] = "Proposed"
  /\ Fire(Txt("States", "Constitution", "Amend", "Ratify"))
  /\ amendment' = [amendment EXCEPT ![x] = "Ratified"]
  /\ SetEdges((edges \ Drops(x)) \cup Adds(x))
  /\ UNCHANGED <<live, officeVars, lawVars>>

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
  /\ UNCHANGED <<graphVars, officeVars, lawVars, amendment>>

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

\* Fairness: someone eventually sues over a challengeable edge, and a
\* court eventually rules on a pending case.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A e \in Challengeable : WF_vars(Sue(e)) /\ WF_vars(Review(e))

-----------------------------------------------------------------------------
(* Safety: the shape of the graph                                          *)

EdgesConnectLiveNodes ==
  \A e \in edges : e.from \in LiveNodes /\ e.to \in LiveNodes

OfficesAreLive ==
  /\ seated \subseteq {"Executive", "VicePresident"} \cup live
  /\ nominated \subseteq live \cup {"VicePresident"}

\* Only the People and the States write the Constitution. Nothing in any
\* layer runs from a branch into it.
ConstitutionWrittenByPeopleAndStates ==
  \A e \in edges : e.to = "Constitution" => e.from \in {"People", "States"}

\* The grant layer with the People and the States set aside.
InnerGrant == Restrict(GrantEdges, LiveNodes \ {"People", "States"})

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
\* nominated by Ford). They are kept, unchanged, as refuted claims:
\* Government_strict.cfg checks them and reproduces the counterexample.
GrantCyclesPassThroughPeopleOrStates == Acyclic(InnerGrant)

GrantFollowsChain == \A e \in InnerGrant : Rank(e.from) < Rank(e.to)

\* What does hold. Every grant cycle closes through the People, the
\* States, or the Vice Presidency ...
GrantCyclesPassThroughPeopleStatesOrVP ==
  Acyclic(Restrict(GrantEdges, LiveNodes \ {"People", "States", "VicePresident"}))

\* ... every grant edge but the President's nomination of a Vice President
\* runs forward along the chain ...
GrantFollowsChainExceptXXV ==
  \A e \in InnerGrant : e.label # "NominateVP" => Rank(e.from) < Rank(e.to)

\* ... and the President-Vice President loop is the only inner grant
\* cycle there is, present exactly when XXV is in force.
OnlyGrantCycleIsXXV ==
  /\ ~Acyclic(InnerGrant) <=> amendment["XXV"] = "Ratified"
  /\ \A e \in InnerGrant :
       e.from \in Reach(InnerGrant, e.to) => {e.from, e.to} = {"Executive", "VicePresident"}

\* Every branch, agency and court traces its authority back to the People.
PowerTracesToPeople ==
  \A n \in GovNodes : n \in Reach(GrantEdges, "People")

\* Elections choose who holds power; only the Constitution confers it.
\* Remove the Constitution and no Power or Amend path from the People
\* reaches any part of the government.
ConstitutionIsTheOnlyDoor ==
  \A n \in GovNodes :
    n \notin Reach(Restrict(OfKind(edges, {"Power", "Amend"}),
                            Nodes \ {"Constitution"}),
                   "People")

\* Every agency and inferior court exists because Congress enacted it.
EveryBodyIsCreatedByLaw ==
  \A n \in live : \E e \in Between(edges, "Congress", n) : e.kind = "Power"

\* The control layer is complete among the branches, and therefore cyclic.
MutualChecks ==
  \A x, y \in Branches : x # y => Between(ControlEdges, x, y) # {}

ControlLayerIsCyclic ==
  "Congress" \in Reach(Restrict(ControlEdges, Branches), "Congress")

\* ... and asymmetric: Congress has more control edges onto each branch
\* than that branch has onto Congress.
LegislativePrimacy ==
  \A x \in Branches \ {"Congress"} :
    Cardinality(Between(ControlEdges, "Congress", x))
      > Cardinality(Between(ControlEdges, x, "Congress"))

\* The text never oversteps itself; only statutes do.
OnlyStatutesOverstep ==
  \A e \in edges : Forbidden(e) => e.basis = "Statute"

Safety ==
  /\ EdgesConnectLiveNodes /\ OfficesAreLive
  /\ ConstitutionWrittenByPeopleAndStates
  /\ GrantCyclesPassThroughPeopleStatesOrVP /\ GrantFollowsChainExceptXXV
  /\ OnlyGrantCycleIsXXV
  /\ PowerTracesToPeople /\ ConstitutionIsTheOnlyDoor
  /\ EveryBodyIsCreatedByLaw
  /\ MutualChecks /\ ControlLayerIsCyclic /\ LegislativePrimacy
  /\ OnlyStatutesOverstep

-----------------------------------------------------------------------------
(* Action properties: how the graph may change                             *)

\* Every exercise of authority is the firing of an edge that was in the
\* graph, by a node that was active.
EveryActIsAnEdge ==
  [][last' # NoEdge => (last' \in edges /\ Active(last'.from))]_vars

\* Text edges change only by ratification of an amendment.
TextChangesOnlyByArticleV ==
  [][TextOf(edges') # TextOf(edges) => last'.label = "Ratify"]_vars

\* Statutory edges change only by the flow of law - presentment or
\* override - or by a court striking them.
StatutesChangeOnlyByLawOrCourt ==
  [][StatuteOf(edges') # StatuteOf(edges) =>
       last'.label \in {"Presentment", "Override", "Review"}]_vars

\* Art. III sec. 1: an inferior-court judge leaves only by resignation,
\* conviction on impeachment, or abolition of the court by statute.
GoodBehaviour ==
  [][\A c \in Courts :
       (c \in seated /\ c \notin seated') =>
         \/ Resign(c)
         \/ last'.label \in {"Impeach", "Presentment", "Override"}]_vars

-----------------------------------------------------------------------------
(* Liveness                                                                *)

\* Marbury, as a process: an unconstitutional statutory edge can exist,
\* but it does not last once someone sues.
UnconstitutionalEdgesAreStruck ==
  \A e \in Challengeable :
    (e \in edges /\ Forbidden(e)) ~> ~(e \in edges /\ Forbidden(e))

=============================================================================
