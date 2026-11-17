--------------------------- MODULE Government_proof ---------------------------
(***************************************************************************)
(* Proofs of the local safety properties of Government.tla, as             *)
(* Spec => []P, for every value of the constants the module's named        *)
(* assumptions admit (PoolsDisjoint, PoolsAreNew, MutIsKnown,              *)
(* BoundsWellFormed, AmendmentsRewriteText). Government.tla is cited by    *)
(* digest in the results file and not edited here. Each theorem assumes    *)
(* only that the mutations which break its property are absent; the TLC    *)
(* rows (results/Government-results-*.txt) show each of those mutations    *)
(* reaching a violation and every other mutation leaving the property      *)
(* intact.                                                                 *)
(*                                                                         *)
(* THEOREMS [hypothesis]                                                   *)
(*   TypeOKAlways, TextFollowsArticleVAlways             [none]            *)
(*   EdgesConnectLiveNodesAlways                         [Mut # M_APPLICABLE] *)
(*   OfficesAreLiveAlways                                [Mut # M_NOSTUART] *)
(*   ArticleVStandsAlways                                [Mut # M_NO_ARTV] *)
(*   ConstitutionWrittenAlways, GrantFollowsChainExceptXXVAlways           *)
(*                                                 [Mut # M_CONGRESS_AMENDS] *)
(*   OnlyStatutesOverstepAlways, NominationLoopIffXXVAlways,               *)
(*   EveryBodyIsCreatedByLawAlways, NamedPathsFromPeopleAlways,            *)
(*   PeoplePowerGoesThroughConstitutionAlways, MutualChecksAlways,         *)
(*   LegislativePrimacyAlways                            [none]            *)
(*   ExecutorsAreRemovableAlways                         [Mut # M_SEVER_PLAIN] *)
(*   BuckleyHonouredAlways   [Mut # M_UPHOLD, Mut # M_PREBUCKLEY]          *)
(*   SeilaLawHonouredAlways  [Mut # M_UPHOLD, Mut # M_HUMPHREY]            *)
(*   BowsherHonouredAlways   [Mut # M_UPHOLD, Mut # M_PREBOWSHER]          *)
(*   ChadhaHonouredAlways    [Mut # M_UPHOLD, Mut # M_PRECHADHA]           *)
(*   WillHonouredAlways      [Mut # M_UPHOLD]                              *)
(*   ActsFollowEdgesAlways, GoodBehaviourAlways          [Mut # M_OFFEDGE] *)
(*   ActsByHoldersAlways                                 [Mut # M_INACTIVE] *)
(*   PocketVetoHonouredAlways                            [Mut # M_NOPOCKET] *)
(*   TextChangesOnlyByArticleVHolds, StatutesChangeOnlyByLawOrCourtHolds   *)
(*     (the action properties, Spec => [][A]_vars)       [none]            *)
(*   SafeAlways  [Mut = "none"]: Spec => []LocalSafety, every one of the   *)
(*     above at once.                                                      *)
(* No theorem assumes Mut # "M_RECHECK": every property holds without the  *)
(* re-check at enactment, which TLC confirms reaches no new state.         *)
(*                                                                         *)
(* THE INDUCTIVE STRENGTHENING. One invariant, Shape, holds under every    *)
(* mutation: the type invariant; a bill in flight is a real bill; the text *)
(* layer is the founding text less what the ratified amendments drop plus  *)
(* what they add (TextFollowsArticleV, the "recorded value agrees with the *)
(* derived truth" pattern: Ratify rewrites the text and the amendment      *)
(* record in one step, every other action leaves both alone); every        *)
(* statutory edge runs from the text or a branch into an agency or court,  *)
(* and a removal edge only into an agency; only statutory edges are        *)
(* challenged; every live body has the edge by which Congress created it.  *)
(* Most properties then follow in one state step, from Shape and a fact    *)
(* about the text (a per-edge fact about the founding edges and each       *)
(* amendment's edges, which is where M_CONGRESS_AMENDS and M_NO_ARTV       *)
(* enter). On top of Shape, under its own hypothesis: StatutesToLive with  *)
(* BillApplies (a statutory edge runs into a live body, and a bill in      *)
(* flight still makes sense - which is why M_RECHECK is harmless) for      *)
(* EdgesConnectLiveNodes; OfficesAreLive itself; ExecutorsAreRemovable     *)
(* itself; and FlagInv, whose conjuncts each say a flag stays down while   *)
(* its guard is in force, for the doctrine, act and breach properties.     *)
(*                                                                         *)
(* NOT PROVED, and why. The global reachability claims -                   *)
(* GrantCyclesPassThroughPeopleStatesOrVP, OnlyGrantCycleIsXXV,            *)
(* PowerTracesToPeople, ConstitutionIsTheOnlyDoor, ControlLayerIsCyclic -  *)
(* are stated over Reach, a recursive function of an iteration count; the  *)
(* prover has no theory of that fixpoint here, so they are checked by TLC  *)
(* at the rows' constants, not proved. Each follows from proved local      *)
(* forms: no inner grant edge but NominateVP descends the rank             *)
(* (GrantFollowsChainExceptXXV), so none outside the VP lies on a cycle;   *)
(* NominateVP is present exactly under XXV and Succession always           *)
(* (NominationLoopIffXXV), which closes the one loop; People -> Congress   *)
(* -> each body by named edges (NamedPathsFromPeople); every Power or      *)
(* Amend edge out of the People enters the text                            *)
(* (PeoplePowerGoesThroughConstitution); every pair of branches has a      *)
(* control edge each way (MutualChecks). The refuted claims are refuted by *)
(* TLC and not stated here. Liveness (UnconstitutionalEdgesAreStruck) is   *)
(* checked by TLC under FairSpec and not proved: it is quantified over the *)
(* challengeable edges with an ENABLED premise per edge, the shape the     *)
(* prover's temporal backend cannot combine from instances.                *)
(*                                                                         *)
(* Check: tools/tlapm --cleanfp --strict --cache-dir <tmp> Government_proof.tla *)
(***************************************************************************)
EXTENDS Government, FiniteSetTheorems, TLAPS

-----------------------------------------------------------------------------
(* Definitions the proof uses                                              *)

ForbiddenLabels == {"AppointInferior", "RemoveForCause", "Remove", "LegislativeVeto",
                    "DiminishPay"}
Upper == {"Constitution", "Congress", "Executive", "Judiciary"}

\* What every text edge is, under every mutation ...
TextFacts(e) ==
  /\ e.basis = "Text" /\ e.from \in Fixed /\ e.to \in Fixed
  /\ e.kind \in Kinds /\ e.label \notin ForbiddenLabels
  /\ (e.from = "People" /\ e.kind \in {"Power", "Amend"}) => e.to = "Constitution"

\* ... and what every text edge but the one M_CONGRESS_AMENDS adds is.
WriterFacts(e) ==
  /\ e.to = "Constitution" => e.from \in {"People", "States"}
  /\ (/\ e.kind \in GrantKinds /\ e.label # "NominateVP"
      /\ e.from \notin {"People", "States"} /\ e.to \notin {"People", "States"})
       => Rank(e.from) < Rank(e.to)

\* Record sets for text and statutory edges.
TextRec(L) == [from : Fixed, to : Fixed, kind : Kinds, label : L, basis : {"Text"}]
StatRec    == [from : Upper, to : Agencies \cup Courts, kind : Kinds,
               label : StatutoryLabels, basis : {"Statute"}]

\* The founding text in three parts (the backends handle a dozen records
\* at a time far better than three dozen).
FoundingPart1 ==
  { Txt("People",   "Constitution", "Amend",   "Ordain"),
    Txt("States",   "Constitution", "Amend",   "Ratify"),
    Txt("Congress", "States",       "Amend",   "Propose"),
    Txt("States",   "Congress",     "Control", "ApplyForConvention"),
    Txt("Constitution", "Congress",  "Power", "ArtI"),
    Txt("Constitution", "Executive", "Power", "ArtII"),
    Txt("Constitution", "Judiciary", "Power", "ArtIII"),
    Txt("People",    "Congress",  "Select", "ElectHouse"),
    Txt("States",    "Congress",  "Select", "ElectSenate"),
    Txt("States",    "Executive", "Select", "AppointElectors"),
    Txt("Congress",  "Executive", "Select", "ContingentElection"),
    Txt("Executive", "Judiciary", "Select", "Nominate") }
FoundingPart2 ==
  { Txt("Congress",  "Judiciary", "Select", "Consent"),
    Txt("Congress", "Executive", "Control", "Presentment"),
    Txt("Congress", "Executive", "Control", "Override"),
    Txt("Congress", "Executive", "Control", "Appropriate"),
    Txt("Congress", "Executive", "Control", "Impeach"),
    Txt("Congress", "Executive", "Control", "AdviseTreaties"),
    Txt("Congress", "Executive", "Control", "DeclareWar"),
    Txt("Executive", "Congress", "Control", "Veto"),
    Txt("Executive", "Congress", "Control", "Convene"),
    Txt("Executive", "Congress", "Control", "Adjourn"),
    Txt("Congress", "Judiciary", "Control", "Impeach"),
    Txt("Congress", "Judiciary", "Control", "Exceptions") }
FoundingPart3 ==
  { Txt("Congress", "Judiciary", "Control", "Organize"),
    Txt("Judiciary", "Congress",  "Control", "Review"),
    Txt("Judiciary", "Executive", "Control", "Review"),
    Txt("Judiciary", "Congress",  "Control", "PresideTrial"),
    Txt("Executive", "Judiciary", "Control", "Pardon"),
    Txt("People", "Judiciary", "Control", "Sue"),
    Txt("Constitution",  "VicePresident", "Power",   "ArtI"),
    Txt("States",        "VicePresident", "Select",  "AppointElectors"),
    Txt("Congress",      "VicePresident", "Select",  "ContingentElection"),
    Txt("VicePresident", "Executive",     "Select",  "Succession"),
    Txt("VicePresident", "Congress",      "Control", "PresideSenate"),
    Txt("Congress",      "VicePresident", "Control", "Impeach") }

\* The labels each part uses, and those the amendments use.
LabelsPart1 == {"Ordain", "Ratify", "Propose", "ApplyForConvention", "ArtI", "ArtII",
                "ArtIII", "ElectHouse", "ElectSenate", "AppointElectors",
                "ContingentElection", "Nominate"}
LabelsPart2 == {"Consent", "Presentment", "Override", "Appropriate", "Impeach",
                "AdviseTreaties", "DeclareWar", "Veto", "Convene", "Adjourn", "Exceptions"}
LabelsPart3 == {"Organize", "Review", "PresideTrial", "Pardon", "Sue", "ArtI",
                "AppointElectors", "ContingentElection", "Succession", "PresideSenate",
                "Impeach"}
LabelsAdds  == {"ElectSenate", "NominateVP", "ConfirmVP", "DeclareInability",
                "DecideInability", "Ratify"}

-----------------------------------------------------------------------------
(* Facts about the constants                                               *)

LEMMA LabelParts ==
  /\ LabelsPart1 \subseteq Labels /\ LabelsPart2 \subseteq Labels
  /\ LabelsPart3 \subseteq Labels /\ LabelsAdds \subseteq Labels
BY DEF LabelsPart1, LabelsPart2, LabelsPart3, LabelsAdds, Labels

LEMMA FoundingSplit == Founding = FoundingPart1 \cup FoundingPart2 \cup FoundingPart3
BY DEF Founding, FoundingPart1, FoundingPart2, FoundingPart3

LEMMA FoundingPart1Text ==
  ASSUME NEW e \in FoundingPart1 PROVE TextFacts(e) /\ e \in TextRec(LabelsPart1)
BY DEF FoundingPart1, Txt, Edge, TextFacts, Fixed, Kinds, ForbiddenLabels, LabelsPart1,
       TextRec

LEMMA FoundingPart1Writers ==
  ASSUME NEW e \in FoundingPart1 PROVE WriterFacts(e)
BY DEF FoundingPart1, Txt, Edge, WriterFacts, GrantKinds, Rank

LEMMA FoundingPart2Text ==
  ASSUME NEW e \in FoundingPart2 PROVE TextFacts(e) /\ e \in TextRec(LabelsPart2)
BY DEF FoundingPart2, Txt, Edge, TextFacts, Fixed, Kinds, ForbiddenLabels, LabelsPart2,
       TextRec

LEMMA FoundingPart2Writers ==
  ASSUME NEW e \in FoundingPart2 PROVE WriterFacts(e)
BY DEF FoundingPart2, Txt, Edge, WriterFacts, GrantKinds, Rank

LEMMA FoundingPart3Text ==
  ASSUME NEW e \in FoundingPart3 PROVE TextFacts(e) /\ e \in TextRec(LabelsPart3)
BY DEF FoundingPart3, Txt, Edge, TextFacts, Fixed, Kinds, ForbiddenLabels, LabelsPart3,
       TextRec

LEMMA FoundingPart3Writers ==
  ASSUME NEW e \in FoundingPart3 PROVE WriterFacts(e)
BY DEF FoundingPart3, Txt, Edge, WriterFacts, GrantKinds, Rank

LEMMA TextRecMono ==
  ASSUME NEW L1, NEW L2, L1 \subseteq L2 PROVE TextRec(L1) \subseteq TextRec(L2)
BY DEF TextRec

LEMMA TextRecType == TextRec(Labels) \subseteq EdgeType
BY DEF TextRec, EdgeType, Nodes, Bases

LEMMA FoundingFacts ==
  ASSUME NEW e \in Founding PROVE TextFacts(e) /\ WriterFacts(e) /\ e \in TextRec(Labels)
BY FoundingSplit, LabelParts, TextRecMono, FoundingPart1Text, FoundingPart2Text, FoundingPart3Text,
   FoundingPart1Writers, FoundingPart2Writers, FoundingPart3Writers

LEMMA AddsText ==
  ASSUME NEW x \in AmendIds, NEW e \in Adds(x)
  PROVE  TextFacts(e) /\ e \in TextRec(Labels)
<1>1. TextFacts(e) /\ e \in TextRec(LabelsAdds)
  BY DEF AmendIds, Adds, Txt, Edge, TextFacts, Fixed, Kinds, ForbiddenLabels, LabelsAdds,
         TextRec
<1> QED
  BY <1>1, LabelParts, TextRecMono

LEMMA AddsWriters ==
  ASSUME Mut # "M_CONGRESS_AMENDS", NEW x \in AmendIds, NEW e \in Adds(x)
  PROVE  WriterFacts(e)
BY DEF AmendIds, Adds, Txt, Edge, WriterFacts, GrantKinds, Rank

LEMMA DropsFacts ==
  ASSUME NEW x \in AmendIds, NEW e \in Drops(x)
  PROVE  e \in Founding
<1>1. e \in FoundingPart1
  BY DEF AmendIds, Drops, ArticleV, FoundingPart1, Txt, Edge
<1> QED
  BY <1>1, FoundingSplit

LEMMA StatutoryLabelsInLabels == StatutoryLabels \subseteq Labels
<1>1. {"Enable", "NominateHead", "ConsentHead", "Appropriate", "Impeach", "Review",
       "ExecutivePower", "Direct", "Remove", "RemoveForCause"} \subseteq Labels
  BY DEF Labels
<1>2. {"AppointInferior", "Establish", "ArtIII", "Nominate", "Consent", "Jurisdiction",
       "Appeal", "LegislativeVeto", "DiminishPay"} \subseteq Labels
  BY DEF Labels
<1> QED
  BY <1>1, <1>2 DEF StatutoryLabels

LEMMA StatRecType == StatRec \subseteq EdgeType
BY StatutoryLabelsInLabels DEF StatRec, EdgeType, Nodes, Upper, Fixed, Bases

LEMMA AgencyEdgesShape ==
  ASSUME NEW a \in Agencies, NEW x \in BOOLEAN, NEW r \in Removers, NEW v \in Vesters
  PROVE  /\ AgencyEdges(a, x, r, v) \subseteq StatRec
         /\ \A e \in AgencyEdges(a, x, r, v) : e.to = a
BY DEF AgencyEdges, StatRec, Law, Edge, Upper, Kinds, StatutoryLabels, Removers, Vesters

LEMMA CourtEdgesShape ==
  ASSUME NEW c \in Courts
  PROVE  /\ CourtEdges(c) \subseteq StatRec
         /\ \A e \in CourtEdges(c) : e.to = c /\ e.label \notin {"Remove", "RemoveForCause"}
BY DEF CourtEdges, StatRec, Law, Edge, Upper, Kinds, StatutoryLabels

LEMMA OpsCases ==
  ASSUME NEW op \in Ops
  PROVE  \/ /\ op.name = "CreateAgency" /\ op.target \in Agencies /\ op.exec \in BOOLEAN
            /\ op.remover \in Removers /\ op.vesting \in Vesters
         \/ op.name \in {"AbolishAgency", "LegislativeVeto"} /\ op.target \in Agencies
         \/ /\ op.name \in {"EstablishCourt", "AbolishCourt", "StripJurisdiction", "CutPay"}
            /\ op.target \in Courts
BY DEF Ops

LEMMA EnactCases ==
  ASSUME NEW op \in Ops
  PROVE  \/ /\ op.name = "CreateAgency" /\ op.target \in Agencies
            /\ op.exec \in BOOLEAN /\ op.remover \in Removers /\ op.vesting \in Vesters
            /\ EdgesAfter(op) = edges \cup AgencyEdges(op.target, op.exec, op.remover, op.vesting)
            /\ LiveAfter(op) = live \cup {op.target}
         \/ /\ op.name = "EstablishCourt" /\ op.target \in Courts
            /\ EdgesAfter(op) = edges \cup CourtEdges(op.target)
            /\ LiveAfter(op) = live \cup {op.target}
         \/ /\ op.name \in {"AbolishAgency", "AbolishCourt"} /\ op.target \in Agencies \cup Courts
            /\ EdgesAfter(op) = edges \ Touching(op.target)
            /\ LiveAfter(op) = live \ {op.target}
         \/ /\ op.name = "LegislativeVeto" /\ op.target \in Agencies
            /\ EdgesAfter(op) = edges \cup {Law("Congress", op.target, "Control", "LegislativeVeto")}
            /\ LiveAfter(op) = live
         \/ /\ op.name = "CutPay" /\ op.target \in Courts
            /\ EdgesAfter(op) = edges \cup {Law("Congress", op.target, "Control", "DiminishPay")}
            /\ LiveAfter(op) = live
         \/ /\ op.name = "StripJurisdiction" /\ op.target \in Courts
            /\ EdgesAfter(op) = edges \ {Law("Judiciary", op.target, "Control", "Appeal")}
            /\ LiveAfter(op) = live
<1>1. CASE op.name = "CreateAgency"
  BY <1>1, OpsCases DEF EdgesAfter, LiveAfter
<1>2. CASE op.name = "EstablishCourt"
  BY <1>2, OpsCases DEF EdgesAfter, LiveAfter
<1>3. CASE op.name \in {"AbolishAgency", "AbolishCourt"}
  BY <1>3, OpsCases DEF EdgesAfter, LiveAfter
<1>4. CASE op.name = "LegislativeVeto"
  BY <1>4, OpsCases DEF EdgesAfter, LiveAfter
<1>5. CASE op.name = "CutPay"
  BY <1>5, OpsCases DEF EdgesAfter, LiveAfter
<1>6. CASE op.name = "StripJurisdiction"
  BY <1>6, OpsCases DEF EdgesAfter, LiveAfter
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, OpsCases

-----------------------------------------------------------------------------
(* The type invariant, under every mutation                                *)

\* TypeOK and the one fact about the bill in flight Sign needs: it is a
\* real bill.
BillIsReal == bill.stage # "None" => bill.op \in Ops
TypeInv == TypeOK /\ BillIsReal

\* The text edges the actions fire.
Fired ==
  { Txt("Congress", "Executive", "Control", "Presentment"),
    Txt("Congress", "Executive", "Control", "Override"),
    Txt("Executive", "Congress", "Control", "Veto"),
    Txt("Constitution", "Congress", "Power", "ArtI"),
    Txt("Executive", "Congress", "Control", "Convene"),
    Txt("States", "Executive", "Select", "AppointElectors"),
    Txt("Congress", "Executive", "Select", "ContingentElection"),
    Txt("States", "VicePresident", "Select", "AppointElectors"),
    Txt("Congress", "VicePresident", "Select", "ContingentElection"),
    Txt("VicePresident", "Executive", "Select", "Succession"),
    Txt("People", "Judiciary", "Control", "Sue"),
    Txt("Judiciary", "Congress", "Control", "Review"),
    Txt("Congress", "States", "Amend", "Propose"),
    Txt("States", "Congress", "Control", "ApplyForConvention"),
    Txt("States", "Constitution", "Amend", "Ratify"),
    Txt("Congress", "Executive", "Control", "Impeach"),
    Txt("Congress", "VicePresident", "Control", "Impeach"),
    Txt("Congress", "Judiciary", "Control", "Impeach"),
    Txt("Congress", "Judiciary", "Control", "Exceptions"),
    Txt("Congress", "Judiciary", "Control", "Organize") }

FiredXXV ==
  { Txt("Executive", "VicePresident", "Select", "NominateVP"),
    Txt("Congress", "VicePresident", "Select", "ConfirmVP") }

LEMMA FiredType == Fired \cup FiredXXV \subseteq EdgeType
<1>1. Fired \subseteq FoundingPart1 \cup FoundingPart2 \cup FoundingPart3
  BY DEF Fired, FoundingPart1, FoundingPart2, FoundingPart3
<1>2. Fired \subseteq EdgeType
  BY <1>1, FoundingSplit, FoundingFacts, TextRecType
<1>3. FiredXXV \subseteq TextRec(LabelsAdds)
  BY DEF FiredXXV, TextRec, Txt, Edge, Fixed, Kinds, LabelsAdds
<1> QED
  BY <1>2, <1>3, LabelParts, TextRecMono, TextRecType

LEMMA LawType ==
  ASSUME NEW f \in Upper, NEW t \in Agencies \cup Courts, NEW k \in Kinds,
         NEW l \in StatutoryLabels
  PROVE  Law(f, t, k, l) \in EdgeType
BY StatRecType DEF StatRec, Law, Edge

LEMMA FireFrame ==
  ASSUME NEW e, Fire(e)
  PROVE  last' = e /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
BY DEF Fire, StrayOf

LEMMA InitTypeInv == Init => TypeInv
<1> SUFFICES ASSUME Init PROVE TypeInv
  OBVIOUS
<1>1. edges \subseteq EdgeType
  BY FoundingFacts, TextRecType DEF Init
<1> QED
  BY <1>1 DEF Init, TypeInv, TypeOK, BillIsReal, NoBill, Offices, Breaches

LEMMA EnactType ==
  ASSUME TypeOK, NEW op \in Ops, Enact(op)
  PROVE  /\ edges' \subseteq EdgeType /\ live' \subseteq Agencies \cup Courts
         /\ seated' \subseteq Offices
         /\ nominated' \subseteq Agencies \cup Courts \cup {"VicePresident"}
         /\ trial' \in Offices \cup {"Judiciary", "None"}
         /\ challenged' \subseteq edges'
<1>1. EdgesAfter(op) \subseteq EdgeType
  <2>1. CASE op.name = "CreateAgency"
    BY <2>1, EnactCases, AgencyEdgesShape, StatRecType DEF TypeOK
  <2>2. CASE op.name = "EstablishCourt"
    BY <2>2, EnactCases, CourtEdgesShape, StatRecType DEF TypeOK
  <2>3. CASE op.name \in {"LegislativeVeto", "CutPay"}
    <3>1. op.target \in Agencies \cup Courts
      BY <2>3, OpsCases
    <3>2. Law("Congress", op.target, "Control", "LegislativeVeto") \in EdgeType
          /\ Law("Congress", op.target, "Control", "DiminishPay") \in EdgeType
      BY <3>1, LawType DEF Upper, Kinds, StatutoryLabels
    <3> QED
      BY <2>3, <3>2, EnactCases DEF TypeOK
  <2>4. CASE op.name \in {"AbolishAgency", "AbolishCourt", "StripJurisdiction"}
    BY <2>4, EnactCases DEF TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, OpsCases
<1>2. LiveAfter(op) \subseteq Agencies \cup Courts
  BY EnactCases DEF TypeOK
<1>3. /\ edges' = EdgesAfter(op) /\ live' = LiveAfter(op)
      /\ challenged' = challenged \cap EdgesAfter(op)
      /\ seated' \subseteq seated /\ nominated' \subseteq nominated
      /\ trial' \in {trial, "None"}
  BY DEF Enact, SetEdges, Unseat
<1> QED
  BY <1>1, <1>2, <1>3 DEF TypeOK

LEMMA RulingType ==
  ASSUME TypeOK, NEW e \in edges
  PROVE  Ruling(e) \subseteq EdgeType
<1>1. Ruling(e) \subseteq edges \cup {Law("Executive", e.to, "Control", "Remove")}
  BY DEF Ruling, Sever
<1>2. e.to \in Nodes
  BY DEF TypeOK, EdgeType
<1>3. Law("Executive", e.to, "Control", "Remove") \in EdgeType
  <2>1. "Executive" \in Nodes /\ "Control" \in Kinds /\ "Remove" \in Labels /\ "Statute" \in Bases
    BY DEF Nodes, Fixed, Kinds, Labels, Bases
  <2> QED
    BY <1>2, <2>1 DEF EdgeType, Law, Edge
<1> QED
  BY <1>1, <1>3 DEF TypeOK

\* Each step below names what the action changes, then the type follows.
LEMMA NextTypeInv == TypeInv /\ [Next]_vars => TypeInv'
<1> SUFFICES ASSUME TypeInv, [Next]_vars PROVE TypeInv'
  OBVIOUS
<1>0. TypeOK /\ BillIsReal /\ Fired \cup FiredXXV \subseteq EdgeType
  BY FiredType DEF TypeInv
<1>1. ASSUME NEW op \in Ops, Pass(op) PROVE TypeInv'
  <2>1. AuthorityFor(op) \in Fired
    BY DEF AuthorityFor, Fired
  <2>2. /\ last' = AuthorityFor(op) /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ bill' = [stage |-> "Presented", op |-> op]
        /\ UNCHANGED <<edges, live, challenged, seated, nominated, trial, inSession,
                       amendment, breaches>>
    BY <1>1, FireFrame DEF Pass, graphVars, officeVars
  <2> QED
    BY <1>0, <2>1, <2>2 DEF TypeInv, TypeOK, BillIsReal
<1>2. CASE Sign \/ Lapse \/ Override
  <2>1. bill.op \in Ops /\ Enact(bill.op)
    BY <1>0, <1>2 DEF Sign, Lapse, Override, BillIsReal
  <2>2. /\ last' \in Fired /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ bill' = NoBill /\ UNCHANGED <<inSession, amendment>>
        /\ breaches' \subseteq breaches \cup {"PocketVeto"}
    <3>1. CASE Sign
      BY <3>1, FireFrame DEF Sign, Fired
    <3>2. CASE Lapse
      BY <3>2, FireFrame DEF Lapse, Fired
    <3>3. CASE Override
      BY <3>3, FireFrame DEF Override, Fired
    <3> QED
      BY <1>2, <3>1, <3>2, <3>3
  <2>3. /\ edges' \subseteq EdgeType /\ live' \subseteq Agencies \cup Courts
        /\ seated' \subseteq Offices
        /\ nominated' \subseteq Agencies \cup Courts \cup {"VicePresident"}
        /\ trial' \in Offices \cup {"Judiciary", "None"}
        /\ challenged' \subseteq edges'
    BY <1>0, <2>1, EnactType
  <2> QED
    BY <1>0, <2>2, <2>3 DEF TypeInv, TypeOK, BillIsReal, NoBill, Breaches
<1>3. CASE Veto \/ PocketVeto \/ BillFails
  <2>1. /\ last' \in Fired \cup {NoEdge} /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ \/ bill' = NoBill
           \/ bill.stage = "Presented" /\ bill' = [bill EXCEPT !.stage = "Vetoed"]
        /\ UNCHANGED <<edges, live, challenged, seated, nominated, trial, inSession,
                       amendment, breaches>>
    BY <1>3, FireFrame DEF Veto, PocketVeto, BillFails, Fired, graphVars, officeVars
  <2> QED
    <3>1. bill'.stage # "None" => bill'.op = bill.op /\ bill.stage # "None"
      BY <1>0, <2>1 DEF NoBill, TypeOK
    <3> QED
      BY <1>0, <2>1, <3>1 DEF TypeInv, TypeOK, BillIsReal, NoBill
<1>4. CASE Adjourn \/ Convene \/ ConveneByPresident
  <2>1. /\ last' \in Fired /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ inSession' \in BOOLEAN
        /\ UNCHANGED <<edges, live, challenged, seated, nominated, trial, bill,
                       amendment, breaches>>
    BY <1>4, FireFrame DEF Adjourn, Convene, ConveneByPresident, Fired, graphVars,
                           officeVars
  <2> QED
    BY <1>0, <2>1 DEF TypeInv, TypeOK, BillIsReal
<1>5. CASE ElectPresident \/ ContingentElection \/ ElectVicePresident \/ ContingentElectionVP
           \/ Succeed \/ NominateVP \/ ConfirmVP \/ RejectVP
  <2>1. /\ last' \in Fired \cup FiredXXV
        /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ seated' \subseteq seated \cup {"Executive", "VicePresident"}
        /\ nominated' \subseteq nominated \cup {"VicePresident"}
        /\ UNCHANGED <<edges, live, challenged, trial, bill, inSession, amendment, breaches>>
    BY <1>5, FireFrame
       DEF ElectPresident, ContingentElection, ElectVicePresident, ContingentElectionVP,
           Succeed, NominateVP, ConfirmVP, RejectVP, Fired, FiredXXV, graphVars, lawVars
  <2> QED
    BY <1>0, <2>1 DEF TypeInv, TypeOK, BillIsReal, Offices
<1>6. CASE VicePresidentLeaves \/ PresidentLeaves
  <2>1. /\ last' = NoEdge /\ seated' \subseteq seated
        /\ UNCHANGED <<edges, live, challenged, nominated, trial, bill, inSession,
                       amendment, stray, breaches>>
    BY <1>6 DEF VicePresidentLeaves, PresidentLeaves, graphVars, lawVars
  <2> QED
    BY <1>0, <2>1 DEF TypeInv, TypeOK, BillIsReal
<1>7. ASSUME NEW n \in Agencies \cup Courts,
             Nominate(n) \/ Consent(n) \/ Reject(n) \/ Remove(n) \/ Resign(n)
      PROVE  TypeInv'
  <2>1. /\ Law("Executive", n, "Select", NominateLabel(n)) \in EdgeType
        /\ Law("Congress", n, "Select", ConsentLabel(n)) \in EdgeType
        /\ RemovalEdges(n) \subseteq EdgeType
    BY LawType DEF NominateLabel, ConsentLabel, RemovalEdges, Upper, Kinds, StatutoryLabels
  <2>2. /\ last' \in EdgeType \cup {NoEdge}
        /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ seated' \subseteq seated \cup {n} /\ nominated' \subseteq nominated \cup {n}
        /\ breaches' \subseteq breaches \cup {"GoodBehaviour"}
        /\ UNCHANGED <<edges, live, challenged, trial, bill, inSession, amendment>>
    <3>1. CASE Nominate(n) \/ Consent(n) \/ Reject(n)
      BY <3>1, <2>1, FireFrame DEF Nominate, Consent, Reject, graphVars, lawVars
    <3>2. CASE Remove(n)
      <4>1. PICK e \in RemovalEdges(n) : Fire(e)
        BY <3>2 DEF Remove
      <4> QED
        BY <3>2, <4>1, <2>1, FireFrame DEF Remove, graphVars, lawVars
    <3>3. CASE Resign(n)
      BY <3>3 DEF Resign, graphVars, lawVars
    <3> QED
      BY <1>7, <3>1, <3>2, <3>3
  <2> QED
    BY <1>0, <2>2 DEF TypeInv, TypeOK, BillIsReal, Offices, Breaches
<1>8. ASSUME NEW n \in Offices \cup {"Judiciary"}, Impeach(n) PROVE TypeInv'
  <2>1. ImpeachEdge(n) \in EdgeType
    <3>1. CASE n \in {"Executive", "VicePresident", "Judiciary"}
      BY <3>1, <1>0 DEF ImpeachEdge, Fired
    <3>2. CASE n \notin {"Executive", "VicePresident", "Judiciary"}
      <4>1. n \in Agencies \cup Courts
        BY <3>2 DEF Offices
      <4> QED
        BY <3>2, <4>1, LawType DEF ImpeachEdge, Upper, Kinds, StatutoryLabels
    <3> QED
      BY <3>1, <3>2
  <2>2. /\ last' = ImpeachEdge(n) /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ trial' = n
        /\ UNCHANGED <<edges, live, challenged, seated, nominated, bill, inSession,
                       amendment, breaches>>
    BY <1>8, FireFrame DEF Impeach, graphVars, lawVars
  <2> QED
    BY <1>0, <2>1, <2>2 DEF TypeInv, TypeOK, BillIsReal
<1>9. CASE Convict \/ Acquit
  <2>1. trial \in Offices \cup {"Judiciary"}
    BY <1>0, <1>9 DEF Convict, Acquit, TypeOK
  <2>2. ImpeachEdge(trial) \in EdgeType
    <3>1. CASE trial \in {"Executive", "VicePresident", "Judiciary"}
      BY <3>1, <1>0 DEF ImpeachEdge, Fired
    <3>2. CASE trial \notin {"Executive", "VicePresident", "Judiciary"}
      <4>1. trial \in Agencies \cup Courts
        BY <2>1, <3>2 DEF Offices
      <4> QED
        BY <3>2, <4>1, LawType DEF ImpeachEdge, Upper, Kinds, StatutoryLabels
    <3> QED
      BY <3>1, <3>2
  <2>3. /\ last' = ImpeachEdge(trial) /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ trial' = "None" /\ seated' \subseteq seated
        /\ UNCHANGED <<edges, live, challenged, nominated, bill, inSession, amendment,
                       breaches>>
    BY <1>9, FireFrame DEF Convict, Acquit, graphVars, lawVars
  <2> QED
    BY <1>0, <2>2, <2>3 DEF TypeInv, TypeOK, BillIsReal
<1>10. ASSUME NEW e \in edges, Sue(e) \/ Exercise(e) PROVE TypeInv'
  <2>1. e \in EdgeType
    BY <1>0 DEF TypeOK
  <2>2. /\ last' \in Fired \cup {e} /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ challenged' \subseteq challenged \cup {e}
        /\ UNCHANGED <<edges, live, seated, nominated, trial, bill, inSession, amendment,
                       breaches>>
    BY <1>10, FireFrame DEF Sue, Exercise, Fired, graphVars, officeVars, lawVars
  <2> QED
    BY <1>0, <2>1, <2>2 DEF TypeInv, TypeOK, BillIsReal
<1>11. ASSUME NEW e \in challenged, Review(e) PROVE TypeInv'
  <2>1. Ruling(e) \subseteq EdgeType
    BY <1>0, RulingType DEF TypeOK
  <2>2. /\ last' \in Fired /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ edges' = Ruling(e) /\ challenged' \subseteq edges'
        /\ breaches' \subseteq breaches \cup ViolatedBy(e)
        /\ UNCHANGED <<live, seated, nominated, trial, bill, inSession, amendment>>
    BY <1>11, FireFrame DEF Review, Fired, officeVars, lawVars
  <2>3. ViolatedBy(e) \subseteq Breaches
    BY DEF ViolatedBy, Breaches
  <2> QED
    BY <1>0, <2>1, <2>2, <2>3 DEF TypeInv, TypeOK, BillIsReal
<1>12. ASSUME NEW x \in AmendIds, Propose(x) \/ Ratify(x) PROVE TypeInv'
  <2>1. Adds(x) \subseteq EdgeType
    BY AddsText, TextRecType
  <2>2. /\ last' \in Fired /\ stray' \subseteq stray \cup {"OffGraph", "Vacant"}
        /\ amendment' \in [AmendIds -> {"None", "Proposed", "Ratified"}]
        /\ edges' \subseteq edges \cup Adds(x) /\ challenged' \subseteq edges'
        /\ challenged' \subseteq challenged
        /\ UNCHANGED <<live, seated, nominated, trial, bill, inSession, breaches>>
    <3>1. CASE Propose(x)
      BY <1>0, <3>1, FireFrame DEF Propose, Fired, TypeOK, graphVars, officeVars, lawVars
    <3>2. CASE Ratify(x)
      BY <1>0, <3>2, FireFrame DEF Ratify, SetEdges, Fired, TypeOK, officeVars, lawVars
    <3> QED
      BY <1>12, <3>1, <3>2
  <2> QED
    BY <1>0, <2>1, <2>2 DEF TypeInv, TypeOK, BillIsReal
<1>13. CASE UNCHANGED vars
  BY <1>0, <1>13 DEF vars, TypeInv, TypeOK, BillIsReal
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12,
     <1>13 DEF Next

-----------------------------------------------------------------------------
(* The shape of the graph, under every mutation                            *)

\* What every statutory edge is: from a branch or the text, into a body of
\* statute; a removal edge always into an agency.
StatuteFacts(e) ==
  /\ e \in StatRec
  /\ e.label \in {"Remove", "RemoveForCause"} => e.to \in Agencies

\* The edge by which Congress created a live body.
CreationEdge(n) ==
  IF n \in Agencies THEN Law("Congress", n, "Power", "Enable")
                    ELSE Law("Congress", n, "Power", "Establish")

\* The text layer is the amended founding text; every statutory edge is a
\* StatuteFacts edge; only statutory edges are challenged; every live body
\* has its creation edge.
StatutesShaped == \A e \in edges : e.basis = "Statute" => StatuteFacts(e)
CasesOnStatutes == \A e \in challenged : e.basis = "Statute"
BodiesCreated  == \A n \in live : CreationEdge(n) \in edges

Shape == TypeInv /\ TextFollowsArticleV /\ StatutesShaped /\ CasesOnStatutes /\ BodiesCreated

\* The steps that touch neither the graph, the bodies, the docket nor the
\* text.
QuietStep ==
  \/ \E op \in Ops : Pass(op)
  \/ Veto \/ PocketVeto \/ BillFails
  \/ Adjourn \/ Convene \/ ConveneByPresident
  \/ ElectPresident \/ ContingentElection \/ PresidentLeaves
  \/ ElectVicePresident \/ ContingentElectionVP \/ VicePresidentLeaves \/ Succeed
  \/ NominateVP \/ ConfirmVP \/ RejectVP
  \/ \E n \in Agencies \cup Courts :
       Nominate(n) \/ Consent(n) \/ Reject(n) \/ Remove(n) \/ Resign(n)
  \/ \E n \in Offices \cup {"Judiciary"} : Impeach(n)
  \/ Convict \/ Acquit
  \/ \E e \in edges : Exercise(e)

LawStep == Sign \/ Lapse \/ Override

LEMMA NextSplit ==
  [Next]_vars =>
    \/ QuietStep \/ LawStep
    \/ \E e \in edges : Sue(e)
    \/ \E e \in challenged : Review(e)
    \/ \E x \in AmendIds : Propose(x)
    \/ \E x \in AmendIds : Ratify(x)
    \/ UNCHANGED vars
BY DEF Next, QuietStep, LawStep

LEMMA QuietFrame == QuietStep => UNCHANGED <<edges, live, challenged, amendment>>
BY DEF QuietStep, Pass, Veto, PocketVeto, BillFails, Adjourn, Convene, ConveneByPresident,
       ElectPresident, ContingentElection, PresidentLeaves, ElectVicePresident,
       ContingentElectionVP, VicePresidentLeaves, Succeed, NominateVP, ConfirmVP, RejectVP,
       Nominate, Consent, Reject, Remove, Resign, Impeach, Convict, Acquit, Exercise,
       graphVars

\* The bill in flight under a law step is a real bill and is enacted.
LEMMA LawStepEnacts ==
  ASSUME TypeInv, LawStep
  PROVE  /\ bill.op \in Ops /\ Enact(bill.op) /\ UNCHANGED amendment
         /\ last'.label \in {"Presentment", "Override"}
BY DEF LawStep, Sign, Lapse, Override, Fire, TypeInv, BillIsReal, Txt, Edge

LEMMA TextForOf ==
  ASSUME NEW a \in [AmendIds -> {"None", "Proposed", "Ratified"}]
  PROVE  TextFor(a) \subseteq Founding \cup Adds("XVII") \cup Adds("XXV")
BY DEF TextFor, Applied

\* Facts every text edge of the graph has, given the text is amended.
LEMMA TextEdges ==
  ASSUME TypeOK, TextFollowsArticleV, NEW e \in edges, e.basis = "Text"
  PROVE  /\ TextFacts(e) /\ e \in TextRec(Labels)
         /\ Mut # "M_CONGRESS_AMENDS" => WriterFacts(e)
<1>1. e \in TextFor(amendment)
  BY DEF TextFollowsArticleV, TextOf
<1>2. e \in Founding \cup Adds("XVII") \cup Adds("XXV")
  BY <1>1, TextForOf DEF TypeOK
<1> QED
  BY <1>2, FoundingFacts, AddsText, AddsWriters DEF AmendIds

LEMMA InitShape == Init => Shape
<1> SUFFICES ASSUME Init PROVE Shape
  OBVIOUS
<1>1. TypeInv
  BY InitTypeInv
<1>2. TextOf(edges) = Founding
  BY FoundingFacts DEF Init, TextOf, TextFacts
<1>3. TextFor(amendment) = Founding
  BY DEF Init, TextFor, Applied, AmendIds
<1>4. \A e \in edges : e.basis # "Statute"
  BY FoundingFacts DEF Init, TextFacts
<1> QED
  BY <1>1, <1>2, <1>3, <1>4
     DEF Init, Shape, TextFollowsArticleV, StatutesShaped, CasesOnStatutes, BodiesCreated

LEMMA ForbiddenLabelsOf ==
  ASSUME NEW e, Forbidden(e) PROVE e.label \in ForbiddenLabels
BY DEF Forbidden, Violates, Doctrines, ForbiddenLabels

LEMMA AddsDropsDisjoint ==
  /\ Adds("XXV") \cap Drops("XVII") = {}
  /\ Adds("XVII") \cap Drops("XXV") = {}
BY DEF Adds, Drops, ArticleV, Txt, Edge

\* A step that only proposes leaves the text as it was.
LEMMA TextForProposed ==
  ASSUME NEW a \in [AmendIds -> {"None", "Proposed", "Ratified"}], NEW x \in AmendIds,
         a[x] = "None"
  PROVE  TextFor([a EXCEPT ![x] = "Proposed"]) = TextFor(a)
BY DEF TextFor, Applied, AmendIds

\* Ratifying x drops its Drops and adds its Adds to the text.
LEMMA TextForRatified ==
  ASSUME NEW a \in [AmendIds -> {"None", "Proposed", "Ratified"}], NEW x \in AmendIds,
         a[x] = "Proposed"
  PROVE  TextFor([a EXCEPT ![x] = "Ratified"]) = (TextFor(a) \ Drops(x)) \cup Adds(x)
<1>1. CASE x = "XVII"
  BY <1>1, AddsDropsDisjoint DEF TextFor, Applied, AmendIds
<1>2. CASE x = "XXV"
  BY <1>2, AddsDropsDisjoint DEF TextFor, Applied, AmendIds
<1> QED
  BY <1>1, <1>2 DEF AmendIds

\* What an enactment does to the text, the statutes and the bodies.
LEMMA EnactText ==
  ASSUME TypeOK, TextFollowsArticleV, NEW op \in Ops
  PROVE  TextOf(EdgesAfter(op)) = TextOf(edges)
<1>1. CASE op.name = "CreateAgency"
  BY <1>1, EnactCases, AgencyEdgesShape DEF TextOf, StatRec
<1>2. CASE op.name = "EstablishCourt"
  BY <1>2, EnactCases, CourtEdgesShape DEF TextOf, StatRec
<1>3. CASE op.name \in {"AbolishAgency", "AbolishCourt"}
  <2>1. op.target \in Agencies \cup Courts /\ EdgesAfter(op) = edges \ Touching(op.target)
    BY <1>3, EnactCases
  <2>2. \A e \in edges : e.basis = "Text" => e \notin Touching(op.target)
    BY <2>1, TextEdges, PoolsAreNew DEF TextFacts, Touching
  <2> QED
    BY <2>1, <2>2 DEF TextOf
<1>4. CASE op.name \in {"LegislativeVeto", "CutPay", "StripJurisdiction"}
  BY <1>4, EnactCases DEF TextOf, Law, Edge
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, OpsCases

LEMMA EnactStatutes ==
  ASSUME TypeOK, StatutesShaped, NEW op \in Ops
  PROVE  \A e \in EdgesAfter(op) : e.basis = "Statute" => StatuteFacts(e)
<1>1. CASE op.name = "CreateAgency"
  BY <1>1, EnactCases, AgencyEdgesShape DEF StatutesShaped, StatuteFacts
<1>2. CASE op.name = "EstablishCourt"
  BY <1>2, EnactCases, CourtEdgesShape, PoolsDisjoint DEF StatutesShaped, StatuteFacts
<1>3. CASE op.name \in {"AbolishAgency", "AbolishCourt", "StripJurisdiction"}
  BY <1>3, EnactCases DEF StatutesShaped
<1>4. CASE op.name \in {"LegislativeVeto", "CutPay"}
  <2>1. op.target \in Agencies \cup Courts
    BY <1>4, OpsCases
  <2>2. /\ StatuteFacts(Law("Congress", op.target, "Control", "LegislativeVeto"))
        /\ StatuteFacts(Law("Congress", op.target, "Control", "DiminishPay"))
    BY <2>1 DEF StatuteFacts, StatRec, Law, Edge, Upper, Kinds, StatutoryLabels
  <2> QED
    BY <1>4, <2>2, EnactCases DEF StatutesShaped
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, OpsCases

LEMMA EnactBodies ==
  ASSUME TypeOK, BodiesCreated, NEW op \in Ops
  PROVE  \A n \in LiveAfter(op) : CreationEdge(n) \in EdgesAfter(op)
<1>1. CASE op.name = "CreateAgency"
  <2>1. Law("Congress", op.target, "Power", "Enable")
          \in AgencyEdges(op.target, op.exec, op.remover, op.vesting)
    BY DEF AgencyEdges
  <2> QED
    BY <1>1, <2>1, EnactCases DEF BodiesCreated, CreationEdge
<1>2. CASE op.name = "EstablishCourt"
  <2>1. Law("Congress", op.target, "Power", "Establish") \in CourtEdges(op.target)
    BY DEF CourtEdges
  <2>2. op.target \notin Agencies
    BY <1>2, EnactCases, PoolsDisjoint
  <2> QED
    BY <1>2, <2>1, <2>2, EnactCases DEF BodiesCreated, CreationEdge
<1>3. CASE op.name \in {"AbolishAgency", "AbolishCourt"}
  <2>1. op.target \in Agencies \cup Courts /\ EdgesAfter(op) = edges \ Touching(op.target)
        /\ LiveAfter(op) = live \ {op.target}
    BY <1>3, EnactCases
  <2>2. "Congress" # op.target
    BY <2>1, PoolsAreNew DEF Fixed
  <2> QED
    BY <2>1, <2>2 DEF BodiesCreated, CreationEdge, Touching, Law, Edge
<1>4. CASE op.name \in {"LegislativeVeto", "CutPay", "StripJurisdiction"}
  BY <1>4, EnactCases DEF BodiesCreated, CreationEdge, Law, Edge
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, OpsCases

\* What a ruling does: it keeps the text, shapes what it adds, and never
\* removes a creation edge.
LEMMA RulingFacts ==
  ASSUME TypeOK, StatutesShaped, CasesOnStatutes, NEW e \in challenged
  PROVE  /\ TextOf(Ruling(e)) = TextOf(edges)
         /\ \A f \in Ruling(e) : f.basis = "Statute" => StatuteFacts(f)
         /\ \A n \in Agencies \cup Courts : CreationEdge(n) \in edges => CreationEdge(n) \in Ruling(e)
<1>1. e \in edges /\ e.basis = "Statute" /\ StatuteFacts(e)
  BY DEF TypeOK, CasesOnStatutes, StatutesShaped
<1>2. CASE ~Strikes(e)
  BY <1>2 DEF Ruling, StatutesShaped
<1>3. CASE Strikes(e)
  <2>1. e.label \in ForbiddenLabels
    BY <1>3, ForbiddenLabelsOf DEF Strikes
  <2>2. \A n \in Agencies \cup Courts : CreationEdge(n) # e
    BY <2>1 DEF CreationEdge, Law, Edge, ForbiddenLabels
  <2>3. CASE Mut = "M_SEVER_PLAIN"
    BY <1>1, <1>3, <2>2, <2>3 DEF Ruling, Sever, TextOf, StatutesShaped
  <2>4. CASE Mut # "M_SEVER_PLAIN" /\ e.label = "RemoveForCause"
    <3>1. e.to \in Agencies
      BY <1>1, <2>4 DEF StatuteFacts
    <3>2. StatuteFacts(Law("Executive", e.to, "Control", "Remove"))
      BY <3>1 DEF StatuteFacts, StatRec, Law, Edge, Upper, Kinds, StatutoryLabels
    <3>3. Ruling(e) = (edges \ {e}) \cup {Law("Executive", e.to, "Control", "Remove")}
      BY <1>3, <2>4 DEF Ruling, Sever
    <3> QED
      BY <1>1, <2>2, <3>2, <3>3 DEF TextOf, StatutesShaped, Law, Edge
  <2>5. CASE Mut # "M_SEVER_PLAIN" /\ e.label = "Remove" /\ e.from = "Congress"
    <3>1. Ruling(e) = edges \ {Law("Executive", e.to, "Power", "ExecutivePower"),
                               Law("Executive", e.to, "Control", "Direct")}
      BY <1>3, <2>5 DEF Ruling, Sever
    <3> QED
      BY <3>1 DEF TextOf, StatutesShaped, CreationEdge, Law, Edge
  <2>6. CASE Mut # "M_SEVER_PLAIN" /\ e.label # "RemoveForCause"
             /\ ~(e.label = "Remove" /\ e.from = "Congress")
    <3>1. Ruling(e) = edges \ {e}
      BY <1>3, <2>6 DEF Ruling, Sever
    <3> QED
      BY <1>1, <2>2, <3>1 DEF TextOf, StatutesShaped
  <2> QED
    BY <2>3, <2>4, <2>5, <2>6
<1> QED
  BY <1>2, <1>3

\* Ratification changes only the text.
LEMMA RatifyStatutes ==
  ASSUME TypeOK, NEW x \in AmendIds
  PROVE  StatuteOf((edges \ Drops(x)) \cup Adds(x)) = StatuteOf(edges)
<1>1. \A e \in Drops(x) \cup Adds(x) : e.basis = "Text"
  BY DropsFacts, AddsText, FoundingFacts DEF TextFacts
<1> QED
  BY <1>1 DEF StatuteOf

LEMMA RatifyText ==
  ASSUME TypeOK, TextFollowsArticleV, NEW x \in AmendIds, amendment[x] = "Proposed"
  PROVE  TextOf((edges \ Drops(x)) \cup Adds(x))
           = TextFor([amendment EXCEPT ![x] = "Ratified"])
<1>1. \A e \in Adds(x) : e.basis = "Text"
  BY AddsText DEF TextFacts
<1>2. TextOf((edges \ Drops(x)) \cup Adds(x)) = (TextOf(edges) \ Drops(x)) \cup Adds(x)
  BY <1>1 DEF TextOf
<1> QED
  BY <1>2, TextForRatified DEF TypeOK, TextFollowsArticleV

LEMMA NextShape == Shape /\ [Next]_vars => Shape'
<1> SUFFICES ASSUME Shape, [Next]_vars PROVE Shape'
  OBVIOUS
<1>0. TypeInv /\ TypeInv' /\ TypeOK /\ TypeOK'
  BY NextTypeInv DEF Shape, TypeInv
<1>1. CASE QuietStep
  BY <1>0, <1>1, QuietFrame
     DEF Shape, TextFollowsArticleV, StatutesShaped, CasesOnStatutes, BodiesCreated, TextOf
<1>2. CASE LawStep
  <2>1. bill.op \in Ops /\ Enact(bill.op) /\ UNCHANGED amendment
    BY <1>0, <1>2, LawStepEnacts
  <2>2. /\ edges' = EdgesAfter(bill.op) /\ live' = LiveAfter(bill.op)
        /\ challenged' = challenged \cap EdgesAfter(bill.op)
    BY <2>1 DEF Enact, SetEdges
  <2>3. TextFollowsArticleV'
    BY <1>0, <2>1, <2>2, EnactText DEF Shape, TextFollowsArticleV
  <2>4. StatutesShaped'
    BY <1>0, <2>1, <2>2, EnactStatutes DEF Shape, StatutesShaped
  <2>5. CasesOnStatutes'
    BY <2>2 DEF Shape, CasesOnStatutes
  <2>6. BodiesCreated'
    BY <1>0, <2>1, <2>2, EnactBodies DEF Shape, BodiesCreated
  <2> QED
    BY <1>0, <2>3, <2>4, <2>5, <2>6 DEF Shape
<1>3. ASSUME NEW e \in edges, Sue(e) PROVE Shape'
  BY <1>0, <1>3 DEF Sue, Shape, TextFollowsArticleV, StatutesShaped, CasesOnStatutes,
                    BodiesCreated, TextOf
<1>4. ASSUME NEW e \in challenged, Review(e) PROVE Shape'
  <2>1. edges' = Ruling(e) /\ challenged' = (challenged \ {e}) \cap Ruling(e)
        /\ UNCHANGED <<live, amendment>>
    BY <1>4 DEF Review
  <2>2. live \subseteq Agencies \cup Courts
    BY <1>0 DEF TypeOK
  <2> QED
    BY <1>0, <2>1, <2>2, RulingFacts
       DEF Shape, TextFollowsArticleV, StatutesShaped, CasesOnStatutes, BodiesCreated
<1>5. ASSUME NEW x \in AmendIds, Propose(x) PROVE Shape'
  <2>1. amendment' = [amendment EXCEPT ![x] = "Proposed"] /\ amendment[x] = "None"
        /\ UNCHANGED <<edges, live, challenged>>
    BY <1>5 DEF Propose, graphVars
  <2> QED
    BY <1>0, <2>1, TextForProposed
       DEF Shape, TypeOK, TextFollowsArticleV, StatutesShaped, CasesOnStatutes, BodiesCreated
<1>6. ASSUME NEW x \in AmendIds, Ratify(x) PROVE Shape'
  <2>1. /\ amendment' = [amendment EXCEPT ![x] = "Ratified"] /\ amendment[x] = "Proposed"
        /\ edges' = (edges \ Drops(x)) \cup Adds(x)
        /\ challenged' = challenged \cap edges'
        /\ UNCHANGED live
    BY <1>6 DEF Ratify, SetEdges
  <2>2. TextFollowsArticleV'
    BY <1>0, <2>1, RatifyText DEF Shape, TextFollowsArticleV
  <2>3. StatuteOf(edges') = StatuteOf(edges)
    BY <1>0, <2>1, RatifyStatutes
  <2>4. StatutesShaped' /\ BodiesCreated'
    BY <2>1, <2>3 DEF Shape, StatutesShaped, BodiesCreated, StatuteOf, CreationEdge, Law, Edge
  <2>5. CasesOnStatutes'
    BY <2>1 DEF Shape, CasesOnStatutes
  <2> QED
    BY <1>0, <2>2, <2>4, <2>5 DEF Shape
<1>7. CASE UNCHANGED vars
  BY <1>0, <1>7 DEF vars, Shape, TextFollowsArticleV, StatutesShaped, CasesOnStatutes,
                    BodiesCreated, TextOf
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, NextSplit

-----------------------------------------------------------------------------
(* Constant facts the properties read off the text                         *)

\* Text edges in the founding graph that no amendment drops.
Kept ==
  { Txt("People",    "Congress",      "Select",  "ElectHouse"),
    Txt("Congress",  "Executive",     "Select",  "ContingentElection"),
    Txt("Congress",  "VicePresident", "Select",  "ContingentElection"),
    Txt("Congress",  "Judiciary",     "Select",  "Consent"),
    Txt("VicePresident", "Executive", "Select",  "Succession"),
    Txt("Congress",  "Executive",     "Control", "Presentment"),
    Txt("Executive", "Congress",      "Control", "Veto"),
    Txt("Congress",  "Judiciary",     "Control", "Impeach"),
    Txt("Judiciary", "Congress",      "Control", "Review"),
    Txt("Executive", "Judiciary",     "Control", "Pardon"),
    Txt("Judiciary", "Executive",     "Control", "Review") }

NominateVPEdge == Txt("Executive", "VicePresident", "Select", "NominateVP")

LEMMA KeptInFounding == Kept \subseteq Founding
<1>1. Kept \subseteq FoundingPart1 \cup FoundingPart2 \cup FoundingPart3
  BY DEF Kept, FoundingPart1, FoundingPart2, FoundingPart3
<1> QED
  BY <1>1, FoundingSplit

LEMMA KeptNeverDropped ==
  ASSUME NEW x \in AmendIds PROVE Kept \cap Drops(x) = {}
BY DEF Kept, Drops, ArticleV, AmendIds, Txt, Edge

LEMMA ArticleVInFounding == ArticleV \subseteq Founding
<1>1. ArticleV \subseteq FoundingPart1
  BY DEF ArticleV, FoundingPart1
<1> QED
  BY <1>1, FoundingSplit

LEMMA NominateVPOnlyInXXV ==
  /\ NominateVPEdge \notin Founding
  /\ NominateVPEdge \notin Adds("XVII")
  /\ NominateVPEdge \in Adds("XXV")
<1>1. NominateVPEdge \notin FoundingPart1 \cup FoundingPart2 \cup FoundingPart3
  BY DEF NominateVPEdge, FoundingPart1, FoundingPart2, FoundingPart3, Txt, Edge
<1> QED
  BY <1>1, FoundingSplit DEF NominateVPEdge, Adds, Txt, Edge

\* What the text guarantees in every amendment state.
LEMMA TextKeeps ==
  ASSUME NEW a \in [AmendIds -> {"None", "Proposed", "Ratified"}]
  PROVE  /\ Kept \subseteq TextFor(a)
         /\ Mut # "M_NO_ARTV" => ArticleV \subseteq TextFor(a)
         /\ NominateVPEdge \in TextFor(a) <=> a["XXV"] = "Ratified"
<1>1. Kept \subseteq TextFor(a)
  BY KeptInFounding, KeptNeverDropped DEF TextFor, Applied, AmendIds
<1>2. Mut # "M_NO_ARTV" => ArticleV \subseteq TextFor(a)
  <2>1. ArticleV \cap Drops("XVII") = {} /\ (Mut # "M_NO_ARTV" => Drops("XXV") = {})
    BY DEF ArticleV, Drops, Txt, Edge
  <2> QED
    BY <2>1, ArticleVInFounding DEF TextFor, Applied
<1>3. NominateVPEdge \in TextFor(a) <=> a["XXV"] = "Ratified"
  BY NominateVPOnlyInXXV DEF TextFor, Applied
<1> QED
  BY <1>1, <1>2, <1>3

LEMMA UnconstitutionalLabels ==
  ASSUME NEW e, Unconstitutional(e) PROVE e.label \in ForbiddenLabels
BY DEF Unconstitutional, Violates, Doctrines, ForbiddenLabels

-----------------------------------------------------------------------------
(* Properties that follow from Shape alone (every mutation, or the one     *)
(* constant mutation that changes the text)                                *)

LEMMA EdgeBases ==
  ASSUME TypeOK, NEW e \in edges PROVE e.basis \in {"Text", "Statute"}
BY DEF TypeOK, EdgeType, Bases

LEMMA ShapeWriters ==
  ASSUME Mut # "M_CONGRESS_AMENDS", Shape PROVE ConstitutionWrittenByPeopleAndStates
<1> SUFFICES ASSUME NEW e \in edges, e.to = "Constitution"
             PROVE  e.from \in {"People", "States"}
  BY DEF ConstitutionWrittenByPeopleAndStates
<1>1. TypeOK /\ TextFollowsArticleV /\ StatutesShaped
  BY DEF Shape, TypeInv
<1>2. CASE e.basis = "Text"
  BY <1>1, <1>2, TextEdges DEF WriterFacts
<1>3. CASE e.basis = "Statute"
  BY <1>1, <1>3, PoolsAreNew DEF StatutesShaped, StatuteFacts, StatRec, Fixed
<1> QED
  BY <1>1, <1>2, <1>3, EdgeBases

LEMMA ShapeRanked ==
  ASSUME Mut # "M_CONGRESS_AMENDS", Shape PROVE GrantFollowsChainExceptXXV
<1> SUFFICES ASSUME NEW e \in InnerGrant, e.label # "NominateVP"
             PROVE  Rank(e.from) < Rank(e.to)
  BY DEF GrantFollowsChainExceptXXV
<1>1. TypeOK /\ TextFollowsArticleV /\ StatutesShaped
  BY DEF Shape, TypeInv
<1>2. /\ e \in edges /\ e.kind \in GrantKinds
      /\ e.from \notin {"People", "States"} /\ e.to \notin {"People", "States"}
  <2>1. e \in GrantEdges /\ e.from \in LiveNodes \ {"People", "States"}
        /\ e.to \in LiveNodes \ {"People", "States"}
    BY DEF InnerGrant, Among
  <2> QED
    BY <2>1 DEF GrantEdges, OfKind
<1>3. CASE e.basis = "Text"
  BY <1>1, <1>2, <1>3, TextEdges DEF WriterFacts
<1>4. CASE e.basis = "Statute"
  <2>1. e.from \in Upper /\ e.to \in Agencies \cup Courts
    BY <1>1, <1>2, <1>4 DEF StatutesShaped, StatuteFacts, StatRec
  <2>2. Rank(e.to) = 6
    BY <2>1, PoolsAreNew DEF Rank, Fixed
  <2> QED
    BY <2>1, <2>2 DEF Rank, Upper
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, EdgeBases

LEMMA ShapeArticleV ==
  ASSUME Mut # "M_NO_ARTV", Shape PROVE ArticleVStands
BY TextKeeps DEF Shape, TypeInv, TypeOK, TextFollowsArticleV, TextOf, ArticleVStands

LEMMA ShapeNominationLoop ==
  ASSUME Shape PROVE NominationLoopIffXXV
<1>1. TypeOK /\ TextFollowsArticleV
  BY DEF Shape, TypeInv
<1>2. NominateVPEdge \in edges <=> NominateVPEdge \in TextFor(amendment)
  BY <1>1 DEF TextFollowsArticleV, TextOf, NominateVPEdge, Txt, Edge
<1>3. Txt("VicePresident", "Executive", "Select", "Succession") \in TextFor(amendment)
  BY <1>1, TextKeeps DEF TypeOK, Kept
<1> QED
  BY <1>1, <1>2, <1>3, TextKeeps
     DEF TypeOK, TextFollowsArticleV, TextOf, NominationLoopIffXXV, NominateVPEdge

LEMMA ShapeKept ==
  ASSUME Shape PROVE Kept \subseteq edges
BY TextKeeps DEF Shape, TypeInv, TypeOK, TextFollowsArticleV, TextOf

LEMMA ShapeMutualChecks ==
  ASSUME Shape PROVE MutualChecks
<1>1. Kept \subseteq edges
  BY ShapeKept
<1> QED
  BY <1>1 DEF MutualChecks, Between, ControlEdges, OfKind, Kept, Branches, Txt, Edge

LEMMA ShapeCreatedByLaw ==
  ASSUME Shape PROVE EveryBodyIsCreatedByLaw
BY DEF Shape, BodiesCreated, EveryBodyIsCreatedByLaw, Between, CreationEdge, Law, Edge

LEMMA ShapeNamedPaths ==
  ASSUME Shape PROVE NamedPathsFromPeople
<1> SUFFICES ASSUME NEW n \in GovNodes
             PROVE  {Txt("People", "Congress", "Select", "ElectHouse")} \cup FromCongress(n)
                      \subseteq edges
  BY DEF NamedPathsFromPeople
<1>1. Kept \subseteq edges /\ TypeOK /\ BodiesCreated
  BY ShapeKept DEF Shape, TypeInv
<1>2. CASE n \in Branches \cup {"VicePresident"}
  <2>1. FromCongress(n) \subseteq Kept
    \* CASE is encoded as a choice among every arm whose guard holds, so each
    \* case needs the arm `n \in Agencies` ruled out: PoolsAreNew does that.
    <3>1. CASE n = "Congress"       BY <3>1, PoolsAreNew DEF FromCongress, Kept, Fixed
    <3>2. CASE n = "Executive"      BY <3>2, PoolsAreNew DEF FromCongress, Kept, Fixed
    <3>3. CASE n = "VicePresident"  BY <3>3, PoolsAreNew DEF FromCongress, Kept, Fixed
    <3>4. CASE n = "Judiciary"      BY <3>4, PoolsAreNew DEF FromCongress, Kept, Fixed
    <3> QED
      BY <1>2, <3>1, <3>2, <3>3, <3>4 DEF Branches
  <2>2. Txt("People", "Congress", "Select", "ElectHouse") \in Kept
    BY DEF Kept
  <2> QED
    BY <1>1, <2>1, <2>2
<1>3. CASE n \in live
  <2>1. n \in Agencies \cup Courts /\ n \notin Fixed /\ CreationEdge(n) \in edges
    BY <1>1, <1>3, PoolsAreNew DEF TypeOK, BodiesCreated
  <2>2. FromCongress(n) = {CreationEdge(n)}
    BY <2>1 DEF FromCongress, CreationEdge, Fixed
  <2> QED
    BY <1>1, <2>1, <2>2 DEF Kept
<1> QED
  BY <1>2, <1>3 DEF GovNodes

LEMMA ShapePeopleDoor ==
  ASSUME Shape PROVE PeoplePowerGoesThroughConstitution
<1> SUFFICES ASSUME NEW e \in edges, e.from = "People", e.kind \in {"Power", "Amend"}
             PROVE  e.to = "Constitution"
  BY DEF PeoplePowerGoesThroughConstitution
<1>1. TypeOK /\ TextFollowsArticleV /\ StatutesShaped
  BY DEF Shape, TypeInv
<1>2. CASE e.basis = "Text"
  BY <1>1, <1>2, TextEdges DEF TextFacts
<1>3. CASE e.basis = "Statute"
  BY <1>1, <1>3 DEF StatutesShaped, StatuteFacts, StatRec, Upper
<1> QED
  BY <1>1, <1>2, <1>3, EdgeBases

LEMMA ShapeOverstep ==
  ASSUME Shape PROVE OnlyStatutesOverstep
<1> SUFFICES ASSUME NEW e \in edges, Unconstitutional(e) PROVE e.basis = "Statute"
  BY DEF OnlyStatutesOverstep
<1>1. TypeOK /\ TextFollowsArticleV
  BY DEF Shape, TypeInv
<1>2. e.label \in ForbiddenLabels
  BY UnconstitutionalLabels
<1>3. e.basis # "Text"
  BY <1>1, <1>2, TextEdges DEF TextFacts
<1> QED
  BY <1>1, <1>3, EdgeBases
-----------------------------------------------------------------------------
(* What a ruling and a ratification leave of the statutory edges            *)

LEMMA ForbiddenRemove ==
  ASSUME NEW e, Forbidden(e), e.label = "Remove" PROVE e.from = "Congress"
BY DEF Forbidden, Violates, Doctrines

\* A ruling adds at most the at-will removal edge, and keeps every edge
\* whose label no doctrine names and that is not executive power.
LEMMA RulingFrame ==
  ASSUME TypeOK, NEW e \in edges
  PROVE  /\ \A f \in Ruling(e) : f \in edges \/ f = Law("Executive", e.to, "Control", "Remove")
         /\ \A f \in edges :
              f.label \notin ForbiddenLabels \cup {"ExecutivePower", "Direct"} => f \in Ruling(e)
<1>1. CASE ~Strikes(e)
  BY <1>1 DEF Ruling
<1>2. CASE Strikes(e)
  <2>1. e.label \in ForbiddenLabels
    BY <1>2, ForbiddenLabelsOf DEF Strikes
  <2> QED
    BY <1>2, <2>1 DEF Ruling, Sever, Law, Edge
<1> QED
  BY <1>1, <1>2

LEMMA RatifyFrame ==
  ASSUME TypeOK, NEW x \in AmendIds, NEW f, f.basis = "Statute"
  PROVE  f \in (edges \ Drops(x)) \cup Adds(x) <=> f \in edges
<1>1. \A g \in Drops(x) \cup Adds(x) : g.basis = "Text"
  BY DropsFacts, AddsText, FoundingFacts DEF TextFacts
<1> QED
  BY <1>1

-----------------------------------------------------------------------------
(* EdgesConnectLiveNodes: every statutory edge runs into a live body, and  *)
(* a bill in flight still makes sense. Needs the precondition (M_APPLICABLE).*)

StatutesToLive == \A e \in edges : e.basis = "Statute" => e.to \in live
BillApplies    == bill.stage # "None" => Precondition(bill.op)
LiveInv        == StatutesToLive /\ BillApplies

LEMMA InitLiveInv == Init => LiveInv
BY FoundingFacts DEF Init, LiveInv, StatutesToLive, BillApplies, NoBill, TextFacts

LEMMA LiveConnects ==
  ASSUME Shape, LiveInv PROVE EdgesConnectLiveNodes
<1> SUFFICES ASSUME NEW e \in edges PROVE e.from \in LiveNodes /\ e.to \in LiveNodes
  BY DEF EdgesConnectLiveNodes
<1>1. TypeOK /\ TextFollowsArticleV /\ StatutesShaped
  BY DEF Shape, TypeInv
<1>2. CASE e.basis = "Text"
  BY <1>1, <1>2, TextEdges DEF TextFacts, LiveNodes
<1>3. CASE e.basis = "Statute"
  BY <1>1, <1>3 DEF StatutesShaped, StatuteFacts, StatRec, Upper, LiveNodes, Fixed,
                    LiveInv, StatutesToLive
<1> QED
  BY <1>1, <1>2, <1>3, EdgeBases

LEMMA EnactLive ==
  ASSUME TypeOK, StatutesToLive, NEW op \in Ops, Precondition(op)
  PROVE  \A e \in EdgesAfter(op) : e.basis = "Statute" => e.to \in LiveAfter(op)
<1>1. CASE op.name = "CreateAgency"
  BY <1>1, EnactCases, AgencyEdgesShape DEF StatutesToLive
<1>2. CASE op.name = "EstablishCourt"
  BY <1>2, EnactCases, CourtEdgesShape DEF StatutesToLive
<1>3. CASE op.name \in {"AbolishAgency", "AbolishCourt"}
  BY <1>3, EnactCases DEF StatutesToLive, Touching
<1>4. CASE op.name \in {"LegislativeVeto", "CutPay"}
  BY <1>4, EnactCases DEF StatutesToLive, Precondition, Law, Edge
<1>5. CASE op.name = "StripJurisdiction"
  BY <1>5, EnactCases DEF StatutesToLive
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, OpsCases

\* A bill's precondition survives a step that keeps the bodies, adds no
\* legislative veto or pay cut, and removes no appeal.
LEMMA PreconditionStable ==
  ASSUME NEW op \in Ops, Precondition(op), live' = live,
         \A t : Law("Congress", t, "Control", "LegislativeVeto") \in edges'
                => Law("Congress", t, "Control", "LegislativeVeto") \in edges,
         \A t : Law("Congress", t, "Control", "DiminishPay") \in edges'
                => Law("Congress", t, "Control", "DiminishPay") \in edges,
         \A t : Law("Judiciary", t, "Control", "Appeal") \in edges
                => Law("Judiciary", t, "Control", "Appeal") \in edges'
  PROVE  Precondition(op)'
<1>1. CASE op.name \in {"CreateAgency", "EstablishCourt", "AbolishAgency", "AbolishCourt"}
  BY <1>1 DEF Precondition
<1>2. CASE op.name = "LegislativeVeto"
  BY <1>2 DEF Precondition
<1>3. CASE op.name = "CutPay"
  BY <1>3 DEF Precondition
<1>4. CASE op.name = "StripJurisdiction"
  BY <1>4 DEF Precondition
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, OpsCases

LEMMA NextLiveInv ==
  ASSUME Mut # "M_APPLICABLE", Shape, Shape', LiveInv, [Next]_vars
  PROVE  LiveInv'
<1>0. TypeInv /\ TypeOK /\ TypeOK' /\ StatutesShaped /\ CasesOnStatutes
  BY DEF Shape, TypeInv
<1>1. ASSUME NEW op \in Ops, Pass(op) PROVE LiveInv'
  BY <1>1 DEF Pass, Applicable, LiveInv, StatutesToLive, BillApplies, Precondition, graphVars
<1>2. CASE Veto \/ PocketVeto \/ BillFails
  <2>1. /\ UNCHANGED <<edges, live>>
        /\ \/ bill' = NoBill
           \/ bill.stage = "Presented" /\ bill' = [bill EXCEPT !.stage = "Vetoed"]
    BY <1>2 DEF Veto, PocketVeto, BillFails, graphVars
  <2>2. bill'.stage # "None" => bill'.op = bill.op /\ bill.stage # "None"
    BY <1>0, <2>1 DEF NoBill, TypeOK
  <2> QED
    BY <2>1, <2>2 DEF LiveInv, StatutesToLive, BillApplies, Precondition
<1>3. CASE QuietStep /\ ~(\E op \in Ops : Pass(op)) /\ ~(Veto \/ PocketVeto \/ BillFails)
  <2>1. UNCHANGED <<edges, live, bill>>
    BY <1>3 DEF QuietStep, Adjourn, Convene, ConveneByPresident,
       ElectPresident, ContingentElection, PresidentLeaves, ElectVicePresident,
       ContingentElectionVP, VicePresidentLeaves, Succeed, NominateVP, ConfirmVP, RejectVP,
       Nominate, Consent, Reject, Remove, Resign, Impeach, Convict, Acquit, Exercise,
       graphVars, lawVars
  <2> QED
    BY <2>1 DEF LiveInv, StatutesToLive, BillApplies, Precondition
<1>4. CASE LawStep
  <2>1. bill.op \in Ops /\ Enact(bill.op) /\ bill' = NoBill
    BY <1>0, <1>4, LawStepEnacts DEF LawStep, Sign, Lapse, Override
  <2>2. Precondition(bill.op)
    BY <1>4 DEF LawStep, Sign, Lapse, Override, Rechecked, Applicable, LiveInv, BillApplies
  <2>3. edges' = EdgesAfter(bill.op) /\ live' = LiveAfter(bill.op)
    BY <2>1 DEF Enact, SetEdges
  <2> QED
    BY <1>0, <2>1, <2>2, <2>3, EnactLive DEF LiveInv, StatutesToLive, BillApplies, NoBill
<1>5. ASSUME NEW e \in edges, Sue(e) PROVE LiveInv'
  <2>1. UNCHANGED <<edges, live, bill>>
    BY <1>5 DEF Sue, lawVars
  <2> QED
    BY <2>1 DEF LiveInv, StatutesToLive, BillApplies, Precondition
<1>6. ASSUME NEW e \in challenged, Review(e) PROVE LiveInv'
  <2>1. e \in edges /\ e.basis = "Statute" /\ e.to \in live
    BY <1>0 DEF TypeOK, CasesOnStatutes, LiveInv, StatutesToLive
  <2>2. edges' = Ruling(e) /\ UNCHANGED <<live, bill>>
    BY <1>6 DEF Review, lawVars
  <2>3. StatutesToLive'
    BY <1>0, <2>1, <2>2, RulingFrame DEF LiveInv, StatutesToLive, Law, Edge
  <2>4. BillApplies'
    <3>1. /\ \A f \in Ruling(e) : f \in edges \/ f.label = "Remove"
          /\ \A f \in edges : f.label \in {"Appeal"} => f \in Ruling(e)
      BY <1>0, <2>1, RulingFrame DEF Law, Edge, ForbiddenLabels
    <3>2. bill.stage # "None" => bill.op \in Ops
      BY <1>0 DEF TypeInv, BillIsReal
    <3> QED
      BY <2>2, <3>1, <3>2, PreconditionStable DEF LiveInv, BillApplies, Law, Edge
  <2> QED
    BY <2>3, <2>4 DEF LiveInv
<1>7. ASSUME NEW x \in AmendIds, Propose(x) PROVE LiveInv'
  BY <1>7 DEF Propose, LiveInv, StatutesToLive, BillApplies, Precondition, graphVars, lawVars
<1>8. ASSUME NEW x \in AmendIds, Ratify(x) PROVE LiveInv'
  <2>1. edges' = (edges \ Drops(x)) \cup Adds(x) /\ UNCHANGED <<live, bill>>
    BY <1>8 DEF Ratify, SetEdges, lawVars
  <2>2. \A f : f.basis = "Statute" => (f \in edges' <=> f \in edges)
    BY <1>0, <2>1, RatifyFrame
  <2>3. \A f \in edges' : f.basis = "Statute" => f \in edges
    BY <2>2
  <2>4. StatutesToLive'
    BY <2>1, <2>3 DEF LiveInv, StatutesToLive
  <2>5. bill.stage # "None" => bill.op \in Ops
    BY <1>0 DEF TypeInv, BillIsReal
  <2>6. BillApplies'
    BY <2>1, <2>2, <2>5, PreconditionStable DEF LiveInv, BillApplies, Law, Edge
  <2> QED
    BY <2>4, <2>6 DEF LiveInv
<1>9. CASE UNCHANGED vars
  BY <1>9 DEF vars, LiveInv, StatutesToLive, BillApplies, Precondition
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, NextSplit DEF QuietStep

-----------------------------------------------------------------------------
(* OfficesAreLive: inductive by itself; needs Stuart v. Laird (M_NOSTUART) *)

LEMMA InitOffices == Init => OfficesAreLive
BY DEF Init, OfficesAreLive

LEMMA NextOffices ==
  ASSUME Mut # "M_NOSTUART", TypeInv, OfficesAreLive, [Next]_vars
  PROVE  OfficesAreLive'
<1>1. ASSUME NEW n \in Agencies \cup Courts,
             Nominate(n) \/ Consent(n) \/ Reject(n) \/ Remove(n) \/ Resign(n)
      PROVE  OfficesAreLive'
  <2>1. n # "VicePresident" /\ TypeOK
    BY PoolsAreNew DEF Fixed, TypeInv
  <2> QED
    BY <1>1, <2>1 DEF Nominate, Consent, Reject, Remove, Resign, OfficesAreLive, graphVars
<1>2. CASE LawStep
  <2>1. \E op \in Ops : Enact(op)
    BY <1>2, LawStepEnacts
  <2> QED
    BY <2>1 DEF Enact, Unseat, OfficesAreLive
<1>3. CASE \/ \E op \in Ops : Pass(op)
           \/ Veto \/ PocketVeto \/ BillFails \/ Adjourn \/ Convene \/ ConveneByPresident
           \/ ElectPresident \/ ContingentElection \/ PresidentLeaves
           \/ ElectVicePresident \/ ContingentElectionVP \/ VicePresidentLeaves \/ Succeed
           \/ NominateVP \/ ConfirmVP \/ RejectVP
           \/ \E n \in Offices \cup {"Judiciary"} : Impeach(n)
           \/ Convict \/ Acquit
           \/ \E e \in edges : Sue(e) \/ Exercise(e)
           \/ \E e \in challenged : Review(e)
           \/ \E x \in AmendIds : Propose(x) \/ Ratify(x)
  BY <1>3 DEF Pass, Veto, PocketVeto, BillFails, Adjourn, Convene, ConveneByPresident,
              ElectPresident, ContingentElection, PresidentLeaves, ElectVicePresident,
              ContingentElectionVP, VicePresidentLeaves, Succeed, NominateVP, ConfirmVP,
              RejectVP, Impeach, Convict, Acquit, Sue, Exercise, Review, Propose, Ratify,
              OfficesAreLive, graphVars, officeVars
<1>4. CASE UNCHANGED vars
  BY <1>4 DEF vars, OfficesAreLive
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next, LawStep

-----------------------------------------------------------------------------
(* ExecutorsAreRemovable: needs the severance rules (M_SEVER_PLAIN)        *)

ExecIn(E, a)    == Law("Executive", a, "Power", "ExecutivePower") \in E
RemovableIn(E, a) == RemovalEdges(a) \cap E # {}
RemovableAll(E) == \A a \in Agencies : ExecIn(E, a) => RemovableIn(E, a)

LEMMA RemovableIsAll == ExecutorsAreRemovable <=> RemovableAll(edges)
BY DEF ExecutorsAreRemovable, RemovableAll, ExecIn, RemovableIn, ExecPower

LEMMA InitRemovable == Init => ExecutorsAreRemovable
<1>1. Init => \A a \in Agencies : ~ExecIn(edges, a)
  BY FoundingFacts DEF Init, ExecIn, Law, Edge, TextFacts
<1> QED
  BY <1>1, RemovableIsAll DEF RemovableAll

LEMMA EnactRemovable ==
  ASSUME TypeOK, RemovableAll(edges), NEW op \in Ops
  PROVE  RemovableAll(EdgesAfter(op))
<1>1. CASE op.name = "CreateAgency"
  <2>1. RemovalEdges(op.target) \cap AgencyEdges(op.target, op.exec, op.remover, op.vesting) # {}
    BY <1>1, OpsCases DEF RemovalEdges, AgencyEdges, Removers
  <2>2. \A f \in AgencyEdges(op.target, op.exec, op.remover, op.vesting) : f.to = op.target
    BY <1>1, OpsCases, AgencyEdgesShape
  <2> QED
    BY <1>1, <2>1, <2>2, EnactCases DEF RemovableAll, ExecIn, RemovableIn, Law, Edge
<1>2. CASE op.name = "EstablishCourt"
  <2>1. \A f \in CourtEdges(op.target) : f.to = op.target
    BY <1>2, OpsCases, CourtEdgesShape
  <2>2. op.target \notin Agencies
    BY <1>2, OpsCases, PoolsDisjoint
  <2> QED
    BY <1>2, <2>1, <2>2, EnactCases DEF RemovableAll, ExecIn, RemovableIn, Law, Edge
<1>3. CASE op.name \in {"AbolishAgency", "AbolishCourt"}
  <2>1. op.target \notin {"Executive", "Congress"}
    BY <1>3, OpsCases, PoolsAreNew DEF Fixed
  <2> QED
    BY <1>3, <2>1, EnactCases DEF RemovableAll, ExecIn, RemovableIn, RemovalEdges, Touching,
                                  Law, Edge
<1>4. CASE op.name \in {"LegislativeVeto", "CutPay", "StripJurisdiction"}
  BY <1>4, EnactCases DEF RemovableAll, ExecIn, RemovableIn, RemovalEdges, Law, Edge
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, OpsCases

LEMMA RulingRemovable ==
  ASSUME Mut # "M_SEVER_PLAIN", TypeOK, RemovableAll(edges), NEW e \in edges
  PROVE  RemovableAll(Ruling(e))
<1>1. CASE ~Strikes(e)
  BY <1>1 DEF Ruling
<1>2. CASE Strikes(e) /\ e.label = "RemoveForCause"
  <2>1. Ruling(e) = (edges \ {e}) \cup {Law("Executive", e.to, "Control", "Remove")}
    BY <1>2 DEF Ruling, Sever
  <2> QED
    BY <2>1, <1>2 DEF RemovableAll, ExecIn, RemovableIn, RemovalEdges, Law, Edge
<1>3. CASE Strikes(e) /\ e.label = "Remove"
  <2>1. e.from = "Congress"
    BY <1>3, ForbiddenRemove DEF Strikes
  <2>2. Ruling(e) = edges \ {Law("Executive", e.to, "Power", "ExecutivePower"),
                             Law("Executive", e.to, "Control", "Direct")}
    BY <1>3, <2>1 DEF Ruling, Sever
  <2> QED
    BY <2>2 DEF RemovableAll, ExecIn, RemovableIn, RemovalEdges, Law, Edge
<1>4. CASE Strikes(e) /\ e.label \notin {"RemoveForCause", "Remove"}
  <2>1. e.label \in ForbiddenLabels
    BY <1>4, ForbiddenLabelsOf DEF Strikes
  <2>2. Ruling(e) = edges \ {e}
    BY <1>4 DEF Ruling, Sever
  <2> QED
    BY <1>4, <2>1, <2>2 DEF RemovableAll, ExecIn, RemovableIn, RemovalEdges, Law, Edge,
                            ForbiddenLabels
<1> QED
  BY <1>1, <1>2, <1>3, <1>4

LEMMA NextRemovable ==
  ASSUME Mut # "M_SEVER_PLAIN", Shape, ExecutorsAreRemovable, [Next]_vars
  PROVE  ExecutorsAreRemovable'
<1>0. TypeInv /\ TypeOK /\ CasesOnStatutes /\ RemovableAll(edges)
  BY RemovableIsAll DEF Shape, TypeInv
<1>1. ExecutorsAreRemovable' <=> RemovableAll(edges')
  BY DEF ExecutorsAreRemovable, RemovableAll, ExecIn, RemovableIn, ExecPower
<1>2. CASE QuietStep \/ (\E e \in edges : Sue(e)) \/ (\E x \in AmendIds : Propose(x))
            \/ UNCHANGED vars
  <2>1. edges' = edges
    BY <1>2, QuietFrame DEF Sue, Propose, vars, graphVars
  <2> QED
    BY <1>0, <1>1, <2>1
<1>3. CASE LawStep
  <2>1. bill.op \in Ops /\ edges' = EdgesAfter(bill.op)
    BY <1>0, <1>3, LawStepEnacts DEF Enact, SetEdges
  <2> QED
    BY <1>0, <1>1, <2>1, EnactRemovable
<1>4. ASSUME NEW e \in challenged, Review(e) PROVE ExecutorsAreRemovable'
  <2>1. e \in edges /\ edges' = Ruling(e)
    BY <1>0, <1>4 DEF Review, TypeOK
  <2> QED
    BY <1>0, <1>1, <2>1, RulingRemovable
<1>5. ASSUME NEW x \in AmendIds, Ratify(x) PROVE ExecutorsAreRemovable'
  <2>1. edges' = (edges \ Drops(x)) \cup Adds(x)
    BY <1>5 DEF Ratify, SetEdges
  <2>2. \A f : f.basis = "Statute" => (f \in edges' <=> f \in edges)
    BY <1>0, <2>1, RatifyFrame
  <2> QED
    BY <1>0, <1>1, <2>2 DEF RemovableAll, ExecIn, RemovableIn, RemovalEdges, Law, Edge
<1> QED
  BY <1>2, <1>3, <1>4, <1>5, NextSplit
-----------------------------------------------------------------------------
(* The flags: what each guard keeps out of stray and breaches              *)

\* Each conjunct is the flag the guard of one mutation keeps down; the
\* invariant holds under every mutation, and each theorem below picks the
\* conjunct its hypothesis enables.
FlagInv ==
  /\ Mut # "M_OFFEDGE"  => "OffGraph" \notin stray
  /\ Mut # "M_INACTIVE" => "Vacant" \notin stray
  /\ Mut # "M_OFFEDGE"  => "GoodBehaviour" \notin breaches
  /\ Mut # "M_NOPOCKET" => "PocketVeto" \notin breaches
  /\ \A d \in Doctrines : (Mut # "M_UPHOLD" /\ InForce(d)) => d \notin breaches

LEMMA InitFlags == Init => FlagInv
BY DEF Init, FlagInv

LEMMA FireStray ==
  ASSUME NEW e, Fire(e)
  PROVE  /\ Mut # "M_OFFEDGE"  => ("OffGraph" \in stray' => "OffGraph" \in stray)
         /\ Mut # "M_INACTIVE" => ("Vacant" \in stray' => "Vacant" \in stray)
BY DEF Fire, OnGraph, Held, StrayOf

\* A court that upholds an edge under a doctrine in force has found it
\* does not violate that doctrine.
LEMMA UpheldIsLawful ==
  ASSUME Mut # "M_UPHOLD", NEW e, ~Strikes(e), NEW d \in Doctrines, InForce(d)
  PROVE  d \notin ViolatedBy(e)
BY DEF Strikes, Forbidden, ViolatedBy

\* No removal edge runs into a court, so firing one at a judge is off the graph.
LEMMA NoJudgeRemoval ==
  ASSUME Mut # "M_OFFEDGE", TypeOK, StatutesShaped, NEW n \in Courts, NEW e \in RemovalEdges(n),
         Fire(e)
  PROVE  FALSE
<1>1. e \in edges /\ e.basis = "Statute" /\ e.label \in {"Remove", "RemoveForCause"} /\ e.to = n
  BY DEF Fire, OnGraph, RemovalEdges, Law, Edge
<1> QED
  BY <1>1, PoolsDisjoint DEF StatutesShaped, StatuteFacts

LEMMA NextFlags ==
  ASSUME TypeOK, StatutesShaped, FlagInv, [Next]_vars
  PROVE  FlagInv'
<1>1. CASE UNCHANGED <<stray, breaches>>
  BY <1>1 DEF FlagInv
<1>2. CASE (\E e : Fire(e)) /\ UNCHANGED breaches
  BY <1>2, FireStray DEF FlagInv
<1>3. ASSUME NEW op \in Ops, Pass(op) PROVE FlagInv'
  BY <1>3, <1>2 DEF Pass
<1>4. CASE Sign \/ Override \/ Veto \/ PocketVeto \/ Adjourn \/ Convene \/ ConveneByPresident
           \/ ElectPresident \/ ContingentElection \/ ElectVicePresident
           \/ ContingentElectionVP \/ Succeed \/ NominateVP \/ ConfirmVP \/ RejectVP
           \/ Convict \/ Acquit
  BY <1>4, <1>2 DEF Sign, Override, Veto, PocketVeto, Adjourn, Convene, ConveneByPresident,
                    ElectPresident, ContingentElection, ElectVicePresident,
                    ContingentElectionVP, Succeed, NominateVP, ConfirmVP, RejectVP,
                    Convict, Acquit
<1>5. CASE BillFails \/ VicePresidentLeaves \/ PresidentLeaves
  BY <1>5, <1>1 DEF BillFails, VicePresidentLeaves, PresidentLeaves
<1>6. CASE Lapse
  <2>1. Fire(Txt("Congress", "Executive", "Control", "Presentment"))
    BY <1>6 DEF Lapse
  <2>2. Mut # "M_NOPOCKET" => breaches' = breaches
    BY <1>6 DEF Lapse, CanReturn
  <2>3. breaches' \subseteq breaches \cup {"PocketVeto"}
    BY <1>6 DEF Lapse
  <2> QED
    BY <2>1, <2>2, <2>3, FireStray DEF FlagInv, Doctrines
<1>7. ASSUME NEW n \in Agencies \cup Courts,
             Nominate(n) \/ Consent(n) \/ Reject(n) \/ Remove(n) \/ Resign(n)
      PROVE  FlagInv'
  <2>1. CASE Nominate(n) \/ Consent(n) \/ Reject(n)
    BY <2>1, <1>2 DEF Nominate, Consent, Reject
  <2>2. CASE Resign(n)
    BY <2>2, <1>1 DEF Resign
  <2>3. CASE Remove(n)
    <3>1. PICK e \in RemovalEdges(n) : Fire(e)
      BY <2>3 DEF Remove
    <3>2. Mut # "M_OFFEDGE" => breaches' = breaches
      BY <2>3, <3>1, NoJudgeRemoval DEF Remove
    <3>3. breaches' \subseteq breaches \cup {"GoodBehaviour"}
      BY <2>3 DEF Remove
    <3> QED
      BY <3>1, <3>2, <3>3, FireStray DEF FlagInv, Doctrines
  <2> QED
    BY <1>7, <2>1, <2>2, <2>3
<1>8. ASSUME NEW n \in Offices \cup {"Judiciary"}, Impeach(n) PROVE FlagInv'
  BY <1>8, <1>2 DEF Impeach
<1>9. ASSUME NEW e \in edges, Sue(e) \/ Exercise(e) PROVE FlagInv'
  BY <1>9, <1>2 DEF Sue, Exercise
<1>10. ASSUME NEW e \in challenged, Review(e) PROVE FlagInv'
  <2>1. Fire(Txt("Judiciary", "Congress", "Control", "Review"))
    BY <1>10 DEF Review
  <2>2. breaches' = IF Strikes(e) THEN breaches ELSE breaches \cup ViolatedBy(e)
    BY <1>10 DEF Review
  <2>3. \A d \in Doctrines : (Mut # "M_UPHOLD" /\ InForce(d)) => (d \in breaches' => d \in breaches)
    BY <2>2, UpheldIsLawful
  <2>4. ViolatedBy(e) \subseteq Doctrines
    BY DEF ViolatedBy
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, FireStray DEF FlagInv, Doctrines
<1>11. ASSUME NEW x \in AmendIds, Propose(x) \/ Ratify(x) PROVE FlagInv'
  BY <1>11, <1>2 DEF Propose, Ratify
<1> QED
  BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF Next, vars

-----------------------------------------------------------------------------
(* The theorems: each property always holds, under the mutations that do   *)
(* not break it                                                            *)

LEMMA ShapeAlways == Spec => []Shape
<1>1. Shape /\ [Next]_vars => Shape'
  BY NextShape
<1> QED
  BY InitShape, <1>1, PTL DEF Spec

THEOREM TypeOKAlways == Spec => []TypeOK
<1>1. Shape => TypeOK
  BY DEF Shape, TypeInv
<1> QED
  BY ShapeAlways, <1>1, PTL

THEOREM TextFollowsArticleVAlways == Spec => []TextFollowsArticleV
<1>1. Shape => TextFollowsArticleV
  BY DEF Shape
<1> QED
  BY ShapeAlways, <1>1, PTL

THEOREM EdgesConnectLiveNodesAlways ==
  ASSUME Mut # "M_APPLICABLE" PROVE Spec => []EdgesConnectLiveNodes
<1>1. Shape /\ LiveInv /\ [Next]_vars => (Shape /\ LiveInv)'
  BY NextShape, NextLiveInv
<1> QED
  BY InitShape, InitLiveInv, <1>1, LiveConnects, PTL DEF Spec

THEOREM OfficesAreLiveAlways ==
  ASSUME Mut # "M_NOSTUART" PROVE Spec => []OfficesAreLive
<1>1. Shape /\ OfficesAreLive /\ [Next]_vars => (Shape /\ OfficesAreLive)'
  BY NextShape, NextOffices DEF Shape
<1> QED
  BY InitShape, InitOffices, <1>1, PTL DEF Spec

THEOREM ArticleVStandsAlways ==
  ASSUME Mut # "M_NO_ARTV" PROVE Spec => []ArticleVStands
<1>1. Shape => ArticleVStands
  BY ShapeArticleV
<1> QED
  BY ShapeAlways, <1>1, PTL

THEOREM ConstitutionWrittenAlways ==
  ASSUME Mut # "M_CONGRESS_AMENDS" PROVE Spec => []ConstitutionWrittenByPeopleAndStates
<1>1. Shape => ConstitutionWrittenByPeopleAndStates
  BY ShapeWriters
<1> QED
  BY ShapeAlways, <1>1, PTL

THEOREM GrantFollowsChainExceptXXVAlways ==
  ASSUME Mut # "M_CONGRESS_AMENDS" PROVE Spec => []GrantFollowsChainExceptXXV
<1>1. Shape => GrantFollowsChainExceptXXV
  BY ShapeRanked
<1> QED
  BY ShapeAlways, <1>1, PTL

THEOREM OnlyStatutesOverstepAlways == Spec => []OnlyStatutesOverstep
BY ShapeAlways, ShapeOverstep, PTL

THEOREM NominationLoopIffXXVAlways == Spec => []NominationLoopIffXXV
BY ShapeAlways, ShapeNominationLoop, PTL

THEOREM EveryBodyIsCreatedByLawAlways == Spec => []EveryBodyIsCreatedByLaw
BY ShapeAlways, ShapeCreatedByLaw, PTL

THEOREM NamedPathsFromPeopleAlways == Spec => []NamedPathsFromPeople
BY ShapeAlways, ShapeNamedPaths, PTL

THEOREM PeoplePowerGoesThroughConstitutionAlways ==
  Spec => []PeoplePowerGoesThroughConstitution
BY ShapeAlways, ShapePeopleDoor, PTL

THEOREM MutualChecksAlways == Spec => []MutualChecks
BY ShapeAlways, ShapeMutualChecks, PTL

THEOREM ExecutorsAreRemovableAlways ==
  ASSUME Mut # "M_SEVER_PLAIN" PROVE Spec => []ExecutorsAreRemovable
<1>1. Shape /\ ExecutorsAreRemovable /\ [Next]_vars => (Shape /\ ExecutorsAreRemovable)'
  BY NextShape, NextRemovable
<1> QED
  BY InitShape, InitRemovable, <1>1, PTL DEF Spec

LEMMA FlagsAlways == Spec => [](Shape /\ FlagInv)
<1>1. Shape /\ FlagInv /\ [Next]_vars => (Shape /\ FlagInv)'
  BY NextShape, NextFlags DEF Shape, TypeInv
<1> QED
  BY InitShape, InitFlags, <1>1, PTL DEF Spec

THEOREM BuckleyHonouredAlways ==
  ASSUME Mut # "M_UPHOLD", Mut # "M_PREBUCKLEY" PROVE Spec => []BuckleyHonoured
<1>1. Shape /\ FlagInv => BuckleyHonoured
  BY DEF FlagInv, BuckleyHonoured, InForce, Doctrines
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM SeilaLawHonouredAlways ==
  ASSUME Mut # "M_UPHOLD", Mut # "M_HUMPHREY" PROVE Spec => []SeilaLawHonoured
<1>1. Shape /\ FlagInv => SeilaLawHonoured
  BY DEF FlagInv, SeilaLawHonoured, InForce, Doctrines
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM BowsherHonouredAlways ==
  ASSUME Mut # "M_UPHOLD", Mut # "M_PREBOWSHER" PROVE Spec => []BowsherHonoured
<1>1. Shape /\ FlagInv => BowsherHonoured
  BY DEF FlagInv, BowsherHonoured, InForce, Doctrines
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM ChadhaHonouredAlways ==
  ASSUME Mut # "M_UPHOLD", Mut # "M_PRECHADHA" PROVE Spec => []ChadhaHonoured
<1>1. Shape /\ FlagInv => ChadhaHonoured
  BY DEF FlagInv, ChadhaHonoured, InForce, Doctrines
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM WillHonouredAlways ==
  ASSUME Mut # "M_UPHOLD" PROVE Spec => []WillHonoured
<1>1. Shape /\ FlagInv => WillHonoured
  BY DEF FlagInv, WillHonoured, InForce, Doctrines
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM ActsFollowEdgesAlways ==
  ASSUME Mut # "M_OFFEDGE" PROVE Spec => []ActsFollowEdges
<1>1. Shape /\ FlagInv => ActsFollowEdges
  BY DEF FlagInv, ActsFollowEdges
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM ActsByHoldersAlways ==
  ASSUME Mut # "M_INACTIVE" PROVE Spec => []ActsByHolders
<1>1. Shape /\ FlagInv => ActsByHolders
  BY DEF FlagInv, ActsByHolders
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM GoodBehaviourAlways ==
  ASSUME Mut # "M_OFFEDGE" PROVE Spec => []GoodBehaviour
<1>1. Shape /\ FlagInv => GoodBehaviour
  BY DEF FlagInv, GoodBehaviour
<1> QED
  BY FlagsAlways, <1>1, PTL

THEOREM PocketVetoHonouredAlways ==
  ASSUME Mut # "M_NOPOCKET" PROVE Spec => []PocketVetoHonoured
<1>1. Shape /\ FlagInv => PocketVetoHonoured
  BY DEF FlagInv, PocketVetoHonoured
<1> QED
  BY FlagsAlways, <1>1, PTL

-----------------------------------------------------------------------------
(* The action properties                                                    *)

LEMMA TextStep ==
  ASSUME Shape, [Next]_vars
  PROVE  [TextOf(edges') # TextOf(edges) => last'.label = "Ratify"]_vars
<1>0. TypeInv /\ TypeOK /\ TextFollowsArticleV /\ StatutesShaped /\ CasesOnStatutes
  BY DEF Shape, TypeInv
<1>1. CASE QuietStep \/ (\E e \in edges : Sue(e)) \/ (\E x \in AmendIds : Propose(x))
            \/ UNCHANGED vars
  BY <1>1, QuietFrame DEF Sue, Propose, vars, graphVars
<1>2. CASE LawStep
  <2>1. bill.op \in Ops /\ edges' = EdgesAfter(bill.op)
    BY <1>0, <1>2, LawStepEnacts DEF Enact, SetEdges
  <2> QED
    BY <1>0, <2>1, EnactText
<1>3. ASSUME NEW e \in challenged, Review(e) PROVE TextOf(edges') = TextOf(edges)
  BY <1>0, <1>3, RulingFacts DEF Review
<1>4. ASSUME NEW x \in AmendIds, Ratify(x) PROVE last'.label = "Ratify"
  BY <1>4 DEF Ratify, Fire, Txt, Edge
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, NextSplit

THEOREM TextChangesOnlyByArticleVHolds == Spec => TextChangesOnlyByArticleV
<1>1. Shape /\ [Next]_vars => [TextOf(edges') # TextOf(edges) => last'.label = "Ratify"]_vars
  BY TextStep
<1> QED
  BY ShapeAlways, <1>1, PTL DEF Spec, TextChangesOnlyByArticleV

LEMMA StatuteStep ==
  ASSUME Shape, [Next]_vars
  PROVE  [StatuteOf(edges') # StatuteOf(edges) =>
            last'.label \in {"Presentment", "Override", "Review"}]_vars
<1>0. TypeInv /\ TypeOK
  BY DEF Shape, TypeInv
<1>1. CASE QuietStep \/ (\E e \in edges : Sue(e)) \/ (\E x \in AmendIds : Propose(x))
            \/ UNCHANGED vars
  BY <1>1, QuietFrame DEF Sue, Propose, vars, graphVars
<1>2. CASE LawStep
  BY <1>0, <1>2, LawStepEnacts
<1>3. ASSUME NEW e \in challenged, Review(e) PROVE last'.label = "Review"
  BY <1>3 DEF Review, Fire, Txt, Edge
<1>4. ASSUME NEW x \in AmendIds, Ratify(x) PROVE StatuteOf(edges') = StatuteOf(edges)
  BY <1>0, <1>4, RatifyStatutes DEF Ratify, SetEdges
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, NextSplit

THEOREM StatutesChangeOnlyByLawOrCourtHolds == Spec => StatutesChangeOnlyByLawOrCourt
<1>1. Shape /\ [Next]_vars => [StatuteOf(edges') # StatuteOf(edges) =>
                                 last'.label \in {"Presentment", "Override", "Review"}]_vars
  BY StatuteStep
<1> QED
  BY ShapeAlways, <1>1, PTL DEF Spec, StatutesChangeOnlyByLawOrCourt
-----------------------------------------------------------------------------
(* LegislativePrimacy: counting the control edges between the branches     *)

CE6 == { Txt("Congress", "Executive", "Control", "Presentment"),
         Txt("Congress", "Executive", "Control", "Override"),
         Txt("Congress", "Executive", "Control", "Appropriate"),
         Txt("Congress", "Executive", "Control", "Impeach"),
         Txt("Congress", "Executive", "Control", "AdviseTreaties"),
         Txt("Congress", "Executive", "Control", "DeclareWar") }
CE7 == CE6 \cup {Txt("Congress", "Executive", "Control", "DecideInability")}
EC3 == { Txt("Executive", "Congress", "Control", "Veto"),
         Txt("Executive", "Congress", "Control", "Convene"),
         Txt("Executive", "Congress", "Control", "Adjourn") }
CJ3 == { Txt("Congress", "Judiciary", "Control", "Impeach"),
         Txt("Congress", "Judiciary", "Control", "Exceptions"),
         Txt("Congress", "Judiciary", "Control", "Organize") }
JC2 == { Txt("Judiciary", "Congress", "Control", "Review"),
         Txt("Judiciary", "Congress", "Control", "PresideTrial") }
\* Every control edge the text ever draws between two branches.
BranchControl ==
  CE7 \cup EC3 \cup CJ3 \cup JC2
  \cup {Txt("Judiciary", "Executive", "Control", "Review"),
        Txt("Executive", "Judiciary", "Control", "Pardon")}

BetweenBranches(e) ==
  e.kind = "Control" /\ e.from \in Branches /\ e.to \in Branches

LEMMA BranchControlPart1 ==
  ASSUME NEW e \in FoundingPart1, BetweenBranches(e) PROVE e \in BranchControl
<1>1. FALSE
  BY DEF FoundingPart1, BetweenBranches, Branches, Txt, Edge
<1> QED
  BY <1>1

LEMMA BranchControlPart2 ==
  ASSUME NEW e \in FoundingPart2, BetweenBranches(e) PROVE e \in BranchControl
BY DEF FoundingPart2, BetweenBranches, BranchControl, CE7, CE6, EC3, CJ3, JC2, Branches,
       Txt, Edge

LEMMA BranchControlPart3 ==
  ASSUME NEW e \in FoundingPart3, BetweenBranches(e) PROVE e \in BranchControl
<1>1. e \in {Txt("Congress", "Judiciary", "Control", "Organize"),
             Txt("Judiciary", "Congress",  "Control", "Review"),
             Txt("Judiciary", "Executive", "Control", "Review"),
             Txt("Judiciary", "Congress",  "Control", "PresideTrial"),
             Txt("Executive", "Judiciary", "Control", "Pardon")}
  BY DEF FoundingPart3, BetweenBranches, Branches, Txt, Edge
<1>2. {Txt("Congress", "Judiciary", "Control", "Organize"),
       Txt("Judiciary", "Congress",  "Control", "Review"),
       Txt("Judiciary", "Executive", "Control", "Review"),
       Txt("Judiciary", "Congress",  "Control", "PresideTrial"),
       Txt("Executive", "Judiciary", "Control", "Pardon")} \subseteq BranchControl
  BY DEF BranchControl, CJ3, JC2
<1> QED
  BY <1>1, <1>2

LEMMA BranchControlAdds ==
  ASSUME NEW x \in AmendIds, NEW e \in Adds(x), BetweenBranches(e) PROVE e \in BranchControl
<1>1. e = Txt("Congress", "Executive", "Control", "DecideInability")
  BY DEF AmendIds, Adds, BetweenBranches, Branches, Txt, Edge
<1> QED
  BY <1>1 DEF BranchControl, CE7

LEMMA ShapeBranchControl ==
  ASSUME Shape, NEW e \in edges, BetweenBranches(e) PROVE e \in BranchControl
<1>1. TypeOK /\ TextFollowsArticleV /\ StatutesShaped
  BY DEF Shape, TypeInv
<1>2. CASE e.basis = "Statute"
  BY <1>1, <1>2, PoolsAreNew DEF StatutesShaped, StatuteFacts, StatRec, BetweenBranches,
                                 Branches, Fixed
<1>3. CASE e.basis = "Text"
  <2>1. e \in Founding \cup Adds("XVII") \cup Adds("XXV")
    BY <1>1, <1>3, TextForOf DEF TextFollowsArticleV, TextOf, TypeOK
  <2> QED
    BY <2>1, FoundingSplit, BranchControlPart1, BranchControlPart2, BranchControlPart3,
       BranchControlAdds DEF AmendIds
<1> QED
  BY <1>1, <1>2, <1>3, EdgeBases

LEMMA PrimacyKept ==
  ASSUME Shape PROVE CE6 \cup CJ3 \subseteq edges
<1>1. CE6 \cup CJ3 \subseteq FoundingPart2 \cup FoundingPart3
  BY DEF CE6, CJ3, FoundingPart2, FoundingPart3
<1>2. \A x \in AmendIds : (CE6 \cup CJ3) \cap Drops(x) = {}
  <2>1. (CE6 \cup CJ3) \cap Drops("XVII") = {}
    BY DEF CE6, CJ3, Drops, Txt, Edge
  <2>2. (CE6 \cup CJ3) \cap ArticleV = {}
    BY DEF CE6, CJ3, ArticleV, Txt, Edge
  <2>3. Drops("XXV") \subseteq ArticleV
    BY DEF Drops
  <2> QED
    BY <2>1, <2>2, <2>3 DEF AmendIds
<1>3. CE6 \cup CJ3 \subseteq TextFor(amendment)
  BY <1>1, <1>2, FoundingSplit DEF TextFor, Applied, AmendIds
<1> QED
  BY <1>3, FoundingFacts DEF Shape, TypeInv, TextFollowsArticleV, TextOf, CE6, CJ3, Txt, Edge

\* The four sets the claim compares, bounded by literal sets.
LEMMA PrimacyBounds ==
  ASSUME Shape
  PROVE  /\ CE6 \subseteq Between(ControlEdges, "Congress", "Executive")
         /\ Between(ControlEdges, "Congress", "Executive") \subseteq CE7
         /\ Between(ControlEdges, "Executive", "Congress") \subseteq EC3
         /\ CJ3 \subseteq Between(ControlEdges, "Congress", "Judiciary")
         /\ Between(ControlEdges, "Congress", "Judiciary") \subseteq CJ3
         /\ Between(ControlEdges, "Judiciary", "Congress") \subseteq JC2
<1>1. CE6 \cup CJ3 \subseteq edges
  BY PrimacyKept
<1>2. \A e \in ControlEdges : e.from \in Branches /\ e.to \in Branches => e \in BranchControl
  BY ShapeBranchControl DEF ControlEdges, OfKind, BetweenBranches
<1>3. /\ {e \in BranchControl : e.from = "Congress" /\ e.to = "Executive"} \subseteq CE7
      /\ {e \in BranchControl : e.from = "Executive" /\ e.to = "Congress"} \subseteq EC3
      /\ {e \in BranchControl : e.from = "Congress" /\ e.to = "Judiciary"} \subseteq CJ3
      /\ {e \in BranchControl : e.from = "Judiciary" /\ e.to = "Congress"} \subseteq JC2
  BY DEF BranchControl, CE7, CE6, EC3, CJ3, JC2, Txt, Edge
<1>4. CE6 \cup CJ3 \subseteq ControlEdges
  BY <1>1 DEF ControlEdges, OfKind, CE6, CJ3, Txt, Edge
<1> QED
  BY <1>2, <1>3, <1>4 DEF Between, Branches, CE6, CJ3, Txt, Edge

LEMMA CardAdd ==
  ASSUME NEW S, IsFiniteSet(S), NEW x, x \notin S
  PROVE  IsFiniteSet(S \cup {x}) /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
BY FS_AddElement

LEMMA PrimacyCounts ==
  /\ IsFiniteSet(CE7) /\ IsFiniteSet(CE6) /\ Cardinality(CE6) = 6
  /\ IsFiniteSet(EC3) /\ Cardinality(EC3) = 3
  /\ IsFiniteSet(CJ3) /\ Cardinality(CJ3) = 3
  /\ IsFiniteSet(JC2) /\ Cardinality(JC2) = 2
<1> DEFINE a1 == Txt("Congress", "Executive", "Control", "Presentment")
           a2 == Txt("Congress", "Executive", "Control", "Override")
           a3 == Txt("Congress", "Executive", "Control", "Appropriate")
           a4 == Txt("Congress", "Executive", "Control", "Impeach")
           a5 == Txt("Congress", "Executive", "Control", "AdviseTreaties")
           a6 == Txt("Congress", "Executive", "Control", "DeclareWar")
           a7 == Txt("Congress", "Executive", "Control", "DecideInability")
           b1 == Txt("Executive", "Congress", "Control", "Veto")
           b2 == Txt("Executive", "Congress", "Control", "Convene")
           b3 == Txt("Executive", "Congress", "Control", "Adjourn")
           c1 == Txt("Congress", "Judiciary", "Control", "Impeach")
           c2 == Txt("Congress", "Judiciary", "Control", "Exceptions")
           c3 == Txt("Congress", "Judiciary", "Control", "Organize")
           d1 == Txt("Judiciary", "Congress", "Control", "Review")
           d2 == Txt("Judiciary", "Congress", "Control", "PresideTrial")
<1>1. IsFiniteSet({a1}) /\ Cardinality({a1}) = 1
  BY FS_Singleton
<1>2. IsFiniteSet({a1} \cup {a2}) /\ Cardinality({a1} \cup {a2}) = 2
  BY <1>1, CardAdd DEF Txt, Edge
<1>3. IsFiniteSet({a1} \cup {a2} \cup {a3}) /\ Cardinality({a1} \cup {a2} \cup {a3}) = 3
  BY <1>2, CardAdd DEF Txt, Edge
<1>4. IsFiniteSet({a1} \cup {a2} \cup {a3} \cup {a4})
      /\ Cardinality({a1} \cup {a2} \cup {a3} \cup {a4}) = 4
  BY <1>3, CardAdd DEF Txt, Edge
<1>5. IsFiniteSet({a1} \cup {a2} \cup {a3} \cup {a4} \cup {a5})
      /\ Cardinality({a1} \cup {a2} \cup {a3} \cup {a4} \cup {a5}) = 5
  BY <1>4, CardAdd DEF Txt, Edge
<1>6. IsFiniteSet({a1} \cup {a2} \cup {a3} \cup {a4} \cup {a5} \cup {a6})
      /\ Cardinality({a1} \cup {a2} \cup {a3} \cup {a4} \cup {a5} \cup {a6}) = 6
  BY <1>5, CardAdd DEF Txt, Edge
<1>7. CE6 = {a1} \cup {a2} \cup {a3} \cup {a4} \cup {a5} \cup {a6} /\ CE7 = CE6 \cup {a7}
  BY DEF CE6, CE7
<1>8. IsFiniteSet(CE7)
  BY <1>6, <1>7, FS_AddElement
<1>9. IsFiniteSet({b1} \cup {b2} \cup {b3}) /\ Cardinality({b1} \cup {b2} \cup {b3}) = 3
  <2>1. IsFiniteSet({b1} \cup {b2}) /\ Cardinality({b1} \cup {b2}) = 2
    BY FS_Singleton, CardAdd DEF Txt, Edge
  <2> QED
    BY <2>1, CardAdd DEF Txt, Edge
<1>10. IsFiniteSet({c1} \cup {c2} \cup {c3}) /\ Cardinality({c1} \cup {c2} \cup {c3}) = 3
  <2>1. IsFiniteSet({c1} \cup {c2}) /\ Cardinality({c1} \cup {c2}) = 2
    BY FS_Singleton, CardAdd DEF Txt, Edge
  <2> QED
    BY <2>1, CardAdd DEF Txt, Edge
<1>11. IsFiniteSet({d1} \cup {d2}) /\ Cardinality({d1} \cup {d2}) = 2
  BY FS_Singleton, CardAdd DEF Txt, Edge
<1>12. EC3 = {b1} \cup {b2} \cup {b3} /\ CJ3 = {c1} \cup {c2} \cup {c3} /\ JC2 = {d1} \cup {d2}
  BY DEF EC3, CJ3, JC2
<1> QED
  BY <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12

LEMMA ShapePrimacy ==
  ASSUME Shape PROVE LegislativePrimacy
<1> DEFINE CEx == Between(ControlEdges, "Congress", "Executive")
           ECx == Between(ControlEdges, "Executive", "Congress")
           CJx == Between(ControlEdges, "Congress", "Judiciary")
           JCx == Between(ControlEdges, "Judiciary", "Congress")
<1>1. CE6 \subseteq CEx /\ CEx \subseteq CE7 /\ ECx \subseteq EC3
      /\ CJ3 \subseteq CJx /\ CJx \subseteq CJ3 /\ JCx \subseteq JC2
  BY PrimacyBounds
<1>2. IsFiniteSet(CEx) /\ Cardinality(CE6) <= Cardinality(CEx)
  BY <1>1, PrimacyCounts, FS_Subset
<1>3. Cardinality(ECx) <= 3
  BY <1>1, PrimacyCounts, FS_Subset
<1>4. IsFiniteSet(CJx) /\ Cardinality(CJ3) <= Cardinality(CJx)
  BY <1>1, PrimacyCounts, FS_Subset
<1>5. Cardinality(JCx) <= 2
  BY <1>1, PrimacyCounts, FS_Subset
<1>6. Cardinality(CEx) > Cardinality(ECx) /\ Cardinality(CJx) > Cardinality(JCx)
  <2>1. /\ Cardinality(CEx) \in Nat /\ Cardinality(ECx) \in Nat
        /\ Cardinality(CJx) \in Nat /\ Cardinality(JCx) \in Nat
    BY <1>1, <1>2, <1>4, PrimacyCounts, FS_Subset, FS_CardinalityType
  <2> QED
    BY <1>2, <1>3, <1>4, <1>5, <2>1, PrimacyCounts
<1>7. Branches \ {"Congress"} = {"Executive", "Judiciary"}
  BY DEF Branches
<1> QED
  BY <1>6, <1>7 DEF LegislativePrimacy

THEOREM LegislativePrimacyAlways == Spec => []LegislativePrimacy
BY ShapeAlways, ShapePrimacy, PTL

-----------------------------------------------------------------------------
(* Every proved property at once, for the module as specified               *)

LocalSafety ==
  /\ TypeOK /\ TextFollowsArticleV /\ EdgesConnectLiveNodes /\ OfficesAreLive
  /\ ArticleVStands /\ ConstitutionWrittenByPeopleAndStates /\ OnlyStatutesOverstep
  /\ GrantFollowsChainExceptXXV /\ NominationLoopIffXXV
  /\ EveryBodyIsCreatedByLaw /\ NamedPathsFromPeople /\ PeoplePowerGoesThroughConstitution
  /\ MutualChecks /\ LegislativePrimacy /\ ExecutorsAreRemovable
  /\ BuckleyHonoured /\ SeilaLawHonoured /\ BowsherHonoured /\ ChadhaHonoured /\ WillHonoured
  /\ ActsFollowEdges /\ ActsByHolders /\ GoodBehaviour /\ PocketVetoHonoured

THEOREM SafeAlways ==
  ASSUME Mut = "none" PROVE Spec => []LocalSafety
<1>1. Spec => []TypeOK
  BY TypeOKAlways
<1>2. Spec => []TextFollowsArticleV
  BY TextFollowsArticleVAlways
<1>3. Spec => []EdgesConnectLiveNodes
  BY EdgesConnectLiveNodesAlways
<1>4. Spec => []OfficesAreLive
  BY OfficesAreLiveAlways
<1>5. Spec => []ArticleVStands
  BY ArticleVStandsAlways
<1>6. Spec => []ConstitutionWrittenByPeopleAndStates
  BY ConstitutionWrittenAlways
<1>7. Spec => []OnlyStatutesOverstep
  BY OnlyStatutesOverstepAlways
<1>8. Spec => []GrantFollowsChainExceptXXV
  BY GrantFollowsChainExceptXXVAlways
<1>9. Spec => []NominationLoopIffXXV
  BY NominationLoopIffXXVAlways
<1>10. Spec => []EveryBodyIsCreatedByLaw
  BY EveryBodyIsCreatedByLawAlways
<1>11. Spec => []NamedPathsFromPeople
  BY NamedPathsFromPeopleAlways
<1>12. Spec => []PeoplePowerGoesThroughConstitution
  BY PeoplePowerGoesThroughConstitutionAlways
<1>13. Spec => []MutualChecks
  BY MutualChecksAlways
<1>14. Spec => []ExecutorsAreRemovable
  BY ExecutorsAreRemovableAlways
<1>15. Spec => []BuckleyHonoured
  BY BuckleyHonouredAlways
<1>16. Spec => []SeilaLawHonoured
  BY SeilaLawHonouredAlways
<1>17. Spec => []BowsherHonoured
  BY BowsherHonouredAlways
<1>18. Spec => []ChadhaHonoured
  BY ChadhaHonouredAlways
<1>19. Spec => []WillHonoured
  BY WillHonouredAlways
<1>20. Spec => []ActsFollowEdges
  BY ActsFollowEdgesAlways
<1>21. Spec => []ActsByHolders
  BY ActsByHoldersAlways
<1>22. Spec => []GoodBehaviour
  BY GoodBehaviourAlways
<1>23. Spec => []PocketVetoHonoured
  BY PocketVetoHonouredAlways
<1>24. Spec => []LegislativePrimacy
  BY LegislativePrimacyAlways
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13,
     <1>14, <1>15, <1>16, <1>17, <1>18, <1>19, <1>20, <1>21, <1>22, <1>23, <1>24,
     PTL DEF LocalSafety

-----------------------------------------------------------------------------
(* What each mutation admits. The counterexamples are TLC's                *)
(* (results/Government-results-*.txt); these say which guard each removes. *)

LEMMA MutOffEdgeFiresAnyEdge ==
  ASSUME Mut = "M_OFFEDGE", NEW e PROVE OnGraph(e)
BY DEF OnGraph

LEMMA MutInactiveFiresForAVacancy ==
  ASSUME Mut = "M_INACTIVE", NEW e PROVE Held(e)
BY DEF Held

LEMMA MutApplicablePassesAnyBill ==
  ASSUME Mut = "M_APPLICABLE", NEW op PROVE Applicable(op) /\ Rechecked(op)
BY DEF Applicable, Rechecked

LEMMA MutRecheckSkipsTheRecheck ==
  ASSUME Mut = "M_RECHECK", NEW op PROVE Rechecked(op) /\ (Applicable(op) <=> Precondition(op))
BY DEF Rechecked, Applicable

LEMMA MutNoStuartKeepsTheJudge ==
  ASSUME Mut = "M_NOSTUART", NEW s, NEW l PROVE Unseat(s, l) = s
BY DEF Unseat

LEMMA MutNoPocketLapsesInRecess ==
  ASSUME Mut = "M_NOPOCKET" PROVE CanReturn
BY DEF CanReturn

LEMMA MutUpholdStrikesNothing ==
  ASSUME Mut = "M_UPHOLD", NEW e PROVE ~Strikes(e) /\ Ruling(e) = edges
BY DEF Strikes, Ruling

LEMMA MutHumphreyUpholdsTenure ==
  ASSUME Mut = "M_HUMPHREY", NEW e, e.label = "RemoveForCause" PROVE ~Forbidden(e)
BY DEF Forbidden, InForce, Violates, Doctrines

LEMMA MutPreChadhaUpholdsTheVeto ==
  ASSUME Mut = "M_PRECHADHA", NEW e, e.label = "LegislativeVeto" PROVE ~Forbidden(e)
BY DEF Forbidden, InForce, Violates, Doctrines

LEMMA MutPreBuckleyUpholdsAppointment ==
  ASSUME Mut = "M_PREBUCKLEY", NEW e, e.label = "AppointInferior" PROVE ~Forbidden(e)
BY DEF Forbidden, InForce, Violates, Doctrines

LEMMA MutPreBowsherUpholdsRemoval ==
  ASSUME Mut = "M_PREBOWSHER", NEW e, e.label = "Remove" PROVE ~Forbidden(e)
BY DEF Forbidden, InForce, Violates, Doctrines

LEMMA MutSeverPlainStrikesOnlyTheEdge ==
  ASSUME Mut = "M_SEVER_PLAIN", NEW e PROVE Sever(e) = edges \ {e}
BY DEF Sever

LEMMA MutCongressAmendsWritesTheText ==
  ASSUME Mut = "M_CONGRESS_AMENDS"
  PROVE  /\ Txt("Congress", "Constitution", "Amend", "Ratify") \in Adds("XXV")
         /\ ~WriterFacts(Txt("Congress", "Constitution", "Amend", "Ratify"))
BY DEF Adds, WriterFacts, Txt, Edge, GrantKinds, Rank

LEMMA MutNoArtVRepealsArticleV ==
  ASSUME Mut = "M_NO_ARTV" PROVE Drops("XXV") = ArticleV
BY DEF Drops

=============================================================================
