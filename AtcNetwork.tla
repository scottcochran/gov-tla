----------------------------- MODULE AtcNetwork -----------------------------
(***************************************************************************)
(* An abstract failover mechanism for a converged air traffic control      *)
(* network: facilities that each reach the network over a primary path and *)
(* over a backup path whose capacity they share.                           *)
(*                                                                         *)
(* THIS IS NOT A MODEL OF ANY FIELDED NETWORK. It was written from no      *)
(* design document of the FAA Telecommunications Infrastructure, of its    *)
(* successor or of any vendor's equipment. It states one small mechanism   *)
(* and three ways of building it wrongly, to test a claim made about the   *)
(* method: that an abstract TLA+ specification of such an architecture     *)
(* would expose (1) failover states that never converge, (2) control-plane *)
(* starvation by data-plane traffic and (3) a permanent failover           *)
(* oscillation. Each of the three is a mutation here, and the row list     *)
(* says which property each one breaks. What that shows, and what it does  *)
(* not, is in the README.                                                  *)
(*                                                                         *)
(* THE MECHANISM (Mut = "none")                                            *)
(*   Each site s has two access links, linkUp[s]["pri"] and                *)
(*   linkUp[s]["bak"], which the environment fails and repairs. Over each  *)
(*   runs a keepalive session; adj[s][p] is what the control plane         *)
(*   believes about it. active[s] is the path the site's traffic is on:    *)
(*   "pri", "bak" or "none".                                               *)
(*     Detection.  A session is declared down when its keepalives are      *)
(*       lost, and traffic on that path is withdrawn in the same step. It  *)
(*       is established again when they get through. Control traffic has   *)
(*       a queue of its own, so keepalives are lost only when the link is  *)
(*       physically down.                                                  *)
(*     Selection.  A site prefers its primary. It takes the backup only    *)
(*       when its primary session is down, and only if the backup has room *)
(*       (admission control: at most BakCap sites). It returns to the      *)
(*       primary when that session is up again (revertive switching).      *)
(*   The environment may also put a traffic surge on a site's primary      *)
(*   (surge[s]): data-plane load, a telemetry flood for one, that the      *)
(*   mechanism does not admit or route. A primary carries the site's       *)
(*   traffic or the surge, not both: it is congested exactly when the      *)
(*   surge is on and the site's traffic is on it. The backup is congested  *)
(*   when it carries more than BakCap sites.                               *)
(*                                                                         *)
(* PROPERTIES                                                              *)
(*   NoFalseDown            no session is declared down while its link is  *)
(*                          up. A flag, raised in DeclareDown.             *)
(*   NoOverbooking          no site is put on the backup when it has no    *)
(*                          room. A flag, raised in UseBak.                *)
(*   BackupWithinCapacity   the backup never carries more than BakCap      *)
(*                          sites. The global form of NoOverbooking.       *)
(*   StopsOnlyWhenQuiet     a state in which nothing further can happen is *)
(*                          one where the environment is spent and the     *)
(*                          network has converged. The mechanism has no    *)
(*                          deadlock short of the right answer.            *)
(*   Settles                the sites change path only finitely often.     *)
(*                          Needs no fairness.                             *)
(*   Converges              eventually, and from then on, every session    *)
(*                          agrees with its link and every site is on the  *)
(*                          best path its links and the backup's capacity  *)
(*                          allow. Under SpecLive.                         *)
(*   NoSiteStranded         eventually, and from then on, no site is kept  *)
(*                          off the backup by a site that holds it while   *)
(*                          its own primary link is up. Under SpecLive.    *)
(*                                                                         *)
(* MUTATIONS, each one check removed, and the properties it must break     *)
(*   M_INBAND      keepalives share the data queue, so a congested path    *)
(*                 loses them (the control plane is in band and nothing    *)
(*                 is reserved for it). Breaks NoFalseDown, Settles,       *)
(*                 Converges and NoSiteStranded: the session drops, the    *)
(*                 traffic leaves, the congestion clears, the session      *)
(*                 returns, the traffic returns, for ever, after one       *)
(*                 surge and no physical fault.                            *)
(*   M_NOADMIT     the backup admits without counting. Breaks              *)
(*                 NoOverbooking and BackupWithinCapacity, and nothing     *)
(*                 else: with the control queue reserved the overload is   *)
(*                 stable.                                                 *)
(*   M_NONREVERT   a site on the backup does not return to a restored      *)
(*                 primary. Breaks StopsOnlyWhenQuiet, Converges and       *)
(*                 NoSiteStranded: the network stops, for good, with a     *)
(*                 site holding the backup it does not need and another    *)
(*                 refused it.                                             *)
(*                                                                         *)
(* WHAT IS ABSTRACTED                                                      *)
(*   Time. A keepalive is lost or gets through by an action that may fire  *)
(*     whenever its guard holds; there are no timers and no hold counts.   *)
(*     Wait-to-restore and flap damping are therefore not modelled, and    *)
(*     nothing here says how fast anything happens.                        *)
(*   The environment is finite. budget counts the physical events (a link  *)
(*     failing or being repaired, a surge starting or stopping) still to   *)
(*     come, from MaxEvents down. Whatever happens infinitely often is     *)
(*     then the control plane's own doing, which is what Settles is about. *)
(*     It also makes the system terminating: see Quiet.                    *)
(*   Topology. Each site has one hop on each path. There is no routing     *)
(*     protocol, no multi-hop path, no vendor state machine.               *)
(*   The data plane. A congested primary under Mut = "none" still carries  *)
(*     the site, badly; no property here is about throughput.              *)
(*                                                                         *)
(* Constants are bounded in rows/AtcNetwork-rows.txt, not here.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Mut,        \* "none" or one mutation
          Sites,      \* the facilities
          BakCap,     \* how many sites the shared backup can carry
          MaxEvents   \* how many physical events the environment has

Paths  == {"pri", "bak"}
Places == {"pri", "bak", "none"}

VARIABLES linkUp,      \* linkUp[s][p]: the access link is physically up
          surge,       \* surge[s]: a data-plane surge is on s's primary
          budget,      \* physical events still to come
          adj,         \* adj[s][p]: the control plane holds the session up
          active,      \* active[s]: the path s's traffic is on
          falseDown,   \* a session was declared down over a link that was up
          overbooked,  \* a site was put on the backup when it had no room
          refused      \* witness: admission control refused a site

vars == <<linkUp, surge, budget, adj, active, falseDown, overbooked, refused>>

TypeOK ==
  /\ linkUp \in [Sites -> [Paths -> BOOLEAN]]
  /\ surge  \in [Sites -> BOOLEAN]
  /\ budget \in 0..MaxEvents
  /\ adj    \in [Sites -> [Paths -> BOOLEAN]]
  /\ active \in [Sites -> Places]
  /\ falseDown \in BOOLEAN /\ overbooked \in BOOLEAN /\ refused \in BOOLEAN

Init ==
  /\ linkUp = [s \in Sites |-> [p \in Paths |-> TRUE]]
  /\ surge  = [s \in Sites |-> FALSE]
  /\ budget = MaxEvents
  /\ adj    = [s \in Sites |-> [p \in Paths |-> TRUE]]
  /\ active = [s \in Sites |-> "pri"]
  /\ falseDown = FALSE /\ overbooked = FALSE /\ refused = FALSE

---------------------------------------------------------------------------
\* The mechanism's checks, each with the mutation that removes it.

BakLoad == Cardinality({s \in Sites : active[s] = "bak"})

Congested(s, p) == IF p = "pri" THEN surge[s] /\ active[s] = "pri"
                                ELSE BakLoad > BakCap

\* Control traffic has a queue of its own.           M_INBAND removes it.
Reserved == Mut # "M_INBAND"
\* Keepalives on s's path p do not get through.
Lost(s, p) == ~linkUp[s][p] \/ (~Reserved /\ Congested(s, p))

\* The backup takes a site only if it has room.      M_NOADMIT removes it.
Admits == Mut = "M_NOADMIT" \/ BakLoad < BakCap

\* A site on the backup returns to its primary.      M_NONREVERT removes it.
Revertive == Mut # "M_NONREVERT"

---------------------------------------------------------------------------
\* The environment: physical events, each spending one unit of the budget.

Fail(s, p) ==
  /\ budget > 0 /\ linkUp[s][p]
  /\ linkUp' = [linkUp EXCEPT ![s][p] = FALSE]
  /\ budget' = budget - 1
  /\ UNCHANGED <<surge, adj, active, falseDown, overbooked, refused>>

Repair(s, p) ==
  /\ budget > 0 /\ ~linkUp[s][p]
  /\ linkUp' = [linkUp EXCEPT ![s][p] = TRUE]
  /\ budget' = budget - 1
  /\ UNCHANGED <<surge, adj, active, falseDown, overbooked, refused>>

SurgeOn(s) ==
  /\ budget > 0 /\ ~surge[s]
  /\ surge' = [surge EXCEPT ![s] = TRUE]
  /\ budget' = budget - 1
  /\ UNCHANGED <<linkUp, adj, active, falseDown, overbooked, refused>>

SurgeOff(s) ==
  /\ budget > 0 /\ surge[s]
  /\ surge' = [surge EXCEPT ![s] = FALSE]
  /\ budget' = budget - 1
  /\ UNCHANGED <<linkUp, adj, active, falseDown, overbooked, refused>>

---------------------------------------------------------------------------
\* Detection: the keepalive sessions.

DeclareDown(s, p) ==
  /\ adj[s][p] /\ Lost(s, p)
  /\ adj' = [adj EXCEPT ![s][p] = FALSE]
  /\ active' = [active EXCEPT ![s] = IF active[s] = p THEN "none" ELSE active[s]]
  /\ falseDown' = (falseDown \/ linkUp[s][p])
  /\ UNCHANGED <<linkUp, surge, budget, overbooked, refused>>

Establish(s, p) ==
  /\ ~adj[s][p] /\ ~Lost(s, p)
  /\ adj' = [adj EXCEPT ![s][p] = TRUE]
  /\ UNCHANGED <<linkUp, surge, budget, active, falseDown, overbooked, refused>>

---------------------------------------------------------------------------
\* Selection: which path a site's traffic is on.

UsePri(s) ==
  /\ adj[s]["pri"]
  /\ active[s] = "none" \/ (active[s] = "bak" /\ Revertive)
  /\ active' = [active EXCEPT ![s] = "pri"]
  /\ UNCHANGED <<linkUp, surge, budget, adj, falseDown, overbooked, refused>>

UseBak(s) ==
  /\ active[s] = "none" /\ ~adj[s]["pri"] /\ adj[s]["bak"]
  /\ Admits
  /\ active' = [active EXCEPT ![s] = "bak"]
  /\ overbooked' = (overbooked \/ ~(BakLoad < BakCap))
  /\ UNCHANGED <<linkUp, surge, budget, adj, falseDown, refused>>

Refuse(s) ==
  /\ active[s] = "none" /\ ~adj[s]["pri"] /\ adj[s]["bak"]
  /\ ~Admits /\ ~refused
  /\ refused' = TRUE
  /\ UNCHANGED <<linkUp, surge, budget, adj, active, falseDown, overbooked>>

---------------------------------------------------------------------------
Next ==
  \/ \E s \in Sites, p \in Paths : Fail(s, p) \/ Repair(s, p)
  \/ \E s \in Sites : SurgeOn(s) \/ SurgeOff(s)
  \/ \E s \in Sites, p \in Paths : DeclareDown(s, p) \/ Establish(s, p)
  \/ \E s \in Sites : UsePri(s) \/ UseBak(s) \/ Refuse(s)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
\* Safety.

NoFalseDown          == ~falseDown
NoOverbooking        == ~overbooked
BackupWithinCapacity == BakLoad <= BakCap

Safety == NoFalseDown /\ NoOverbooking /\ BackupWithinCapacity

\* The right answer for site s, given the physical links and the backup's room.
OnRight(s) ==
  IF linkUp[s]["pri"] THEN active[s] = "pri"
  ELSE IF linkUp[s]["bak"]
       THEN active[s] = "bak" \/ (active[s] = "none" /\ BakLoad >= BakCap)
       ELSE active[s] = "none"

Converged == adj = linkUp /\ \A s \in Sites : OnRight(s)

\* The terminal predicate. The environment is finite, so the system stops;
\* this is where it must have stopped.
Quiet == budget = 0 /\ Converged

StopsOnlyWhenQuiet == (~ENABLED Next) => Quiet

---------------------------------------------------------------------------
\* Liveness.

\* Site s is kept off the backup by a site that does not need it.
Stranded(s) ==
  /\ active[s] = "none" /\ ~linkUp[s]["pri"] /\ linkUp[s]["bak"]
  /\ \E t \in Sites : active[t] = "bak" /\ linkUp[t]["pri"]

Settles        == <>[][active' = active]_vars
Converges      == <>[]Converged
NoSiteStranded == <>[](\A s \in Sites : ~Stranded(s))

\* Fairness, each an action of Next, named for whose obligation it is. Weak
\* fairness is enough: with the environment finite, each of these stays
\* enabled until it is taken or another site's step makes it moot.
DetectionRuns ==      \* the keepalive timers fire
  \A s \in Sites, p \in Paths : WF_vars(DeclareDown(s, p)) /\ WF_vars(Establish(s, p))
SelectionRuns ==      \* a site that can move to a better path does
  \A s \in Sites : WF_vars(UsePri(s)) /\ WF_vars(UseBak(s))

SpecLive     == Spec /\ DetectionRuns /\ SelectionRuns
SpecNoDetect == Spec /\ SelectionRuns        \* drops DetectionRuns
SpecNoSelect == Spec /\ DetectionRuns        \* drops SelectionRuns

\* Must be VIOLATED under SpecLive: the fair specification has a behaviour.
NoBehaviour == <>FALSE

---------------------------------------------------------------------------
\* Witnesses. Each must be VIOLATED under Mut = "none": the state or step it
\* forbids is one the mechanism reaches.

NeverOnBackup   == \A s \in Sites : active[s] # "bak"            \* a site fails over
NeverBackupFull == BakLoad < BakCap                             \* the backup fills
NeverRefused    == ~refused                                     \* admission refuses a site
NeverCongested  == \A s \in Sites : ~Congested(s, "pri")        \* a primary is congested
NeverCutOff     == \A s \in Sites : linkUp[s]["pri"] \/ linkUp[s]["bak"]   \* a site loses both links
NeverQuiet      == ~(Quiet /\ budget < MaxEvents)               \* the network converges after a fault
NeverReverts    ==                                              \* a site returns to its primary
  [][\A s \in Sites : ~(active[s] = "bak" /\ active'[s] = "pri")]_vars
=============================================================================
