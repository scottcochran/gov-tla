# `AtcNetwork.tla`: testing a claim about TLA+ and air traffic control networks

Written by Claude, 2026.11.16, at Scott Cochran's prompt. The model, its
row list and this note are Claude's; the question is his.

## The question

> Isn't TLA+ specifically suited to the problem? Even if it only identifies
> the gaps?

The problem is a wide-area telecommunications network that carries air
traffic control services, and a failure of it that stops traffic. The
question was put to another assistant, which answered that yes, an abstract
TLA+ specification of such an architecture "would likely expose" three
things that testing misses:

1. **State transition deadlocks**: simultaneous link failures cause
   competing route recalculations that never converge.
2. **Control-plane starvation**: data-plane traffic floods the in-band
   management channel and chokes the keepalives.
3. **Liveness violations**: a backup path saturates on activation, traffic
   bounces back to the primary, and the two oscillate for ever.

That answer was an assertion. `AtcNetwork.tla` is the experiment: write the
abstract specification, and see what the model checker does with it.

## What the module is, and is not

It is **not a model of any fielded network**. It was written from no design
document of the FAA Telecommunications Infrastructure, of its successor or
of any vendor's equipment, and nothing in it says what any real network
does or did on any day.

It is one small failover mechanism. Each site reaches the network over a
primary path of its own and a backup path whose capacity the sites share.
A keepalive session runs over each path. A site's traffic is on its
primary, on the backup, or nowhere. The environment fails and repairs
links and puts traffic surges on primaries, a fixed number of times.

The mechanism as specified (`Mut = "none"`) has three checks, and each
mutation removes one:

| Check | Mutation that removes it |
|---|---|
| Control traffic has a queue of its own, so a keepalive is lost only when the link is down | `M_INBAND` |
| The backup admits a site only if it has room | `M_NOADMIT` |
| A site on the backup returns to its primary when the primary is restored | `M_NONREVERT` |

## What TLC found

Checked at two sites, a backup for one and three physical events; the
unmutated rows also at three sites, four events and a backup for one or
two. All 62 rows are as expected
([`results/AtcNetwork-results-2026.11.16.txt`](../results/AtcNetwork-results-2026.11.16.txt)).

| Property | `none` | `M_INBAND` | `M_NOADMIT` | `M_NONREVERT` |
|---|---|---|---|---|
| `NoFalseDown`: no session declared down over a live link | holds | **broken** | holds | holds |
| `NoOverbooking`, `BackupWithinCapacity` | holds | holds | **broken** | holds |
| `StopsOnlyWhenQuiet`: the network stops only when converged | holds | holds | holds | **broken** |
| `Settles`: sites change path finitely often | holds | **broken** | holds | holds |
| `Converges`: sessions and paths end up right, for good | holds | **broken** | holds | **broken** |
| `NoSiteStranded`: no site kept off a backup another holds needlessly | holds | **broken** | holds | **broken** |

The counterexamples, in words:

- **`M_INBAND`, the oscillation.** One surge on one site's primary, and no
  physical fault at all. The primary is congested, its keepalives are lost,
  the session is declared down over a live link and the traffic leaves. The
  congestion clears, the session comes back, the traffic comes back, and
  the primary is congested again. Four steps, repeated for ever. This is
  claims 2 and 3 together.
- **`M_NOADMIT`, the overload.** Two primaries fail, both sites take a
  backup built for one. Nothing further happens.
- **`M_NONREVERT`, the deadlock.** A primary fails, the site takes the
  backup, the primary is repaired, and the site stays where it is. Every
  action is now disabled. With a third event, a second site loses its
  primary and is refused the backup that the first is holding for no
  reason. This is the nearest thing to claim 1.

## What the experiment shows

**The method does what was claimed for it, at this level of abstraction.**
A module of under 300 lines, with no router, no protocol and no firmware
in it, separates three architectural defects and attributes each property
to the one check it rests on. The objection that the vendors' state
machines are closed does not reach a model like this one. It does not
describe their equipment. It states conditions the composed system must
meet, such as "a keepalive must not share fate with data-plane
congestion", which are then requirements on a configuration and things a
test laboratory can be asked to demonstrate.

**It also sharpened the three claims, which is the more useful result.**

- Claims 2 and 3 are one defect. Starvation is its safety face (the flag
  `falseDown`), oscillation is its liveness face (`Settles`), and a single
  mutation breaks both.
- Claim 3 as worded did not happen. A backup that saturates on activation
  (`M_NOADMIT`) is a stable overload here, not an oscillation. The loop
  needs a path from load back to session state, and that path is the
  in-band control plane. Saturation alone does not provide it.
- Claim 1 misnames its failure. The competing-recalculation loop is a
  livelock, and `StopsOnlyWhenQuiet` holds under `M_INBAND`: that network
  never stops. The one true deadlock came from a defect the answer did not
  list, non-revertive switching, and it needs no simultaneous failures,
  only three events one after another.
- The defences are not independent. With admission control in place, the
  backup never congests, so `M_INBAND` does no harm there. It bites on the
  primary, where the surge is load the mechanism does not admit.

## What it does not show

**The model checker discovered nothing here.** Each gap is a mutation I
wrote on purpose, knowing the failure it would produce, and every one of
the 62 rows came out as I had predicted before running it. What TLC
contributed was confirmation, the shortest traces, the cells of the table
that say a mutation breaks *nothing else*, and the check that the
unmutated mechanism has none of the three faults at these constants. That
is a real contribution, but it is not the discovery of an unknown flaw.

Discovery happens when the specification is of a design its authors
believe to be correct. That needs the design: which queue the keepalives
are in, what the admission rule on the shared path is, whether switching
is revertive, what the timers are. I have none of that for any FAA
network, and neither did the assistant that gave the original answer. So
the honest form of its conclusion is conditional. If the fielded
architecture has an in-band control plane with nothing reserved for it,
then a specification of it would show this loop. Whether it has, the
model cannot say.

**It cannot see a redundancy that exists on paper and not in the field.**
`Mut = "none"` has a working backup because the module says so. A backup
circuit that shares a conduit with the primary, or was never tested, or
was misconfigured, is a gap between the design and the thing built, and a
specification of the design is silent about it. Staging laboratories and
fault injection, which the original answer set against formal methods,
are the tools for that gap. The two are complements.

**The results are checked, not proved, and at small constants.** Three
sites and four events is not a national network. Time is abstracted to
nondeterminism, so wait-to-restore timers and flap damping, which are the
standard remedies for an oscillation, are not in the model, and nothing
here says how fast anything happens. There is no proof module:
[`PROOF-GAPS.txt`](../PROOF-GAPS.txt) says why.

## Running it

```bash
./install-tla.sh
python3 scripts/tlc_rows.py rows/AtcNetwork-rows.txt -j 4
```

The system terminates, because the environment is finite, so an ad hoc run
with `AtcNetwork.cfg` needs `-deadlock`.
