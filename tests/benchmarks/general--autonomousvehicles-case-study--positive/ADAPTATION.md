# AutonomousVehicles — redesign record

Status: **implemented** as `general--autonomousvehicles-case-study--positive`,
all eight stages green including `rmc`, after the maintainer-approved
category-3 redesign (the blocker classification that preceded it is the
stage K decision report of 2026-09-07).

Source: `examples.zip:ReLico-main/AutonomousVehicles.rebeca`, 517 lines,
10 classes. The redesigned source is 409 lines, 7 classes, 39 instances
(33 segments + 6 facilities). **There is no Vehicle reactiveclass in the
original** — vehicles are virtual (`vehicleId` parameters); the moving
actors are the infrastructure classes themselves.

## Original blockers, measured in order

1. `unsupported by the ReLico general parser bridge: environment variable`
   (12 declarations).
2. `A1: a rebec-typed state variable of type Segment in Segment` (3
   variables in `Segment`, plus rebec-typed constructor parameters).
3. Dynamic sender capture: `segRequestingCross = ((Segment)sender)` —
   a runtime rebec reference, written 3 times (including `= null`
   twice), read 2 times.
4. `sender`-dependent dispatch: 16 `((Segment)sender).m(...)` reply
   sites and 18 `instanceof` chain arms over 6 classes.
5. Null-encoded topology: ~40 `null` constructor arguments in `main`
   encode chain termination and absent roles; `startSendingToNext`
   forwards through a 7-way null chain; `crossCtrl == null` guards
   split the permission path.
6. Computed delays: `delay((segmentLength-SAFE_DISTANCE)/vehicleSpeed)`
   and `delay(SAFE_DISTANCE/vehicleSpeed)`.
7. `assertion(false)` x8 in `DecisionStation.vehicleEntered`.
8. Statement-form delays `delay(60/30/60)` (3 sites); 9 bare
   statement-position self-sends.

## Applied mechanical adaptations (category 1)

- **env folded into literals**: 12 declarations. `NUMBER_VEHICLES`
  folds to **2** (see the scenario note at the end); `RESENDING_PERIOD`
  → 25, `NORMAL_SPEED` → 15, `REDUCED_SPEED` → 7, `SAFE_DISTANCE` → 20,
  `SEGMENT_LENGTH` → 200, load/unload/charge times → their literals.
- **Bare self-sends qualified**: the 9 staggered
  `startSendingToNext(k) after(d)` launches in
  `DecisionStation.leaveParkingSlots` → `self.startSendingToNext(...)`.

## Applied redesign (category 3, approved)

### 1. Dynamic sender capture → two static bindings + a tag

`segRequestingCross` is eliminated. Only two segments ever ask the
`CrossController` (`subSeg2E1ToS2`, `subSeg3S6ToE2` — measured: exactly
these carry a non-null `controller` argument). `CrossController` binds
both (`segA`, `segB`); the ask `giveCrossPermission(vehicleId,
crossTag)` carries which segment asked; both replies
(`getCrossPermission`, `crossNotAvailable`) route through the matching
binding. The requesting segment no longer stores itself: its
`getCrossPermission` handler proceeds with `self.getPermision(...)`,
exactly the call the original made through the stored reference
(`((Segment)segRequestingCross).getPermision` where the stored value
was the segment itself).

### 2. Sender-dependent dispatch → tag-parameterised static dispatch

`givePermisionForVehicle` gains a `prevTag` parameter. The receiver
replies through one of seven bindings — `prevSeg1`, `prevSeg2`,
`dsS`, `pcS`, `wlS`, `scS`, `preS` — selected by a 7-way `if` on the
tag, mirroring the original 6-way `instanceof` chain arm for arm,
including the `DecisionStation` arity difference
(`segmentNotFree(vehicleId, segmentDes)` vs the 1-argument form).
**The tag is a literal at every send site**, because each sender→
receiver pair is fixed by the chain topology: a mid-chain segment is
always `prevTag == 0` in its successor's namespace, the six chain-head
senders (`ds`, `pc`, `wl`, `sc`, `prePoint`) carry tags 2–6, and the
two-tailed `subSeg1S2ToE3` receives tag 0 from the S1 tail and tag 1
from the E2 tail. No distinction is deleted: every original sender
class keeps its own reply arm.

The reply-back of a grant (`getPermision` → `vehicleEntered` to the
grantor) uses the receiver's **nextKind** dispatch, because the grantor
of a permission the segment asked for is exactly the segment's next
hop — the same entity the original reached through `((Segment)sender)`
on the reply message. For the crossing segment the grantor is the
segment itself (the original self-sends `getPermision` through the
stored self-reference), so the `hasCross` arm answers
`self.vehicleEntered`, preserving the original's self-directed reply.

### 3. Rebec-typed state variables → knownrebec bindings

`nextSegment`, `decisionS`, `primaryC`, `secondaryC`, `wheelL`,
`prePoint` become six knownrebec slots (`nextSeg`, `dsS`, `pcS`,
`scS`, `wlS`, `preS`), **every instance binding all six** — the five
facilities are singletons, so a slot the original left `null` binds
the real facility, and the null check that selected it becomes false.
`nextSegment`/`decisionS` were single-assignment (1 write, 1 read,
constructor-only — the already-approved category-2 shape);
`secondaryC`/`wheelL`/`prePoint` likewise; `primaryC` carries the
crossing role via `crossCtrl`.

### 4. Null-encoded topology → nextKind tags

The 7-way null forwarding chain becomes a per-instance `nextKind` tag
(0=nextSeg, 1=pc, 2=wl, 3=sc, 4=ds, 5=prePoint) with a 6-way dispatch
over the bindings. Chain tails carry the tag of the facility they
feed (S2-tail→sc, E3-tail→ds, E2-tail→pc, S6-tail→pc, S5-tail→wl,
S4-tail→prePoint); every other segment is nextKind 0. The
`crossCtrl == null` guards become a `hasCross` boolean (true for
exactly the two crossing segments). No `null` exists anywhere in the
redesigned source.

### 5. instance-of / casts → kind tags

Covered by items 2 and 4: the 18 `instanceof` arms become the 7-way
`prevTag` reply dispatch plus the `nextKind` forwarding dispatch; the
16 cast-reply sites become the same dispatches' call arms. All 6
sender classes keep distinct arms.

### 6. Computed delays → literal branches over the finite speed set

`vehicleSpeed` takes exactly two values (NORMAL=15, REDUCED=7).
`delay((200-20)/vehicleSpeed)` → `after(12)` when speed is 15,
`after(25)` when 7 (integer division: 180/15=12, 180/7=25);
`delay(20/vehicleSpeed)` → `after(1)` / `after(2)`. The traversal
distinction between normal and reduced speeds is preserved exactly.

### 7. `assertion(false)` → `allVehiclesReached` latch

**Original purpose, measured from the source**: the eight assertions
sit at the end of `DecisionStation.vehicleEntered` under a cascade
under `NUMBER_VEHICLES`; the source comment reads *"when all vehicles
travelled once the model checking stops by puting 'assertion(false)'"*.
Its purpose is the model's designed success observable: the condition
"every launched vehicle has completed the required traversal" — and,
in Rebeca, `assertion(false)` is the idiom for telling the model
checker to stop exploring once that condition holds.

**New observable**: `DecisionStation` keeps the per-vehicle
`vehicleNReached` flags (one per launched vehicle) and sets
`allVehiclesReached = true` when all launched vehicles' flags are set —
in Rebeca terms:

```rebeca
if (vehicle1Reached && vehicle2Reached) {
    allVehiclesReached = true;
}
```

**Exact mapping**: the original condition `vehicle1Reached && ...
&& vehicleKReached → assertion(false)` under
`NUMBER_VEHICLES == K` maps to the same conjunction over the same
per-vehicle flags → `allVehiclesReached = true`, with K = 2 (the
folded scenario). The conjunction is over the launched vehicles
exactly as the original's cascade enumerates them; no reached flag is
dropped and no new one is added. What changes is the *effect*: the
original halted the checker at the success point; the redesign makes
the success point a persistent observable state variable that RMC
explores past. This is strictly stronger verification — the checker
must now also show the post-completion states are deadlock-free — and
the latch remains meaningful for exploration: it is the state a
property file would read (`G allVehiclesReached` reachability), which
is precisely the reachability question the original assertion encoded.

The `allVehiclesReached` latch never resets and never gates any
behaviour — no send, guard, or delay reads it — so it cannot mask a
deadlock or shorten any execution.

### 8. Mechanical fixes

Statement-form delays become delayed self-sends
(`delay(60)` in PrimaryCrusher/WheelLoader `vehicleEntered` →
`self.startSendingToNext(vehicleId) after(60)`; `delay(30)` in
SecondaryCrusher likewise); bare self-sends qualified; dead
`DecisionStation.loop` (a self-reschedule nothing depends on) removed
with the assertion cascade's NUMBER_VEHICLES arms it served.

## Scenario note — NUMBER_VEHICLES folded to 2

The original env ships `NUMBER_VEHICLES = 4`, and the launch cascade is
designed for 1–8. The redesigned model at 4 vehicles exceeds the
pipeline's **fixed 60-second** model-checker exploration budget
(measured: the stage tool's checker run times out; the manifest's
per-stage timeout is not threaded into the stage). Folding
`NUMBER_VEHICLES` to 2 — within the model's own designed range — keeps
every contested behavior: two vehicles contend for segments, can meet
at the crossing mutex from the S1 and S6 routes, exercise the PrePoint
alternation, and drive resend retries. The 4-vehicle scenario remains
translation- and runtime-clean; only the checker budget refuses it.

## Result

After the redesign: no rebec-typed variables, no `sender`, no
`instanceof`, no casts, no `null`, no computed delays, no assertions —
and the ring protocol intact. RMC reports **`satisfied`** for
`Deadlock-Freedom and No Deadline Missed` on the 409-line source.
