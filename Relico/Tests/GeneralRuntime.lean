import Relico.Common.WeakTransition
import Relico.DTR.GeneralRuntime
import Relico.LF.GeneralRuntime

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GeneralRuntime

/-!
# Compile-time pins for the general runtime state types

`docs/STAGE_G_DESIGN.md` §13, obligation G2a-ii. `Relico/DTR/GeneralRuntime.lean` and
`Relico/LF/GeneralRuntime.lean` declare the two runtime state types, the two label types, the τ
classification and the observable projection, and they prove the erasure lemmas. This module pins the
things those theorems are structurally unable to see.

Every pin below is chosen so that some specific wrong implementation fails it. That standard is
`docs/STAGE_F_FINDINGS.md` F60's, which records an assertion that was invariant under the sort it was
credited with pinning, and it is the reason several obvious-looking pins are **absent** here — see the
last section.

## The round-trip theorem cannot see what `ofConfiguration` attaches

This is the important one. `erase_ofConfiguration` says `erase (ofConfiguration config) = config`, and it
is proved for all configurations — but it is **blind to the continuation**, because `erase` drops whatever
`ofConfiguration` attached. Rewrite `attachEmptyContinuations` to attach an arbitrary non-empty body to
every actor and that theorem still holds, unchanged, while the initial state of every run would have every
actor mid-body and therefore ineligible for dispatch. Nothing in either definition module would fail.

Test 3 is the only instrument that sees it: it pins the *attached* store against a literal in which both
actors are idle.

## Erasure's other two failure modes

Test 1 pins `erase` on a two-actor configuration against a hand-written `DTR.GeneralConfiguration`
literal, rather than against anything built from the same functions. An `erase` that dropped an actor,
reordered the store, or returned the wrong actor's state fails it; `eraseContinuations_lookup` does not,
because a lookup lemma is blind to order and, on a store whose keys are distinct, to duplication.

Test 2 pins that continuations are the *only* thing erasure drops, by erasing two configurations that
differ in nothing else. The wrong implementation it catches is a plausible one: an `erase` that consulted
`activeBody` — for instance to omit actors part-way through a body — would pass test 1 and fail this.

## The tag pins target landed v0 code on purpose

`LF.Tag.PrecedesOrEqual` is not new; it has existed since vertical slice v0 in
`Relico/LF/Scheduling.lean` and is used throughout the existing development. What G2a-ii adds to it is a
`Decidable` instance, transitivity and totality, and of those three only the instance can be pinned at
all: transitivity and totality are universally quantified, so a literal instance of either is a
tautology under any relation that has them.

A `Decidable` instance, though, is pinned by exactly one thing — a proof `by decide`, which forces the
instance to reduce in the kernel rather than merely to elaborate. Tests 4 through 7 are therefore stated
with `decide`, and their *inputs* are chosen to discriminate the two ways a lexicographic tag order can be
wrong:

* Tests 4 and 5 are a pair at equal logical time. An order that compared only `time` — which is precisely
  the reading of the tag that P24 shows makes the paper's Theorem 1 false — satisfies test 4 and **fails
  test 5**, because it would make `⟨5, 1⟩` precede `⟨5, 0⟩`.
* Tests 6 and 7 are a pair whose microstep and time disagree. An order that compared microstep first
  **fails test 6**, because `⟨4, 9⟩` has the larger microstep and the earlier time.

## The microstep must be carried and must not be observable

Both halves, because they are separate failure modes. Test 8 pins that `now` **drops** the microstep: a
`now` defined as `time + microstep` fails it. Test 9 pins that the state nevertheless **distinguishes**
two tags that differ only in microstep, which is what makes the target's τ steps real rather than a
relabelling of nothing.

Together they are P24's claim, made checkable: the microstep is carried, it is not observed, and that is
what makes the repaired Theorem 1 true where the paper's is false.

## The projections must compose with the generic foundation

Tests 11 and 12 apply `Common.observableProjection` — the generic function in
`Relico/Common/WeakTransition.lean`, already proved with three `@[simp]` lemmas — to the two `project`
functions. These pins do two jobs at once. The value they assert is that τ labels are dropped and visible
ones retained in order. The *type* they assert is that `project` has the shape the generic development
requires, which is the reason `isTau` is `Prop`-valued rather than `Bool`-valued: `Common.TauSteps` and
`Common.WeakStep` take `isTau : Label → Prop`, and a `Bool` would have needed a coercion at every use and
become a second spelling of one convention.

## What is deliberately not pinned

* **`Tag.schedule` monotonicity.** `LF.Tag.precedesOrEqual_schedule` already proves it for all tags and
  delays, in `Relico/LF/PendingNotPast.lean`, and `schedule_zero` and `schedule_positive` fix both
  branches. A literal instance would follow by `rfl` and discriminate nothing — F60's failure mode exactly.
* **`idle`.** `idle_of_nil` and `idle_of_cons` are stated against explicit structure literals, so they
  already are the value pins, and restating them here would duplicate rather than extend them.
* **`isTau` at a τ label.** Its proof is `True.intro`; there is no wrong implementation of `isTau` that
  makes `isTau tau` fail while the module still compiles.
* **Anything about a step.** There is no step relation yet. The `Common.TauSteps` and `Common.WeakStep`
  instantiations, and the pin that a microstep-only advance really is classified τ, are owed by G2a-iii,
  which is where a rule first exists to emit a label.
-/

def sensorName : ActorName :=
  ActorName.mk "sensor"

def hubName : ActorName :=
  ActorName.mk "hub"

def counterName : VarName :=
  VarName.mk "counter"

def reportName : MsgName :=
  MsgName.mk "report"

def reportPortName : PortName :=
  PortName.mk "reportToHub"

def sensorState : DTR.GeneralActorState :=
  {
    valuation :=
      [
        (counterName, DTR.GeneralValue.int 3)
      ]
    bag := []
  }

def pendingReport : DTR.GeneralMessage :=
  {
    sender := sensorName
    messageName := reportName
    payload :=
      [
        DTR.GeneralValue.int 7
      ]
    arrival := 2
  }

def hubState : DTR.GeneralActorState :=
  {
    valuation := []
    bag :=
      [
        pendingReport
      ]
  }

/--
The configuration the existing development already reasons about: two actors, one of them holding a
message due at the current time.
-/
def baseConfiguration : DTR.GeneralConfiguration :=
  {
    now := 2
    actors :=
      [
        (sensorName, sensorState),
        (hubName, hubState)
      ]
  }

def busyBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.assign
      counterName
      (DTR.GeneralExpr.intLiteral 9)
  ]

def idleSensor : DTR.GeneralActorRuntime :=
  {
    state := sensorState
  }

def busySensor : DTR.GeneralActorRuntime :=
  {
    state := sensorState
    activeBody := busyBody
  }

def idleHub : DTR.GeneralActorRuntime :=
  {
    state := hubState
  }

def idleRuntime : DTR.GeneralRuntimeConfiguration :=
  {
    now := 2
    actors :=
      [
        (sensorName, idleSensor),
        (hubName, idleHub)
      ]
  }

/--
The same runtime configuration with one actor part-way through a body, and nothing else changed.
-/
def busyRuntime : DTR.GeneralRuntimeConfiguration :=
  {
    now := 2
    actors :=
      [
        (sensorName, busySensor),
        (hubName, idleHub)
      ]
  }

/- Test 1: erasure keeps every actor, in the model's order, with its state unchanged. -/
example :
    idleRuntime.erase =
      baseConfiguration := by
  rfl

/- Test 2: the continuation is the only thing erasure drops. -/
example :
    busyRuntime.erase =
      idleRuntime.erase := by
  rfl

/- Test 3: the initial runtime configuration attaches EMPTY continuations, not arbitrary ones. -/
example :
    (DTR.GeneralRuntimeConfiguration.ofConfiguration
        baseConfiguration).actors =
      [
        (sensorName, idleSensor),
        (hubName, idleHub)
      ] := by
  rfl

def tagFiveZero : LF.Tag :=
  {
    time := 5
    microstep := 0
  }

def tagFiveOne : LF.Tag :=
  {
    time := 5
    microstep := 1
  }

def tagFourNine : LF.Tag :=
  {
    time := 4
    microstep := 9
  }

/- Test 4: at equal logical time, an earlier microstep precedes a later one. -/
example :
    LF.Tag.PrecedesOrEqual
      tagFiveZero
      tagFiveOne := by
  decide

/- Test 5: and not conversely. A time-only order fails here. -/
example :
    ¬ LF.Tag.PrecedesOrEqual
        tagFiveOne
        tagFiveZero := by
  decide

/- Test 6: logical time dominates the microstep. A microstep-first order fails here. -/
example :
    LF.Tag.PrecedesOrEqual
      tagFourNine
      tagFiveZero := by
  decide

/- Test 7: and not conversely. -/
example :
    ¬ LF.Tag.PrecedesOrEqual
        tagFiveZero
        tagFourNine := by
  decide

def quietReactor : LF.GeneralReactorRuntime :=
  {
    valuation := []
  }

def stateAtMicrostepZero : LF.GeneralRuntimeState :=
  {
    currentTag := tagFiveZero
    reactors :=
      [
        (sensorName, quietReactor)
      ]
  }

def stateAtMicrostepOne : LF.GeneralRuntimeState :=
  {
    currentTag := tagFiveOne
    reactors :=
      [
        (sensorName, quietReactor)
      ]
  }

/- Test 8: the microstep is not observable. A `now` that folded it into the time fails here. -/
example :
    stateAtMicrostepZero.now =
      stateAtMicrostepOne.now := by
  rfl

/- Test 9: the microstep is nevertheless carried, so the two states are distinct. -/
example :
    stateAtMicrostepZero ≠
      stateAtMicrostepOne := by
  decide

/- Test 10: the pending queue defaults to empty, so a fresh state schedules nothing. -/
example :
    stateAtMicrostepZero.pending = [] := by
  rfl

/- Test 11: the source projection drops τ, keeps visible labels, and composes with the generic
   observable projection of `Relico/Common/WeakTransition.lean`. -/
example :
    Common.observableProjection
        DTR.GeneralLabel.project
        [
          DTR.GeneralLabel.tau,
          DTR.GeneralLabel.timeAdvance 2 5,
          DTR.GeneralLabel.tau
        ] =
      [
        DTR.GeneralLabel.timeAdvance 2 5
      ] := by
  rfl

/- Test 12: the target projection does the same, so a source trace and a target trace are comparable
   through one generic function rather than two bespoke ones. -/
example :
    Common.observableProjection
        LF.GeneralLabel.project
        [
          LF.GeneralLabel.tau,
          LF.GeneralLabel.consume
            hubName
            (LF.GeneralEventKind.inputPort
              reportPortName),
          LF.GeneralLabel.tau
        ] =
      [
        LF.GeneralLabel.consume
          hubName
          (LF.GeneralEventKind.inputPort
            reportPortName)
      ] := by
  rfl

end GeneralRuntime
end Tests
end Relico
