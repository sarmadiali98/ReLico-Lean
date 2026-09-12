import Relico.Translation.GeneralBasic
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false

/-!
# Zero-delay send pins: one instantaneous event, then time advances

The accepted General fragment admits `after(0)`: a `Delay` is a bare `Nat`, nonnegative by
construction, so zero is in the fragment and the capability ledger recorded it as the one
accepted capability with no executable pipeline evidence until the
`general--zero-delay-send--positive` fixture landed. This module is that fixture's pin
instrument, and it exists because the shape theorems cannot see the delay value:

`compileGeneralStmt_send_selfTarget` is quantified over an arbitrary delay, so it holds of a
translator that mis-rendered the offset, and the runtime boundary the external corpus screen
recorded for Minimal is about *unbounded instantaneous recurrence*, not about a single
zero-delay event. The distinction this module pins is exactly the one the fixture's README
draws: the constructor's `after(0)` send compiles to a `schedule` at delay zero, the
re-arming send inside `ping` compiles to a `schedule` at delay one, and no other
zero-delay schedule exists anywhere in the compiled program. A translator that collapsed
the re-arm's delay to zero, or that propagated the constructor's, fails here while every
theorem in the development still holds.

Every pin is `rfl`, because the point is reducibility: these evaluate `wellFormed`,
`compileGeneralModel`, and the compiled bodies through the kernel, and a regression to
well-founded recursion in any of them fails here while the library stays green. That is F89
part 1's lesson applied to the functions this capability depends on.
-/

namespace Relico
namespace Tests

/-! ## The model -/

def zeroDelayPulseClassName : ClassName :=
  ClassName.mk "Pulse"

def zeroDelayPulseName : ActorName :=
  ActorName.mk "pulse"

def zeroDelayFiredName : VarName :=
  VarName.mk "fired"

def zeroDelayPingName : MsgName :=
  MsgName.mk "ping"

/-- The constructor body: assign zero, then the capability itself, the `after(0)` self-send. -/
def zeroDelayConstructorBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.assign
      zeroDelayFiredName
      (DTR.GeneralExpr.intLiteral 0),
    DTR.GeneralStmt.send
      DTR.GeneralSendTarget.selfTarget
      zeroDelayPingName
      []
      { value := 0 }
  ]

/-- The message server's body: assign one, then the positive-delay re-arm. -/
def zeroDelayPingBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.assign
      zeroDelayFiredName
      (DTR.GeneralExpr.intLiteral 1),
    DTR.GeneralStmt.send
      DTR.GeneralSendTarget.selfTarget
      zeroDelayPingName
      []
      { value := 1 }
  ]

def zeroDelayPulseClass : DTR.GeneralReactiveClass where
  name :=
    zeroDelayPulseClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name := zeroDelayFiredName
        declaredType := .int
      }
    ]

  constructor :=
    {
      parameters := []
      body := zeroDelayConstructorBody
    }

  messageServers :=
    [
      {
        name := zeroDelayPingName
        parameters := []
        body := zeroDelayPingBody
      }
    ]

def zeroDelayPulse : DTR.GeneralActorInstance where
  name :=
    zeroDelayPulseName

  className :=
    zeroDelayPulseClassName

  bindings :=
    []

  arguments :=
    []

def zeroDelayModel : DTR.GeneralModel where
  classes :=
    [zeroDelayPulseClass]

  instances :=
    [zeroDelayPulse]

/-! ## Pin 0: the fragment accepts the model -/

/- Test 0: the model is well-formed. Zero is a legal delay by construction, and this `rfl`
   evaluates the five clauses of `DTR.GeneralModel.wellFormed` over both send sites. -/
example :
    zeroDelayModel.wellFormed =
      true := by
  rfl

/-! ## Pin 1: the model compiles -/

/- Test 1: the whole model compiles, routing and program guard included. -/
example :
    (Translation.compileGeneralModel
      zeroDelayModel).isOk =
      true := by
  rfl

/-- The compiled program, read out of the compilation so the pins below can be about its
shape. The fallback is unreachable, pin 1 says so, and it exists only so the definition
has a total value. -/
def zeroDelayCompiledProgram : LF.GeneralProgram :=
  match
      Translation.compileGeneralModel
        zeroDelayModel with
  | .ok program =>
      program
  | .error _ =>
      default

/-- The single reactor, named for the class. -/
def zeroDelayReactor : LF.GeneralReactor :=
  match zeroDelayCompiledProgram.reactors with
  | [reactor] =>
      reactor
  | _ =>
      default

/-! ## Pin 2: the instantaneous schedule -/

/- Test 2: the startup reaction, compiled from the constructor, schedules at delay zero. The
   assign comes first and the schedule second, mirroring the constructor body's statement
   order; a translator that rendered the offset in the wrong unit, dropped it into the
   payload, or swapped it with the re-arm's delay fails here. -/
example :
    (match zeroDelayReactor.startupReaction.body with
      | [
          LF.GeneralStmt.assign _ _,
          LF.GeneralStmt.schedule _ _ delay
        ] =>
          delay.value
      | _ =>
          4294967295) =
      0 := by
  rfl

/-! ## Pin 3: the re-arm advances time -/

/- Test 3: each reaction compiled for a self-send site into `ping` — there are two, one per
   site, and both carry the server's compiled body — schedules at delay one. The two sites
   are distinct actions by F56; this pin is the boundary the fixture exists to draw: the
   recurrence, at every site, is positive-delay. -/
example :
    zeroDelayReactor.messageReactions.all
      (fun reaction =>
        match reaction.body with
        | [
            LF.GeneralStmt.assign _ _,
            LF.GeneralStmt.schedule _ _ delay
          ] =>
            delay.value == 1
        | _ =>
          false) =
      true := by
  rfl

/-! ## Pin 4: exactly one instantaneous schedule exists -/

/- Test 4: across the startup reaction and every message reaction, exactly one `schedule`
   statement carries delay zero, and it belongs to the startup reaction, the constructor's
   single `after(0)` send. This is the bounded-instantaneous-scheduling claim in one
   reducible fact: no zero-delay recurrence, anywhere in the program. -/
example :
    (
      zeroDelayReactor.startupReaction.body.filterMap
        (fun statement =>
          match statement with
          | LF.GeneralStmt.schedule _ _ delay =>
              some delay.value
          | _ =>
              none) ++
      zeroDelayReactor.messageReactions.flatMap
        (fun reaction =>
          reaction.body.filterMap
            (fun statement =>
              match statement with
              | LF.GeneralStmt.schedule _ _ delay =>
                  some delay.value
              | _ =>
                  none))
    ).countP
        (fun value =>
          value == 0) =
      1 := by
  rfl

end Tests
end Relico
