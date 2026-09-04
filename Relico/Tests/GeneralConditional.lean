import Relico.LF.GeneralCppPrinter
import Relico.Translation.GeneralBasic
import Relico.DTR.GeneralSemantics
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false

/-!
# Stage H regression pins: a conditional with an external send inside a branch

`docs/decisions/0046-send-site-identity-under-nested-control-flow.md`. Stage H's `ifThenElse` support
is proved across ten layers, and every one of those proofs is quantified over *arbitrary* bodies. That
is exactly why they cannot see an addressing mistake: swap the two branch selectors, or drop the
`levelPath` prefix when a branch is entered, and every theorem in the development still holds — they
would hold of a translator that addresses branch sends differently from the way `0046` says it does.
The gates could not see it either when this module was written, and that is now only half true.
`GENERAL_LEAN_GATE_OK` **does** see the feature as of stage I0: `frontend/fixtures/general/branching.parser.json`
carries conditionals nested two deep with a send in each branch, and the frontend runner inside that gate
decodes it as `PASS_ACCEPT_BRANCHING`. `GENERAL_LF_TARGET_OK` is still silent, and precisely: **real `lfc`
has never compiled a generated conditional.** That gate compiles programs built by the bridge mains, none
of which contains one, so the emitted `if (…) { … } else {}` text is pinned only by test 8 below and has
never been consumed by the target compiler. Do not read a green LF target gate as evidence that `lfc`
accepts what this printer emits for a branch.

This module is the instrument that sees it. One model, one conditional, one external send inside its
then-branch, pinned three ways:

1. **The address.** `Translation.externalSendsOfClass` reports the send at path `[1, 0, 0]`, rendered
   `1.0.0`: statement 1 of the message-server body, then-branch, statement 0 of that branch. That is the
   alternating encoding of `0046` read off a real body, and it is the pin that fails if a selector, a
   prefix or an ordinal moves.
2. **The compiled shape.** The body compiles, and the compiled statement at position 1 is an
   `LF.GeneralStmt.ifThenElse` whose then-branch holds exactly one `setPort` and whose else-branch is
   empty. So the nesting survives translation rather than being flattened.
3. **The emitted text.** `LF.CppPrinter.renderGeneralStmt` puts the whole conditional on one
   line, with an empty else-branch printed `{}`. That is the option (b) formatting decision of stage H,
   and it is the property `renderGeneralBody`'s single four-space indent depends on.
4. **The runtime.** A concrete three-step run through `DTR.GeneralStep`: enter the then-branch, execute
   the statement inside it, resume the enclosing level. Plus the mirror entry into the else-branch, and
   the idleness fact the whole continuation stack exists for.

The static pins and the runtime pins are complementary and neither implies the other. The first three
groups are about the *artefact* the translator emits; the fourth is about the *relation* that steps a
source configuration, and a translator and a semantics can disagree while each is internally
consistent.

The model **is** claimed to be well-formed, and pin 0 below is that claim. Until stage I0 this
paragraph said the opposite, and it was right at the time: `DTR.GeneralModel.statementResolves`
answered `false` for `DTR.GeneralStmt.ifThenElse`, so the accepted fragment excluded this model and
stage H's declared fragment was unchanged by this file. Stage I0 made that arm a recursion into both
branch bodies, so a conditional whose nested sends resolve is now accepted, and this model's nested
send does resolve.

Pin 0 earns its place twice. It is the acceptance claim, and it is the **only** reducibility
instrument the recursion has: `DTR.GeneralModel.wellFormed` is a `Bool` that no other
`Relico/Tests/*` module evaluates, so if `statementResolves` ever falls from structural to
well-founded recursion, nothing else in the development notices and this `rfl` is what fails. That is
F89 part 1's failure mode, aimed at the definition stage I0 changed.
-/

namespace Relico
namespace Tests

/-! ## The model -/

def conditionalSensorClassName : ClassName :=
  ClassName.mk "Sensor"

def conditionalHubClassName : ClassName :=
  ClassName.mk "Hub"

def conditionalSensorName : ActorName :=
  ActorName.mk "sensor"

def conditionalHubName : ActorName :=
  ActorName.mk "hub"

/-- The sensor's known rebec, through which the branch's send is routed. -/
def conditionalPeerName : KnownRebecName :=
  KnownRebecName.mk "peer"

def conditionalActiveName : VarName :=
  VarName.mk "active"

def conditionalPollName : MsgName :=
  MsgName.mk "poll"

def conditionalReportName : MsgName :=
  MsgName.mk "report"

/--
The body under test: an assignment, then a conditional whose then-branch sends.

Positions matter and are the whole point. The assignment is statement `0`, so the conditional is
statement `1`, and the send is statement `0` of the then-branch — address `[1, 0, 0]`. The else-branch
is empty, which `LF.stmtWellFormed` accepts and the printer prints as `{}`, so the empty case is
exercised rather than avoided.
-/
def conditionalPollBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.assign
      conditionalActiveName
      (DTR.GeneralExpr.boolLiteral true),
    DTR.GeneralStmt.ifThenElse
      (DTR.GeneralExpr.stateVar
        conditionalActiveName)
      [
        DTR.GeneralStmt.send
          (DTR.GeneralSendTarget.knownRebec
            conditionalPeerName)
          conditionalReportName
          [DTR.GeneralExpr.intLiteral 1]
          { value := 0 }
      ]
      []
  ]

def conditionalSensorClass : DTR.GeneralReactiveClass where
  name :=
    conditionalSensorClassName

  knownRebecs :=
    [
      {
        name := conditionalPeerName
        className := conditionalHubClassName
      }
    ]

  stateVariables :=
    [
      {
        name := conditionalActiveName
        declaredType := .boolean
      }
    ]

  constructor :=
    {
      parameters := []
      body := []
    }

  messageServers :=
    [
      {
        name := conditionalPollName
        parameters := []
        body := conditionalPollBody
      }
    ]

def conditionalHubClass : DTR.GeneralReactiveClass where
  name :=
    conditionalHubClassName

  knownRebecs :=
    []

  stateVariables :=
    []

  constructor :=
    {
      parameters := []
      body := []
    }

  messageServers :=
    [
      {
        name := conditionalReportName
        parameters :=
          [
            {
              name := VarName.mk "value"
              declaredType := .int
            }
          ]
        body := []
      }
    ]

def conditionalSensor : DTR.GeneralActorInstance where
  name :=
    conditionalSensorName

  className :=
    conditionalSensorClassName

  bindings :=
    [
      (conditionalPeerName, conditionalHubName)
    ]

  arguments :=
    []

def conditionalHub : DTR.GeneralActorInstance where
  name :=
    conditionalHubName

  className :=
    conditionalHubClassName

  bindings :=
    []

  arguments :=
    []

def conditionalModel : DTR.GeneralModel where
  classes :=
    [
      conditionalSensorClass,
      conditionalHubClass
    ]

  instances :=
    [
      conditionalSensor,
      conditionalHub
    ]

/-! ## Pin 0: the fragment accepts the model -/

/- Test 0: the model is well-formed. Stage I0's whole subject, and the reducibility instrument for the
   recursion it added: `rfl` here evaluates `sendsResolveToMessageServers`, which evaluates
   `bodyResolves`, which descends into the then-branch and reaches the nested send. -/
example :
    conditionalModel.wellFormed =
      true := by
  rfl

/-! ## Pin 1: the nested address -/

/- Test 1: the class's only external send sits at the alternating path `[1, 0, 0]`. -/
example :
    (Translation.externalSendsOfClass
      conditionalSensorClass).map
      (fun send =>
        send.site.index) =
      [[1, 0, 0]] := by
  rfl

/- Test 2: the same address as the diagnostics render it, `1.0.0` and not `[1, 0, 0]`. -/
example :
    (Translation.externalSendsOfClass
      conditionalSensorClass).map
      (fun send =>
        Translation.renderGeneralSitePath
          send.site.index) =
      ["1.0.0"] := by
  rfl

/- Test 3: the send is attributed to the message server's body, not the constructor's. -/
example :
    (Translation.externalSendsOfClass
      conditionalSensorClass).map
      (fun send =>
        send.site.body) =
      [
        Translation.GeneralBodyKey.messageServer
          conditionalPollName
      ] := by
  rfl

/-! ## Pin 2: the compiled shape -/

/-- The port environment the routing side derives for the sensor class. -/
def conditionalEnv : Translation.GeneralOutputPortEnv :=
  match
      Translation.outputPortEnvOf
        conditionalModel.classes
        conditionalSensorClass with
  | .ok env =>
      env
  | .error _ =>
      []

/-- The compilation context of the message-server body, at the top level. -/
def conditionalContext : Translation.GeneralBodyContext where
  bodyKey :=
    .messageServer
      conditionalPollName

  selfSends :=
    Translation.selfSendsOfClass
      conditionalSensorClass

/-- The compiled body, read out of the compilation so the pins below can be about its shape. -/
def conditionalCompiledBody : LF.GeneralBody :=
  match
      Translation.compileGeneralBody
        conditionalEnv
        conditionalContext
        0
        conditionalPollBody with
  | .ok compiled =>
      compiled
  | .error _ =>
      []

/- Test 4: the whole model compiles, routing and program guard included. -/
example :
    (Translation.compileGeneralModel
      conditionalModel).isOk =
      true := by
  rfl

/- Test 5: the message-server body compiles, and `conditionalCompiledBody` is what it produced. -/
example :
    Translation.compileGeneralBody
        conditionalEnv
        conditionalContext
        0
        conditionalPollBody =
      .ok conditionalCompiledBody := by
  rfl

/- Test 6: the nesting survives translation. Two statements, the second a conditional with one
   `setPort` in its then-branch and nothing in its else-branch. A translator that flattened the branch
   into the enclosing body, or that dropped the empty branch, fails here. -/
example :
    (match conditionalCompiledBody with
      | [
          LF.GeneralStmt.assign _ _,
          LF.GeneralStmt.ifThenElse
            _
            [LF.GeneralStmt.setPort _ _]
            []
        ] =>
          true
      | _ =>
          false) =
      true := by
  rfl

/- Test 7: the branch's port is counted by the static port list. This is the conservative static
   reading of stage H: `LF.setPortNamesOfBody` looks inside both branches, so a port set only under a
   condition is still a port of the compiled reaction. A path-dependent reading would report zero. -/
example :
    (LF.setPortNamesOfBody
      conditionalCompiledBody).length =
      1 := by
  rfl

/-! ## Pin 3: the emitted text -/

/-- An output port for the printer pin, with the scalar payload the branch's send carries. -/
def conditionalPrinterPort : LF.GeneralPortDecl where
  name :=
    PortName.mk "reportToHub"

  payload :=
    .scalar .int

/-- The compiled conditional, written out so the printer pin is about text and nothing else. -/
def conditionalPrinterStmt : LF.GeneralStmt :=
  .ifThenElse
    (LF.GeneralExpr.stateVar
      conditionalActiveName)
    [
      LF.GeneralStmt.setPort
        (PortName.mk "reportToHub")
        [LF.GeneralExpr.intLiteral 1]
    ]
    []

/- Test 8: a conditional is emitted on one line, and an empty else-branch prints `{}`. Both are load
   bearing: `renderGeneralBody` prefixes exactly one four-space indent to a statement's first line, so a
   multi-line conditional would emit its interior flush left. -/
example :
    LF.CppPrinter.renderGeneralStmt
        (ReactorName.mk "Sensor")
        [conditionalPrinterPort]
        conditionalPrinterStmt =
      Except.ok
        "if (active) { reportToHub.set(1); } else {}" := by
  rfl

/-! ## Pin 4: the runtime

Concrete `DTR.GeneralStep` derivations, following `Relico/Tests/GeneralSemantics.lean`'s convention: an
actor runtime, a configuration, the expected successor written out, and the rule applied with its
implicits named and its premises `rfl`.

The body is two traces rather than the send of the static pins above. That is deliberate and minimal:
the branch rules read a condition and rewrite two continuation fields, and they consult neither the
routing table nor the bag, so a send here would add machinery the pins are not about. What the run does
exercise is the whole of stage H's step-into design — that entering a branch *pushes* rather than
concatenates, that the pushed frame comes back, and that an actor mid-branch is not idle.
-/

/-- The body under test at run time: one conditional, one trace in each branch. -/
def conditionalRuntimeBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.ifThenElse
      (DTR.GeneralExpr.stateVar
        conditionalActiveName)
      [DTR.GeneralStmt.trace "then"]
      [DTR.GeneralStmt.trace "else"]
  ]

/-- An actor whose condition holds. -/
def conditionalRuntimeTrueActor : DTR.GeneralActorRuntime where
  state :=
    {
      valuation :=
        [
          (conditionalActiveName,
            DTR.GeneralValue.bool true)
        ]
      bag := []
    }

  activeBody :=
    conditionalRuntimeBody

  frames :=
    []

/-- The same actor with the condition false, for the else-branch pin. -/
def conditionalRuntimeFalseActor : DTR.GeneralActorRuntime where
  state :=
    {
      valuation :=
        [
          (conditionalActiveName,
            DTR.GeneralValue.bool false)
        ]
      bag := []
    }

  activeBody :=
    conditionalRuntimeBody

  frames :=
    []

def conditionalTrueConfig : DTR.GeneralRuntimeConfiguration where
  now := 5

  actors :=
    [
      (conditionalSensorName,
        conditionalRuntimeTrueActor)
    ]

def conditionalFalseConfig : DTR.GeneralRuntimeConfiguration where
  now := 5

  actors :=
    [
      (conditionalSensorName,
        conditionalRuntimeFalseActor)
    ]

/--
After entering the then-branch: the branch is the active body and the enclosing remainder — here the
empty tail of the one-statement body — is on the stack.

`frames := [[]]` rather than `frames := []` is the pin that distinguishes step-into from splicing. A
translator-semantics that concatenated would leave the stack empty and the two states would be
indistinguishable by `activeBody` alone.
-/
def conditionalAfterEnterTrue : DTR.GeneralRuntimeConfiguration where
  now := 5

  actors :=
    [
      (conditionalSensorName,
        {
          state :=
            conditionalRuntimeTrueActor.state
          activeBody :=
            [DTR.GeneralStmt.trace "then"]
          frames := [[]]
        })
    ]

/-- After entering the else-branch, the mirror image. -/
def conditionalAfterEnterFalse : DTR.GeneralRuntimeConfiguration where
  now := 5

  actors :=
    [
      (conditionalSensorName,
        {
          state :=
            conditionalRuntimeFalseActor.state
          activeBody :=
            [DTR.GeneralStmt.trace "else"]
          frames := [[]]
        })
    ]

/-- After the branch's own statement runs: the level is spent but the frame is still owed. -/
def conditionalAfterBranchBody : DTR.GeneralRuntimeConfiguration where
  now := 5

  actors :=
    [
      (conditionalSensorName,
        {
          state :=
            conditionalRuntimeTrueActor.state
          activeBody := []
          frames := [[]]
        })
    ]

/-- After resuming: nothing left at any level. -/
def conditionalAfterResume : DTR.GeneralRuntimeConfiguration where
  now := 5

  actors :=
    [
      (conditionalSensorName,
        {
          state :=
            conditionalRuntimeTrueActor.state
          activeBody := []
          frames := []
        })
    ]

/- Test 9: a true condition enters the then-branch and pushes the enclosing remainder. -/
theorem conditionalBranchTrueStep :
    DTR.GeneralStep
      conditionalModel
      conditionalTrueConfig
      DTR.GeneralLabel.tau
      conditionalAfterEnterTrue :=
  DTR.GeneralStep.branchTrue
    (actorName := conditionalSensorName)
    (actor := conditionalRuntimeTrueActor)
    (condition :=
      DTR.GeneralExpr.stateVar
        conditionalActiveName)
    (thenBody :=
      [DTR.GeneralStmt.trace "then"])
    (elseBody :=
      [DTR.GeneralStmt.trace "else"])
    (remaining := [])
    rfl
    rfl
    rfl

/- Test 10: a false condition enters the else-branch, and nothing else about the state moves. -/
theorem conditionalBranchFalseStep :
    DTR.GeneralStep
      conditionalModel
      conditionalFalseConfig
      DTR.GeneralLabel.tau
      conditionalAfterEnterFalse :=
  DTR.GeneralStep.branchFalse
    (actorName := conditionalSensorName)
    (actor := conditionalRuntimeFalseActor)
    (condition :=
      DTR.GeneralExpr.stateVar
        conditionalActiveName)
    (thenBody :=
      [DTR.GeneralStmt.trace "then"])
    (elseBody :=
      [DTR.GeneralStmt.trace "else"])
    (remaining := [])
    rfl
    rfl
    rfl

/- Test 11: the statement inside the branch runs as any statement does, and the frame is untouched. -/
theorem conditionalBranchBodyStep :
    DTR.GeneralStep
      conditionalModel
      conditionalAfterEnterTrue
      DTR.GeneralLabel.tau
      conditionalAfterBranchBody :=
  DTR.GeneralStep.trace
    (actorName := conditionalSensorName)
    (actor :=
      {
        state :=
          conditionalRuntimeTrueActor.state
        activeBody :=
          [DTR.GeneralStmt.trace "then"]
        frames := [[]]
      })
    (tag := "then")
    (remaining := [])
    rfl
    rfl

/- Test 12: resume pops the frame. This is the step without which an actor that entered a branch could
   never leave it, because `take` is premised on idleness and idleness reads the stack. -/
theorem conditionalResumeStep :
    DTR.GeneralStep
      conditionalModel
      conditionalAfterBranchBody
      DTR.GeneralLabel.tau
      conditionalAfterResume :=
  DTR.GeneralStep.resume
    (actorName := conditionalSensorName)
    (actor :=
      {
        state :=
          conditionalRuntimeTrueActor.state
        activeBody := []
        frames := [[]]
      })
    (frame := [])
    (frames := [])
    rfl
    rfl
    rfl

/- Test 13: the three steps are τ, so the clock does not move across the whole run. -/
example :
    conditionalAfterEnterTrue.now =
      conditionalTrueConfig.now :=
  DTR.GeneralStep.now_eq_of_tau
    conditionalBranchTrueStep

example :
    conditionalAfterResume.now =
      conditionalAfterBranchBody.now :=
  DTR.GeneralStep.now_eq_of_tau
    conditionalResumeStep

/- Test 14: an actor that has finished a branch but still owes its frame is **not** idle. This is the
   reason the stack exists and the reason `idle` gained a second conjunct: reading `activeBody` alone
   would let `take` install a second message-server body on top of a half-executed one. -/
example :
    DTR.GeneralActorRuntime.idle
        {
          state :=
            conditionalRuntimeTrueActor.state
          activeBody := []
          frames := [[]]
        } =
      false := by
  rfl

/- Test 15: after resuming, the same actor is idle. -/
example :
    DTR.GeneralActorRuntime.idle
        {
          state :=
            conditionalRuntimeTrueActor.state
          activeBody := []
          frames := []
        } =
      true := by
  rfl
