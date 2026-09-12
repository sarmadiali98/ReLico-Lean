import Relico.Translation.GeneralBasic
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false

/-!
# Constructor argument pins: literals bind positionally into reactor parameters

The fragment admits literal constructor arguments, integer or boolean, and the generated
target subset says constructor formals become reactor parameters while an instance's arguments
become its parameter values. Those two sentences are the capability the
`general--constructor-arguments--positive` fixture demonstrates, and neither the shape
theorems nor the actor-priority fixture's incidental integer identifiers can see the two
halves together: boolean parameter flow through the target toolchain was unmeasured before
this fixture's `lfc` stage, and no pin held the positional binding of a mixed-type argument
list.

This module is the fixture's pin instrument. The model is the frontend anchor
`constructor-arguments` verbatim: one class with an integer and a boolean constructor formal,
two instances carrying `(7, true)` and `(0, false)`. The pins hold the assembly: the reactor's
parameter list in the formals' declared order with their declared types, and each instance's
argument list as the literal values in positional order. A translator that swapped the
parameters, dropped a type, or reordered an instance's arguments fails here while the
library's quantified theorems still hold.

Every pin is `rfl`, for the reducibility reason the sibling modules record.
-/

namespace Relico
namespace Tests

/-! ## The model -/

def ctorConfiguredClassName : ClassName :=
  ClassName.mk "Configured"

def ctorConfiguredOnName : ActorName :=
  ActorName.mk "configuredOn"

def ctorConfiguredOffName : ActorName :=
  ActorName.mk "configuredOff"

def ctorLimitName : VarName :=
  VarName.mk "limit"

def ctorEnabledName : VarName :=
  VarName.mk "enabled"

def ctorBoundName : VarName :=
  VarName.mk "bound"

def ctorActiveName : VarName :=
  VarName.mk "active"

def ctorReconfigureName : MsgName :=
  MsgName.mk "reconfigure"

def ctorConfiguredClass : DTR.GeneralReactiveClass where
  name :=
    ctorConfiguredClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name := ctorLimitName
        declaredType := .int
      },
      {
        name := ctorEnabledName
        declaredType := .boolean
      }
    ]

  constructor :=
    {
      parameters :=
        [
          {
            name := ctorBoundName
            declaredType := .int
          },
          {
            name := ctorActiveName
            declaredType := .boolean
          }
        ],
      body :=
        [
          DTR.GeneralStmt.assign
            ctorLimitName
            (DTR.GeneralExpr.parameterVar
              ctorBoundName),
          DTR.GeneralStmt.assign
            ctorEnabledName
            (DTR.GeneralExpr.parameterVar
              ctorActiveName)
        ]
    }

  messageServers :=
    [
      {
        name := ctorReconfigureName
        parameters :=
          [
            {
              name := ctorBoundName
              declaredType := .int
            },
            {
              name := ctorActiveName
              declaredType := .boolean
            }
          ]
        body :=
          [
            DTR.GeneralStmt.assign
              ctorLimitName
              (DTR.GeneralExpr.parameterVar
                ctorBoundName),
            DTR.GeneralStmt.assign
              ctorEnabledName
              (DTR.GeneralExpr.parameterVar
                ctorActiveName)
          ]
      }
    ]

def ctorConfiguredOn : DTR.GeneralActorInstance where
  name :=
    ctorConfiguredOnName

  className :=
    ctorConfiguredClassName

  bindings :=
    []

  arguments :=
    [
      DTR.GeneralValue.int 7,
      DTR.GeneralValue.bool true
    ]

def ctorConfiguredOff : DTR.GeneralActorInstance where
  name :=
    ctorConfiguredOffName

  className :=
    ctorConfiguredClassName

  bindings :=
    []

  arguments :=
    [
      DTR.GeneralValue.int 0,
      DTR.GeneralValue.bool false
    ]

def ctorModel : DTR.GeneralModel where
  classes :=
    [ctorConfiguredClass]

  instances :=
    [ctorConfiguredOn, ctorConfiguredOff]

/-! ## Pin 0: the fragment accepts the model -/

/- Test 0: the model is well-formed. The `rfl` evaluates `argumentsMatchConstructor` over both
   instances, which is the arity-and-type half of positional binding on the source side. -/
example :
    ctorModel.wellFormed =
      true := by
  rfl

/-! ## Pin 1: the model compiles -/

/- Test 1: the whole model compiles, routing and program guard included. -/
example :
    (Translation.compileGeneralModel
      ctorModel).isOk =
      true := by
  rfl

def ctorCompiledProgram : LF.GeneralProgram :=
  match
      Translation.compileGeneralModel
        ctorModel with
  | .ok program =>
      program
  | .error _ =>
      default

def ctorReactor : LF.GeneralReactor :=
  match ctorCompiledProgram.reactors with
  | [reactor] =>
      reactor
  | _ =>
      default

/-! ## Pin 2: the formals become reactor parameters, in order, with their types -/

/- Test 2: the reactor's parameter list is the constructor's formals in declared order:
   `bound : int` then `active : boolean`. A translator that reordered the parameters,
   dropped one, or lost the boolean's type fails here. -/
example :
    ctorReactor.parameters =
      [
        {
          name := ctorBoundName
          declaredType := .int
        },
        {
          name := ctorActiveName
          declaredType := .boolean
        }
      ] := by
  rfl

/-! ## Pin 3: the instances' arguments become parameter values, positionally -/

/- Test 3: `configuredOn` carries `[int 7, bool true]` and `configuredOff` carries
   `[int 0, bool false]`, each matched positionally against the parameter list of pin 2.
   The lookup is by instance name so the pin does not depend on the program's instance
   ordering. This is the target-side half of the binding: a swapped pair, a widened
   boolean, or a dropped literal fails here. -/
example :
    (
      List.map
        (fun row =>
          row.arguments)
        (ctorCompiledProgram.instances.filter
          (fun row =>
            row.name == ctorConfiguredOnName)),
      List.map
        (fun row =>
          row.arguments)
        (ctorCompiledProgram.instances.filter
          (fun row =>
            row.name == ctorConfiguredOffName))
    ) =
      ([[LF.GeneralValue.int 7,
          LF.GeneralValue.bool true]],
        [[LF.GeneralValue.int 0,
          LF.GeneralValue.bool false]]) := by
  rfl

end Tests
end Relico
