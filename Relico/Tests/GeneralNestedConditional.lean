import Relico.Translation.GeneralBasic
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false

/-!
# Nested conditional pins: branch-local lifetime is a semantic claim

Stage I's local-declaration support is proved for arbitrary bodies, so none of those theorems
can see the two facts this module pins on a real model: that a local declared in one arm of a
conditional dies with that arm, and that it stays live across a conditional nested inside the
same arm. The `general--nested-conditional--positive` fixture exists because those facts are
about the elaborator's scope threading on a body that actually has the shape, and this module
is the fixture's pin instrument.

The model is one class with one message server whose body is an outer conditional. The outer
then-arm declares `t`, contains an inner conditional whose arms assign to `t`, and reads `t`
after the inner conditional closes. The outer else-arm declares its own `t`. The redeclaration
is legal only under branch-local lifetime: under body-wide scoping the elaborator's
`localShadowsDeclaredName` would refuse the model, so the model's well-formedness below is the
executable form of the lifetime-death claim, and the compiled shape is its translated form.

Every pin is `rfl` for the reducibility reason the sibling modules record: a regression to
well-founded recursion in the traversals this walks fails here while the library stays green.
-/

namespace Relico
namespace Tests

/-! ## The model -/

def nestedSelectorClassName : ClassName :=
  ClassName.mk "Selector"

def nestedSelectorName : ActorName :=
  ActorName.mk "selector"

def nestedTotalName : VarName :=
  VarName.mk "total"

def nestedStepName : MsgName :=
  MsgName.mk "step"

def nestedParameterName : VarName :=
  VarName.mk "v"

def nestedLocalName : VarName :=
  VarName.mk "t"

/-- The outer then-arm: declare `t`, branch on it, then read it after the inner branch. -/
def nestedThenBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.localDecl
      nestedLocalName
      .int
      (DTR.GeneralExpr.intLiteral 1),
    DTR.GeneralStmt.ifThenElse
      (DTR.GeneralExpr.binary
        .gt
        (DTR.GeneralExpr.parameterVar nestedParameterName)
        (DTR.GeneralExpr.intLiteral 10))
      [
        DTR.GeneralStmt.assign
          nestedLocalName
          (DTR.GeneralExpr.binary
            .add
            (DTR.GeneralExpr.parameterVar nestedLocalName)
            (DTR.GeneralExpr.intLiteral 1)),
        DTR.GeneralStmt.send
          DTR.GeneralSendTarget.selfTarget
          nestedStepName
          [DTR.GeneralExpr.intLiteral 5]
          { value := 1 }
      ]
      [
        DTR.GeneralStmt.assign
          nestedLocalName
          (DTR.GeneralExpr.binary
            .add
            (DTR.GeneralExpr.parameterVar nestedLocalName)
            (DTR.GeneralExpr.intLiteral 2)),
        DTR.GeneralStmt.send
          DTR.GeneralSendTarget.selfTarget
          nestedStepName
          [DTR.GeneralExpr.intLiteral 0]
          { value := 1 }
      ],
    DTR.GeneralStmt.assign
      nestedTotalName
      (DTR.GeneralExpr.parameterVar nestedLocalName)
  ]

/-- The outer else-arm: a fresh `t`, legal only because the then-arm's `t` died with its
branch. -/
def nestedElseBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.localDecl
      nestedLocalName
      .int
      (DTR.GeneralExpr.intLiteral 100),
    DTR.GeneralStmt.assign
      nestedTotalName
      (DTR.GeneralExpr.parameterVar nestedLocalName),
    DTR.GeneralStmt.send
      DTR.GeneralSendTarget.selfTarget
      nestedStepName
      [DTR.GeneralExpr.intLiteral 50]
      { value := 1 }
  ]

def nestedStepBody : DTR.GeneralBody :=
  [
    DTR.GeneralStmt.ifThenElse
      (DTR.GeneralExpr.binary
        .gt
        (DTR.GeneralExpr.parameterVar nestedParameterName)
        (DTR.GeneralExpr.intLiteral 0))
      nestedThenBody
      nestedElseBody
  ]

def nestedSelectorClass : DTR.GeneralReactiveClass where
  name :=
    nestedSelectorClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name := nestedTotalName
        declaredType := .int
      }
    ]

  constructor :=
    {
      parameters := []
      body :=
        [
          DTR.GeneralStmt.assign
            nestedTotalName
            (DTR.GeneralExpr.intLiteral 0),
          DTR.GeneralStmt.send
            DTR.GeneralSendTarget.selfTarget
            nestedStepName
            [DTR.GeneralExpr.intLiteral 50]
            { value := 1 }
        ]
    }

  messageServers :=
    [
      {
        name := nestedStepName
        parameters :=
          [
            {
              name := nestedParameterName
              declaredType := .int
            }
          ]
        body := nestedStepBody
      }
    ]

def nestedSelector : DTR.GeneralActorInstance where
  name :=
    nestedSelectorName

  className :=
    nestedSelectorClassName

  bindings :=
    []

  arguments :=
    []

def nestedModel : DTR.GeneralModel where
  classes :=
    [nestedSelectorClass]

  instances :=
    [nestedSelector]

/-! ## Pin 0: the fragment accepts the model -/

/- Test 0: the model is well-formed. This is the lifetime-death claim: the else-arm's
   `localDecl` of a name the then-arm also declares is accepted, which under body-wide
   scoping the elaborator would refuse as `localShadowsDeclaredName`. The `rfl` evaluates
   the five well-formedness clauses over both branch bodies. -/
example :
    nestedModel.wellFormed =
      true := by
  rfl

/-! ## Pin 1: the model compiles -/

/- Test 1: the whole model compiles, routing and program guard included. -/
example :
    (Translation.compileGeneralModel
      nestedModel).isOk =
      true := by
  rfl

def nestedCompiledProgram : LF.GeneralProgram :=
  match
      Translation.compileGeneralModel
        nestedModel with
  | .ok program =>
      program
  | .error _ =>
      default

def nestedReactor : LF.GeneralReactor :=
  match nestedCompiledProgram.reactors with
  | [reactor] =>
      reactor
  | _ =>
      default

/-! ## Pin 2: the nesting survives translation -/

/- Test 2: every reaction compiled for a self-send site into `step` — there are four, one
   per site, and all carry the server's compiled body — is a single conditional whose
   then-branch has three statements and whose else-branch has three. A translator that
   flattened the branches into the enclosing body, reordered them, or dropped one fails
   here. -/
example :
    nestedReactor.messageReactions.all
      (fun reaction =>
        match reaction.body with
        | [
            LF.GeneralStmt.ifThenElse
              _
              thenBody
              elseBody
          ] =>
            (thenBody.length == 3) &&
              (elseBody.length == 3)
        | _ =>
          false) =
      true := by
  rfl

/-! ## Pin 3: the branch-local declarations survive translation -/

/- Test 3: in the first site reaction's body, both branch bodies lead with a `localDecl` of
   the same name, and the then-branch reads it after its inner conditional, which is
   statement 1. This is the translated shape of the lifetime claim: two same-name
   declarations in sibling arms, one read after the nested branch closes. -/
example :
    (match
        nestedReactor.messageReactions with
      | reaction :: _ =>
          match reaction.body with
          | [
              LF.GeneralStmt.ifThenElse
                _
                (
                  LF.GeneralStmt.localDecl
                    thenLocal
                    _
                    _ ::
                  LF.GeneralStmt.ifThenElse
                    _ _ _ ::
                  LF.GeneralStmt.assign
                    afterRead
                    _ ::
                  restThen
                )
                (
                  LF.GeneralStmt.localDecl
                    elseLocal
                    _
                    _ ::
                  restElse
                )
            ] =>
              (thenLocal, afterRead, elseLocal,
                restThen.length, restElse.length)
          | _ =>
              (VarName.mk "", VarName.mk "",
                VarName.mk "",
                4294967295, 4294967295)
      | [] =>
          (VarName.mk "", VarName.mk "",
            VarName.mk "",
            4294967295, 4294967295)) =
      (nestedLocalName, nestedTotalName,
        nestedLocalName, 0, 2) := by
  rfl

/-! ## Pin 4: the inner conditional survives with its sends -/

/- Test 4: the inner conditional of the then-branch has exactly one statement in each arm,
   the assignment to the live local followed by the re-arming schedule with its distinct
   payload. The per-site actions for the three sends are distinct by construction; this pin
   holds the shape that makes them distinguishable. -/
example :
    (match
        nestedReactor.messageReactions with
      | reaction :: _ =>
          match reaction.body with
          | [
              LF.GeneralStmt.ifThenElse
                _
                (
                  LF.GeneralStmt.localDecl _ _ _ ::
                  LF.GeneralStmt.ifThenElse
                    _
                    innerThen
                    innerElse ::
                  _
                )
                _
            ] =>
              (innerThen.length, innerElse.length)
          | _ =>
              (4294967295, 4294967295)
      | [] =>
          (4294967295, 4294967295)) =
      (2, 2) := by
  rfl

end Tests
end Relico
