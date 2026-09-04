import Relico.LF.GeneralSyntax
import Relico.LF.GeneralWellFormed
import Relico.LF.GeneralCppPrinter
import Relico.DTR.GeneralSyntax
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false

/-!
# Stage I regression pins: the local declaration constructor exists and is not yet a source

`LF.GeneralStmt.localDecl` landed in S-I2, the target half of stage I's local-declaration support,
and this module is the instrument that pins what the milestones so far actually established. The
design is deliberately split across steps: the DTR constructor `DTR.GeneralStmt.localDecl` exists
since S-I1 and is refused by every guard; the LF constructor exists as of S-I2; and as of S-I3 the
translator compiles the source constructor into it, so the LF form *is* producible — from a
hand-built source model, because no well-formed one can contain a declaration yet. The guards'
refusal is the load-bearing property this module pins, now from the one direction that still
holds it.

**What the stage so far did not do, and this module says so rather than implying it.** No runtime
support: an actor whose head statement is an `LF.GeneralStmt.localDecl` has no step rule, so
nothing steps it, and no pin below claims any transition. No store or environment change: the
declaration is a statement, not a binding form the valuation knows about. No expression
constructor: a local *read* is a `.parameterVar` by the stage I rulings, and no pin below involves
reading a local back, which is a later layer's concern. No guard widening:
`stmtWellFormed`'s `.assign` arm still demands a declared **state variable**, and the pin below
proves an assignment to a local name is still refused. The remaining refusals are pinned on the
DTR side, executable against `statementResolves` and `statementTargetDeclared` directly. This
module still imports no `Translation.*`: not because the translation module is red — S-I3 closed
that — but because the translation's own behaviour is the next layer's pin, and this module's
subject is the boundary, not the compilation.

Every pin is `rfl` or `decide`, because the whole point is reducibility: these evaluate the
constructor through `decEqGeneralStmt`, the guard, the port census and the printer, and a
regression to well-founded recursion in any of them would fail here while the library stayed
green. That is F89 part 1's lesson applied to the functions stage I touched.
-/

namespace Relico
namespace Tests

/-! ## Shared names and reactors -/

def localDeclReactorName :
    ReactorName :=
  ⟨"LocalDecl"⟩

def localDeclVarName :
    VarName :=
  ⟨"temporary"⟩

def localDeclFlagName :
    VarName :=
  ⟨"flag"⟩

def localDeclUnusedName :
    VarName :=
  ⟨"nowhere"⟩

def localDeclStartupReactionName :
    ReactionName :=
  ⟨"startup"⟩

/--
A reactor with one integer state variable and nothing else, so every guard pin's answer is a fact
about the statement alone and not about a larger declaration context.
-/
def localDeclReactor :
    LF.GeneralReactor where

  name :=
    localDeclReactorName

  parameters :=
    []

  inputPorts :=
    []

  outputPorts :=
    []

  stateVariables :=
    [
      {
        name :=
          localDeclVarName

        declaredType :=
          .int
      }
    ]

  logicalActions :=
    []

  startupReaction :=
    {
      name :=
        localDeclStartupReactionName

      trigger :=
        .startup

      parameters :=
        []

      body :=
        []
    }

  messageReactions :=
    []

/-! ## Pin 1: the constructor exists and equals only itself -/

/- Test 1: two identical declarations are equal, through the hand-written
   `decEqGeneralStmt`. A regression from structural recursion to well-founded recursion in that
   definition stops this `decide` from evaluating while the library stays green. -/
example :
    (decide (
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1) :
        LF.GeneralStmt) =
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1)))) =
    true := by
  decide

/- Test 2: a declaration is distinct from an assignment, and from a conditional. The cross arms
   exist so that a new constructor breaks the match loudly; this pins that they decide. -/
example :
    (decide (
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1) :
        LF.GeneralStmt) =
      (LF.GeneralStmt.assign
        localDeclVarName
        (LF.GeneralExpr.intLiteral 1)))) =
    false := by
  decide

example :
    (decide (
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1) :
        LF.GeneralStmt) =
      (LF.GeneralStmt.ifThenElse
        (LF.GeneralExpr.boolLiteral true)
        [] []))) =
    false := by
  decide

/- Test 3: two declarations differing in name, in type, or in initialiser are unequal, one pin per
   diagonal hypothesis of the hand-written decision procedure. -/
example :
    (decide (
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1) :
        LF.GeneralStmt) =
      (LF.GeneralStmt.localDecl
        localDeclFlagName
        .int
        (LF.GeneralExpr.intLiteral 1)))) =
    false := by
  decide

example :
    (decide (
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1) :
        LF.GeneralStmt) =
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .boolean
        (LF.GeneralExpr.intLiteral 1)))) =
    false := by
  decide

example :
    (decide (
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 1) :
        LF.GeneralStmt) =
      (LF.GeneralStmt.localDecl
        localDeclVarName
        .int
        (LF.GeneralExpr.intLiteral 2)))) =
    false := by
  decide

/-! ## Pin 2: the printer emits a C++ declaration -/

/- Test 4: the int spelling. One line, because `renderGeneralBody` prefixes exactly one four-space
   indent to a statement's first line and a multi-line form would emit its continuation flush
   left; that constraint is why the stage H conditional is single-line too. -/
example :
    LF.CppPrinter.renderGeneralStmt
        localDeclReactorName
        []
        (LF.GeneralStmt.localDecl
          localDeclVarName
          .int
          (LF.GeneralExpr.intLiteral 1)) =
      Except.ok "int temporary = 1;" := by
  rfl

/- Test 5: the boolean spelling, through the same `renderGeneralType` that state-variable
   declarations already use, so the two spellings cannot drift apart. -/
example :
    LF.CppPrinter.renderGeneralStmt
        localDeclReactorName
        []
        (LF.GeneralStmt.localDecl
          localDeclFlagName
          .boolean
          (LF.GeneralExpr.boolLiteral true)) =
      Except.ok "bool flag = true;" := by
  rfl

/-! ## Pin 3: the port census ignores a declaration -/

/- Test 6: a declaration contributes no output port. -/
example :
    LF.setPortNamesOfStmt
        (LF.GeneralStmt.localDecl
          localDeclVarName
          .int
          (LF.GeneralExpr.intLiteral 1)) =
    [] := by
  rfl

/- Test 7: a declaration in front of a `setPort` shifts nothing: the body's ports are the tail's.
   A traversal that skipped the tail, or that consumed an index for a port, fails here. -/
example :
    LF.setPortNamesOfBody
        [
          LF.GeneralStmt.localDecl
            localDeclVarName
            .int
            (LF.GeneralExpr.intLiteral 1),
          LF.GeneralStmt.setPort
            (PortName.mk "out")
            [LF.GeneralExpr.intLiteral 2]
        ] =
    [PortName.mk "out"] := by
  rfl

/-! ## Pin 4: the guard accepts a declaration and still refuses a local assignment -/

/- Test 8: a declaration with a well-formed initialiser is well-formed. The name is unconstrained
   by the arm, so even a name the reactor never declares passes, which is the S-I2 ruling: scope
   is the source elaborator's concern, not this predicate's. -/
example :
    LF.GeneralReactor.stmtWellFormed
        localDeclReactor
        []
        (LF.GeneralStmt.localDecl
          localDeclUnusedName
          .int
          (LF.GeneralExpr.intLiteral 1)) =
    true := by
  rfl

/- Test 9: the initialiser is checked. A `stateVar` initialiser naming a variable the reactor does
   not declare is refused. -/
example :
    LF.GeneralReactor.stmtWellFormed
        localDeclReactor
        []
        (LF.GeneralStmt.localDecl
          localDeclVarName
          .int
          (LF.GeneralExpr.stateVar
            localDeclUnusedName)) =
    false := by
  rfl

/- Test 10: **assignment to a local name is still refused.** This is the "without enabling"
   pin: `stmtWellFormed`'s `.assign` arm still demands a declared state variable, and `temporary`
   is one here, so the refusal below is specifically about `nowhere`, a name that exists only as
   a local. Widening the assign arm is a later layer's work and this pin is what it must
   deliberately move. -/
example :
    LF.GeneralReactor.stmtWellFormed
        localDeclReactor
        []
        (LF.GeneralStmt.assign
          localDeclUnusedName
          (LF.GeneralExpr.intLiteral 1)) =
    false := by
  rfl

/-! ## Pin 5: the effect census ignores a declaration -/

/- Test 11: a declaration contributes no effect name, and one in front of a schedule leaves the
   schedule's action as the only effect. -/
example :
    LF.CppPrinter.generalEffectNames
        [
          LF.GeneralStmt.localDecl
            localDeclVarName
            .int
            (LF.GeneralExpr.intLiteral 1),
          LF.GeneralStmt.schedule
            (ActionName.mk "tick")
            []
            { value := 1 }
        ] =
    ["tick"] := by
  simp [
    LF.CppPrinter.generalEffectNames,
    LF.CppPrinter.generalEffectNamesFrom
  ]

/-! ## Pin 6: the DTR side still refuses -/

/- Test 12: the S-I1 refusal arms, pinned executably. `statementResolves` and
   `statementTargetDeclared` answer `false` for a local declaration, so no well-formed source
   model contains one and the accepted fragment is unchanged. Nothing else in the development
   measures these two arms; this is their instrument. -/
def localDeclSourceModel :
    DTR.GeneralModel where

  classes :=
    []

  instances :=
    []

example :
    DTR.GeneralModel.statementResolves
        localDeclSourceModel
        {
          name :=
            ⟨"unused"⟩

          knownRebecs :=
            []

          stateVariables :=
            []

          constructor :=
            {
              parameters :=
                []

              body :=
                []
            }

          messageServers :=
            []
        }
        (DTR.GeneralStmt.localDecl
          localDeclVarName
          .int
          (DTR.GeneralExpr.intLiteral 1)) =
    false := by
  rfl

example :
    DTR.GeneralReactiveClass.statementTargetDeclared
        {
          name :=
            ⟨"unused"⟩

          knownRebecs :=
            []

          stateVariables :=
            []

          constructor :=
            {
              parameters :=
                []

              body :=
                []
            }

          messageServers :=
            []
        }
        (DTR.GeneralStmt.localDecl
          localDeclVarName
          .int
          (DTR.GeneralExpr.intLiteral 1)) =
    false := by
  rfl

end Tests
end Relico
