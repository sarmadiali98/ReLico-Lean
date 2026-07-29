import Relico.Common.ParameterStore
import Relico.Common.StateStore
import Relico.LF.MultiStoreSyntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
Expressions for the generated payload-aware finite-store LF fragment.
-/
inductive MultiStorePayloadExpr where

  | intLiteral :
      Int →
      MultiStorePayloadExpr

  | stateVar :
      VarName →
      MultiStorePayloadExpr

  | parameterVar :
      VarName →
      MultiStorePayloadExpr

deriving Repr, DecidableEq, BEq, Inhabited

namespace MultiStorePayloadExpr

/--
Evaluate one generated expression against persistent reactor state and
trigger-payload parameters.
-/
def evaluate
    (stateStore : StateStore)
    (parameters : ParameterStore) :
    LF.MultiStorePayloadExpr →
    Option Int

  | .intLiteral value =>
      some value

  | .stateVar variableName =>
      StateStore.lookup
        stateStore
        variableName

  | .parameterVar parameterName =>
      ParameterStore.lookup
        parameters
        parameterName

/--
Evaluate an ordered generated payload-expression list.
-/
def evaluateAll
    (stateStore : StateStore)
    (parameters : ParameterStore) :
    List LF.MultiStorePayloadExpr →
    Option Payload

  | [] =>
      some []

  | expression :: remaining =>
      match
          evaluate
            stateStore
            parameters
            expression,
          evaluateAll
            stateStore
            parameters
            remaining
      with
      | some value, some values =>
          some
            (value :: values)

      | _, _ =>
          none

end MultiStorePayloadExpr

/--
Generated reaction statements with arbitrary ordered action payloads.
-/
inductive MultiStorePayloadStmt where

  | assign :
      VarName →
      LF.MultiStorePayloadExpr →
      MultiStorePayloadStmt

  | schedule :
      ActionName →
      List LF.MultiStorePayloadExpr →
      Delay →
      MultiStorePayloadStmt

deriving Repr, DecidableEq, BEq, Inhabited

abbrev MultiStorePayloadBody :=
  List LF.MultiStorePayloadStmt

/--
A generated typed logical-action declaration.

The ordered field names mirror source formal-parameter order. The
current value domain is integer-only.
-/
structure MultiStorePayloadAction where
  name :
    ActionName

  parameters :
    List VarName

deriving Repr, DecidableEq, BEq, Inhabited

inductive MultiStorePayloadTrigger where
  | startup
  | logicalAction :
      ActionName →
      MultiStorePayloadTrigger

deriving Repr, DecidableEq, BEq, Inhabited

structure MultiStorePayloadReaction where
  name :
    ReactionName

  trigger :
    LF.MultiStorePayloadTrigger

  parameters :
    List VarName

  body :
    LF.MultiStorePayloadBody

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

structure MultiStorePayloadReactor where
  name :
    ReactorName

  stateVariables :
    List LF.StateVariableDecl

  logicalActions :
    List LF.MultiStorePayloadAction

  startupReaction :
    LF.MultiStorePayloadReaction

  messageReactions :
    List LF.MultiStorePayloadReaction

deriving Repr, DecidableEq, BEq, Inhabited

structure MultiStorePayloadProgram where
  reactor :
    LF.MultiStorePayloadReactor

  reactorInstance :
    LF.ReactorInstance

deriving Repr, DecidableEq, BEq, Inhabited

end LF
end Relico
