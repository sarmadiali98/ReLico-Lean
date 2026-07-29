import Relico.Common.ParameterStore
import Relico.Common.StateStore
import Relico.DTR.MultiStoreSyntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Expressions for the additive payload-aware finite-store fragment.

State references read persistent actor state. Parameter references read
the activation-local environment established when a message occurrence
is dispatched.
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
Evaluate one expression against persistent state and activation-local
parameters.
-/
def evaluate
    (stateStore : StateStore)
    (parameters : ParameterStore) :
    DTR.MultiStorePayloadExpr →
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
Evaluate an ordered payload-expression list without changing component
order.
-/
def evaluateAll
    (stateStore : StateStore)
    (parameters : ParameterStore) :
    List DTR.MultiStorePayloadExpr →
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
Statements for the additive payload-aware finite-store fragment.

Payloads are arbitrary ordered lists of integer-valued expressions.
Zero and positive delays are both represented by the existing `Delay`
type; this syntax imposes no positive-delay restriction.
-/
inductive MultiStorePayloadStmt where

  | assign :
      VarName →
      DTR.MultiStorePayloadExpr →
      MultiStorePayloadStmt

  | selfSend :
      MsgName →
      List DTR.MultiStorePayloadExpr →
      Delay →
      MultiStorePayloadStmt

deriving Repr, DecidableEq, BEq, Inhabited

abbrev MultiStorePayloadBody :=
  List DTR.MultiStorePayloadStmt

structure MultiStorePayloadConstructor where
  body :
    DTR.MultiStorePayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
A payload-aware message-server declaration with ordered formal
parameters and optional local-priority metadata.
-/
structure MultiStorePayloadMessageServer where
  name :
    MsgName

  parameters :
    List VarName

  body :
    DTR.MultiStorePayloadBody

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

/--
The names declared by an ordered payload-message-server list.
-/
def multiStorePayloadMessageServerNames
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    List MsgName :=
  messageServers.map
    (fun messageServer =>
      messageServer.name)

namespace MultiStorePayloadMessageServers

/--
The selected Option-C fragment forbids equal local priorities.

Because `none` is itself a priority class, this condition also permits
at most one unannotated message server in a class. The source AST keeps
priority metadata separate from this explicit well-formedness premise.
-/
def PrioritiesDistinct
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Prop :=
  (messageServers.map
    (fun messageServer =>
      messageServer.priority)).Nodup

/--
The distinct-priority well-formedness predicate is executable because
priority metadata has decidable equality.
-/
instance prioritiesDistinctDecidable
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Decidable
      (PrioritiesDistinct
        messageServers) := by
  unfold PrioritiesDistinct
  infer_instance

end MultiStorePayloadMessageServers

/--
A one-actor payload-aware class with finite persistent state and
multiple message servers.

This is the local foundation for Option C. Actor multiplicity,
known-rebec topology, and external sends remain a later additive global
layer.
-/
structure MultiStorePayloadReactiveClass where
  name :
    ClassName

  stateVariables :
    List DTR.StateVariableDecl

  constructor :
    DTR.MultiStorePayloadConstructor

  messageServers :
    List DTR.MultiStorePayloadMessageServer

deriving Repr, DecidableEq, BEq, Inhabited

structure MultiStorePayloadModel where
  reactiveClass :
    DTR.MultiStorePayloadReactiveClass

  actor :
    DTR.ActorInstance

deriving Repr, DecidableEq, BEq, Inhabited

end DTR
end Relico
