import Relico.Frontend.StoreSchema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/--
Schema version for finite-store models containing multiple message
servers and optional local message-server priorities.
-/
def multiStoreBridgeSchemaVersion : Nat :=
  3

/--
Parser-independent representation of one message-server declaration.

`priority? = none` represents an unannotated message server.
-/
structure RawMessageServer where
  name :
    String

  priority? :
    Option Nat :=
      none

  body :
    List RawStmt

deriving Repr, DecidableEq, FromJson, ToJson

/--
Parser-independent representation of the current one-class,
one-actor, finite-store, multiple-message-server fragment.

The `messageServers` list retains source declaration order.
-/
structure RawMultiStoreModel where
  schemaVersion :
    Nat

  className :
    String

  actorName :
    String

  actorClass :
    String

  stateVariables :
    List RawStateVariable

  constructorBody :
    List RawStmt

  messageServers :
    List RawMessageServer

deriving Repr, DecidableEq, FromJson, ToJson

end Frontend
end Relico
