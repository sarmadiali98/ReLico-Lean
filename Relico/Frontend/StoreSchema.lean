import Relico.Frontend.Schema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

def storeBridgeSchemaVersion : Nat :=
  2

structure RawStateVariable where
  name : String
  initialValue : Int
deriving Repr, DecidableEq, FromJson, ToJson

structure RawStoreModel where
  schemaVersion : Nat
  className : String
  actorName : String
  actorClass : String
  stateVariables : List RawStateVariable
  messageServer : String
  constructorBody : List RawStmt
  messageServerBody : List RawStmt
deriving Repr, DecidableEq, FromJson, ToJson

end Frontend
end Relico
