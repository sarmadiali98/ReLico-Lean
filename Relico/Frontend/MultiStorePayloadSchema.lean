import Lean.Data.Json

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/--
Version of the parser-independent interchange format for the current
one-class, one-actor, finite-store, multi-message-server payload fragment.
-/
def multiStorePayloadBridgeSchemaVersion : Nat :=
  1

/--
Stable family discriminator for the payload bridge.
-/
def multiStorePayloadBridgeFamily : String :=
  "multiStorePayload"

/--
Parser-independent payload-expression representation.

Supported forms are:

- `intLiteral`, with `value`;
- `stateVar`, with `name`;
- `parameterVar`, with `name`.
-/
structure RawMultiStorePayloadExpr where
  kind :
    String

  value :
    Option Int :=
      none

  name :
    Option String :=
      none

deriving Repr, DecidableEq, FromJson, ToJson

/--
Parser-independent payload-statement representation.

Supported forms are:

- `assign`, with `target` and `expression`;
- `selfSend`, with `message`, ordered `arguments`, and `delay`.
-/
structure RawMultiStorePayloadStmt where
  kind :
    String

  target :
    Option String :=
      none

  expression :
    Option RawMultiStorePayloadExpr :=
      none

  message :
    Option String :=
      none

  arguments :
    Option (List RawMultiStorePayloadExpr) :=
      none

  delay :
    Option Nat :=
      none

deriving Repr, DecidableEq, FromJson, ToJson

structure RawMultiStorePayloadStateVariable where
  name :
    String

  initialValue :
    Int

deriving Repr, DecidableEq, FromJson, ToJson

/--
One message-server declaration with ordered formal parameters and optional
local priority.
-/
structure RawMultiStorePayloadMessageServer where
  name :
    String

  parameters :
    List String

  priority :
    Option Nat :=
      none

  body :
    List RawMultiStorePayloadStmt

deriving Repr, DecidableEq, FromJson, ToJson

/--
Stable parser-independent representation of the current local payload model.
-/
structure RawMultiStorePayloadModel where
  schemaVersion :
    Nat

  family :
    String

  className :
    String

  actorName :
    String

  actorClass :
    String

  stateVariables :
    List RawMultiStorePayloadStateVariable

  constructorBody :
    List RawMultiStorePayloadStmt

  messageServers :
    List RawMultiStorePayloadMessageServer

deriving Repr, DecidableEq, FromJson, ToJson

end Frontend
end Relico
