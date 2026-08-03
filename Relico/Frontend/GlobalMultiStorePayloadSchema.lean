import Relico.Frontend.MultiStorePayloadSchema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/--
Version of the additive parser-independent global payload interchange format.

The existing local payload bridge remains version 1. Version 4 wraps one
version-1 local payload model per actor and adds separate actor-priority
metadata without changing local message-server priority.
-/
def globalMultiStorePayloadBridgeSchemaVersion : Nat :=
  4

/--
Stable family discriminator for the additive global payload bridge.
-/
def globalMultiStorePayloadBridgeFamily : String :=
  "globalMultiStorePayload"

/--
One declaration-ordered actor entry in the global payload bridge.

`priority` is actor-level metadata. Local message-server priority remains in
`RawMultiStorePayloadMessageServer.priority` inside `model`.
-/
structure RawGlobalMultiStorePayloadActor where
  priority :
    Option Nat :=
      none

  model :
    RawMultiStorePayloadModel

deriving Repr, DecidableEq, FromJson, ToJson

/--
Additive version-4 global frontend representation.

Actor list order is the main-block declaration order. Each entry carries one
existing version-1 local payload model.
-/
structure RawGlobalMultiStorePayloadModel where
  schemaVersion :
    Nat

  family :
    String

  actors :
    List RawGlobalMultiStorePayloadActor

deriving Repr, DecidableEq, FromJson, ToJson

end Frontend
end Relico
