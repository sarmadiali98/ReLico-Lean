import Relico.Frontend.MultiStorePayloadDecoder
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Frontend

/--
Decode parser output into the canonical DTR payload model and enter the
existing verified structural translation.

This bridge deliberately stops before LF source rendering. The complete
multi-store-payload printer/backend is a separate installation boundary.
-/
def runMultiStorePayloadBridgeCheck
    (jsonPath : String) :
    IO UInt32 := do

  let text ←
    IO.FS.readFile jsonPath

  match
    decodeMultiStorePayloadModelText
      text
  with

  | .error message =>
      IO.eprintln
        ("payload frontend decode failed: " ++
          message)

      pure 1

  | .ok model =>
      let program :=
        Translation.translateMultiStorePayloadCore
          model

      IO.println
        "MULTI_STORE_PAYLOAD_FRONTEND_OK"

      IO.println
        s!"Decoded actor `{model.actor.name.value}` as class `{model.actor.className.value}`."

      IO.println
        s!"Translated reactor `{program.reactor.name.value}` with {program.reactor.logicalActions.length} logical action(s)."

      pure 0

end Frontend
end Relico
