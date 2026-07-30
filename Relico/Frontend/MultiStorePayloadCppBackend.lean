import Relico.Frontend.MultiStorePayloadDecoder
import Relico.Translation.MultiStorePayloadCppBackend

set_option autoImplicit false

namespace Relico
namespace Frontend

/--
Decode one versioned multi-store-payload JSON artifact, translate it,
render LF/C++ source, and write the source to the requested path.
-/
def runMultiStorePayloadCppBackend
    (jsonPath : String)
    (lfPath : String) :
    IO UInt32 := do

  let text ←
    IO.FS.readFile
      jsonPath

  match
      decodeMultiStorePayloadModelText
        text
  with

  | .error message =>
      IO.eprintln
        ("MULTI_STORE_PAYLOAD_BACKEND_DECODE_ERROR: " ++
          message)

      pure 3

  | .ok model =>
      match
          Translation.translateMultiStorePayloadToCppSource
            model
      with

      | .error message =>
          IO.eprintln
            ("MULTI_STORE_PAYLOAD_BACKEND_RENDER_ERROR: " ++
              message)

          pure 4

      | .ok source =>
          IO.FS.writeFile
            lfPath
            source

          let program :=
            Translation.translateMultiStorePayloadCore
              model

          IO.println
            "MULTI_STORE_PAYLOAD_CPP_BACKEND_OK"

          IO.println
            ("actor=" ++
              model.actor.name.value)

          IO.println
            ("reactor=" ++
              program.reactor.name.value)

          IO.println
            ("logicalActions=" ++
              toString
                program.reactor.logicalActions.length)

          IO.println
            ("messageReactions=" ++
              toString
                program.reactor.messageReactions.length)

          IO.println
            ("output=" ++
              lfPath)

          pure 0

end Frontend
end Relico
