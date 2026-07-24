import Relico.Frontend.StoreDecoder
import Relico.Translation.StoreCppBackend

set_option autoImplicit false

namespace Relico
namespace Frontend

def runStoreBridgeCheck
    (jsonPath lfPath : String) :
    IO UInt32 := do

  let jsonText ←
    IO.FS.readFile jsonPath

  match decodeStoreModelText jsonText with
  | .error decodeError =>
      IO.eprintln
        s!"finite-store frontend decode failed: {decodeError}"

      pure 1

  | .ok model =>
      match
        Translation.translateStoreToCppSource model
      with
      | .error translationError =>
          IO.eprintln
            s!"finite-store translation failed: {reprStr translationError}"

          pure 1

      | .ok lfSource =>
          IO.FS.writeFile
            lfPath
            lfSource

          IO.println
            s!"Decoded finite-store JSON and wrote LF/C++ source: {lfPath}"

          pure 0

end Frontend
end Relico

def main
    (arguments : List String) :
    IO UInt32 := do

  match arguments with
  | [jsonPath, lfPath] =>
      Relico.Frontend.runStoreBridgeCheck
        jsonPath
        lfPath

  | _ =>
      IO.eprintln
        "usage: StoreBridgeCheck <input.json> <output.lf>"

      pure 2
