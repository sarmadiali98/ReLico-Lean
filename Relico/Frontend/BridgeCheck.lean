import Relico.Frontend.Decoder
import Relico.Translation.CppBackend

set_option autoImplicit false

namespace Relico
namespace Frontend

def runBridgeCheck
    (jsonPath lfPath : String) :
    IO UInt32 := do

  let jsonText ←
    IO.FS.readFile jsonPath

  match decodeModelText jsonText with

  | .error decodeError =>
      IO.eprintln
        s!"frontend decode failed: {decodeError}"

      pure 1

  | .ok model =>
      match
        Translation.translateToCppSource model
      with

      | .error translationError =>
          IO.eprintln
            s!"translation failed: {reprStr translationError}"

          pure 1

      | .ok lfSource =>
          IO.FS.writeFile
            lfPath
            lfSource

          IO.println
            s!"Decoded parser output and wrote LF/C++ source: {lfPath}"

          pure 0

end Frontend
end Relico

def main
    (arguments : List String) :
    IO UInt32 := do

  match arguments with

  | [jsonPath, lfPath] =>
      Relico.Frontend.runBridgeCheck
        jsonPath
        lfPath

  | _ =>
      IO.eprintln
        "usage: BridgeCheck <input.json> <output.lf>"

      pure 2
