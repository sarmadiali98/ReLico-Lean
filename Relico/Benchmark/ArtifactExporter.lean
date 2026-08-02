import Relico.Frontend.Decoder
import Relico.Translation.Basic
import Relico.LF.CppPrinter

set_option autoImplicit false

namespace Relico
namespace Benchmark

def decodeModelFile (jsonPath : String) : IO (Except UInt32 DTR.Model) := do
  let jsonText ← IO.FS.readFile jsonPath
  match Frontend.decodeModelText jsonText with
  | .error error =>
      IO.eprintln s!"frontend decode failed: {error}"
      pure (.error 1)
  | .ok model =>
      pure (.ok model)

def exportDecodedDtrAst (jsonPath outputPath : String) : IO UInt32 := do
  match ← decodeModelFile jsonPath with
  | .error code => pure code
  | .ok model =>
      IO.FS.writeFile outputPath (reprStr model ++ "\n")
      pure 0

def translateModelFile (jsonPath : String) : IO (Except UInt32 LF.Program) := do
  match ← decodeModelFile jsonPath with
  | .error code => pure (.error code)
  | .ok model =>
      match Translation.translate model with
      | .error _ =>
          IO.eprintln "verified translation failed"
          pure (.error 1)
      | .ok program => pure (.ok program)

def exportTranslatedLfAst (jsonPath outputPath : String) : IO UInt32 := do
  match ← translateModelFile jsonPath with
  | .error code => pure code
  | .ok program =>
      IO.FS.writeFile outputPath (reprStr program ++ "\n")
      pure 0

def exportLfSource (jsonPath outputPath : String) : IO UInt32 := do
  match ← translateModelFile jsonPath with
  | .error code => pure code
  | .ok program =>
      IO.FS.writeFile outputPath (LF.CppPrinter.renderProgram program)
      pure 0

end Benchmark
end Relico

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["decoded-dtr-ast", jsonPath, outputPath] =>
      Relico.Benchmark.exportDecodedDtrAst jsonPath outputPath
  | ["translated-lf-ast", jsonPath, outputPath] =>
      Relico.Benchmark.exportTranslatedLfAst jsonPath outputPath
  | ["lf-source", jsonPath, outputPath] =>
      Relico.Benchmark.exportLfSource jsonPath outputPath
  | _ =>
      IO.eprintln "usage: ArtifactExporter <decoded-dtr-ast|translated-lf-ast|lf-source> <input.json> <output>"
      pure 2
