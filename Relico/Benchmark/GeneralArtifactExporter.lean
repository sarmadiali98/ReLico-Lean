import Relico.Frontend.GeneralDecoder
import Relico.Translation.GeneralBasic
import Relico.LF.GeneralCppPrinter
import Relico.Correctness.GeneralCorrespondence

set_option autoImplicit false

/-!
# The general family's benchmark artifact exporter

Stage K's benchmark pipeline runs every corpus model through the same nine stages the older
families use, and three of those stages — `decoded-dtr-ast`, `translated-lf-ast` and `lf-source` —
are Lean exports of a decoded model. This file is the general family's version of
`Relico/Benchmark/ArtifactExporter.lean` (the `v0` family) and
`Relico/Benchmark/MultiStorePayloadArtifactExporter.lean`, and it follows the first one's shape
exactly: decode, then either print the decoded model, print the translated program, or render the
program to LF/C++ source.

**Why a bridge main and not a library function.** `lakefile.toml` declares one `lean_lib` and one
`lean_exe`; this file, like its two siblings, holds an inline `def main` and is compiled on demand
by `tools/relico_bench_stage.py` under `lake env lean --run`. Nothing in the verified library
imports it, so adding it changes no proof, no gate count and no `EXPECTED_PRINTER_ASSERTIONS`.

**One difference from the `v0` sibling, and it is the whole point of this family.** The `v0`
exporter decodes and translates; the general pipeline must additionally demonstrate that the
translation it emits *carries the proved correspondence*, which is what the benchmark's
`formal-witness` stage asserts. The witness stage runs `lake env lean` over the modules a
benchmark's `coverage.json` names; this exporter does not compute the witness itself. What it does
do, in every mode, is decode through `Frontend.decodeGeneralModelText` — the same entry the
frontend gate uses — so that a benchmark's model satisfies `DTR.GeneralModel.wellFormed` before
any artifact exists, exactly the hypothesis `Translation.compileGeneralModel`'s guard and the
stage-F/G correspondence theorems are written against.

The three modes write what the older families write, so the runner's artifact comparisons stay
uniform: a `repr` of the decoded model, a `repr` of the translated program, and the rendered
LF source file.
-/

namespace Relico
namespace Benchmark

/-- Read and decode a `general-v1` JSON document into a well-formed DTR model. -/
def decodeGeneralFile
    (jsonPath : String) :
    IO (Except UInt32 DTR.GeneralModel) := do

  let jsonText ←
    IO.FS.readFile
      jsonPath

  match
      Frontend.decodeGeneralModelText
        jsonText
  with

  | .error diagnostic =>
      IO.eprintln
        ("general artifact decode failed: " ++
          diagnostic.render)

      pure (.error 1)

  | .ok model =>
      pure (.ok model)

/-- Decode, then translate, in one `Except`. -/
def translateGeneralFile
    (jsonPath : String) :
    IO (Except UInt32 LF.GeneralProgram) := do

  match ← decodeGeneralFile jsonPath with

  | .error code =>
      pure (.error code)

  | .ok model =>
      match
          Translation.compileGeneralModel
            model
      with

      | .error reason =>
          IO.eprintln
            ("verified general translation failed: " ++
              reason)

          pure (.error 1)

      | .ok program =>
          pure (.ok program)

/-- `decoded-dtr-ast`: the decoded model's `repr`. -/
def exportGeneralDecodedDtrAst
    (jsonPath outputPath : String) :
    IO UInt32 := do

  match ← decodeGeneralFile jsonPath with

  | .error code =>
      pure code

  | .ok model =>
      IO.FS.writeFile
        outputPath
        (reprStr model ++ "\n")

      IO.println
        "GENERAL_EXPORT_OK:decoded-dtr-ast"

      pure 0

/-- `translated-lf-ast`: the compiled program's `repr`. -/
def exportGeneralTranslatedLfAst
    (jsonPath outputPath : String) :
    IO UInt32 := do

  match ← translateGeneralFile jsonPath with

  | .error code =>
      pure code

  | .ok program =>
      IO.FS.writeFile
        outputPath
        (reprStr program ++ "\n")

      IO.println
        "GENERAL_EXPORT_OK:translated-lf-ast"

      pure 0

/-- `lf-source`: the rendered LF/C++ source file. -/
def exportGeneralLfSource
    (jsonPath outputPath : String) :
    IO UInt32 := do

  match ← translateGeneralFile jsonPath with

  | .error code =>
      pure code

  | .ok program =>
      match
          LF.CppPrinter.renderGeneralProgram
            program
      with

      | .error reason =>
          IO.eprintln
            ("general LF rendering failed: " ++
              reason)

          pure 1

      | .ok source =>
          IO.FS.writeFile
            outputPath
            source

          IO.println
            "GENERAL_EXPORT_OK:lf-source"

          pure 0

end Benchmark
end Relico

def main
    (arguments : List String) :
    IO UInt32 := do

  match arguments with

  | [mode, inputPath, outputPath] =>
      match mode with

      | "decoded-dtr-ast" =>
          Relico.Benchmark.exportGeneralDecodedDtrAst
            inputPath
            outputPath

      | "translated-lf-ast" =>
          Relico.Benchmark.exportGeneralTranslatedLfAst
            inputPath
            outputPath

      | "lf-source" =>
          Relico.Benchmark.exportGeneralLfSource
            inputPath
            outputPath

      | _ =>
          IO.eprintln
            ("unsupported general artifact mode: " ++
              mode)

          pure 2

  | _ =>
      IO.eprintln
        "usage: GeneralArtifactExporter <decoded-dtr-ast|translated-lf-ast|lf-source> <input.json> <output>"

      pure 2
