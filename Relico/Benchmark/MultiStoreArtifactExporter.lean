import Relico.Frontend.MultiStoreDecoder
import Relico.Translation.MultiStoreBasic
import Relico.Translation.MultiStoreCppBackend

private def writeOutput
    (path text : String) :
    IO Unit :=
  IO.FS.writeFile
    path
    text

private def exportMultiStoreArtifact
    (mode inputPath outputPath : String) :
    IO UInt32 := do

  let text ←
    IO.FS.readFile
      inputPath

  match
    Relico.Frontend.decodeMultiStoreModelText
      text
  with

  | .error message =>
      IO.eprintln
        s!"multistore artifact decode failed: {repr message}"

      pure 1

  | .ok model =>
      match mode with

      | "decoded-dtr-ast" =>
          writeOutput
            outputPath
            (reprStr model ++ "\n")

          IO.println
            "MULTISTORE_EXPORT_OK:decoded-dtr-ast"

          pure 0

      | "translated-lf-ast" =>
          let program :=
            Relico.Translation.translateMultiStoreCore
              model

          writeOutput
            outputPath
            (reprStr program ++ "\n")

          IO.println
            "MULTISTORE_EXPORT_OK:translated-lf-ast"

          pure 0

      | "lf-source" =>
          match
            Relico.Translation.translateMultiStoreToCppSource
              model
          with

          | .error message =>
              IO.eprintln
                s!"multistore LF rendering failed: {repr message}"

              pure 1

          | .ok source =>
              writeOutput
                outputPath
                source

              IO.println
                "MULTISTORE_EXPORT_OK:lf-source"

              pure 0

      | _ =>
          IO.eprintln
            ("unsupported multistore artifact mode: " ++
              mode)

          pure 2

def main
    (arguments : List String) :
    IO UInt32 := do

  match arguments with

  | [mode, inputPath, outputPath] =>
      exportMultiStoreArtifact
        mode
        inputPath
        outputPath

  | _ =>
      IO.eprintln
        "usage: MultiStoreArtifactExporter <decoded-dtr-ast|translated-lf-ast|lf-source> <input.json> <output>"

      pure 2
