import Relico.Frontend.StoreDecoder
import Relico.Translation.StoreBasic
import Relico.Translation.StoreCppBackend

private def writeOutput
    (path text : String) :
    IO Unit :=
  IO.FS.writeFile
    path
    text

private def exportStoreArtifact
    (mode inputPath outputPath : String) :
    IO UInt32 := do

  let text ←
    IO.FS.readFile
      inputPath

  match
    Relico.Frontend.decodeStoreModelText
      text
  with

  | .error message =>
      IO.eprintln
        s!"store artifact decode failed: {message}"

      pure 1

  | .ok model =>
      match mode with

      | "decoded-dtr-ast" =>
          writeOutput
            outputPath
            (reprStr model ++ "\n")

          IO.println
            "STORE_EXPORT_OK:decoded-dtr-ast"

          pure 0

      | "translated-lf-ast" =>
          let program :=
            Relico.Translation.translateStoreCore
              model

          writeOutput
            outputPath
            (reprStr program ++ "\n")

          IO.println
            "STORE_EXPORT_OK:translated-lf-ast"

          pure 0

      | "lf-source" =>
          match
            Relico.Translation.translateStoreToCppSource
              model
          with

          | .error message =>
              IO.eprintln
                s!"store LF rendering failed: {reprStr message}"

              pure 1

          | .ok source =>
              writeOutput
                outputPath
                source

              IO.println
                "STORE_EXPORT_OK:lf-source"

              pure 0

      | _ =>
          IO.eprintln
            ("unsupported store artifact mode: " ++
              mode)

          pure 2

def main
    (arguments : List String) :
    IO UInt32 := do

  match arguments with

  | [mode, inputPath, outputPath] =>
      exportStoreArtifact
        mode
        inputPath
        outputPath

  | _ =>
      IO.eprintln
        "usage: StoreArtifactExporter <decoded-dtr-ast|translated-lf-ast|lf-source> <input.json> <output>"

      pure 2
