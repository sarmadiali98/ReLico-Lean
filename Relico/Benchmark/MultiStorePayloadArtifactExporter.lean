import Relico.Frontend.MultiStorePayloadDecoder
import Relico.Translation.MultiStorePayloadBasic
import Relico.Translation.MultiStorePayloadCppBackend

private def writeOutput
    (path text : String) :
    IO Unit :=
  IO.FS.writeFile
    path
    text

private def exportPayloadArtifact
    (mode inputPath outputPath : String) :
    IO UInt32 := do

  let text ←
    IO.FS.readFile
      inputPath

  match
    Relico.Frontend.decodeMultiStorePayloadModelText
      text
  with

  | .error message =>
      IO.eprintln
        ("payload artifact decode failed: " ++
          message)

      pure 1

  | .ok model =>
      match mode with

      | "decoded-dtr-ast" =>
          writeOutput
            outputPath
            (reprStr model ++ "\n")

          IO.println
            "PAYLOAD_EXPORT_OK:decoded-dtr-ast"

          pure 0

      | "translated-lf-ast" =>
          let program :=
            Relico.Translation.translateMultiStorePayloadCore
              model

          writeOutput
            outputPath
            (reprStr program ++ "\n")

          IO.println
            "PAYLOAD_EXPORT_OK:translated-lf-ast"

          pure 0

      | "lf-source" =>
          match
            Relico.Translation.translateMultiStorePayloadToCppSource
              model
          with

          | .error message =>
              IO.eprintln
                ("payload LF rendering failed: " ++
                  message)

              pure 1

          | .ok source =>
              writeOutput
                outputPath
                source

              IO.println
                "PAYLOAD_EXPORT_OK:lf-source"

              pure 0

      | _ =>
          IO.eprintln
            ("unsupported payload artifact mode: " ++
              mode)

          pure 2

def main
    (arguments : List String) :
    IO UInt32 := do

  match arguments with

  | [mode, inputPath, outputPath] =>
      exportPayloadArtifact
        mode
        inputPath
        outputPath

  | _ =>
      IO.eprintln
        "usage: MultiStorePayloadArtifactExporter <decoded-dtr-ast|translated-lf-ast|lf-source> <input.json> <output>"

      pure 2
