import Relico.Frontend.MultiStorePayloadCppBackend

def main
    (args : List String) :
    IO UInt32 := do

  match args with

  | [jsonPath, lfPath] =>
      Relico.Frontend.runMultiStorePayloadCppBackend
        jsonPath
        lfPath

  | _ =>
      IO.eprintln
        "usage: MultiStorePayloadCppBackendMain <payload.json> <output.lf>"

      pure 2
