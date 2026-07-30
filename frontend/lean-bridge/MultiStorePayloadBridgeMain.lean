import Relico.Frontend.MultiStorePayloadBridgeCheck

def main
    (args : List String) :
    IO UInt32 :=
  match args with

  | [jsonPath] =>
      Relico.Frontend.runMultiStorePayloadBridgeCheck
        jsonPath

  | _ => do
      IO.eprintln
        "usage: MultiStorePayloadBridgeMain <payload.json>"

      pure 2
