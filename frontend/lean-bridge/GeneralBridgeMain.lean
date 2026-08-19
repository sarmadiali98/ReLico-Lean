import Relico.Frontend.GeneralBridgeCheck

def main
    (arguments : List String) :
    IO UInt32 :=
  match arguments with

  | [jsonPath] =>
      Relico.Frontend.runGeneralBridgeCheck
        jsonPath

  | _ => do
      IO.eprintln
        "usage: GeneralBridgeMain <model.parser.json>"

      pure 2
