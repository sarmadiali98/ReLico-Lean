import Relico.Tests.MultiStorePayloadFrontend

def main
    (args : List String) :
    IO UInt32 :=
  match args with

  | [fixtureDirectory] =>
      Relico.Tests.runMultiStorePayloadFrontendTests
        fixtureDirectory

  | _ => do
      IO.eprintln
        "usage: MultiStorePayloadFrontendTestMain <fixture-directory>"

      pure 2
