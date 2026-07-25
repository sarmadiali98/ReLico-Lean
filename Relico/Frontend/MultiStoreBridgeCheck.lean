import Relico.Frontend.MultiStoreDecoder
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Frontend

private def joinStrings
    (values : List String) :
    String :=
  String.intercalate
    ","
    values

private def renderPriority :
    Option Nat →
    String

  | some priority =>
      toString priority

  | none =>
      "none"

def runMultiStoreBridgeCheck
    (inputPath outputPath : String) :
    IO UInt32 := do

  let jsonText ←
    IO.FS.readFile
      inputPath

  match
    decodeMultiStoreModelText
      jsonText
  with

  | .error decodeError =>
      IO.eprintln
        s!"Multi-server bridge decode failed: {repr decodeError}"

      pure 1

  | .ok model =>
      let program :=
        Translation.translateMultiStoreCore
          model

      let sourceNames :=
        model.reactiveClass.messageServers.map
          (fun messageServer =>
            messageServer.name.value)

      let sourcePriorities :=
        model.reactiveClass.messageServers.map
          (fun messageServer =>
            renderPriority
              messageServer.priority)

      let logicalActions :=
        program.reactor.logicalActions.map
          (fun logicalAction =>
            logicalAction.value)

      let summary :=
        String.intercalate
          "\n"
          [
            "class=" ++
              model.reactiveClass.name.value,

            "actor=" ++
              model.actor.name.value,

            "sourceMessageServers=" ++
              joinStrings sourceNames,

            "sourcePriorities=" ++
              joinStrings sourcePriorities,

            "logicalActions=" ++
              joinStrings logicalActions,

            "messageReactionCount=" ++
              toString
                program.reactor.messageReactions.length
          ] ++
          "\n"

      IO.FS.writeFile
        outputPath
        summary

      IO.println
        s!"Wrote decoded multi-server summary: {outputPath}"

      pure 0

end Frontend
end Relico

def main
    (arguments : List String) :
    IO UInt32 :=
  match arguments with

  | [inputPath, outputPath] =>
      Relico.Frontend.runMultiStoreBridgeCheck
        inputPath
        outputPath

  | _ => do
      IO.eprintln
        "usage: MultiStoreBridgeCheck <input.json> <output.txt>"

      pure 2
