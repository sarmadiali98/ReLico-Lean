import Relico.Frontend.MultiStoreDecoder
import Relico.Translation.MultiStoreCppBackend

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

private def renderMultiStoreSummary
    (model : DTR.MultiStoreModel) :
    String :=

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
      IO.FS.writeFile
        outputPath
        (renderMultiStoreSummary
          model)

      IO.println
        s!"Wrote decoded multi-server summary: {outputPath}"

      pure 0

def runMultiStoreBridgeToCpp
    (inputPath summaryPath lfPath : String) :
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
      match
        Translation.translateMultiStoreToCppSource
          model
      with

      | .error translationError =>
          IO.eprintln
            s!"Multi-server translation failed: {reprStr translationError}"

          pure 1

      | .ok lfSource =>
          IO.FS.writeFile
            summaryPath
            (renderMultiStoreSummary
              model)

          IO.FS.writeFile
            lfPath
            lfSource

          IO.println
            s!"Decoded multi-server JSON and wrote summary: {summaryPath}"

          IO.println
            s!"Decoded multi-server JSON and wrote LF/C++ source: {lfPath}"

          pure 0

end Frontend
end Relico

def main
    (arguments : List String) :
    IO UInt32 :=
  match arguments with

  | [inputPath, summaryPath] =>
      Relico.Frontend.runMultiStoreBridgeCheck
        inputPath
        summaryPath

  | [inputPath, summaryPath, lfPath] =>
      Relico.Frontend.runMultiStoreBridgeToCpp
        inputPath
        summaryPath
        lfPath

  | _ => do
      IO.eprintln
        "usage: MultiStoreBridgeCheck <input.json> <summary.txt> [output.lf]"

      pure 2
