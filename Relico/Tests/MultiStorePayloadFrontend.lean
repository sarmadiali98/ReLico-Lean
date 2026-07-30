import Relico.Frontend.MultiStorePayloadDecoder
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Tests

private def frontendFailure
    {α : Type}
    (message : String) :
    IO α :=
  throw
    (IO.userError message)

private def expectDecodeFailure
    (label path : String) :
    IO Unit := do

  let text ←
    IO.FS.readFile path

  match
    Frontend.decodeMultiStorePayloadModelText
      text
  with

  | .error _ =>
      IO.println
        s!"PASS_INVALID_{label}"

  | .ok _ =>
      frontendFailure
        ("expected decoding failure: " ++
          label)

private def validatePositiveModel
    (path : String) :
    IO Unit := do

  let text ←
    IO.FS.readFile path

  let model ←
    match
      Frontend.decodeMultiStorePayloadModelText
        text
    with

    | .error message =>
        frontendFailure
          ("positive payload decode failed: " ++
            message)

    | .ok model =>
        pure model

  unless
      model.reactiveClass.name.value ==
        "PayloadController"
  do
    frontendFailure
      "incorrect decoded class name"

  unless
      model.actor.name.value ==
        "controller"
  do
    frontendFailure
      "incorrect decoded actor name"

  match
      model.reactiveClass.constructor.body
  with

  | [
      .assign
        target
        (.intLiteral initialValue),

      .selfSend
        message
        [.intLiteral payloadValue]
        delay
    ] =>

      unless
          target.value == "x" &&
          initialValue == 0 &&
          message.value == "deliver" &&
          payloadValue == 7 &&
          delay.value == 1
      do
        frontendFailure
          "incorrect decoded constructor payload body"

  | _ =>
      frontendFailure
        "unexpected decoded constructor shape"

  match
      model.reactiveClass.messageServers
  with

  | [messageServer] =>
      match messageServer.parameters with

      | [parameter] =>
          unless
              parameter.value == "value"
          do
            frontendFailure
              "incorrect decoded formal parameter"

      | _ =>
          frontendFailure
            "unexpected decoded formal-parameter list"

      match messageServer.body with

      | [
          .assign
            target
            (.parameterVar parameter)
        ] =>

          unless
              target.value == "x" &&
              parameter.value == "value"
          do
            frontendFailure
              "incorrect decoded parameter assignment"

      | _ =>
          frontendFailure
            "unexpected decoded message-server body"

  | _ =>
      frontendFailure
        "unexpected decoded message-server list"

  let program :=
    Translation.translateMultiStorePayloadCore
      model

  unless
      program.reactor.name.value ==
        "PayloadController"
  do
    frontendFailure
      "incorrect translated reactor name"

  IO.println
    "PASS_VALID_MULTI_STORE_PAYLOAD_FRONTEND"

def runMultiStorePayloadFrontendTests
    (fixtureDirectory : String) :
    IO UInt32 := do

  try
    validatePositiveModel
      (fixtureDirectory ++
        "/payload-single.parser.json")

    expectDecodeFailure
      "MISSING_FORMAL"
      (fixtureDirectory ++
        "/invalid-missing-formal.json")

    expectDecodeFailure
      "ARITY_MISMATCH"
      (fixtureDirectory ++
        "/invalid-arity-mismatch.json")

    expectDecodeFailure
      "UNKNOWN_PARAMETER"
      (fixtureDirectory ++
        "/invalid-unknown-parameter.json")

    expectDecodeFailure
      "UNSUPPORTED_EXPRESSION"
      (fixtureDirectory ++
        "/invalid-unsupported-expression.json")

    expectDecodeFailure
      "NEGATIVE_DELAY"
      (fixtureDirectory ++
        "/invalid-negative-delay.json")

    IO.println
      "MULTI_STORE_PAYLOAD_FRONTEND_TESTS_OK"

    pure 0

  catch exception =>
    IO.eprintln
      s!"multi-store-payload frontend tests failed: {exception}"

    pure 1

end Tests
end Relico
