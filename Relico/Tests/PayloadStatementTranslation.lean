import Relico.LF.PayloadCppPrinter
import Relico.Translation.PayloadBasic

set_option autoImplicit false

namespace Relico
namespace Tests

def payloadStatementMessageName :
    MsgName :=
  ⟨"deliver"⟩

def payloadStatementActionName :
    ActionName :=
  Translation.actionNameFor
    payloadStatementMessageName

def payloadStatementSource :
    DTR.PayloadStmt :=
  .selfSendInt
    payloadStatementMessageName
    (.intLiteral 42)
    { value := 1 }

def payloadStatementTarget :
    LF.PayloadStmt :=
  .scheduleInt
    payloadStatementActionName
    (.intLiteral 42)
    { value := 1 }

theorem payload_statement_translation_exact :
    Translation.compilePayloadStmt
        payloadStatementSource =
      payloadStatementTarget := by
  rfl

theorem payload_statement_cpp_exact :
    LF.CppPrinter.renderPayloadStmt
        payloadStatementTarget =
      "deliver_action.schedule(42, 1ms);" := by
  rfl

def payloadStatementProgram :
    LF.CppPrinter.IntPayloadProgram where

  reactorName :=
    ⟨"PayloadController"⟩

  stateVariable :=
    ⟨"x"⟩

  logicalAction :=
    payloadStatementActionName

  initialPayload :=
    (.intLiteral 42)

  delay :=
    { value := 1 }

  reactorInstance := {
    name :=
      ⟨"controller"⟩

    reactorName :=
      ⟨"PayloadController"⟩
  }

def payloadStatementProgramSource :
    String :=
  LF.CppPrinter.renderIntPayloadProgram
    payloadStatementProgram

def expectedPayloadStatementProgramSource :
    String :=
  "target Cpp\n\n" ++
    "reactor PayloadController {\n" ++
    "  state x: int = 0\n" ++
    "  logical action deliver_action: int\n\n" ++
    "  reaction(startup) -> deliver_action {=\n" ++
    "    deliver_action.schedule(42, 1ms);\n" ++
    "  =}\n\n" ++
    "  reaction(deliver_action) {=\n" ++
    "    x = *deliver_action.get();\n" ++
    "  =}\n" ++
    "}\n\n" ++
    "main reactor {\n" ++
    "  controller = new PayloadController()\n" ++
    "}\n"

set_option maxRecDepth 4096 in
theorem payload_statement_program_cpp_exact :
    payloadStatementProgramSource =
      expectedPayloadStatementProgramSource := by
  rfl

theorem payload_statement_translation_preserves_value :
    match
        Translation.compilePayloadStmt
          payloadStatementSource
      with
    | .scheduleInt _ (.intLiteral value) _ =>
        value = 42
    | _ =>
        False := by
  rfl

theorem payload_statement_translation_preserves_delay :
    match
        Translation.compilePayloadStmt
          payloadStatementSource
      with
    | .scheduleInt _ _ delay =>
        delay.value = 1 := by
  rfl

end Tests
end Relico
