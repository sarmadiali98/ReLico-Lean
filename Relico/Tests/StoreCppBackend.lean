import Relico.Tests.StoreFrontendDecoder
import Relico.Translation.StoreCppBackend

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Relico
namespace Tests

def expectedStoreCppSource :
    String :=
  "target Cpp\n\n" ++
  "reactor TwoStateController {\n" ++
  "  state x: int = 0\n" ++
  "  state y: int = 0\n" ++
  "  logical action tick_action: void\n\n" ++
  "  reaction(startup) -> tick_action {=\n" ++
  "    x = 1;\n" ++
  "    y = 2;\n" ++
  "    tick_action.schedule(1ms);\n" ++
  "  =}\n\n" ++
  "  reaction(tick_action) {=\n" ++
  "    y = x;\n" ++
  "  =}\n" ++
  "}\n\n" ++
  "main reactor {\n" ++
  "  controller = new TwoStateController()\n" ++
  "}\n"

theorem decodedStoreModel_renders_as_cpp :
    LF.CppPrinter.renderStoreProgram
        (Translation.translateStoreCore
          expectedDecodedStoreModel) =
      expectedStoreCppSource := by
  rfl

theorem decodedStoreModel_translates_to_cpp_source :
    Translation.translateStoreToCppSource
        expectedDecodedStoreModel =
      Except.ok expectedStoreCppSource := by
  rfl

theorem renderedStoreSource_contains_both_declarations :
    LF.CppPrinter.renderStateVariableDecls [
      {
        name :=
          decoderStoreX

        initialValue :=
          0
      },
      {
        name :=
          decoderStoreY

        initialValue :=
          0
      }
    ] =
      "  state x: int = 0\n" ++
      "  state y: int = 0" := by
  rfl

end Tests
end Relico
