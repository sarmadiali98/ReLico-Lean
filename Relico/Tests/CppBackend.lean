import Relico.Translation.CppBackend
import Relico.Tests.Translation

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Relico
namespace Tests

def expectedCppSource : String :=
  "target Cpp\n\n" ++
  "reactor Controller {\n" ++
  "  state x: int = 0\n" ++
  "  logical action tick_action: void\n\n" ++
  "  reaction(startup) {=\n" ++
  "    x = 0;\n" ++
  "    tick_action.schedule(1ms);\n" ++
  "  =}\n\n" ++
  "  reaction(tick_action) {=\n" ++
  "    x = x;\n" ++
  "    tick_action.schedule(1ms);\n" ++
  "  =}\n" ++
  "}\n\n" ++
  "main reactor Main {\n" ++
  "  controller = new Controller()\n" ++
  "}\n"

theorem expectedProgram_renders_as_cpp :
    LF.CppPrinter.renderProgram
        expectedProgram =
      expectedCppSource := by
  rfl

theorem validModel_translates_to_cpp_source :
    Translation.translateToCppSource
        validModel =
      Except.ok expectedCppSource := by
  rfl

theorem rendered_source_uses_cpp_target :
    LF.CppPrinter.targetHeader =
      "target Cpp" := by
  exact
    LF.CppPrinter.targetHeader_is_cpp

end Tests
end Relico
