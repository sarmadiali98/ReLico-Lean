import Relico.LF.CppPrinter
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Execute the verified v0 AST translation and render its result as an
LF/C++ source file.

The AST translation is verified. The concrete text printer is currently
part of the trusted backend boundary.
-/
def translateToCppSource
    (model : DTR.Model) :
    Except TranslationError String := do
  let program ← translate model
  pure
    (LF.CppPrinter.renderProgram program)

/--
A successful executable AST translation is rendered by the LF/C++
printer without changing the translated program.
-/
theorem translateToCppSource_of_success
    {model : DTR.Model}
    {program : LF.Program}
    (hTranslate :
      translate model =
        Except.ok program) :
    translateToCppSource model =
      Except.ok
        (LF.CppPrinter.renderProgram program) := by
  have hProgram :
      program =
        translateCore model := by
    simpa [translate] using hTranslate.symm

  subst program

  rfl

end Translation
end Relico
