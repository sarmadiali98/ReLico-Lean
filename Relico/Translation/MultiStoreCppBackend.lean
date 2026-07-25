import Relico.Translation.MultiStoreBasic
import Relico.LF.MultiStoreCppPrinter

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Translate a multiple-message-server finite-store DTR model through the
official executable Lean translator and render the resulting LF/C++
program.
-/
def translateMultiStoreToCppSource
    (model : DTR.MultiStoreModel) :
    Except TranslationError String := do

  let program ←
    translateMultiStore
      model

  pure
    (LF.CppPrinter.renderMultiStoreProgram
      program)

/--
A successful public multi-server translation is rendered without
changing the translated LF AST.
-/
theorem translateMultiStoreToCppSource_of_success
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    (hTranslate :
      translateMultiStore model =
        .ok program) :
    translateMultiStoreToCppSource model =
      .ok
        (LF.CppPrinter.renderMultiStoreProgram
          program) := by

  change
    (.ok
        (translateMultiStoreCore
          model) :
      Except
        TranslationError
        LF.MultiStoreProgram) =
      .ok program
    at hTranslate

  cases hTranslate

  rfl

/--
The backend always renders the exact program produced by
`translateMultiStoreCore`.
-/
@[simp]
theorem translateMultiStoreToCppSource_eq_ok
    (model : DTR.MultiStoreModel) :
    translateMultiStoreToCppSource model =
      .ok
        (LF.CppPrinter.renderMultiStoreProgram
          (translateMultiStoreCore
            model)) := by
  rfl

end Translation
end Relico
