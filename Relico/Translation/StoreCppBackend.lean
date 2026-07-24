import Relico.LF.StoreCppPrinter
import Relico.Translation.StoreBasic

set_option autoImplicit false

namespace Relico
namespace Translation

def translateStoreToCppSource
    (model : DTR.StoreModel) :
    Except TranslationError String := do

  let program ←
    translateStore model

  pure
    (LF.CppPrinter.renderStoreProgram
      program)

theorem translateStoreToCppSource_of_success
    {model : DTR.StoreModel}
    {program : LF.StoreProgram}
    (hTranslate :
      translateStore model =
        Except.ok program) :
    translateStoreToCppSource model =
      Except.ok
        (LF.CppPrinter.renderStoreProgram
          program) := by

  have hProgram :
      program =
        translateStoreCore model := by

    simpa [
      translateStore
    ] using
      hTranslate.symm

  subst program

  rfl

end Translation
end Relico
