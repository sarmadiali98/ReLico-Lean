import Relico.LF.MultiStorePayloadCppPrinter
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Translate a payload-aware finite-store DTR model and render the exact
resulting LF AST as reactor-cpp source.

The structural translation remains the verified component. Concrete
source rendering remains part of the trusted backend boundary.
-/
def translateMultiStorePayloadToCppSource
    (model : DTR.MultiStorePayloadModel) :
    Except String String :=
  LF.CppPrinter.renderMultiStorePayloadProgram
    (translateMultiStorePayloadCore
      model)

/--
The payload backend is definitionally the composition of the published
structural translator and the published payload LF/C++ printer.
-/
@[simp]
theorem translateMultiStorePayloadToCppSource_eq
    (model : DTR.MultiStorePayloadModel) :
    translateMultiStorePayloadToCppSource
        model =
      LF.CppPrinter.renderMultiStorePayloadProgram
        (translateMultiStorePayloadCore
          model) := by
  rfl

/--
A successful render result is propagated without changing the rendered
source.
-/
theorem translateMultiStorePayloadToCppSource_of_render_success
    {model : DTR.MultiStorePayloadModel}
    {source : String}
    (hRender :
      LF.CppPrinter.renderMultiStorePayloadProgram
          (translateMultiStorePayloadCore
            model) =
        .ok source) :
    translateMultiStorePayloadToCppSource
        model =
      .ok source := by
  simpa using hRender

/--
A printer-boundary error is propagated unchanged.
-/
theorem translateMultiStorePayloadToCppSource_of_render_error
    {model : DTR.MultiStorePayloadModel}
    {message : String}
    (hRender :
      LF.CppPrinter.renderMultiStorePayloadProgram
          (translateMultiStorePayloadCore
            model) =
        .error message) :
    translateMultiStorePayloadToCppSource
        model =
      .error message := by
  simpa using hRender

end Translation
end Relico
