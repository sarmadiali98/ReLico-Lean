import Relico.Frontend.MultiStorePayloadCppBackend

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadCppBackend

/--
The public payload backend exposes the exact translated LF program to
the published printer.
-/
example
    (model : DTR.MultiStorePayloadModel) :
    Translation.translateMultiStorePayloadToCppSource
        model =
      LF.CppPrinter.renderMultiStorePayloadProgram
        (Translation.translateMultiStorePayloadCore
          model) := by
  rfl

/--
Successful printer output is preserved by the backend wrapper.
-/
example
    {model : DTR.MultiStorePayloadModel}
    {source : String}
    (hRender :
      LF.CppPrinter.renderMultiStorePayloadProgram
          (Translation.translateMultiStorePayloadCore
            model) =
        .ok source) :
    Translation.translateMultiStorePayloadToCppSource
        model =
      .ok source := by
  exact
    Translation.translateMultiStorePayloadToCppSource_of_render_success
      hRender

/--
Printer-boundary rejection is also preserved exactly.
-/
example
    {model : DTR.MultiStorePayloadModel}
    {message : String}
    (hRender :
      LF.CppPrinter.renderMultiStorePayloadProgram
          (Translation.translateMultiStorePayloadCore
            model) =
        .error message) :
    Translation.translateMultiStorePayloadToCppSource
        model =
      .error message := by
  exact
    Translation.translateMultiStorePayloadToCppSource_of_render_error
      hRender

end MultiStorePayloadCppBackend
end Tests
end Relico
