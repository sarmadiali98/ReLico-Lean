import Relico.DTR.GlobalMultiStorePayloadExternalSendFrame
import Relico.LF.GlobalMultiStorePayloadExternalSendFrame
import Relico.Translation.GlobalMultiStorePayloadExternalSendStatement

set_option autoImplicit false

namespace Relico
namespace Translation

def translateGlobalMultiStorePayloadExternalSendFrame
    (source :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    LF.GlobalMultiStorePayloadExternalSendFrame.Frame where

  statement :=
    translateGlobalMultiStorePayloadExternalSendStatement
      source.statement

  remaining :=
    compileMultiStorePayloadBody
      source.remaining

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendFrame_statement
    (source :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    (translateGlobalMultiStorePayloadExternalSendFrame
      source).statement =
      translateGlobalMultiStorePayloadExternalSendStatement
        source.statement := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendFrame_remaining
    (source :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    (translateGlobalMultiStorePayloadExternalSendFrame
      source).remaining =
      compileMultiStorePayloadBody
        source.remaining := by
  rfl

end Translation
end Relico
