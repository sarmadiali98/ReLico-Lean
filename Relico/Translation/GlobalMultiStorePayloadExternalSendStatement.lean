import Relico.DTR.GlobalMultiStorePayloadExternalSendStatement
import Relico.LF.GlobalMultiStorePayloadExternalSendStatement
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Translate one expression-bearing external-send statement adapter.

Topology remains unresolved at this layer. The published E3a foundation resolves
the sender-relative known-rebec name only after payload evaluation.
-/
def translateGlobalMultiStorePayloadExternalSendStatement
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    LF.GlobalMultiStorePayloadExternalSendStatement.Statement where

  sender :=
    source.sender

  knownRebec :=
    source.knownRebec

  actionName :=
    actionNameFor
      source.messageName

  payloadExpressions :=
    compileMultiStorePayloadExprs
      source.payloadExpressions

  delay :=
    source.delay

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendStatement_sender
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    (translateGlobalMultiStorePayloadExternalSendStatement
      source).sender =
      source.sender := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendStatement_knownRebec
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    (translateGlobalMultiStorePayloadExternalSendStatement
      source).knownRebec =
      source.knownRebec := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendStatement_actionName
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    (translateGlobalMultiStorePayloadExternalSendStatement
      source).actionName =
      actionNameFor
        source.messageName := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendStatement_payloadExpressions
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    (translateGlobalMultiStorePayloadExternalSendStatement
      source).payloadExpressions =
      compileMultiStorePayloadExprs
        source.payloadExpressions := by
  rfl

@[simp]
theorem translateGlobalMultiStorePayloadExternalSendStatement_delay
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    (translateGlobalMultiStorePayloadExternalSendStatement
      source).delay =
      source.delay := by
  rfl

end Translation
end Relico
