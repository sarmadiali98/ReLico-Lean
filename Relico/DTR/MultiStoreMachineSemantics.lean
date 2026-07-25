import Relico.DTR.MultiStoreDispatchSemantics
import Relico.DTR.MultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Labels for the combined finite-store, multiple-message-server DTR
machine.

A dispatch label retains both the selected pending occurrence and the
declared message server whose body is loaded.
-/
inductive MultiStoreMachineLabel where

  | statement :
      DTR.Label →
      MultiStoreMachineLabel

  | dispatch :
      DTR.PendingMessage →
      DTR.MessageServer →
      MultiStoreMachineLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Combined one-step DTR semantics for finite state and multiple message
servers.
-/
inductive MultiStoreMachineStep
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    DTR.StoreState →
    DTR.MultiStoreMachineLabel →
    DTR.StoreState →
    Prop where

  | statement
      {stateBefore stateAfter : DTR.StoreState}
      {label : DTR.Label}
      (hStep :
        DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          stateBefore
          label
          stateAfter) :

      MultiStoreMachineStep
        declaredVariables
        messageServers
        stateBefore
        (DTR.MultiStoreMachineLabel.statement
          label)
        stateAfter

  | dispatch
      {stateBefore stateAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {selectedServer : DTR.MessageServer}
      (hDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          stateBefore
          selectedMessage
          selectedServer
          stateAfter) :

      MultiStoreMachineStep
        declaredVariables
        messageServers
        stateBefore
        (DTR.MultiStoreMachineLabel.dispatch
          selectedMessage
          selectedServer)
        stateAfter

end DTR
end Relico
