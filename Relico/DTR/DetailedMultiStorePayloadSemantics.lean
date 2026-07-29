import Relico.DTR.DetailedMultiStorePayloadRuntime
import Relico.DTR.MultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Detailed one-step decomposition of the payload-aware DTR runtime.

Ordinary payload statement execution is internal. Dispatch is decomposed into
visible metric-time progression followed by visible message consumption.
Same-time dispatch consumes directly from a stable state.
-/
inductive DetailedMultiStorePayloadStep
    (messageServers :
      List MultiStorePayloadMessageServer) :
    DetailedMultiStorePayloadState
        messageServers →
      DetailedMultiStorePayloadLabel →
        DetailedMultiStorePayloadState
            messageServers →
          Prop where

  | statement
      {before after :
        MultiStorePayloadState}
      (statementStep :
        MultiStorePayloadStep
          before
          after) :
      DetailedMultiStorePayloadStep
        messageServers
        (.stable before)
        .tau
        (.stable after)

  | timeAdvance
      {before after :
        MultiStorePayloadState}
      {selectedMessage :
        PendingMessage}
      {selectedServer :
        MultiStorePayloadMessageServer}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageServers
          before
          selectedMessage
          selectedServer
          after)
      (future :
        before.currentTime <
          after.currentTime) :
      DetailedMultiStorePayloadStep
        messageServers
        (.stable before)
        (.timeAdvance
          before.currentTime
          after.currentTime)
        (.dispatchReady
          before
          selectedMessage
          selectedServer
          after
          dispatch)

  | consumeReady
      {before after :
        MultiStorePayloadState}
      {selectedMessage :
        PendingMessage}
      {selectedServer :
        MultiStorePayloadMessageServer}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageServers
          before
          selectedMessage
          selectedServer
          after) :
      DetailedMultiStorePayloadStep
        messageServers
        (.dispatchReady
          before
          selectedMessage
          selectedServer
          after
          dispatch)
        (.consume
          selectedMessage
          selectedServer)
        (.stable after)

  | consumeNow
      {before after :
        MultiStorePayloadState}
      {selectedMessage :
        PendingMessage}
      {selectedServer :
        MultiStorePayloadMessageServer}
      (dispatch :
        MultiStorePayloadDispatchStep
          messageServers
          before
          selectedMessage
          selectedServer
          after)
      (sameTime :
        before.currentTime =
          after.currentTime) :
      DetailedMultiStorePayloadStep
        messageServers
        (.stable before)
        (.consume
          selectedMessage
          selectedServer)
        (.stable after)

end DTR
end Relico
