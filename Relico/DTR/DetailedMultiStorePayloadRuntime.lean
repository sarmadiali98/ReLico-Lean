import Relico.DTR.MultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Proof-indexed phases for payload-aware multi-server DTR dispatch.

DTR has no microstep phase. A future dispatch pauses in `dispatchReady`
between its visible metric-time transition and visible consumption.
-/
inductive DetailedMultiStorePayloadState
    (messageServers :
      List MultiStorePayloadMessageServer) where

  | stable
      (state :
        MultiStorePayloadState) :
      DetailedMultiStorePayloadState
        messageServers

  | dispatchReady
      (before :
        MultiStorePayloadState)
      (selectedMessage :
        PendingMessage)
      (selectedServer :
        MultiStorePayloadMessageServer)
      (after :
        MultiStorePayloadState)
      (dispatch :
        MultiStorePayloadDispatchStep
          messageServers
          before
          selectedMessage
          selectedServer
          after) :
      DetailedMultiStorePayloadState
        messageServers

/--
Detailed observable labels for payload-aware multi-server DTR dispatch.

Statement execution is represented by `tau`. Dispatch exposes metric-time
progression and exact message/server consumption.
-/
inductive DetailedMultiStorePayloadLabel where

  | tau :
      DetailedMultiStorePayloadLabel

  | timeAdvance
      (before after :
        LogicalTime) :
      DetailedMultiStorePayloadLabel

  | consume
      (selectedMessage :
        PendingMessage)
      (selectedServer :
        MultiStorePayloadMessageServer) :
      DetailedMultiStorePayloadLabel

end DTR
end Relico
