import Relico.Correctness.DirectLFPayloadSelectionCompatibility

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFPayloadSelectionCompatibility

#check
  Correctness.DirectLFPayloadBagQueueCorresponds

#check
  Correctness.DirectLFPayloadBagQueueCorresponds.toBagQueueCorresponds

#check
  Correctness.DirectLFPayloadBagQueueCorresponds.perm_source

#check
  Correctness.DirectLFPayloadBagQueueCorresponds.perm_target

#check
  Correctness.DirectLFPayloadBagQueueCorresponds.append_one

#check
  Correctness.PayloadQueueCorresponds.append_one

#check
  Correctness.PayloadQueueCorresponds.pendingPayloadCorresponds_of_aligned

#check
  Correctness.DirectLFPayloadOrderedSelectionCompatible

#check
  Correctness.DirectLFPayloadOrderedSelectionCompatible.toOrderedSelectionCompatible

#check
  Correctness.DirectLFPayloadOrderedSelectionCompatible.alignedPayload

#check
  Correctness.DirectLFPayloadSelectionCompatible

#check
  Correctness.DirectLFPayloadSelectionCompatible.toSelectionCompatible

#check
  Correctness.DirectLFPayloadSelectionCompatible.toPayloadBagQueueCorresponds

#check
  Correctness.DirectLFPayloadSelectionCompatible.toBagQueueCorresponds

#check
  Correctness.DirectLFPayloadSelectionCompatible.perm_source

#check
  Correctness.DirectLFPayloadSelectionCompatible.perm_target

#check
  Correctness.directLFPayloadSelectionCompatible_nil

example
    (messageServers : List DTR.MessageServer) :
    Correctness.DirectLFPayloadSelectionCompatible
      messageServers
      []
      [] := by

  exact
    Correctness.directLFPayloadSelectionCompatible_nil
      messageServers

example
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      Correctness.DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      sourceBag
      targetQueue := by

  exact
    hPayload.toSelectionCompatible

example
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      Correctness.DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    Correctness.DirectLFPayloadBagQueueCorresponds
      sourceBag
      targetQueue := by

  exact
    hPayload.toPayloadBagQueueCorresponds

end DirectLFPayloadSelectionCompatibility
end Tests
end Relico
