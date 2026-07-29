import Relico.Correctness.MultiStorePayloadSelectionCompatibility

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadSelectionCompatibility

theorem empty_compatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      []
      [] :=

  Correctness.multiStorePayloadSelectionCompatible_nil
    messageServers

theorem same_microstep_pair_compatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      Correctness.PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      Correctness.PendingCorresponds
        sourceRight
        targetRight)
    (hSameMicrostep :
      targetLeft.tag.microstep =
        targetRight.tag.microstep) :
    Correctness.MultiStorePayloadBasePairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight :=

  Correctness.multiStorePayloadBasePairSelectionCompatible_of_sameMicrostep
      hLeft
      hRight
      hSameMicrostep

theorem earlier_microstep_pair_compatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      Correctness.PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      Correctness.PendingCorresponds
        sourceRight
        targetRight)
    (hMicrostep :
      targetLeft.tag.microstep <
        targetRight.tag.microstep)
    (hPriority :
      Correctness.MultiStorePayloadBaseStrictPriorityPrecedes
        messageServers
        sourceLeft.name
        sourceRight.name) :
    Correctness.MultiStorePayloadBasePairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight :=

  Correctness.multiStorePayloadBasePairSelectionCompatible_of_leftEarlier
      hLeft
      hRight
      hMicrostep
      hPriority

theorem earlier_microstep_recovers_priority
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight)
    (hSameTime :
      sourceLeft.arrivalTime =
        sourceRight.arrivalTime)
    (hEarlier :
      targetLeft.tag.microstep <
        targetRight.tag.microstep) :
    Correctness.MultiStorePayloadBaseStrictPriorityPrecedes
      messageServers
      sourceLeft.name
      sourceRight.name :=

  hCompatible.strictPriority_of_leftEarlier
    hSameTime
    hEarlier

theorem payload_projects_base
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    Correctness.MultiStorePayloadBaseSelectionCompatible
      messageServers
      sourceBag
      targetQueue :=

  hCompatible.toSelectionCompatible

theorem payload_projects_exact_bag
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    Correctness.MultiStorePayloadBagQueueCorresponds
      sourceBag
      targetQueue :=

  hCompatible.toPayloadBagQueueCorresponds

theorem aligned_occurrence_preserves_payload
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceRepresentative :
      DTR.MessageBag}
    {targetRepresentative :
      LF.ActionQueue}
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadOrderedSelectionCompatible
        messageServers
        sourceRepresentative
        targetRepresentative)
    (hAligned :
      Correctness.MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceRepresentative
        targetRepresentative) :
    Correctness.PendingPayloadCorresponds
      sourceMessage
      targetAction :=

  hCompatible.alignedPayload
    hAligned

theorem source_permutation_preserves_compatibility
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    (hPermutation :
      sourceLeft.Perm
        sourceRight)
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceRight
        targetQueue) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      sourceLeft
      targetQueue :=

  Correctness.MultiStorePayloadSelectionCompatible.perm_source
    hPermutation
    hCompatible

theorem target_permutation_preserves_compatibility
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag :
      DTR.MessageBag}
    {targetLeft targetRight :
      LF.ActionQueue}
    (hPermutation :
      targetLeft.Perm
        targetRight)
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetRight) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      sourceBag
      targetLeft :=

  Correctness.MultiStorePayloadSelectionCompatible.perm_target
    hPermutation
    hCompatible

end MultiStorePayloadSelectionCompatibility
end Tests
end Relico
