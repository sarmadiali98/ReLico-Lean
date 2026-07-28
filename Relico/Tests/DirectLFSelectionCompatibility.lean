import Relico.Correctness.DirectLFSelectionCompatibility

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFSelectionCompatibility

/--
The empty source bag and LF action queue satisfy selection compatibility.
-/
theorem empty_compatible
    (messageServers :
      List DTR.MessageServer) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      []
      [] :=
  Correctness.directLFSelectionCompatible_nil
    messageServers

/--
Two corresponding occurrences at the same LF microstep are pair-compatible.
Reaction declaration order resolves their same-tag priority.
-/
theorem same_microstep_pair_compatible
    {messageServers :
      List DTR.MessageServer}
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
    Correctness.DirectLFPairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight :=
  Correctness.directLFPairSelectionCompatible_of_sameMicrostep
    hLeft
    hRight
    hSameMicrostep

/--
An earlier LF microstep is compatible when it follows strict DTR priority.
-/
theorem earlier_microstep_pair_compatible
    {messageServers :
      List DTR.MessageServer}
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
      Correctness.DirectLFStrictPriorityPrecedes
        messageServers
        sourceLeft.name
        sourceRight.name) :
    Correctness.DirectLFPairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight :=
  Correctness.directLFPairSelectionCompatible_of_leftEarlier
    hLeft
    hRight
    hMicrostep
    hPriority

/--
For equal metric times, an earlier LF microstep recovers the required strict
DTR message-server order.
-/
theorem earlier_microstep_recovers_priority
    {messageServers :
      List DTR.MessageServer}
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hCompatible :
      Correctness.DirectLFPairSelectionCompatible
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
    Correctness.DirectLFStrictPriorityPrecedes
      messageServers
      sourceLeft.name
      sourceRight.name :=
  hCompatible.strictPriority_of_leftEarlier
    hSameTime
    hEarlier

#check Correctness.DirectLFStrictPriorityPrecedes
#check Correctness.DirectLFPairSelectionCompatible
#check Correctness.DirectLFPairSelectionCompatible.symm
#check Correctness.DirectLFAlignedOccurrence
#check Correctness.DirectLFOrderedSelectionCompatible
#check Correctness.DirectLFSelectionCompatible

#check
  Correctness.DirectLFSelectionCompatible.toBagQueueCorresponds

#check
  Correctness.directLFAlignedOccurrence_of_source_mem

#check
  Correctness.directLFAlignedOccurrence_of_target_mem

#check
  Correctness.directLF_sourcePriorityEligible_implies_exists_targetReactionPriorityEligible

#check
  Correctness.directLF_targetReactionPriorityEligible_implies_exists_sourcePriorityEligible

#check empty_compatible
#check same_microstep_pair_compatible
#check earlier_microstep_pair_compatible
#check earlier_microstep_recovers_priority

end DirectLFSelectionCompatibility
end Tests
end Relico
