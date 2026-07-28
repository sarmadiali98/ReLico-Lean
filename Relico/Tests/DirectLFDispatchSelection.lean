import Relico.Correctness.DirectLFDispatchSelection

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFDispatchSelection

/--
A concrete source occurrence selected for DTR dispatch determines a concrete
corresponding LF occurrence that can be removed and is reaction-priority
eligible.
-/
theorem source_selection_pairs_removal_and_eligibility
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceSelected :
      DTR.PendingMessage}
    (hCompatible :
      Correctness.DirectLFSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        sourceSelected
        sourceQueue
        sourceRemaining)
    (hEligible :
      DTR.IsPriorityEligible
        messageServers
        sourceSelected
        sourceQueue) :
    ∃ targetSelected targetRemaining,
      Occurrence.RemovesOne
          targetSelected
          targetQueue
          targetRemaining ∧
        Correctness.PendingCorresponds
          sourceSelected
          targetSelected ∧
        LF.IsReactionPriorityEligible
          (Translation.compileMessageReactions
            messageServers)
          targetSelected
          targetQueue ∧
        Correctness.DirectLFSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=
  Correctness.directLF_sourceDispatchSelection
    hCompatible
    hRemoved
    hEligible

/--
A concrete generated-LF occurrence selected for dispatch determines a
concrete corresponding DTR occurrence that can be removed and is
source-priority eligible.
-/
theorem target_selection_pairs_removal_and_eligibility
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {targetSelected :
      LF.PendingAction}
    (hCompatible :
      Correctness.DirectLFSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        targetSelected
        targetQueue
        targetRemaining)
    (hEligible :
      LF.IsReactionPriorityEligible
        (Translation.compileMessageReactions
          messageServers)
        targetSelected
        targetQueue) :
    ∃ sourceSelected sourceRemaining,
      Occurrence.RemovesOne
          sourceSelected
          sourceQueue
          sourceRemaining ∧
        Correctness.PendingCorresponds
          sourceSelected
          targetSelected ∧
        DTR.IsPriorityEligible
          messageServers
          sourceSelected
          sourceQueue ∧
        Correctness.DirectLFSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=
  Correctness.directLF_targetDispatchSelection
    hCompatible
    hRemoved
    hEligible

#check
  Correctness.pendingCorresponds_sourceName_eq_of_sameTarget

#check
  Correctness.pendingCorresponds_sourceTime_eq_of_sameTarget

#check
  Correctness.pendingCorresponds_targetName_eq_of_sameSource

#check
  Correctness.pendingCorresponds_targetTime_eq_of_sameSource

#check Correctness.directLF_sourceDispatchSelection
#check Correctness.directLF_targetDispatchSelection

#check source_selection_pairs_removal_and_eligibility
#check target_selection_pairs_removal_and_eligibility

end DirectLFDispatchSelection
end Tests
end Relico
