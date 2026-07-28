import Relico.Correctness.DirectLFSelectionAppend

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFSelectionAppend

/--
Any structurally corresponding occurrence can be added to empty source and
target collections.
-/
theorem empty_accepts_corresponding_occurrence
    (messageServers :
      List DTR.MessageServer)
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hCorresponds :
      Correctness.PendingCorresponds
        sourceNew
        targetNew) :
    Correctness.DirectLFSelectionAppendCompatible
      messageServers
      []
      []
      sourceNew
      targetNew :=
  Correctness.directLFSelectionAppendCompatible_nil
    messageServers
    hCorresponds

/--
A corresponding singleton source bag and LF action queue satisfy the
selection-compatibility invariant.
-/
theorem singleton_compatible
    (messageServers :
      List DTR.MessageServer)
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hCorresponds :
      Correctness.PendingCorresponds
        sourceMessage
        targetAction) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      [sourceMessage]
      [targetAction] :=
  Correctness.directLFSelectionCompatible_singleton
    messageServers
    hCorresponds

/--
A valid step-local append premise preserves selection compatibility when the
new occurrences are appended to the concrete lists.
-/
theorem append_one_preserves
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hAppend :
      Correctness.DirectLFSelectionAppendCompatible
        messageServers
        sourceQueue
        targetQueue
        sourceNew
        targetNew) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      (sourceQueue ++ [sourceNew])
      (targetQueue ++ [targetNew]) :=
  hAppend.append_one

/--
The same append premise also supports front insertion into representative
lists.
-/
theorem cons_one_preserves
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hAppend :
      Correctness.DirectLFSelectionAppendCompatible
        messageServers
        sourceQueue
        targetQueue
        sourceNew
        targetNew) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      (sourceNew :: sourceQueue)
      (targetNew :: targetQueue) :=
  hAppend.cons_one

/--
The append premise contains the pre-existing selection-compatibility
invariant.
-/
theorem append_premise_contains_previous_invariant
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hAppend :
      Correctness.DirectLFSelectionAppendCompatible
        messageServers
        sourceQueue
        targetQueue
        sourceNew
        targetNew) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      sourceQueue
      targetQueue :=
  hAppend.toSelectionCompatible

#check Correctness.directLF_append_singleton_perm_cons
#check Correctness.directLFAlignedOccurrence_cons_cases

#check Correctness.DirectLFSelectionAppendCompatible

#check
  Correctness.DirectLFSelectionAppendCompatible.toSelectionCompatible

#check Correctness.directLFOrderedSelectionCompatible_cons
#check Correctness.directLFSelectionAppendCompatible_nil

#check Correctness.DirectLFSelectionAppendCompatible.cons_one
#check Correctness.DirectLFSelectionAppendCompatible.append_one

#check Correctness.directLFSelectionCompatible_singleton

#check empty_accepts_corresponding_occurrence
#check singleton_compatible
#check append_one_preserves
#check cons_one_preserves
#check append_premise_contains_previous_invariant

end DirectLFSelectionAppend
end Tests
end Relico
