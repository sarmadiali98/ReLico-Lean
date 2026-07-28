import Relico.LF.PendingNotPast

set_option autoImplicit false

namespace Relico
namespace Tests
namespace LFPendingNotPast

/--
Zero-delay scheduling produces a tag that is not before the current tag.
-/
theorem zero_delay_is_not_past
    (currentTag : LF.Tag) :
    LF.Tag.PrecedesOrEqual
      currentTag
      (LF.Tag.schedule
        currentTag
        { value := 0 }) :=
  LF.Tag.precedesOrEqual_schedule
    currentTag
    { value := 0 }

/--
A singleton scheduled occurrence satisfies the pending-not-past invariant for
every delay, including zero.
-/
theorem scheduled_singleton_not_past
    (currentTag : LF.Tag)
    (actionName : ActionName)
    (delay : Delay) :
    LF.ActionQueue.PendingNotPast
      currentTag
      [
        {
          name :=
            actionName

          tag :=
            LF.Tag.schedule
              currentTag
              delay
        }
      ] := by

  apply
    LF.ActionQueue.PendingNotPast.append_one
      (LF.ActionQueue.pendingNotPast_nil
        currentTag)

  exact
    LF.Tag.precedesOrEqual_schedule
      currentTag
      delay

#check LF.Tag.precedesOrEqual_schedule

#check LF.ActionQueue.PendingNotPast
#check LF.ActionQueue.PendingNotPast.append_one
#check LF.ActionQueue.PendingNotPast.remove

#check
  LF.ActionQueue.pendingNotPast_of_remove_earliest

#check LF.StoreState.PendingNotPast
#check LF.StoreState.PendingNotPast.action

#check
  LF.MultiStoreStep.preserves_pendingNotPast

#check
  LF.MultiStoreDispatchStep.establishes_pendingNotPast

#check zero_delay_is_not_past
#check scheduled_singleton_not_past

end LFPendingNotPast
end Tests
end Relico
