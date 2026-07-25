import Relico.DTR.MessageServerPriority
import Relico.Tests.MultiStoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def priorityHighName :
    MsgName :=
  ⟨"priorityHigh"⟩

def priorityHighTieName :
    MsgName :=
  ⟨"priorityHighTie"⟩

def priorityLowName :
    MsgName :=
  ⟨"priorityLow"⟩

def priorityNoneName :
    MsgName :=
  ⟨"priorityNone"⟩

def priorityHighServer :
    DTR.MessageServer where

  name :=
    priorityHighName

  body :=
    []

  priority :=
    some 1

def priorityHighTieServer :
    DTR.MessageServer where

  name :=
    priorityHighTieName

  body :=
    []

  priority :=
    some 1

def priorityLowServer :
    DTR.MessageServer where

  name :=
    priorityLowName

  body :=
    []

  priority :=
    some 4

def priorityNoneServer :
    DTR.MessageServer where

  name :=
    priorityNoneName

  body :=
    []

/--
Smaller numeric priorities precede larger numeric priorities.
-/
theorem explicit_priority_numeric_order :
    DTR.MessageServerPriority.PrecedesOrEqual
      priorityHighServer
      priorityLowServer := by

  exact
    DTR.MessageServerPriority.lower_numeric_precedes
        (leftPriority := 1)
        (rightPriority := 4)
        rfl
        rfl
        (by decide)

/--
Explicitly prioritized servers precede unannotated servers.
-/
theorem explicit_priority_precedes_none :
    DTR.MessageServerPriority.PrecedesOrEqual
      priorityLowServer
      priorityNoneServer := by

  exact
    DTR.MessageServerPriority.explicit_precedes_unannotated
        (priority := 4)
        rfl
        rfl

/--
Normalization follows numeric priority, places unannotated servers
last, and preserves declaration order for equal numeric priorities.
-/
theorem priority_normalization_regression :
    DTR.MessageServerPriority.normalize [
      priorityLowServer,
      priorityNoneServer,
      priorityHighServer,
      priorityHighTieServer
    ] = [
      priorityHighServer,
      priorityHighTieServer,
      priorityLowServer,
      priorityNoneServer
    ] := by
  rfl

/--
Normalization preserves every declaration occurrence.
-/
theorem priority_normalization_preserves_membership :
    ∀ messageServer,
      messageServer ∈ [
        priorityLowServer,
        priorityNoneServer,
        priorityHighServer,
        priorityHighTieServer
      ] →
      messageServer ∈
        DTR.MessageServerPriority.normalize [
          priorityLowServer,
          priorityNoneServer,
          priorityHighServer,
          priorityHighTieServer
        ] := by

  intro messageServer hMember

  exact
    (DTR.MessageServerPriority.mem_normalize_iff
        messageServer
        _).mpr
          hMember

/--
Normalization preserves declaration count.
-/
theorem priority_normalization_preserves_length :
    (DTR.MessageServerPriority.normalize [
      priorityLowServer,
      priorityNoneServer,
      priorityHighServer,
      priorityHighTieServer
    ]).length =
      4 := by
  rfl

/--
Existing message-server fixtures remain unannotated through the
default field value.
-/
theorem existing_tick_server_has_no_priority :
    tickMessageServer.priority =
      none := by
  rfl

theorem existing_reset_server_has_no_priority :
    resetMessageServer.priority =
      none := by
  rfl

/--
The existing two-server declaration order is unchanged when both
servers are unannotated.
-/
theorem existing_unannotated_order_regression :
    DTR.MessageServerPriority.normalize
        twoMessageServers =
      twoMessageServers := by
  rfl


def priorityTranslationServers :
    List DTR.MessageServer := [
  priorityLowServer,
  priorityNoneServer,
  priorityHighServer,
  priorityHighTieServer
]

/--
The source declaration list itself remains unchanged.
-/
theorem priority_translation_preserves_source_declarations :
    priorityTranslationServers = [
      priorityLowServer,
      priorityNoneServer,
      priorityHighServer,
      priorityHighTieServer
    ] := by
  rfl

/--
Generated logical actions use stable priority order.
-/
theorem priority_translation_action_order :
    Translation.compileLogicalActions
        priorityTranslationServers = [
      Translation.actionNameFor
        priorityHighName,
      Translation.actionNameFor
        priorityHighTieName,
      Translation.actionNameFor
        priorityLowName,
      Translation.actionNameFor
        priorityNoneName
    ] := by
  rfl

/--
Generated message reactions use exactly the same stable priority order.
-/
theorem priority_translation_reaction_order :
    Translation.compileMessageReactions
        priorityTranslationServers = [
      Translation.compileMessageReaction
        priorityHighServer,
      Translation.compileMessageReaction
        priorityHighTieServer,
      Translation.compileMessageReaction
        priorityLowServer,
      Translation.compileMessageReaction
        priorityNoneServer
    ] := by
  rfl

/--
The logical-action and reaction lists remain positionally aligned after
priority normalization.
-/
theorem priority_translation_triggers_align :
    LF.reactionTriggers
        (Translation.compileMessageReactions
          priorityTranslationServers) =
      (Translation.compileLogicalActions
        priorityTranslationServers).map
          LF.Trigger.logicalAction := by
  rfl

end Tests
end Relico
