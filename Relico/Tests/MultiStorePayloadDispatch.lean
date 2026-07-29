import Relico.DTR.MultiStorePayloadDispatch
import Relico.LF.MultiStorePayloadDispatch
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDispatch

def stateName :
    VarName :=
  ⟨"state"⟩

def firstParameter :
    VarName :=
  ⟨"first"⟩

def secondParameter :
    VarName :=
  ⟨"second"⟩

def highMessageName :
    MsgName :=
  ⟨"high"⟩

def lowMessageName :
    MsgName :=
  ⟨"low"⟩

def highServer :
    DTR.MultiStorePayloadMessageServer where

  name :=
    highMessageName

  parameters :=
    [
      firstParameter,
      secondParameter
    ]

  body :=
    [
      .assign
        stateName
        (.parameterVar
          firstParameter)
    ]

  priority :=
    some 1

def lowServer :
    DTR.MultiStorePayloadMessageServer where

  name :=
    lowMessageName

  parameters :=
    []

  body :=
    []

  priority :=
    some 4

/--
The input list is deliberately not priority-normalized.
-/
def sourceServers :
    List DTR.MultiStorePayloadMessageServer :=
  [
    lowServer,
    highServer
  ]

def highReaction :
    LF.MultiStorePayloadReaction :=
  Translation.compileMultiStorePayloadReaction
    highServer

def lowReaction :
    LF.MultiStorePayloadReaction :=
  Translation.compileMultiStorePayloadReaction
    lowServer

def targetReactions :
    List LF.MultiStorePayloadReaction :=
  [
    highReaction,
    lowReaction
  ]

def generatedReactions :
    List LF.MultiStorePayloadReaction :=
  (Translation.priorityOrderedMultiStorePayloadMessageServers
      sourceServers).map
    Translation.compileMultiStorePayloadReaction

/--
Translation generates the same priority-normalized reaction order used
by the target dispatch tests.
-/
theorem generated_reactions_match_priority_order :
    generatedReactions =
      targetReactions := by
  decide

def highMessage :
    DTR.PendingMessage where

  name :=
    highMessageName

  arrivalTime :=
    10

  payload :=
    [7, 3]

def lowMessage :
    DTR.PendingMessage where

  name :=
    lowMessageName

  arrivalTime :=
    10

  payload :=
    []

def sourceQueue :
    DTR.MessageBag :=
  [
    highMessage,
    lowMessage
  ]

def commonTargetTag :
    LF.Tag where

  time :=
    10

  microstep :=
    2

def highAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      highMessageName

  tag :=
    commonTargetTag

  payload :=
    [7, 3]

def lowAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      lowMessageName

  tag :=
    commonTargetTag

  payload :=
    []

def targetQueue :
    LF.ActionQueue :=
  [
    highAction,
    lowAction
  ]

/--
Priority normalization places the explicit priority `1` server before
the explicit priority `4` server.
-/
theorem source_high_precedes_low :
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      highMessageName
      lowMessageName
      sourceServers := by
  decide

/--
The converse priority order is false.
-/
theorem source_low_does_not_precede_high :
    ¬ DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
        lowMessageName
        highMessageName
        sourceServers := by
  decide

/--
The generated high-priority reaction precedes the generated
low-priority reaction.
-/
theorem target_high_precedes_low :
    LF.MultiStorePayloadReactionActionPrecedesOrEqual
      highAction.name
      lowAction.name
      targetReactions := by
  decide

/--
The converse generated reaction order is false.
-/
theorem target_low_does_not_precede_high :
    ¬ LF.MultiStorePayloadReactionActionPrecedesOrEqual
        lowAction.name
        highAction.name
        targetReactions := by
  decide

/--
At equal source metric time, the high-priority occurrence is eligible.
-/
theorem source_high_priority_eligible :
    DTR.MultiStorePayloadIsPriorityEligible
      sourceServers
      highMessage
      sourceQueue := by

  refine
    ⟨?_, ?_⟩

  · intro candidate hCandidate

    simp [sourceQueue] at hCandidate

    rcases hCandidate with
      hCandidate |
      hCandidate

    · subst candidate
      exact Nat.le_refl 10

    · subst candidate
      exact Nat.le_refl 10

  · intro candidate hCandidate _hSameTime

    simp [sourceQueue] at hCandidate

    rcases hCandidate with
      hCandidate |
      hCandidate

    · subst candidate
      decide

    · subst candidate
      decide

/--
At the same source metric time, the lower-priority occurrence is not
eligible while the higher-priority occurrence remains pending.
-/
theorem source_low_not_priority_eligible :
    ¬ DTR.MultiStorePayloadIsPriorityEligible
        sourceServers
        lowMessage
        sourceQueue := by

  intro hEligible

  have hOrder :=
    hEligible.2
      highMessage
      (by
        simp [sourceQueue])
      rfl

  exact
    source_low_does_not_precede_high
      hOrder

/--
At one complete LF tag, the high-priority generated action is eligible.
-/
theorem target_high_priority_eligible :
    LF.MultiStorePayloadIsReactionPriorityEligible
      targetReactions
      highAction
      targetQueue := by

  refine
    ⟨?_, ?_⟩

  · intro candidate hCandidate

    simp [targetQueue] at hCandidate

    rcases hCandidate with
      hCandidate |
      hCandidate

    · subst candidate
      exact
        LF.Tag.precedesOrEqual_refl
          commonTargetTag

    · subst candidate
      exact
        LF.Tag.precedesOrEqual_refl
          commonTargetTag

  · intro candidate hCandidate _hSameTag

    simp [targetQueue] at hCandidate

    rcases hCandidate with
      hCandidate |
      hCandidate

    · subst candidate
      decide

    · subst candidate
      decide

/--
At that same complete LF tag, the lower-priority action is not eligible
while the higher-priority action remains pending.
-/
theorem target_low_not_priority_eligible :
    ¬ LF.MultiStorePayloadIsReactionPriorityEligible
        targetReactions
        lowAction
        targetQueue := by

  intro hEligible

  have hOrder :=
    hEligible.2
      highAction
      (by
        simp [targetQueue])
      rfl

  exact
    target_low_does_not_precede_high
      hOrder

def initialStateStore :
    StateStore :=
  [
    (stateName, 0)
  ]

def boundParameters :
    ParameterStore :=
  [
    (firstParameter, 7),
    (secondParameter, 3)
  ]

def sourceBefore :
    DTR.MultiStorePayloadState where

  currentTime :=
    9

  stateStore :=
    initialStateStore

  parameters :=
    []

  pendingMessages :=
    sourceQueue

  activeBody :=
    []

def sourceAfter :
    DTR.MultiStorePayloadState where

  currentTime :=
    10

  stateStore :=
    initialStateStore

  parameters :=
    boundParameters

  pendingMessages :=
    [lowMessage]

  activeBody :=
    highServer.body

/--
Source dispatch removes the exact selected occurrence and binds the
ordered payload to the ordered formal parameters.
-/
theorem source_dispatch_fires :
    DTR.MultiStorePayloadDispatchStep
      sourceServers
      sourceBefore
      highMessage
      highServer
      sourceAfter := by

  exact
    DTR.MultiStorePayloadDispatchStep.fire
      9
      initialStateStore
      []
      sourceQueue
      [lowMessage]
      highMessage
      highServer
      boundParameters
      (by
        simp [sourceServers])
      (Occurrence.RemovesOne.head
        [lowMessage])
      source_high_priority_eligible
      (by decide)
      rfl
      rfl

def targetBefore :
    LF.MultiStorePayloadState where

  currentTag :=
    {
      time := 9
      microstep := 0
    }

  stateStore :=
    initialStateStore

  parameters :=
    []

  pendingActions :=
    targetQueue

  activeBody :=
    []

def targetAfter :
    LF.MultiStorePayloadState where

  currentTag :=
    commonTargetTag

  stateStore :=
    initialStateStore

  parameters :=
    boundParameters

  pendingActions :=
    [lowAction]

  activeBody :=
    highReaction.body

/--
Generated LF dispatch removes the corresponding action occurrence and
binds the same ordered parameter environment.
-/
theorem target_dispatch_fires :
    LF.MultiStorePayloadDispatchStep
      targetReactions
      targetBefore
      highAction
      highReaction
      targetAfter := by

  exact
    LF.MultiStorePayloadDispatchStep.fire
      {
        time := 9
        microstep := 0
      }
      initialStateStore
      []
      targetQueue
      [lowAction]
      highAction
      highReaction
      boundParameters
      (by
        simp [targetReactions])
      (Occurrence.RemovesOne.head
        [lowAction])
      target_high_priority_eligible
      (Or.inl
        (by decide))
      rfl
      rfl

/--
Both dispatches construct exactly the same ordered parameter store.
-/
theorem source_target_binding_exact :
    sourceAfter.parameters =
        boundParameters ∧
      targetAfter.parameters =
        boundParameters ∧
      sourceAfter.parameters =
        targetAfter.parameters := by
  exact
    ⟨rfl, rfl, rfl⟩

/--
Source and target dispatch remove only their selected concrete
occurrence.
-/
theorem exact_occurrence_removal :
    sourceAfter.pendingMessages =
        [lowMessage] ∧
      targetAfter.pendingActions =
        [lowAction] := by
  exact
    ⟨rfl, rfl⟩

/--
Persistent state is unchanged by dispatch activation.
-/
theorem dispatch_preserves_persistent_state :
    sourceAfter.stateStore =
        sourceBefore.stateStore ∧
      targetAfter.stateStore =
        targetBefore.stateStore := by
  exact
    ⟨
      DTR.MultiStorePayloadDispatchStep.preserves_stateStore
        source_dispatch_fires,
      LF.MultiStorePayloadDispatchStep.preserves_stateStore
        target_dispatch_fires
    ⟩

def duplicateSourceQueue :
    DTR.MessageBag :=
  [
    highMessage,
    highMessage
  ]

def duplicateTargetQueue :
    LF.ActionQueue :=
  [
    highAction,
    highAction
  ]

theorem source_duplicate_high_eligible :
    DTR.MultiStorePayloadIsPriorityEligible
      [highServer]
      highMessage
      duplicateSourceQueue := by

  refine
    ⟨?_, ?_⟩

  · intro candidate hCandidate

    simp [duplicateSourceQueue] at hCandidate
    subst candidate

    exact Nat.le_refl 10

  · intro candidate hCandidate _hSameTime

    simp [duplicateSourceQueue] at hCandidate
    subst candidate

    decide

theorem target_duplicate_high_eligible :
    LF.MultiStorePayloadIsReactionPriorityEligible
      [highReaction]
      highAction
      duplicateTargetQueue := by

  refine
    ⟨?_, ?_⟩

  · intro candidate hCandidate

    simp [duplicateTargetQueue] at hCandidate
    subst candidate

    exact
      LF.Tag.precedesOrEqual_refl
        commonTargetTag

  · intro candidate hCandidate _hSameTag

    simp [duplicateTargetQueue] at hCandidate
    subst candidate

    decide

def duplicateSourceBefore :
    DTR.MultiStorePayloadState where

  currentTime :=
    9

  stateStore :=
    initialStateStore

  parameters :=
    []

  pendingMessages :=
    duplicateSourceQueue

  activeBody :=
    []

def duplicateSourceAfter :
    DTR.MultiStorePayloadState where

  currentTime :=
    10

  stateStore :=
    initialStateStore

  parameters :=
    boundParameters

  pendingMessages :=
    [highMessage]

  activeBody :=
    highServer.body

theorem duplicate_source_dispatch_removes_one :
    DTR.MultiStorePayloadDispatchStep
        [highServer]
        duplicateSourceBefore
        highMessage
        highServer
        duplicateSourceAfter ∧
      duplicateSourceAfter.pendingMessages.length =
        1 := by

  refine
    ⟨?_, rfl⟩

  exact
    DTR.MultiStorePayloadDispatchStep.fire
      9
      initialStateStore
      []
      duplicateSourceQueue
      [highMessage]
      highMessage
      highServer
      boundParameters
      (by simp)
      (Occurrence.RemovesOne.head
        [highMessage])
      source_duplicate_high_eligible
      (by decide)
      rfl
      rfl

def duplicateTargetBefore :
    LF.MultiStorePayloadState where

  currentTag :=
    {
      time := 9
      microstep := 0
    }

  stateStore :=
    initialStateStore

  parameters :=
    []

  pendingActions :=
    duplicateTargetQueue

  activeBody :=
    []

def duplicateTargetAfter :
    LF.MultiStorePayloadState where

  currentTag :=
    commonTargetTag

  stateStore :=
    initialStateStore

  parameters :=
    boundParameters

  pendingActions :=
    [highAction]

  activeBody :=
    highReaction.body

theorem duplicate_target_dispatch_removes_one :
    LF.MultiStorePayloadDispatchStep
        [highReaction]
        duplicateTargetBefore
        highAction
        highReaction
        duplicateTargetAfter ∧
      duplicateTargetAfter.pendingActions.length =
        1 := by

  refine
    ⟨?_, rfl⟩

  exact
    LF.MultiStorePayloadDispatchStep.fire
      {
        time := 9
        microstep := 0
      }
      initialStateStore
      []
      duplicateTargetQueue
      [highAction]
      highAction
      highReaction
      boundParameters
      (by simp)
      (Occurrence.RemovesOne.head
        [highAction])
      target_duplicate_high_eligible
      (Or.inl
        (by decide))
      rfl
      rfl

/--
A payload with too few values cannot bind to the server's two formal
parameters.
-/
theorem missing_payload_component_rejected :
    ParameterStore.bindPayload
        highServer.parameters
        [7] =
      none := by
  rfl

/--
A payload with too many values is also rejected.
-/
theorem extra_payload_component_rejected :
    ParameterStore.bindPayload
        highServer.parameters
        [7, 3, 11] =
      none := by
  rfl

/--
The compiled reaction has the same arity-sensitive binding behavior.
-/
theorem target_payload_arity_rejected :
    ParameterStore.bindPayload
        highReaction.parameters
        [7] =
        none ∧
      ParameterStore.bindPayload
        highReaction.parameters
        [7, 3, 11] =
        none := by
  exact
    ⟨rfl, rfl⟩

end MultiStorePayloadDispatch
end Tests
end Relico
