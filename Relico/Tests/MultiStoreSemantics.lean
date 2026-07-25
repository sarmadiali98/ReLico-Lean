import Relico.Correctness.MultiStoreBackward
import Relico.Tests.MultiStoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def multiStatementVariables :
    List VarName :=
  DTR.stateVariableNames
    twoStateDeclarations

def multiStatementServerNames :
    List MsgName :=
  DTR.messageServerNames
    twoMessageServers

def multiStatementActions :
    List ActionName :=
  Translation.compileLogicalActions
    twoMessageServers

def multiStatementStore :
    StateStore := [
  (twoStateX, 1),
  (twoStateY, 2)
]

def multiStatementCurrentTag :
    LF.Tag where

  time :=
    0

  microstep :=
    0

def multiStatementScheduledTag :
    LF.Tag where

  time :=
    1

  microstep :=
    0

def multiStatementSourceBefore :
    DTR.StoreState where

  currentTime :=
    0

  stateStore :=
    multiStatementStore

  pendingMessages :=
    []

  activeBody := [
    DTR.Stmt.selfSend
      resetMessageName
      { value := 1 }
  ]

def multiStatementSourceAfter :
    DTR.StoreState where

  currentTime :=
    0

  stateStore :=
    multiStatementStore

  pendingMessages := [
    {
      name :=
        resetMessageName

      arrivalTime :=
        1
    }
  ]

  activeBody :=
    []

def multiStatementTargetBefore :
    LF.StoreState where

  currentTag :=
    multiStatementCurrentTag

  stateStore :=
    multiStatementStore

  pendingActions :=
    []

  activeBody :=
    Translation.compileBody
      multiStatementSourceBefore.activeBody

def multiStatementTargetAfter :
    LF.StoreState where

  currentTag :=
    multiStatementCurrentTag

  stateStore :=
    multiStatementStore

  pendingActions := [
    {
      name :=
        Translation.actionNameFor
          resetMessageName

      tag :=
        multiStatementScheduledTag
    }
  ]

  activeBody :=
    []

theorem multi_source_cross_server_send :
    DTR.MultiStoreStep
      multiStatementVariables
      multiStatementServerNames
      multiStatementSourceBefore
      (DTR.Label.send
        resetMessageName
        1)
      multiStatementSourceAfter := by

  apply
    DTR.MultiStoreStep.selfSend

  simp [
    multiStatementServerNames,
    twoMessageServers,
    DTR.messageServerNames,
    tickMessageServer,
    resetMessageServer
  ]

theorem multi_target_cross_server_schedule :
    LF.MultiStoreStep
      multiStatementVariables
      multiStatementActions
      multiStatementTargetBefore
      (LF.Label.schedule
        (Translation.actionNameFor
          resetMessageName)
        multiStatementScheduledTag)
      multiStatementTargetAfter := by

  apply
    LF.MultiStoreStep.schedule

  change
    Translation.actionNameFor
        resetMessageName ∈
      Translation.compileLogicalActions
        twoMessageServers

  have hSourceTarget :
      resetMessageName ∈
        DTR.messageServerNames
          twoMessageServers := by

    simp [
      twoMessageServers,
      DTR.messageServerNames,
      tickMessageServer,
      resetMessageServer
    ]

  have hMapped :
      Translation.actionNameFor
          resetMessageName ∈
        (DTR.messageServerNames
          twoMessageServers).map
            Translation.actionNameFor :=

    List.mem_map_of_mem
      hSourceTarget

  simpa only [
    Translation.compileLogicalActions_names
  ] using
    hMapped

theorem multiStatementInitialStatesCorrespond :
    Correctness.StoreStateCorresponds
      multiStatementSourceBefore
      multiStatementTargetBefore := by

  exact {
    currentTime :=
      rfl

    stateStore :=
      rfl

    pendingEvents :=
      Correctness.QueueCorresponds.nil

    activeBody :=
      rfl
  }

theorem multiStatementSourceBodyWellFormed :
    DTR.Body.MultiStoreWellFormed
      multiStatementVariables
      multiStatementServerNames
      multiStatementSourceBefore.activeBody := by

  simp [
    multiStatementVariables,
    multiStatementServerNames,
    multiStatementSourceBefore,
    twoStateDeclarations,
    twoMessageServers,
    DTR.stateVariableNames,
    DTR.messageServerNames,
    tickMessageServer,
    resetMessageServer,
    DTR.Body.MultiStoreWellFormed,
    DTR.Stmt.MultiStoreWellFormed
  ]

theorem multi_cross_server_send_forward :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreStep
          multiStatementVariables
          multiStatementActions
          multiStatementTargetBefore
          targetLabel
          targetStateAfter ∧
      Correctness.LabelCorresponds
        (DTR.Label.send
          resetMessageName
          1)
        targetLabel ∧
      Correctness.StoreStateCorresponds
        multiStatementSourceAfter
        targetStateAfter := by

  exact
    Correctness.multiStore_step_forward
      multi_source_cross_server_send
      multiStatementInitialStatesCorrespond

theorem multi_cross_server_send_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreStep
          multiStatementVariables
          multiStatementServerNames
          multiStatementSourceBefore
          sourceLabel
          sourceStateAfter ∧
      Correctness.LabelCorresponds
        sourceLabel
        (LF.Label.schedule
          (Translation.actionNameFor
            resetMessageName)
          multiStatementScheduledTag) ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        multiStatementTargetAfter := by

  exact
    Correctness.multiStore_step_backward
      multi_target_cross_server_schedule
      multiStatementInitialStatesCorrespond
      multiStatementSourceBodyWellFormed

theorem multi_cross_server_send_preserves_coverage :
    DTR.StoreState.Covers
      multiStatementVariables
      multiStatementSourceAfter := by

  apply
    DTR.MultiStoreStep.preserves_coverage
      multi_source_cross_server_send

  change
    StateStore.Covers
      multiStatementVariables
      multiStatementStore

  intro variableName hMember

  simp [
    multiStatementVariables,
    twoStateDeclarations,
    DTR.stateVariableNames
  ] at hMember

  rcases hMember with
    rfl | rfl

  · exact
      ⟨1, by
        simp [
          multiStatementStore,
          StateStore.lookup,
          Store.lookup,
          twoStateX,
          twoStateY
        ]⟩

  · exact
      ⟨2, by
        simp [
          multiStatementStore,
          StateStore.lookup,
          Store.lookup,
          twoStateX,
          twoStateY
        ]⟩

theorem multi_cross_server_send_preserves_pending_targets :
    ∀ pendingMessage,
      pendingMessage ∈
        multiStatementSourceAfter.pendingMessages →
      pendingMessage.name ∈
        multiStatementServerNames := by

  apply
    DTR.MultiStoreStep.preserves_pendingTargets
      multi_source_cross_server_send

  intro pendingMessage hMember

  simp [
    multiStatementSourceBefore
  ] at hMember

end Tests
end Relico
