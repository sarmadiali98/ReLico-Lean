/-
Copyright (c) 2026.

Payload-refined ordinary runtime-state correspondence for the direct
DTR-to-generated-LF translation.

This layer strengthens pending-occurrence correspondence with exact payload
equality while projecting to the existing DirectLF state relations.
-/

import Relico.Correctness.DirectLFPayloadSelectionRemoval
import Relico.Correctness.DirectLFRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Payload-refined correspondence between ordinary DTR and LF store states.

All structural fields are unchanged. The pending source bag and LF action
queue use the stronger payload-aware selection relation.
-/
structure DirectLFPayloadStoreStateCorresponds
    (messageServers : List DTR.MessageServer)
    (sourceState : DTR.StoreState)
    (targetState : LF.StoreState) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateStore :
    targetState.stateStore =
      sourceState.stateStore

  pendingEvents :
    DirectLFPayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compileBody
        sourceState.activeBody

/--
Forgetting payload equality yields the existing structural state relation.
-/
theorem DirectLFPayloadStoreStateCorresponds.toStoreStateCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hStates :
      DirectLFPayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFStoreStateCorresponds
      messageServers
      sourceState
      targetState := by

  exact {
    currentTime :=
      hStates.currentTime

    stateStore :=
      hStates.stateStore

    pendingEvents :=
      hStates.pendingEvents.toSelectionCompatible

    activeBody :=
      hStates.activeBody
  }

/--
The payload-refined state relation exposes payload-aware pending occurrence
correspondence directly.
-/
theorem DirectLFPayloadStoreStateCorresponds.payloadSelectionCompatible
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hStates :
      DirectLFPayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFPayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=
  hStates.pendingEvents

/--
The payload-refined state relation retains payload-preserving source-bag/LF
queue correspondence.
-/
theorem DirectLFPayloadStoreStateCorresponds.toPayloadBagQueueCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hStates :
      DirectLFPayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFPayloadBagQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=
  hStates.pendingEvents.toPayloadBagQueueCorresponds

/--
Payload-refined runtime correspondence adds the existing LF pending-not-past
scheduler invariant.
-/
structure DirectLFPayloadRuntimeStateCorresponds
    (messageServers : List DTR.MessageServer)
    (sourceState : DTR.StoreState)
    (targetState : LF.StoreState) :
    Prop where

  states :
    DirectLFPayloadStoreStateCorresponds
      messageServers
      sourceState
      targetState

  pendingNotPast :
    LF.StoreState.PendingNotPast
      targetState

/--
Forgetting payload equality yields the existing runtime-state relation.
-/
theorem DirectLFPayloadRuntimeStateCorresponds.toRuntimeStateCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hRuntime :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFRuntimeStateCorresponds
      messageServers
      sourceState
      targetState := by

  exact {
    states :=
      hRuntime.states.toStoreStateCorresponds

    pendingNotPast :=
      hRuntime.pendingNotPast
  }

/--
The payload-refined runtime package exposes the stronger pending-event
relation.
-/
theorem DirectLFPayloadRuntimeStateCorresponds.selectionCompatible
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hRuntime :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFPayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=
  hRuntime.states.pendingEvents

/--
The payload-refined runtime package retains the existing structural runtime
correspondence.
-/
theorem DirectLFPayloadRuntimeStateCorresponds.toStoreStateCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hRuntime :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFStoreStateCorresponds
      messageServers
      sourceState
      targetState :=
  hRuntime.states.toStoreStateCorresponds

end Correctness
end Relico
