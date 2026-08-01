import Relico.Correctness.GlobalMultiStorePayloadExternalSendCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadExternalSend

open DTR.GlobalMultiStorePayloadExternalSend

def senderActor : ActorName :=
  ⟨"sender"⟩

def receiverActor : ActorName :=
  ⟨"receiver"⟩

def receiverReference : KnownRebecName :=
  ⟨"peer"⟩

def senderClassName : ClassName :=
  ⟨"Sender"⟩

def receiverClassName : ClassName :=
  ⟨"Receiver"⟩

def deliverMessage : MsgName :=
  ⟨"deliver"⟩

def missingMessage : MsgName :=
  ⟨"missing"⟩

def valueParameter : VarName :=
  ⟨"value"⟩

def senderReactiveClass :
    DTR.MultiStorePayloadReactiveClass where
  name :=
    senderClassName

  stateVariables :=
    []

  constructor := {
    body := []
  }

  messageServers :=
    []

def receiverMessageServer :
    DTR.MultiStorePayloadMessageServer where
  name :=
    deliverMessage

  parameters :=
    [valueParameter]

  body :=
    []

  priority :=
    none

def receiverReactiveClass :
    DTR.MultiStorePayloadReactiveClass where
  name :=
    receiverClassName

  stateVariables :=
    []

  constructor := {
    body := []
  }

  messageServers :=
    [receiverMessageServer]

def senderModel :
    DTR.MultiStorePayloadModel where
  reactiveClass :=
    senderReactiveClass

  actor := {
    name := senderActor
    className := senderClassName
  }

def receiverModel :
    DTR.MultiStorePayloadModel where
  reactiveClass :=
    receiverReactiveClass

  actor := {
    name := receiverActor
    className := receiverClassName
  }

def sourceModel :
    DTR.GlobalMultiStorePayloadModel where
  actors :=
    [
      (senderActor, senderModel),
      (receiverActor, receiverModel)
    ]

  topology :=
    [
      (
        senderActor,
        [
          (receiverReference, receiverActor)
        ]
      ),
      (
        receiverActor,
        []
      )
    ]

def senderSourceState :
    DTR.MultiStorePayloadState where
  currentTime :=
    5

  stateStore :=
    []

  parameters :=
    []

  pendingMessages :=
    []

  activeBody :=
    []

def receiverSourceState :
    DTR.MultiStorePayloadState where
  currentTime :=
    2

  stateStore :=
    []

  parameters :=
    []

  pendingMessages :=
    []

  activeBody :=
    []

def sourceState :
    DTR.GlobalMultiStorePayloadState where
  currentTime :=
    5

  actorStates :=
    [
      (senderActor, senderSourceState),
      (receiverActor, receiverSourceState)
    ]

def senderTargetState :
    LF.MultiStorePayloadState where
  currentTag := {
    time := 5
    microstep := 4
  }

  stateStore :=
    []

  parameters :=
    []

  pendingActions :=
    []

  activeBody :=
    []

def receiverTargetState :
    LF.MultiStorePayloadState where
  currentTag := {
    time := 2
    microstep := 0
  }

  stateStore :=
    []

  parameters :=
    []

  pendingActions :=
    []

  activeBody :=
    []

def targetState :
    LF.GlobalMultiStorePayloadState where
  currentTag := {
    time := 5
    microstep := 4
  }

  actorStates :=
    [
      (senderActor, senderTargetState),
      (receiverActor, receiverTargetState)
    ]

def positiveRequest : Request where
  sender :=
    senderActor

  knownRebec :=
    receiverReference

  messageName :=
    deliverMessage

  payload :=
    [7]

  delay :=
    { value := 3 }

def zeroDelayRequest : Request :=
  {
    positiveRequest with
    payload := [9]
    delay := { value := 0 }
  }

def missingMessageRequest : Request :=
  {
    positiveRequest with
    messageName := missingMessage
  }

def wrongArityRequest : Request :=
  {
    positiveRequest with
    payload := []
  }

def unresolvedRequest : Request :=
  {
    positiveRequest with
    knownRebec := ⟨"unknown"⟩
  }

def positiveSourceOccurrence : Occurrence :=
  makeOccurrence
    positiveRequest
    receiverActor
    senderSourceState

def zeroSourceOccurrence : Occurrence :=
  makeOccurrence
    zeroDelayRequest
    receiverActor
    senderSourceState

def positiveTargetOccurrence :
    LF.GlobalMultiStorePayloadExternalSend.Occurrence :=
  Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
    positiveSourceOccurrence
    senderTargetState.currentTag

def zeroTargetOccurrence :
    LF.GlobalMultiStorePayloadExternalSend.Occurrence :=
  Translation.translateGlobalMultiStorePayloadExternalSendOccurrence
    zeroSourceOccurrence
    senderTargetState.currentTag

/--
D1A regression: the source sender is at time 5 and the receiver is at time 2.
The positive-delay occurrence must arrive at 8, not 5.
-/
theorem positive_attempt_uses_sender_time :
    match
      attempt
        sourceModel
        sourceState
        []
        positiveRequest
    with
    | .error _ =>
        False

    | .ok result =>
        result.occurrence.sender = senderActor ∧
        result.occurrence.receiver = receiverActor ∧
        result.occurrence.sendTime = 5 ∧
        result.occurrence.arrivalTime = 8 ∧
        DTR.GlobalMultiStorePayloadState.lookupActor
            result.state
            receiverActor =
          some
            (receiverStateAfter
              receiverSourceState
              positiveSourceOccurrence) := by
  change
    senderActor = senderActor ∧
      receiverActor = receiverActor ∧
      (5 : LogicalTime) = 5 ∧
      (8 : LogicalTime) = 8 ∧
      some
          (receiverStateAfter
            receiverSourceState
            positiveSourceOccurrence) =
        some
          (receiverStateAfter
            receiverSourceState
            positiveSourceOccurrence)

  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
D2B regression: both endpoints and the sender-relative known-rebec name survive
occurrence translation.
-/
theorem sender_receiver_identity_is_preserved :
    positiveTargetOccurrence.sender = senderActor ∧
      positiveTargetOccurrence.receiver = receiverActor ∧
      positiveTargetOccurrence.knownRebec = receiverReference := by
  decide

/--
D3B+ regression: payload and delay are not part of the collision key.
-/
theorem same_edge_same_time_key_ignores_payload_and_delay :
    positiveSourceOccurrence.key =
      zeroSourceOccurrence.key := by
  rfl

/--
D3B+ regression: a second occurrence on the same edge at the same sending time
is rejected before another receiver update is produced.
-/
theorem duplicate_same_edge_time_is_rejected :
    attempt
        sourceModel
        sourceState
        [positiveSourceOccurrence.key]
        zeroDelayRequest =
      .error .duplicateSameEdgeTime := by
  rfl

/--
Target message-server existence is checked.
-/
theorem unknown_message_server_is_rejected :
    attempt
        sourceModel
        sourceState
        []
        missingMessageRequest =
      .error .messageServerMissing := by
  rfl

/--
Ordered payload arity must match the target declaration.
-/
theorem payload_arity_mismatch_is_rejected :
    attempt
        sourceModel
        sourceState
        []
        wrongArityRequest =
      .error .payloadArityMismatch := by
  rfl

/--
Unknown sender-relative topology references are rejected.
-/
theorem unresolved_known_rebec_is_rejected :
    attempt
        sourceModel
        sourceState
        []
        unresolvedRequest =
      .error .receiverResolutionFailed := by
  rfl

/--
D4A+ positive-delay regression: metric time advances and the microstep resets.
-/
theorem positive_delay_target_tag :
    positiveTargetOccurrence.deliveryTag =
      {
        time := 8
        microstep := 0
      } := by
  decide

/--
D4A+ explicit-zero regression: metric time is unchanged and the microstep
advances exactly once.
-/
theorem explicit_zero_delay_target_tag :
    zeroTargetOccurrence.deliveryTag =
      {
        time := 5
        microstep := 5
      } := by
  decide

theorem senderStatesCorrespond :
    Correctness.MultiStorePayloadStateCorresponds
      senderSourceState
      senderTargetState where
  currentTime :=
    rfl

  stateStore :=
    rfl

  parameters :=
    rfl

  pendingQueues :=
    Correctness.PayloadQueueCorresponds.nil

  activeBody :=
    rfl

theorem receiverStatesCorrespond :
    Correctness.MultiStorePayloadStateCorresponds
      receiverSourceState
      receiverTargetState where
  currentTime :=
    rfl

  stateStore :=
    rfl

  parameters :=
    rfl

  pendingQueues :=
    Correctness.PayloadQueueCorresponds.nil

  activeBody :=
    rfl

/--
Appending the external occurrence preserves exact ordered payload queue
correspondence even though the sender and receiver local times differ.
-/
theorem receiver_states_correspond_after_positive_send :
    Correctness.MultiStorePayloadStateCorresponds
      (receiverStateAfter
        receiverSourceState
        positiveSourceOccurrence)
      (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        receiverTargetState
        positiveTargetOccurrence) := by

  exact
    Correctness.translated_globalMultiStorePayloadExternalSend_receiverStates_correspond
      positiveSourceOccurrence
      senderTargetState.currentTag
      receiverSourceState
      receiverTargetState
      receiverStatesCorrespond
      rfl

/--
The complete one-send package records sender state, receiver state, occurrence
translation, both global updates, and receiver-state correspondence.
-/
theorem packaged_positive_send_corresponds :
    Correctness.GlobalMultiStorePayloadExternalSendCorresponds
      positiveSourceOccurrence
      positiveTargetOccurrence
      sourceState
      (DTR.GlobalMultiStorePayloadState.updateActor
        sourceState
        receiverActor
        (receiverStateAfter
          receiverSourceState
          positiveSourceOccurrence))
      targetState
      (LF.GlobalMultiStorePayloadState.updateActor
        targetState
        receiverActor
        (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
          receiverTargetState
          positiveTargetOccurrence)) := by

  exact
    Correctness.translated_globalMultiStorePayloadExternalSend_corresponds
      positiveSourceOccurrence
      sourceState
      targetState
      senderSourceState
      senderTargetState
      receiverSourceState
      receiverTargetState
      rfl
      rfl
      rfl
      rfl
      senderStatesCorrespond
      receiverStatesCorrespond
      rfl
      rfl

/--
The source sender state is unrelated to the receiver update and is preserved.
-/
theorem source_sender_state_is_unchanged :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (DTR.GlobalMultiStorePayloadState.updateActor
          sourceState
          receiverActor
          (receiverStateAfter
            receiverSourceState
            positiveSourceOccurrence))
        senderActor =
      some senderSourceState := by

  calc
    DTR.GlobalMultiStorePayloadState.lookupActor
        (DTR.GlobalMultiStorePayloadState.updateActor
          sourceState
          receiverActor
          (receiverStateAfter
            receiverSourceState
            positiveSourceOccurrence))
        senderActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        sourceState
        senderActor := by
          exact
            Correctness.globalMultiStorePayloadExternalSend_source_unrelated_preserved
              sourceState
              receiverSourceState
              positiveSourceOccurrence
              senderActor
              (by decide)

    _ =
      some senderSourceState := by
        rfl

/--
The target sender state is likewise preserved.
-/
theorem target_sender_state_is_unchanged :
    LF.GlobalMultiStorePayloadState.lookupActor
        (LF.GlobalMultiStorePayloadState.updateActor
          targetState
          receiverActor
          (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverTargetState
            positiveTargetOccurrence))
        senderActor =
      some senderTargetState := by

  calc
    LF.GlobalMultiStorePayloadState.lookupActor
        (LF.GlobalMultiStorePayloadState.updateActor
          targetState
          receiverActor
          (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverTargetState
            positiveTargetOccurrence))
        senderActor =
      LF.GlobalMultiStorePayloadState.lookupActor
        targetState
        senderActor := by
          exact
            Correctness.globalMultiStorePayloadExternalSend_target_unrelated_preserved
              targetState
              receiverTargetState
              positiveTargetOccurrence
              senderActor
              (by decide)

    _ =
      some senderTargetState := by
        rfl

/--
The executable LF application helper performs the same receiver update.
-/
theorem target_apply_updates_receiver :
    LF.GlobalMultiStorePayloadExternalSend.apply?
        targetState
        positiveTargetOccurrence =
      some
        (LF.GlobalMultiStorePayloadState.updateActor
          targetState
          receiverActor
          (LF.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverTargetState
            positiveTargetOccurrence)) := by

  exact
    LF.GlobalMultiStorePayloadExternalSend.apply?_of_lookup
      targetState
      positiveTargetOccurrence
      receiverTargetState
      rfl


/--
A topology reference resolving to the sender belongs to the separate self-send
path, not to this external-send construction.
-/
def selfReactiveClass :
    DTR.MultiStorePayloadReactiveClass where
  name :=
    senderClassName

  stateVariables :=
    []

  constructor := {
    body := []
  }

  messageServers :=
    [receiverMessageServer]

def selfActorModel :
    DTR.MultiStorePayloadModel where
  reactiveClass :=
    selfReactiveClass

  actor := {
    name := senderActor
    className := senderClassName
  }

def selfGlobalModel :
    DTR.GlobalMultiStorePayloadModel where
  actors :=
    [
      (senderActor, selfActorModel)
    ]

  topology :=
    [
      (
        senderActor,
        [
          (receiverReference, senderActor)
        ]
      )
    ]

def selfGlobalState :
    DTR.GlobalMultiStorePayloadState where
  currentTime :=
    5

  actorStates :=
    [
      (senderActor, senderSourceState)
    ]

/--
Endpoint-separation regression: a known-rebec edge resolving back to the sender
is rejected before any receiver queue update.
-/
theorem external_send_rejects_self_resolution :
    attempt
        selfGlobalModel
        selfGlobalState
        []
        positiveRequest =
      .error .selfSendNotExternal := by
  rfl

theorem empty_history_is_unique :
    HistoryUnique [] := by
  simp [HistoryUnique]

/--
The theorem-level D3 invariant preserves uniqueness when a fresh key is
appended.
-/
theorem append_fresh_preserves_history_unique :
    HistoryUnique
      ([] ++ [positiveSourceOccurrence.key]) := by

  exact
    historyUnique_append_fresh
      empty_history_is_unique
      (by simp)

/--
The executable successful-send branch returns the corresponding unique
singleton history from an empty unique history.
-/
theorem successful_attempt_returns_unique_history :
    match
      attempt
        sourceModel
        sourceState
        []
        positiveRequest
    with
    | .error _ =>
        False

    | .ok result =>
        HistoryUnique result.history := by

  change
    HistoryUnique
      ([] ++ [positiveSourceOccurrence.key])

  exact
    historyUnique_append_fresh
      empty_history_is_unique
      (by simp)

end GlobalMultiStorePayloadExternalSend
end Tests
end Relico
