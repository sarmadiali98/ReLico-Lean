import Relico.DTR.GlobalMultiStorePayloadExternalSendStatement

set_option autoImplicit false

namespace Relico
namespace DTR
namespace GlobalMultiStorePayloadExternalSend

/--
A successful E3a attempt exposes the exact sender state, resolved receiver,
receiver state, canonical occurrence, receiver-only state update, and
fresh-history append used by the executable function.
-/
theorem attempt_success_decomposes
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (request :
      DTR.GlobalMultiStorePayloadExternalSend.Request)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hSuccess :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          request =
        .ok success) :
    ∃
      senderState :
        DTR.MultiStorePayloadState,
    ∃
      receiver :
        ActorName,
    ∃
      receiverState :
        DTR.MultiStorePayloadState,

      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          request.sender =
        some senderState ∧

      ActorTopology.resolve
          model.topology
          request.sender
          request.knownRebec =
        some receiver ∧

      receiver ≠
        request.sender ∧

      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          receiver =
        some receiverState ∧

      success.occurrence =
        DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
          request
          receiver
          senderState ∧

      success.state =
        DTR.GlobalMultiStorePayloadState.updateActor
          state
          receiver
          (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverState
            success.occurrence) ∧

      success.history =
        history ++
          [success.occurrence.key] := by

  cases hSenderModel :
      DTR.GlobalMultiStorePayloadModel.lookupActor
        model
        request.sender
  with

  | none =>
      simp [
        DTR.GlobalMultiStorePayloadExternalSend.attempt,
        hSenderModel
      ] at hSuccess

  | some senderModel =>
      cases hSenderLookup :
          DTR.GlobalMultiStorePayloadState.lookupActor
            state
            request.sender
      with

      | none =>
          simp [
            DTR.GlobalMultiStorePayloadExternalSend.attempt,
            hSenderModel,
            hSenderLookup
          ] at hSuccess

      | some senderState =>
          cases hResolve :
              ActorTopology.resolve
                model.topology
                request.sender
                request.knownRebec
          with

          | none =>
              simp [
                DTR.GlobalMultiStorePayloadExternalSend.attempt,
                hSenderModel,
                hSenderLookup,
                hResolve
              ] at hSuccess

          | some receiver =>
              by_cases hSame :
                receiver =
                  request.sender

              · simp [
                  DTR.GlobalMultiStorePayloadExternalSend.attempt,
                  hSenderModel,
                  hSenderLookup,
                  hResolve,
                  hSame
                ] at hSuccess

              · cases hReceiverModel :
                    DTR.GlobalMultiStorePayloadModel.lookupActor
                      model
                      receiver
                with

                | none =>
                    simp [
                      DTR.GlobalMultiStorePayloadExternalSend.attempt,
                      hSenderModel,
                      hSenderLookup,
                      hResolve,
                      hSame,
                      hReceiverModel
                    ] at hSuccess

                | some receiverModel =>
                    cases hReceiverLookup :
                        DTR.GlobalMultiStorePayloadState.lookupActor
                          state
                          receiver
                    with

                    | none =>
                        simp [
                          DTR.GlobalMultiStorePayloadExternalSend.attempt,
                          hSenderModel,
                          hSenderLookup,
                          hResolve,
                          hSame,
                          hReceiverModel,
                          hReceiverLookup
                        ] at hSuccess

                    | some receiverState =>
                        cases hMessageServer :
                            DTR.GlobalMultiStorePayloadExternalSend.lookupMessageServer
                              receiverModel.reactiveClass.messageServers
                              request.messageName
                        with

                        | none =>
                            simp [
                              DTR.GlobalMultiStorePayloadExternalSend.attempt,
                              hSenderModel,
                              hSenderLookup,
                              hResolve,
                              hSame,
                              hReceiverModel,
                              hReceiverLookup,
                              hMessageServer
                            ] at hSuccess

                        | some messageServer =>
                            by_cases hArity :
                              messageServer.parameters.length =
                                request.payload.length

                            · cases hDuplicate :
                                  history.contains
                                    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
                                      request
                                      receiver
                                      senderState).key
                              with

                              | true =>
                                  simp [
                                    DTR.GlobalMultiStorePayloadExternalSend.attempt,
                                    hSenderModel,
                                    hSenderLookup,
                                    hResolve,
                                    hSame,
                                    hReceiverModel,
                                    hReceiverLookup,
                                    hMessageServer,
                                    hArity,
                                    hDuplicate
                                  ] at hSuccess

                              | false =>
                                  simp [
                                    DTR.GlobalMultiStorePayloadExternalSend.attempt,
                                    hSenderModel,
                                    hSenderLookup,
                                    hResolve,
                                    hSame,
                                    hReceiverModel,
                                    hReceiverLookup,
                                    hMessageServer,
                                    hArity,
                                    hDuplicate
                                  ] at hSuccess

                                  subst success

                                  exact ⟨
                                    senderState,
                                    receiver,
                                    receiverState,
                                    rfl,
                                    rfl,
                                    hSame,
                                    hReceiverLookup,
                                    rfl,
                                    rfl,
                                    rfl
                                  ⟩

                            · simp [
                                DTR.GlobalMultiStorePayloadExternalSend.attempt,
                                hSenderModel,
                                hSenderLookup,
                                hResolve,
                                hSame,
                                hReceiverModel,
                                hReceiverLookup,
                                hMessageServer,
                                hArity
                              ] at hSuccess

/--
The successful occurrence retains the request sender exactly.
-/
theorem attempt_success_sender
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (request :
      DTR.GlobalMultiStorePayloadExternalSend.Request)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hSuccess :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          request =
        .ok success) :
    success.occurrence.sender =
      request.sender := by

  rcases
      attempt_success_decomposes
        model
        state
        history
        request
        success
        hSuccess
    with
    ⟨
      senderState,
      receiver,
      receiverState,
      _hSenderLookup,
      _hResolve,
      _hDifferent,
      _hReceiverLookup,
      hOccurrence,
      _hState,
      _hHistory
    ⟩

  rw [hOccurrence]
  rfl

/--
Successful E3a execution certifies that the resolved receiver differs from the
request sender.
-/
theorem attempt_success_receiver_ne_sender
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (request :
      DTR.GlobalMultiStorePayloadExternalSend.Request)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hSuccess :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          request =
        .ok success) :
    success.occurrence.receiver ≠
      request.sender := by

  rcases
      attempt_success_decomposes
        model
        state
        history
        request
        success
        hSuccess
    with
    ⟨
      senderState,
      receiver,
      receiverState,
      _hSenderLookup,
      _hResolve,
      hDifferent,
      _hReceiverLookup,
      hOccurrence,
      _hState,
      _hHistory
    ⟩

  rw [hOccurrence]

  exact
    hDifferent

/--
Successful E3a execution returns exactly one fresh-history append.
-/
theorem attempt_success_history
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (request :
      DTR.GlobalMultiStorePayloadExternalSend.Request)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hSuccess :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          request =
        .ok success) :
    success.history =
      history ++
        [success.occurrence.key] := by

  rcases
      attempt_success_decomposes
        model
        state
        history
        request
        success
        hSuccess
    with
    ⟨
      _senderState,
      _receiver,
      _receiverState,
      _hSenderLookup,
      _hResolve,
      _hDifferent,
      _hReceiverLookup,
      _hOccurrence,
      _hState,
      hHistory
    ⟩

  exact
    hHistory

/--
A successful E3a attempt returns exactly the canonical receiver-only global
state update.
-/
theorem attempt_success_state
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (request :
      DTR.GlobalMultiStorePayloadExternalSend.Request)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hSuccess :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          request =
        .ok success) :
    ∃
      receiverState :
        DTR.MultiStorePayloadState,

      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          success.occurrence.receiver =
        some receiverState ∧

      success.state =
        DTR.GlobalMultiStorePayloadState.updateActor
          state
          success.occurrence.receiver
          (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
            receiverState
            success.occurrence) := by

  rcases
      attempt_success_decomposes
        model
        state
        history
        request
        success
        hSuccess
    with
    ⟨
      _senderState,
      _receiver,
      receiverState,
      _hSenderLookup,
      _hResolve,
      _hDifferent,
      hReceiverLookup,
      hOccurrence,
      hState,
      _hHistory
    ⟩

  refine ⟨
    receiverState,
    ?_,
    ?_
  ⟩

  · simpa [
      hOccurrence,
      DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
    ] using
      hReceiverLookup

  · simpa [
      hOccurrence,
      DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
    ] using
      hState

end GlobalMultiStorePayloadExternalSend

namespace GlobalMultiStorePayloadExternalSendFrame

/--
Additive source control frame for one executing external-send statement.
-/
structure Frame where
  statement :
    DTR.GlobalMultiStorePayloadExternalSendStatement.Statement

  remaining :
    DTR.MultiStorePayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
Advance only the source sender continuation.
-/
def senderStateAfter
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    DTR.MultiStorePayloadState :=
  {
    senderBefore with
    activeBody :=
      frame.remaining
  }

@[simp]
theorem senderStateAfter_currentTime
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).currentTime =
      senderBefore.currentTime := by
  rfl

@[simp]
theorem senderStateAfter_stateStore
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).stateStore =
      senderBefore.stateStore := by
  rfl

@[simp]
theorem senderStateAfter_parameters
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).parameters =
      senderBefore.parameters := by
  rfl

@[simp]
theorem senderStateAfter_pendingMessages
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).pendingMessages =
      senderBefore.pendingMessages := by
  rfl

@[simp]
theorem senderStateAfter_activeBody
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    (senderStateAfter
      senderBefore
      frame).activeBody =
      frame.remaining := by
  rfl

/--
Compose the E3a receiver update with the later sender-continuation update.
-/
def globalStateAfter
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (frame :
      Frame)
    (senderBefore :
      DTR.MultiStorePayloadState) :
    DTR.GlobalMultiStorePayloadState :=
  DTR.GlobalMultiStorePayloadState.updateActor
    foundation.state
    frame.statement.sender
    (senderStateAfter
      senderBefore
      frame)

/--
Successful source-frame execution retains the E3a result and sender state.
-/
structure Success where
  foundation :
    DTR.GlobalMultiStorePayloadExternalSend.Success

  senderBefore :
    DTR.MultiStorePayloadState

  state :
    DTR.GlobalMultiStorePayloadState

deriving Repr, DecidableEq, BEq, Inhabited

def makeSuccess
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    Success where

  foundation :=
    foundation

  senderBefore :=
    senderBefore

  state :=
    globalStateAfter
      foundation
      frame
      senderBefore

/--
Execute E3b1/E3a first and advance the sender continuation second.
-/
def attempt
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (state :
      DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (frame :
      Frame) :
    Except
      DTR.GlobalMultiStorePayloadExternalSendStatement.Failure
      Success :=
  match
      DTR.GlobalMultiStorePayloadState.lookupActor
        state
        frame.statement.sender
  with
  | none =>
      .error .senderStateMissing

  | some senderBefore =>
      match
          DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
            model
            state
            history
            frame.statement
      with
      | .error failure =>
          .error failure

      | .ok foundation =>
          .ok
            (makeSuccess
              foundation
              senderBefore
              frame)

theorem attempt_of_statement_success
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (state :
      DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (frame :
      Frame)
    (senderBefore :
      DTR.MultiStorePayloadState)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hSenderLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          frame.statement.sender =
        some senderBefore)
    (hStatement :
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
          model
          state
          history
          frame.statement =
        .ok foundation) :
    attempt
        model
        state
        history
        frame =
      .ok
        (makeSuccess
          foundation
          senderBefore
          frame) := by

  simp [
    attempt,
    hSenderLookup,
    hStatement
  ]

theorem attempt_of_statement_failure
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (state :
      DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (frame :
      Frame)
    (senderBefore :
      DTR.MultiStorePayloadState)
    (failure :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Failure)
    (hSenderLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          frame.statement.sender =
        some senderBefore)
    (hStatement :
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
          model
          state
          history
          frame.statement =
        .error failure) :
    attempt
        model
        state
        history
        frame =
      .error failure := by

  simp [
    attempt,
    hSenderLookup,
    hStatement
  ]

@[simp]
theorem makeSuccess_state
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (senderBefore :
      DTR.MultiStorePayloadState)
    (frame :
      Frame) :
    (makeSuccess
      foundation
      senderBefore
      frame).state =
      globalStateAfter
        foundation
        frame
        senderBefore := by
  rfl

theorem globalStateAfter_sender
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (frame :
      Frame)
    (senderBefore :
      DTR.MultiStorePayloadState) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (globalStateAfter
          foundation
          frame
          senderBefore)
        frame.statement.sender =
      some
        (senderStateAfter
          senderBefore
          frame) := by

  exact
    DTR.GlobalMultiStorePayloadState.lookupActor_update_eq
      foundation.state
      frame.statement.sender
      (senderStateAfter
        senderBefore
        frame)

theorem globalStateAfter_receiver_preserved
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (state :
      DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (frame :
      Frame)
    (payload :
      Payload)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (senderBefore :
      DTR.MultiStorePayloadState)
    (hFoundation :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          (frame.statement.toRequest payload) =
        .ok foundation) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (globalStateAfter
          foundation
          frame
          senderBefore)
        foundation.occurrence.receiver =
      DTR.GlobalMultiStorePayloadState.lookupActor
        foundation.state
        foundation.occurrence.receiver := by

  apply
    DTR.GlobalMultiStorePayloadState.lookupActor_update_ne

  have hReceiverNeSender :
      foundation.occurrence.receiver ≠
        frame.statement.sender := by

    simpa using
      DTR.GlobalMultiStorePayloadExternalSend.attempt_success_receiver_ne_sender
        model
        state
        history
        (frame.statement.toRequest payload)
        foundation
        hFoundation

  exact
    fun hSenderEqReceiver =>
      hReceiverNeSender
        hSenderEqReceiver.symm

theorem globalStateAfter_unrelated_preserved
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (frame :
      Frame)
    (senderBefore :
      DTR.MultiStorePayloadState)
    (otherActor :
      ActorName)
    (hDifferent :
      frame.statement.sender ≠
        otherActor) :
    DTR.GlobalMultiStorePayloadState.lookupActor
        (globalStateAfter
          foundation
          frame
          senderBefore)
        otherActor =
      DTR.GlobalMultiStorePayloadState.lookupActor
        foundation.state
        otherActor := by

  exact
    DTR.GlobalMultiStorePayloadState.lookupActor_update_ne
      foundation.state
      (senderStateAfter
        senderBefore
        frame)
      hDifferent

@[simp]
theorem globalStateAfter_currentTime
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (frame :
      Frame)
    (senderBefore :
      DTR.MultiStorePayloadState) :
    (globalStateAfter
      foundation
      frame
      senderBefore).currentTime =
      foundation.state.currentTime := by
  rfl

end GlobalMultiStorePayloadExternalSendFrame
end DTR
end Relico
