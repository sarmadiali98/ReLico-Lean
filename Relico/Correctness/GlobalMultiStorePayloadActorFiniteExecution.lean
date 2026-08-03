import Relico.Correctness.GlobalMultiStorePayloadActorDispatchCorrespondence

set_option autoImplicit false

namespace Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution

abbrev SourceRequest :=
  _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityRequest

abbrev SourceReadyActor :=
  _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ReadyActor

abbrev SourceModel :=
  _root_.Relico.DTR.GlobalMultiStorePayloadModel

abbrev TargetProgram :=
  _root_.Relico.LF.GlobalMultiStorePayloadProgram

abbrev SourceState :=
  _root_.Relico.DTR.GlobalMultiStorePayloadState

abbrev TargetState :=
  _root_.Relico.LF.GlobalMultiStorePayloadState

/--
A proof index for one global actor-dispatch transition.

The ready-actor snapshot is local to this transition. It is deliberately
not fixed globally across an arbitrary execution.
-/
structure ActorDispatchFrame where
  ready : List SourceReadyActor
  actorName : _root_.Relico.ActorName

/--
The source-side observable dispatch occurrence retained by the finite relation.
-/
structure SourceActorDispatchEvent where
  selectedMessage : _root_.Relico.DTR.PendingMessage
  selectedServer : _root_.Relico.DTR.MultiStorePayloadMessageServer

/--
The target-side observable dispatch occurrence retained by the finite relation.
-/
structure TargetActorDispatchEvent where
  selectedAction : _root_.Relico.LF.PendingAction
  selectedReaction : _root_.Relico.LF.MultiStorePayloadReaction

/--
A source dispatch occurrence corresponds to a target dispatch occurrence when
the pending payloads correspond and the target reaction is the compiled source
message server.
-/
structure ActorDispatchEventCorresponds
    (sourceEvent : SourceActorDispatchEvent)
    (targetEvent : TargetActorDispatchEvent) :
    Prop where
  selectedReaction_eq :
    targetEvent.selectedReaction =
      _root_.Relico.Translation.compileMultiStorePayloadReaction
        sourceEvent.selectedServer
  pending :
    _root_.Relico.Correctness.PendingPayloadCorresponds
      sourceEvent.selectedMessage
      targetEvent.selectedAction

/--
Pointwise occurrence correspondence for a finite dispatch trace.
-/
inductive ActorDispatchEventTraceCorresponds :
    List SourceActorDispatchEvent →
      List TargetActorDispatchEvent →
        Prop
  | nil :
      ActorDispatchEventTraceCorresponds
        []
        []
  | cons
      {sourceEvent : SourceActorDispatchEvent}
      {targetEvent : TargetActorDispatchEvent}
      {sourceRemaining : List SourceActorDispatchEvent}
      {targetRemaining : List TargetActorDispatchEvent}
      (head :
        ActorDispatchEventCorresponds
          sourceEvent
          targetEvent)
      (tail :
        ActorDispatchEventTraceCorresponds
          sourceRemaining
          targetRemaining) :
      ActorDispatchEventTraceCorresponds
        (sourceEvent :: sourceRemaining)
        (targetEvent :: targetRemaining)

/--
Finite source execution consisting only of actor-priority-aware global
dispatch transitions.

Each list element carries the ready snapshot and selected actor used for that
particular transition.
-/
inductive SourceActorPriorityDispatchSteps
    (request : SourceRequest)
    (sourceModel : SourceModel) :
    SourceState →
      List ActorDispatchFrame →
        List SourceActorDispatchEvent →
          SourceState →
            Prop
  | nil
      (state : SourceState) :
      SourceActorPriorityDispatchSteps
        request
        sourceModel
        state
        []
        []
        state
  | cons
      {before middle after : SourceState}
      {frame : ActorDispatchFrame}
      {remainingFrames : List ActorDispatchFrame}
      {event : SourceActorDispatchEvent}
      {remainingEvents : List SourceActorDispatchEvent}
      (head :
        _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
          request
          frame.ready
          sourceModel
          frame.actorName
          before
          event.selectedMessage
          event.selectedServer
          middle)
      (tail :
        SourceActorPriorityDispatchSteps
          request
          sourceModel
          middle
          remainingFrames
          remainingEvents
          after) :
      SourceActorPriorityDispatchSteps
        request
        sourceModel
        before
        (frame :: remainingFrames)
        (event :: remainingEvents)
        after

/--
Finite target execution over the compiled actor-order request and the compiled
ready snapshot associated with each source proof frame.
-/
inductive TargetActorOrderDispatchSteps
    (request : SourceRequest)
    (targetProgram : TargetProgram) :
    TargetState →
      List ActorDispatchFrame →
        List TargetActorDispatchEvent →
          TargetState →
            Prop
  | nil
      (state : TargetState) :
      TargetActorOrderDispatchSteps
        request
        targetProgram
        state
        []
        []
        state
  | cons
      {before middle after : TargetState}
      {frame : ActorDispatchFrame}
      {remainingFrames : List ActorDispatchFrame}
      {event : TargetActorDispatchEvent}
      {remainingEvents : List TargetActorDispatchEvent}
      (head :
        _root_.Relico.LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
          (_root_.Relico.Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest request)
          (_root_.Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors frame.ready)
          targetProgram
          frame.actorName
          before
          event.selectedAction
          event.selectedReaction
          middle)
      (tail :
        TargetActorOrderDispatchSteps
          request
          targetProgram
          middle
          remainingFrames
          remainingEvents
          after) :
      TargetActorOrderDispatchSteps
        request
        targetProgram
        before
        (frame :: remainingFrames)
        (event :: remainingEvents)
        after

theorem sourceActorPriorityDispatchSteps_single
    {request : SourceRequest}
    {sourceModel : SourceModel}
    {before after : SourceState}
    {frame : ActorDispatchFrame}
    {event : SourceActorDispatchEvent}
    (hStep :
      _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
        request
        frame.ready
        sourceModel
        frame.actorName
        before
        event.selectedMessage
        event.selectedServer
        after) :
    SourceActorPriorityDispatchSteps
      request
      sourceModel
      before
      [frame]
      [event]
      after := by
  exact
    SourceActorPriorityDispatchSteps.cons
      hStep
      (SourceActorPriorityDispatchSteps.nil after)

theorem targetActorOrderDispatchSteps_single
    {request : SourceRequest}
    {targetProgram : TargetProgram}
    {before after : TargetState}
    {frame : ActorDispatchFrame}
    {event : TargetActorDispatchEvent}
    (hStep :
      _root_.Relico.LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
        (_root_.Relico.Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest request)
        (_root_.Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors frame.ready)
        targetProgram
        frame.actorName
        before
        event.selectedAction
        event.selectedReaction
        after) :
    TargetActorOrderDispatchSteps
      request
      targetProgram
      before
      [frame]
      [event]
      after := by
  exact
    TargetActorOrderDispatchSteps.cons
      hStep
      (TargetActorOrderDispatchSteps.nil after)

/--
Every finite source actor-priority dispatch execution has a target actor-order
dispatch execution with the same step-local ready snapshots and selected actor
names, a pointwise corresponding occurrence trace, and a corresponding final
runtime state.
-/
theorem sourceActorPriorityDispatchSteps_forward
    {request : SourceRequest}
    {sourceModel : SourceModel}
    {targetProgram : TargetProgram}
    {sourceBefore sourceAfter : SourceState}
    {targetBefore : TargetState}
    {frames : List ActorDispatchFrame}
    {sourceEvents : List SourceActorDispatchEvent}
    (hSteps :
      SourceActorPriorityDispatchSteps
        request
        sourceModel
        sourceBefore
        frames
        sourceEvents
        sourceAfter)
    (hStates :
      _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore
        targetBefore) :
    ∃ targetEvents targetAfter,
      TargetActorOrderDispatchSteps
          request
          targetProgram
          targetBefore
          frames
          targetEvents
          targetAfter ∧
        ActorDispatchEventTraceCorresponds
          sourceEvents
          targetEvents ∧
          _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            sourceAfter
            targetAfter := by
  induction hSteps generalizing targetBefore with
  | nil state =>
      exact
        ⟨[],
          targetBefore,
          TargetActorOrderDispatchSteps.nil targetBefore,
          ActorDispatchEventTraceCorresponds.nil,
          hStates⟩
  | @cons
      before
      middle
      after
      frame
      remainingFrames
      event
      remainingEvents
      hHead
      hTail
      inductionHypothesis =>
      rcases
        _root_.Relico.Correctness.GlobalMultiStorePayloadActorDispatchCorrespondence.synchronizedActorPriorityDispatch_forward
          hHead
          hStates with
        ⟨selectedAction,
          targetMiddle,
          hTargetHead,
          hPending,
          hMiddleStates⟩

      rcases inductionHypothesis hMiddleStates with
        ⟨targetRemainingEvents,
          targetAfter,
          hTargetTail,
          hTraceTail,
          hAfterStates⟩

      let targetEvent : TargetActorDispatchEvent := {
        selectedAction := selectedAction
        selectedReaction :=
          _root_.Relico.Translation.compileMultiStorePayloadReaction
            event.selectedServer
      }

      have hTargetHead' :
          _root_.Relico.LF.GlobalMultiStorePayloadActorOrder.ActorOrderDispatchStep
            (_root_.Relico.Translation.GlobalMultiStorePayloadActorOrder.compileActorPriorityRequest request)
            (_root_.Relico.Translation.GlobalMultiStorePayloadActorOrder.compileReadyActors frame.ready)
            targetProgram
            frame.actorName
            targetBefore
            targetEvent.selectedAction
            targetEvent.selectedReaction
            targetMiddle := by
        simpa [targetEvent] using hTargetHead

      have hEventCorresponds :
          ActorDispatchEventCorresponds
            event
            targetEvent := by
        exact {
          selectedReaction_eq := rfl
          pending := by
            simpa [targetEvent] using hPending
        }

      refine
        ⟨targetEvent :: targetRemainingEvents,
          targetAfter,
          ?_,
          ?_,
          hAfterStates⟩

      · exact
          TargetActorOrderDispatchSteps.cons
            hTargetHead'
            hTargetTail

      · exact
          ActorDispatchEventTraceCorresponds.cons
            hEventCorresponds
            hTraceTail

/--
Every finite target actor-order dispatch execution indexed by compiled
step-local source snapshots has a source actor-priority dispatch execution with
the same selected actor names, a pointwise corresponding occurrence trace, and
a corresponding final runtime state.
-/
theorem targetActorOrderDispatchSteps_backward
    {request : SourceRequest}
    {sourceModel : SourceModel}
    {targetProgram : TargetProgram}
    {sourceBefore : SourceState}
    {targetBefore targetAfter : TargetState}
    {frames : List ActorDispatchFrame}
    {targetEvents : List TargetActorDispatchEvent}
    (hSteps :
      TargetActorOrderDispatchSteps
        request
        targetProgram
        targetBefore
        frames
        targetEvents
        targetAfter)
    (hStates :
      _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore
        targetBefore) :
    ∃ sourceEvents sourceAfter,
      SourceActorPriorityDispatchSteps
          request
          sourceModel
          sourceBefore
          frames
          sourceEvents
          sourceAfter ∧
        ActorDispatchEventTraceCorresponds
          sourceEvents
          targetEvents ∧
          _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            sourceAfter
            targetAfter := by
  induction hSteps generalizing sourceBefore with
  | nil state =>
      exact
        ⟨[],
          sourceBefore,
          SourceActorPriorityDispatchSteps.nil sourceBefore,
          ActorDispatchEventTraceCorresponds.nil,
          hStates⟩
  | @cons
      before
      middle
      after
      frame
      remainingFrames
      event
      remainingEvents
      hHead
      hTail
      inductionHypothesis =>
      rcases
        _root_.Relico.Correctness.GlobalMultiStorePayloadActorDispatchCorrespondence.synchronizedActorPriorityDispatch_backward
          hHead
          hStates with
        ⟨selectedMessage,
          selectedServer,
          sourceMiddle,
          hReaction,
          hSourceHead,
          hPending,
          hMiddleStates⟩

      rcases inductionHypothesis hMiddleStates with
        ⟨sourceRemainingEvents,
          sourceAfter,
          hSourceTail,
          hTraceTail,
          hAfterStates⟩

      let sourceEvent : SourceActorDispatchEvent := {
        selectedMessage := selectedMessage
        selectedServer := selectedServer
      }

      have hSourceHead' :
          _root_.Relico.DTR.GlobalMultiStorePayloadActorPriority.ActorPriorityDispatchStep
            request
            frame.ready
            sourceModel
            frame.actorName
            sourceBefore
            sourceEvent.selectedMessage
            sourceEvent.selectedServer
            sourceMiddle := by
        simpa [sourceEvent] using hSourceHead

      have hEventCorresponds :
          ActorDispatchEventCorresponds
            sourceEvent
            event := by
        exact {
          selectedReaction_eq := by
            simpa [sourceEvent] using hReaction
          pending := by
            simpa [sourceEvent] using hPending
        }

      refine
        ⟨sourceEvent :: sourceRemainingEvents,
          sourceAfter,
          ?_,
          ?_,
          hAfterStates⟩

      · exact
          SourceActorPriorityDispatchSteps.cons
            hSourceHead'
            hSourceTail

      · exact
          ActorDispatchEventTraceCorresponds.cons
            hEventCorresponds
            hTraceTail

theorem actorDispatchEventTraceCorresponds_length_eq
    {sourceEvents : List SourceActorDispatchEvent}
    {targetEvents : List TargetActorDispatchEvent}
    (hTrace :
      ActorDispatchEventTraceCorresponds
        sourceEvents
        targetEvents) :
    sourceEvents.length = targetEvents.length := by
  induction hTrace with
  | nil =>
      rfl
  | cons head tail inductionHypothesis =>
      simpa only [List.length_cons] using
        congrArg Nat.succ inductionHypothesis

example
    (request : SourceRequest)
    (sourceModel : SourceModel)
    (state : SourceState) :
    SourceActorPriorityDispatchSteps
      request
      sourceModel
      state
      []
      []
      state :=
  SourceActorPriorityDispatchSteps.nil state

example
    (request : SourceRequest)
    (targetProgram : TargetProgram)
    (state : TargetState) :
    TargetActorOrderDispatchSteps
      request
      targetProgram
      state
      []
      []
      state :=
  TargetActorOrderDispatchSteps.nil state



end Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution
