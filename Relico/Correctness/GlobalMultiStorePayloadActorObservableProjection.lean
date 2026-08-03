import Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution

set_option autoImplicit false

namespace Relico.Correctness.GlobalMultiStorePayloadActorObservableProjection

abbrev ActorDispatchFrame :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.ActorDispatchFrame

abbrev SourceRequest :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.SourceRequest

abbrev SourceModel :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.SourceModel

abbrev TargetProgram :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.TargetProgram

abbrev SourceState :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.SourceState

abbrev TargetState :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.TargetState

abbrev SourceActorDispatchEvent :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.SourceActorDispatchEvent

abbrev TargetActorDispatchEvent :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.TargetActorDispatchEvent

abbrev ActorDispatchEventTraceCorresponds :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.ActorDispatchEventTraceCorresponds

abbrev SourceActorPriorityDispatchSteps :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.SourceActorPriorityDispatchSteps

abbrev TargetActorOrderDispatchSteps :=
  _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.TargetActorOrderDispatchSteps

def actorDispatchFrameTrace
    (frames : List ActorDispatchFrame) :
    List _root_.Relico.ActorName :=
  frames.map
    _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.ActorDispatchFrame.actorName

def sourceActorDispatchObservableTrace
    (frames : List ActorDispatchFrame) :
    List _root_.Relico.ActorName :=
  actorDispatchFrameTrace frames

def targetActorDispatchObservableTrace
    (frames : List ActorDispatchFrame) :
    List _root_.Relico.ActorName :=
  actorDispatchFrameTrace frames

theorem actorDispatchObservableTrace_eq
    (frames : List ActorDispatchFrame) :
    sourceActorDispatchObservableTrace frames =
      targetActorDispatchObservableTrace frames := by
  rfl

theorem sourceActorPriorityDispatchSteps_actorTrace
    {request : SourceRequest}
    {sourceModel : SourceModel}
    {sourceBefore sourceAfter : SourceState}
    {frames : List ActorDispatchFrame}
    {sourceEvents : List SourceActorDispatchEvent}
    (_hSteps :
      SourceActorPriorityDispatchSteps
        request
        sourceModel
        sourceBefore
        frames
        sourceEvents
        sourceAfter) :
    sourceActorDispatchObservableTrace frames =
      actorDispatchFrameTrace frames := by
  rfl

theorem targetActorOrderDispatchSteps_actorTrace
    {request : SourceRequest}
    {targetProgram : TargetProgram}
    {targetBefore targetAfter : TargetState}
    {frames : List ActorDispatchFrame}
    {targetEvents : List TargetActorDispatchEvent}
    (_hSteps :
      TargetActorOrderDispatchSteps
        request
        targetProgram
        targetBefore
        frames
        targetEvents
        targetAfter) :
    targetActorDispatchObservableTrace frames =
      actorDispatchFrameTrace frames := by
  rfl

theorem sourceActorPriorityDispatchObservable_forward
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
        sourceActorDispatchObservableTrace frames =
          targetActorDispatchObservableTrace frames ∧
        ActorDispatchEventTraceCorresponds
          sourceEvents
          targetEvents ∧
        _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by
  rcases
    _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.sourceActorPriorityDispatchSteps_forward
      hSteps
      hStates with
    ⟨targetEvents,
      targetAfter,
      hTargetSteps,
      hEventTrace,
      hFinalStates⟩

  exact
    ⟨targetEvents,
      targetAfter,
      hTargetSteps,
      actorDispatchObservableTrace_eq frames,
      hEventTrace,
      hFinalStates⟩

theorem targetActorOrderDispatchObservable_backward
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
        sourceActorDispatchObservableTrace frames =
          targetActorDispatchObservableTrace frames ∧
        ActorDispatchEventTraceCorresponds
          sourceEvents
          targetEvents ∧
        _root_.Relico.Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by
  rcases
    _root_.Relico.Correctness.GlobalMultiStorePayloadActorFiniteExecution.targetActorOrderDispatchSteps_backward
      hSteps
      hStates with
    ⟨sourceEvents,
      sourceAfter,
      hSourceSteps,
      hEventTrace,
      hFinalStates⟩

  exact
    ⟨sourceEvents,
      sourceAfter,
      hSourceSteps,
      actorDispatchObservableTrace_eq frames,
      hEventTrace,
      hFinalStates⟩



end Relico.Correctness.GlobalMultiStorePayloadActorObservableProjection
