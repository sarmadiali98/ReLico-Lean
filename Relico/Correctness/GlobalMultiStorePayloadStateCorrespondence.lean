import Relico.Correctness.MultiStorePayloadRuntimeStateCorrespondence
import Relico.Translation.GlobalMultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise lifting of the published local runtime-state correspondence.

The three ordered stores must have exactly the same actor sequence.
-/
inductive GlobalMultiStorePayloadActorStatesCorrespond :
    DTR.GlobalMultiStorePayloadActors →
    DTR.GlobalMultiStorePayloadActorStates →
    LF.GlobalMultiStorePayloadActorStates →
    Prop

  | nil :
      GlobalMultiStorePayloadActorStatesCorrespond
        []
        []
        []

  | cons
      {actorName :
        ActorName}
      {model :
        DTR.MultiStorePayloadModel}
      {sourceState :
        DTR.MultiStorePayloadState}
      {targetState :
        LF.MultiStorePayloadState}
      {remainingModels :
        DTR.GlobalMultiStorePayloadActors}
      {remainingSourceStates :
        DTR.GlobalMultiStorePayloadActorStates}
      {remainingTargetStates :
        LF.GlobalMultiStorePayloadActorStates}
      (localCorrespondence :
        MultiStorePayloadRuntimeStateCorresponds
          model.reactiveClass.messageServers
          sourceState
          targetState)
      (remaining :
        GlobalMultiStorePayloadActorStatesCorrespond
          remainingModels
          remainingSourceStates
          remainingTargetStates) :
      GlobalMultiStorePayloadActorStatesCorrespond
        (
          (actorName, model) ::
            remainingModels
        )
        (
          (actorName, sourceState) ::
            remainingSourceStates
        )
        (
          (actorName, targetState) ::
            remainingTargetStates
        )

/--
The source and target global programs preserve the same abstract topology.
-/
def GlobalMultiStorePayloadTopologyCorresponds
    (source :
      DTR.GlobalMultiStorePayloadModel)
    (target :
      LF.GlobalMultiStorePayloadProgram) :
    Prop :=
  source.topology =
    target.topology

/--
Structural E2 correspondence.

This packages actor-wise compilation, abstract topology preservation, global
metric-time agreement, and pointwise lifting of the local runtime relation.
-/
structure GlobalMultiStorePayloadRuntimeStateCorresponds
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel)
    (targetProgram :
      LF.GlobalMultiStorePayloadProgram)
    (sourceState :
      DTR.GlobalMultiStorePayloadState)
    (targetState :
      LF.GlobalMultiStorePayloadState) :
    Prop where

  compiledActorPrograms :
    targetProgram.actorPrograms =
      Translation.compileGlobalMultiStorePayloadActors
        sourceModel.actors

  topology :
    GlobalMultiStorePayloadTopologyCorresponds
      sourceModel
      targetProgram

  currentTime :
    sourceState.currentTime =
      targetState.currentTag.time

  actorStates :
    GlobalMultiStorePayloadActorStatesCorrespond
      sourceModel.actors
      sourceState.actorStates
      targetState.actorStates

@[simp]
theorem translateGlobalMultiStorePayloadCore_topologyCorresponds
    (model :
      DTR.GlobalMultiStorePayloadModel) :
    GlobalMultiStorePayloadTopologyCorresponds
      model
      (Translation.translateGlobalMultiStorePayloadCore
        model) := by
  rfl

theorem GlobalMultiStorePayloadActorStatesCorrespond.model_source_keys
    {models :
      DTR.GlobalMultiStorePayloadActors}
    {sourceStates :
      DTR.GlobalMultiStorePayloadActorStates}
    {targetStates :
      LF.GlobalMultiStorePayloadActorStates}
    (hCorrespond :
      GlobalMultiStorePayloadActorStatesCorrespond
        models
        sourceStates
        targetStates) :
    Store.keys models =
      Store.keys sourceStates := by

  induction hCorrespond with

  | nil =>
      rfl

  | cons localCorrespondence remaining inductionHypothesis =>
      rename_i actorName model sourceState targetState
        remainingModels remainingSourceStates remainingTargetStates

      change
        actorName ::
            Store.keys remainingModels =
          actorName ::
            Store.keys remainingSourceStates

      exact
        congrArg
          (List.cons actorName)
          inductionHypothesis

theorem GlobalMultiStorePayloadActorStatesCorrespond.source_target_keys
    {models :
      DTR.GlobalMultiStorePayloadActors}
    {sourceStates :
      DTR.GlobalMultiStorePayloadActorStates}
    {targetStates :
      LF.GlobalMultiStorePayloadActorStates}
    (hCorrespond :
      GlobalMultiStorePayloadActorStatesCorrespond
        models
        sourceStates
        targetStates) :
    Store.keys sourceStates =
      Store.keys targetStates := by

  induction hCorrespond with

  | nil =>
      rfl

  | cons localCorrespondence remaining inductionHypothesis =>
      rename_i actorName model sourceState targetState
        remainingModels remainingSourceStates remainingTargetStates

      change
        actorName ::
            Store.keys remainingSourceStates =
          actorName ::
            Store.keys remainingTargetStates

      exact
        congrArg
          (List.cons actorName)
          inductionHypothesis

end Correctness
end Relico
