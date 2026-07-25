import Relico.LF.MultiStoreWellFormed
import Relico.LF.StoreModelWellFormed

set_option autoImplicit false

namespace Relico
namespace LF
namespace MultiStoreReactor

/--
Structural validity of a generated finite-store LF reactor with
multiple logical actions and message reactions.
-/
structure WellFormed
    (reactor : LF.MultiStoreReactor) :
    Prop where

  reactorNameValid :
    ReactorName.isValid
      reactor.name

  stateVariableNamesValid :
    ∀ declaration,
      declaration ∈
        reactor.stateVariables →
      VarName.isValid
        declaration.name

  stateVariableNamesUnique :
    (LF.stateVariableNames
      reactor.stateVariables).Nodup

  logicalActionsNonempty :
    reactor.logicalActions ≠
      []

  logicalActionNamesValid :
    ∀ logicalAction,
      logicalAction ∈
        reactor.logicalActions →
      ActionName.isValid
        logicalAction

  logicalActionNamesUnique :
    reactor.logicalActions.Nodup

  startupReactionNameValid :
    ReactionName.isValid
      reactor.startupReaction.name

  startupTriggerCorrect :
    reactor.startupReaction.trigger =
      LF.Trigger.startup

  startupBodyWellFormed :
    LF.Body.MultiStoreWellFormed
      (LF.stateVariableNames
        reactor.stateVariables)
      reactor.logicalActions
      reactor.startupReaction.body

  messageReactionNamesValid :
    ∀ reaction,
      reaction ∈
        reactor.messageReactions →
      ReactionName.isValid
        reaction.name

  messageReactionNamesUnique :
    (LF.reactionNames
      reactor.messageReactions).Nodup

  messageReactionTriggersCorrect :
    LF.reactionTriggers
        reactor.messageReactions =
      reactor.logicalActions.map
        LF.Trigger.logicalAction

  messageReactionBodiesWellFormed :
    ∀ reaction,
      reaction ∈
        reactor.messageReactions →
      LF.Body.MultiStoreWellFormed
        (LF.stateVariableNames
          reactor.stateVariables)
        reactor.logicalActions
        reaction.body

end MultiStoreReactor

namespace MultiStoreProgram

structure WellFormed
    (program : LF.MultiStoreProgram) :
    Prop where

  reactorWellFormed :
    LF.MultiStoreReactor.WellFormed
      program.reactor

  instanceNameValid :
    ActorName.isValid
      program.reactorInstance.name

  instanceReactorMatches :
    program.reactorInstance.reactorName =
      program.reactor.name

end MultiStoreProgram

namespace StoreProgram

/--
Every well-formed one-reaction finite-store program embeds as a
well-formed multi-reaction program.
-/
theorem wellFormed_toMultiStoreProgram
    {program : LF.StoreProgram}
    (hProgram :
      LF.StoreProgram.WellFormed
        program) :
    LF.MultiStoreProgram.WellFormed
      (LF.StoreProgram.toMultiStoreProgram
        program) := by

  refine {
    reactorWellFormed := ?_

    instanceNameValid :=
      hProgram.instanceNameValid

    instanceReactorMatches :=
      hProgram.instanceReactorMatches
  }

  refine {
    reactorNameValid :=
      hProgram.reactorWellFormed.reactorNameValid

    stateVariableNamesValid :=
      hProgram.reactorWellFormed.stateVariableNamesValid

    stateVariableNamesUnique :=
      hProgram.reactorWellFormed.stateVariableNamesUnique

    logicalActionsNonempty := ?_

    logicalActionNamesValid := ?_

    logicalActionNamesUnique := ?_

    startupReactionNameValid :=
      hProgram.reactorWellFormed.startupReactionNameValid

    startupTriggerCorrect :=
      hProgram.reactorWellFormed.startupTriggerCorrect

    startupBodyWellFormed := ?_

    messageReactionNamesValid := ?_

    messageReactionNamesUnique := ?_

    messageReactionTriggersCorrect := ?_

    messageReactionBodiesWellFormed := ?_
  }

  · simp [
      LF.StoreProgram.toMultiStoreProgram
    ]

  · intro logicalAction hMember

    simp [
      LF.StoreProgram.toMultiStoreProgram
    ] at hMember

    subst logicalAction

    exact
      hProgram.reactorWellFormed.actionNameValid

  · simp [
      LF.StoreProgram.toMultiStoreProgram
    ]

  · simpa [
      LF.StoreProgram.toMultiStoreProgram,
      LF.Body.multiStoreWellFormed_singleton_iff
    ] using
      hProgram.reactorWellFormed.startupBodyWellFormed

  · intro reaction hMember

    simp [
      LF.StoreProgram.toMultiStoreProgram
    ] at hMember

    subst reaction

    exact
      hProgram.reactorWellFormed.messageReactionNameValid

  · simp [
      LF.StoreProgram.toMultiStoreProgram,
      LF.reactionNames
    ]

  · simpa [
      LF.reactionTriggers,
      LF.StoreProgram.toMultiStoreProgram
    ] using
      hProgram.reactorWellFormed.messageTriggerCorrect

  · intro reaction hMember

    simp [
      LF.StoreProgram.toMultiStoreProgram
    ] at hMember

    subst reaction

    simpa [
      LF.StoreProgram.toMultiStoreProgram,
      LF.Body.multiStoreWellFormed_singleton_iff
    ] using
      hProgram.reactorWellFormed.messageBodyWellFormed

end StoreProgram
end LF
end Relico
