import Relico.DTR.GeneralInitialization
import Relico.LF.GeneralSemantics
import Relico.Translation.GeneralBasic

set_option autoImplicit false

namespace Relico
namespace LF

/-!
# The canonical initial runtime state of the general family, target half

Row 11's acquired obligation, target half (**F75** part 2); `Relico/DTR/GeneralInitialization.lean` is
the source half and records why "initial" means constructor entry rather than a continuation-free lift.
This module builds the initial `LF.GeneralRuntimeState` of a **successfully compiled** program, and it
imports the translation because the initial target state is not a function of the LF program alone: the
per-reactor runtime state needs the source instance's constructor arguments, and those live on
`DTR.GeneralActorInstance`.

## Why the target initializer is indexed by the model as well as the program

The compiled program names its reactors after classes (`Translation.reactorNameFor`), and its reactorInstance
list keeps the source's actor names (`Translation.compileGeneralActorInstance`), so an actor-to-reactor
correspondence is derivable from the program. But constructor arguments cross to the target in two
places with two different jobs: as **reactor parameters** — `assembleGeneralReactor_parameters`, read by
nothing at run time in this model — and as the instance's `arguments`. `LF.GeneralStep.fire` binds
reaction parameters into the valuation only when an event carries a payload, and `startup` events are
never queued (`LF.GeneralEventKind` has no `startup` constructor, by the docstring's own argument), so
the LF semantics offers no run-time mechanism that hands a startup reaction its parameters. Binding the
compiled arguments into the initial valuation here — `LF.bindReactionParameters` over the compiled
parameter names — is therefore the target-side mirror of the source's `bindParameters`, not a second
copy of information the program already executes. `LF.startupLFMultiStorePayloadState`'s ancestor made
the same choice in a family without constructor parameters at all.

## Time and tag

`currentTag` starts at `⟨0, 0⟩`, following `LF.initialTag` and
`LF.GlobalMultiStorePayloadInitialization.globalStartupTag`. The queue starts empty: nothing is
scheduled before any reaction has run, which is also why the correspondence's `pendingTargeted` field
holds trivially here.
-/

namespace GeneralProgram

/--
The initial tag of a run: logical time zero, microstep zero.

`rfl`-equal to `LF.initialTag`; declared locally because the general family's runtime modules do not
import `Relico/LF/Initialization.lean`, and reaching across families for one structure literal would
couple this module to the singleton family's module for no content.
-/
def generalInitialTag :
    LF.Tag :=
  {
    time := 0
    microstep := 0
  }

end GeneralProgram

/--
The idle default used when an instance's reactor cannot be resolved.

The mirror of `DTR.GeneralActorRuntime.idleDefault`: on a compiled, well-formed program every
instance resolves through the `instancesResolve` clause, so the branch is unreachable for accepted
programs, and naming the witness keeps it greppable rather than an orphaned `default`.
-/
def GeneralReactorRuntime.idleDefault :
    LF.GeneralReactorRuntime :=
  {
    valuation := []
    activeBody := []
    frames := []
  }

namespace GeneralProgram

/--
One reactor instance's initial runtime state: state-variable defaults from the compiled reactor's own
declaration list, the instance's compiled constructor arguments bound over the reactor's parameter
names, an empty continuation of its own — and the **compiled startup reaction's body** as the active
body.

`bindReactionParameters` is the same function `LF.GeneralStep.fire` uses to bind a reaction's
parameters, so the initial valuation of a reactor with parameters is indistinguishable from one whose
startup reaction had fired with the instance arguments as payload. That is the correspondence the
source side's `bindParameters` sets up, and using one function on both sides is what keeps it a lemma
rather than a coincidence.
-/
def initialReactorRuntime
    (reactor : LF.GeneralReactor)
    (reactorInstance : LF.GeneralReactorInstance) :
    LF.GeneralReactorRuntime :=
  {
    valuation :=
      LF.bindReactionParameters
        reactor.startupReaction.parameters
        reactorInstance.arguments
        (reactor.stateVariables.map
          (fun declaration =>
            (
              declaration.name,
              LF.GeneralType.initialValue
                declaration.declaredType
            )))
    activeBody :=
      reactor.startupReaction.body
    frames := []
  }

/--
The canonical initial runtime state of a compiled program: tag `⟨0, 0⟩`, one reactor runtime per
instance in instance order, and an empty event queue.

Resolution goes through the program's own instance list — `LF.GeneralReactorInstance.name` is the
source's `ActorName`, which is what lets the correspondence key both sides by one name — and through
`reactor?` for the reactor. Both succeed for every instance of a well-formed program
(`instancesResolve`), so the idle branch exists to keep the initializer total, not to be taken.
-/
def initialState
    (program : LF.GeneralProgram) :
    LF.GeneralRuntimeState :=
  {
    currentTag :=
      generalInitialTag
    reactors :=
      program.instances.map
        (fun reactorInstance =>
          (
            reactorInstance.name,
            match program.reactorOfInstance? reactorInstance.name with

            | none =>
              LF.GeneralReactorRuntime.idleDefault

            | some reactor =>
              initialReactorRuntime
                reactor
                reactorInstance
          ))
    pending := []
  }

/-!
## Field lemmas

The same shape as the source side's: time, tag components, pending queue, and a lookup lemma stated
through successful resolution. `reactorOfInstance?` composes `instance?` with `reactor?`, so the
hypotheses of the lookup lemma are the two resolutions, and the proof mirrors
`DTR.GeneralModel.initialState_lookup`'s induction-and-case-split.
-/

@[simp]
theorem initialState_currentTag
    (program : LF.GeneralProgram) :
    (initialState program).currentTag =
      generalInitialTag := by
  rfl

@[simp]
theorem initialState_currentTime
    (program : LF.GeneralProgram) :
    (initialState program).currentTag.time =
      0 := by
  rfl

@[simp]
theorem initialState_microstep
    (program : LF.GeneralProgram) :
    (initialState program).currentTag.microstep =
      0 := by
  rfl

@[simp]
theorem initialState_pending
    (program : LF.GeneralProgram) :
    (initialState program).pending =
      [] := by
  rfl

private theorem lookup_initialReactorsOf
    (program : LF.GeneralProgram)
    (reactorInstance : LF.GeneralReactorInstance)
    (reactor : LF.GeneralReactor)
    (hResolution :
      program.reactorOfInstance? reactorInstance.name =
        some reactor) :
    ∀ (instances : List LF.GeneralReactorInstance),
      LF.findInstance?
          instances
          reactorInstance.name =
        some reactorInstance →
      Store.lookup
          (instances.map
            (fun instanceDecl =>
              (
                instanceDecl.name,
                match program.reactorOfInstance? instanceDecl.name with

                | none =>
                  LF.GeneralReactorRuntime.idleDefault

                | some reactor' =>
                  initialReactorRuntime
                    reactor'
                    instanceDecl
              )))
          reactorInstance.name =
        some
          (initialReactorRuntime
            reactor
            reactorInstance) := by

  intro instances
  induction instances with

  | nil =>
      intro hInstance

      simp [
        LF.findInstance?
      ] at hInstance

  | cons head remaining inductionHypothesis =>
      intro hInstance

      by_cases hHead :
          head.name = reactorInstance.name

      · rw [
          LF.findInstance?,
          if_pos hHead
        ] at hInstance

        injection hInstance with hEq

        subst hEq

        simp only [
          List.map_cons
        ]

        rw [
          Store.lookup,
          if_pos hHead,
          hResolution
        ]

      · rw [
          LF.findInstance?,
          if_neg hHead
        ] at hInstance

        simp only [
          List.map_cons
        ]

        rw [
          Store.lookup,
          if_neg hHead
        ]

        exact
          inductionHypothesis
            hInstance

/--
Lookup into the initial reactor store agrees with instance-then-reactor resolution.

The target mirror of `DTR.GeneralModel.initialState_lookup`, with the same shape and the same proof.
The hypothesis is stated through `reactorOfInstance?` rather than through `reactorName`, because that
is the composition `initialState` itself consults and re-deriving it from the instance's reactor name
would be a second definition of one resolution.
-/
theorem initialState_lookup
    (program : LF.GeneralProgram)
    (reactorInstance : LF.GeneralReactorInstance)
    (reactor : LF.GeneralReactor)
    (hInstance :
      program.instance? reactorInstance.name =
        some reactorInstance)
    (hReactor :
      program.reactor?
        reactorInstance.reactorName =
        some reactor) :
    Store.lookup
        (initialState program).reactors
        reactorInstance.name =
      some
        (initialReactorRuntime
          reactor
          reactorInstance) := by

  have hFindInstance :
      LF.findInstance?
          program.instances
          reactorInstance.name =
        some reactorInstance :=
    hInstance

  have hResolution :
      program.reactorOfInstance?
          reactorInstance.name =
        some reactor := by
    simp [
      GeneralProgram.reactorOfInstance?,
      hInstance,
      hReactor
    ]

  unfold initialState

  exact
    lookup_initialReactorsOf
      program
      reactorInstance
      reactor
      hResolution
      program.instances
      hFindInstance

end GeneralProgram

end LF
end Relico
