import Relico.DTR.GeneralSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
# The canonical initial runtime state of the general family

Row 11's acquired obligation, source half (**F75** part 2). Every earlier family in this repository has
an initializer — `Relico/DTR/Initialization.lean`, `DTR/StoreInitialization.lean`,
`DTR/MultiStoreInitialization.lean` and `DTR/GlobalMultiStorePayloadInitialization.lean`, each mirrored
under `Relico/LF/` — and the general family had none, which is why `generalCorrespondence_initial` landed
scoped rather than unconditional. This module is the source half of the repair;
`Relico/LF/GeneralInitialization.lean` is the target half; `Relico/Correctness/GeneralCorrespondence.lean`
states the unconditional theorem over both.

## What "initial" means here, and why it is constructor entry

The corpus-wide convention is visible in `DTR.MultiStoreModel.initialState`: a run begins at logical time
zero, with the declaration-derived store, an empty message bag, and **the constructor body installed as
the active body**. The constructor is not executed before the run starts; it is the first thing the run
does. `DTR.GeneralStep.take` confirms the choice is forced rather than stylistic: its `hServer` premise
reaches the server through `DTR.GeneralModel.messageServerFor?`, which resolves only through a message
name, so no step rule can ever install a constructor body. An initializer that attached empty
continuations instead — the shape `GeneralRuntimeConfiguration.ofConfiguration` builds — would produce a
state from which no actor could ever begin: every actor idle, every bag empty, and the clock unable to
advance because `timeProgress` needs a pending future arrival. That state is dead, and a dead state is
not "initial" in any sense a runnable witness (G5's) can use.

## What the state-variable valuation starts as

`GeneralActorState` has one `Store VarName DTR.GeneralValue` and no second environment, so a parameter
has nowhere to live except the valuation — the `take` rule's `bindParameters` update is the established
mechanism, and its docstring records that the paper's `e_x ∪ v⃗` union is an update of the state
valuation rather than a second store. Constructor arguments are therefore bound into the initial
valuation by the same function, over the class's constructor parameters and the instance's arguments.
`DTR.argumentsMatchParameters` (driven by the model's `argumentsMatchConstructor` well-formedness
clause) is what makes the binding total for accepted models; the initializer itself is defined without
it, because a mismatched pair simply binds the shorter prefix, exactly as `bindParameters` does for a
message payload.

The state-variable defaults come from `DTR.GeneralType.initialValue` over the class's declaration list,
in declaration order, following `DTR.initialStore`'s shape in the earlier families.
-/

/--
The idle default used when an instance's class cannot be resolved.

Not `Inhabited.default` on the whole runtime: spelling the witness makes the unresolved branch of
`GeneralModel.initialState` a named, greppable shape rather than an orphaned `default`, and
`initialState` is the only consumer.
-/
def GeneralActorRuntime.idleDefault :
    DTR.GeneralActorRuntime :=
  {
    state :=
      {
        valuation := []
        bag := []
      }
    activeBody := []
    frames := []
  }

namespace GeneralModel

/--
The initial valuation of one actor: state-variable defaults, then the constructor's parameters bound to
the instance's arguments.

Defaults first and parameters second, so a parameter shadows a state variable of the same name by
overwriting its binding — the same precedence `bindParameters` gives a message-server parameter at
`take` time, and `Store.update`'s replace-first-binding semantics is what keeps the shadowed default
from being observable.
-/
def initialValuation
    (reactiveClass : DTR.GeneralReactiveClass)
    (actor : DTR.GeneralActorInstance) :
    DTR.GeneralValuation :=
  bindParameters
    reactiveClass.constructor.parameters
    actor.arguments
    (reactiveClass.stateVariables.map
      (fun declaration =>
        (
          declaration.name,
          DTR.GeneralType.initialValue
            declaration.declaredType
        )))

/--
One actor's initial runtime state: the initial valuation, an empty bag, and the constructor body as the
continuation.

The frame stack starts empty. The constructor body is a top-level body, so nothing encloses it, and an
initial state in which an actor already owed a pending continuation would be describing a run that had
already begun.
-/
def initialActorRuntime
    (reactiveClass : DTR.GeneralReactiveClass)
    (actor : DTR.GeneralActorInstance) :
    DTR.GeneralActorRuntime :=
  {
    state :=
      {
        valuation :=
          initialValuation
            reactiveClass
            actor
        bag := []
      }
    activeBody :=
      reactiveClass.constructor.body
    frames := []
  }

/--
The canonical initial runtime configuration of a model: logical time zero, one runtime state per
instance, in the model's instance order.

`model.classOfActor?` is the resolution from instance to class, and it succeeds for every instance of a
well-formed model: the `argumentsMatchConstructor` clause returns `false` when the class is missing, so
acceptance excludes the unresolved branch. A missing class here produces an idle actor with an empty
valuation rather than a crash, which keeps the initializer a function; the correspondence theorem
quantifies over successfully compiled programs, so an unresolved class cannot reach it unnoticed.
-/
def initialState
    (model : DTR.GeneralModel) :
    DTR.GeneralRuntimeConfiguration :=
  {
    now := 0
    actors :=
      model.instances.map
        (fun actor =>
          (
            actor.name,
            match model.classOfActor? actor.name with

            | none =>
              DTR.GeneralActorRuntime.idleDefault

            | some reactiveClass =>
              initialActorRuntime
                reactiveClass
                actor
          ))
  }

/-!
## Field lemmas

One per field an argument about the initial state reads, following `DTR.MultiStoreModel`'s
`initialState_currentTime` / `initialState_stateStore` / `initialState_pendingMessages` /
`initialState_activeBody` set. The general family's per-instance store cannot be pinned by an equation
per field, so the per-actor facts are stated through `Store.lookup`, which is the interface both the
step relations and the correspondence relation read stores through.
-/

@[simp]
theorem initialState_now
    (model : DTR.GeneralModel) :
    (initialState model).now =
      0 := by
  rfl

private theorem lookup_initialActorsOf
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance)
    (reactiveClass : DTR.GeneralReactiveClass)
    (hResolution :
      model.classOfActor? actor.name =
        some reactiveClass) :
    ∀ (instances : List DTR.GeneralActorInstance),
      DTR.findActor?
          instances
          actor.name =
        some actor →
      Store.lookup
          (instances.map
            (fun instanceDecl =>
              (
                instanceDecl.name,
                match model.classOfActor? instanceDecl.name with

                | none =>
                  DTR.GeneralActorRuntime.idleDefault

                | some class' =>
                  initialActorRuntime
                    class'
                    instanceDecl
              )))
          actor.name =
        some
          (initialActorRuntime
            reactiveClass
            actor) := by

  intro instances
  induction instances with

  | nil =>
      intro hActor

      simp [
        DTR.findActor?
      ] at hActor

  | cons head remaining inductionHypothesis =>
      intro hActor

      by_cases hHead :
          head.name = actor.name

      · rw [
          DTR.findActor?,
          if_pos hHead
        ] at hActor

        injection hActor with hEq

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
          DTR.findActor?,
          if_neg hHead
        ] at hActor

        simp only [
          List.map_cons
        ]

        rw [
          Store.lookup,
          if_neg hHead
        ]

        exact
          inductionHypothesis
            hActor

/--
Lookup into the initial actor store agrees with instance-then-class resolution.

The same shape as `lookup_topology`, proved the same way: an induction over the instance list with a
decidable-equality case split. Stated through a successful resolution rather than an `Option.map`, so
a caller holds the class and the instance as terms rather than recovering them from a `some`; the
correspondence proof is the consumer, and it needs both to name the constructor body and the arguments.
-/
theorem initialState_lookup
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance)
    (reactiveClass : DTR.GeneralReactiveClass)
    (hActor :
      model.actor? actor.name =
        some actor)
    (hClass :
      model.class? actor.className =
        some reactiveClass) :
    Store.lookup
        (initialState model).actors
        actor.name =
      some
        (initialActorRuntime
          reactiveClass
          actor) := by

  unfold initialState

  exact
    lookup_initialActorsOf
      model
      actor
      reactiveClass
      (by
        simp [
          GeneralModel.classOfActor?,
          hActor,
          hClass
        ])
      model.instances
      (by
        simpa [
          GeneralModel.actor?
        ] using
          hActor)

@[simp]
theorem initialActorRuntime_bag
    (reactiveClass : DTR.GeneralReactiveClass)
    (actor : DTR.GeneralActorInstance) :
    (initialActorRuntime
        reactiveClass
        actor).state.bag =
      [] := by
  rfl

@[simp]
theorem initialActorRuntime_activeBody
    (reactiveClass : DTR.GeneralReactiveClass)
    (actor : DTR.GeneralActorInstance) :
    (initialActorRuntime
        reactiveClass
        actor).activeBody =
      reactiveClass.constructor.body := by
  rfl

@[simp]
theorem initialActorRuntime_valuation
    (reactiveClass : DTR.GeneralReactiveClass)
    (actor : DTR.GeneralActorInstance) :
    (initialActorRuntime
        reactiveClass
        actor).state.valuation =
      initialValuation
        reactiveClass
        actor := by
  rfl

end GeneralModel

end DTR
end Relico
