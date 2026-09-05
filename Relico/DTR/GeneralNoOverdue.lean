/-
! # The source-side no-overdue invariant

The first of the three mechanical invariants the block-transfer audit identified as missing
(2026-08-30): **no message sits in a bag at an arrival the clock has already passed**. The
take-time alignment the forward core lemma premised as `hEventTime` — every message the source
actually takes arrives at exactly `config.now` — is a corollary of this invariant, because the
`take` rule ties the taken message to the selection's `logicalTime`, the selection only ever
answers with an arrival at or before `now` (dueness), and the invariant supplies the other
inequality for free.

Why the invariant is true is a fact about the two clock rules rather than a new constraint:

* `send` appends at `LogicalTime.after config.now delay`, and `LogicalTime.le_after` makes that
  at-or-after `now` for every delay, zero included — the zero-delay case is exactly the
  same-instant generation the instant-block design relies on.
* `timeProgress` refuses to jump (**F74**): `hSelected` pins the destination to
  `nextArrival`, the *minimum* future arrival, so nothing is passed. An arbitrary-jump clock
  would falsify this invariant on its first step, and the rule's own docstring records that
  refusal as deliberate.

The invariant is stated over **members**, in the store-membership shape the correspondence
relation already uses, and proves nothing about key multiplicity — the shadowed-binding
discipline is store-key uniqueness's question, not this one's.

What lives here: the predicate, the initializer theorem (every initial bag is empty), one
step-preservation theorem covering all five `GeneralStep` constructors, and the take-time
corollary. Consumers that need it to survive a weak execution compose from the step theorem;
the raw step is the level every later wrapper already inverts.
-/
import Relico.DTR.GeneralInitialization
import Relico.DTR.GeneralActorSelection

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
### Private store helpers

Two small facts this module needs once each. `Relico/Common/Store.lean`'s public API is
lookup-shaped by design, and the membership lemmas the forward core lemma uses live `private`
in `Relico/Correctness/GeneralWeakBisimulation.lean` — unreachable from here and not worth
moving for one consumer. The house rule applies: duplicate the small lemma rather than widen
an interface for it. (`DTR.mem_eraseContinuations` already exists publicly and is reused, not
restated.)
-/

/--
An update at the head key replaces the head binding.
-/
private theorem update_cons_eq'
    {Key Value : Type}
    [DecidableEq Key]
    (candidate : Key)
    (currentValue : Value)
    (remaining : Store Key Value)
    (key : Key)
    (newValue : Value)
    (hCandidate :
      candidate = key) :
    Store.update
        ((candidate, currentValue) :: remaining)
        key
        newValue =
      (key, newValue) :: remaining := by
  simp [
    Store.update,
    hCandidate
  ]

/--
An update at another key keeps the head binding and recurses.
-/
private theorem update_cons_ne'
    {Key Value : Type}
    [DecidableEq Key]
    (candidate : Key)
    (currentValue : Value)
    (remaining : Store Key Value)
    (key : Key)
    (newValue : Value)
    (hCandidate :
      candidate ≠ key) :
    Store.update
        ((candidate, currentValue) :: remaining)
        key
        newValue =
      (candidate, currentValue) ::
        Store.update
          remaining
          key
          newValue := by
  simp [
    Store.update,
    hCandidate
  ]

/--
Every entry of an updated store is either the new binding or an old entry.
-/
private theorem mem_update_cases
    {Key Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {newValue : Value}
    {entry : Key × Value}
    (hMem :
      entry ∈
        Store.update
          store
          key
          newValue) :
    entry = (key, newValue) ∨
      entry ∈ store := by
  induction store with

  | nil =>
      rcases
          List.mem_cons.mp hMem with
        hEq | hImpossible
      · exact Or.inl hEq
      · cases hImpossible

  | cons head tail IH =>
      rcases head with ⟨candidate, currentValue⟩

      by_cases hCandidate :
        candidate = key

      · rw [
          update_cons_eq'
            candidate
            currentValue
            tail
            key
            newValue
            hCandidate
        ] at hMem

        rcases
            List.mem_cons.mp hMem with
          hEq | hIn
        · exact Or.inl hEq
        · exact
            Or.inr
              (List.mem_cons.mpr
                (Or.inr hIn))

      · rw [
          update_cons_ne'
            candidate
            currentValue
            tail
            key
            newValue
            hCandidate
        ] at hMem

        rcases
            List.mem_cons.mp hMem with
          hEq | hIn
        · exact
            Or.inr
              (List.mem_cons.mpr
                (Or.inl hEq))
        · rcases IH hIn with
            hNew | hOld
          · exact Or.inl hNew
          · exact
              Or.inr
                (List.mem_cons.mpr
                  (Or.inr hOld))

/--
The no-overdue invariant: no message in any bag arrives before the clock.

Membership-shaped, like the correspondence's own store fields, and deliberately silent about
key multiplicity. This is the invariant `take`'s alignment corollary consumes, and the one the
instant-block source predicate's interior (`message.arrival = t`) rests on for reachable
configurations.
-/
def GeneralNoOverdue
    (config : GeneralRuntimeConfiguration) :
    Prop :=
  ∀ entry ∈ config.actors,
    ∀ message ∈ entry.2.state.bag,
      config.now ≤ message.arrival

/--
Every initial configuration is no-overdue: every initial bag is empty, so there is nothing to
be overdue.

Both branches of the initializer's per-instance construction — the resolved class's
`initialActorRuntime` (empty bag by `initialActorRuntime_bag`) and the unresolved class's
`idleDefault` (empty bag by its own literal) — contribute an empty bag, and the invariant is
vacuous over empty bags whatever the clock says.
-/
theorem generalNoOverdue_initial
    (model : DTR.GeneralModel) :
    GeneralNoOverdue
      (DTR.GeneralModel.initialState model) := by
  intro entry hMem message hMessage

  obtain ⟨name, runtime⟩ :=
    entry

  obtain ⟨inst, _, hEntryEq⟩ :=
    List.mem_map.mp hMem

  obtain ⟨nameEq, runtimeEq⟩ :=
    Prod.mk.inj hEntryEq

  subst nameEq

  subst runtimeEq

  cases
    hClass :
      model.classOfActor? inst.name with

  | none =>
      rw [hClass] at hMessage

      cases hMessage

  | some reactiveClass =>
      rw [
        hClass,
        GeneralModel.initialActorRuntime_bag
          reactiveClass
          inst
      ] at hMessage

      cases hMessage

/--
The no-overdue invariant survives every source step.

Case by case: the τ rules that rewrite one actor rebuild it with the same bag (`assign`
rebinds a valuation, `trace` consumes a statement, `send`'s sender half consumes a statement),
so the membership transport is the store-update split plus the old fact, with the actor
recovered from the rule's own lookup premise; `send`'s receiver half appends one message at
`LogicalTime.after config.now delay`, which `le_after` covers for every delay — the zero-delay
same-instant case included; `take` only ever removes an occurrence; and `timeProgress`
advances exactly to `nextArrival` (**F74**), whose minimality (`earliestFutureArrivalOf_minimal`)
keeps the new clock at-or-under every surviving arrival. Quiescence feeds that argument:
`arrival_future_of_readyActors_nil` turns the empty ready cohort into "every bag arrival is
strictly future", read through the public `mem_eraseContinuations` transfer.
-/
theorem generalNoOverdue_of_step
    {model : DTR.GeneralModel}
    {config config' : GeneralRuntimeConfiguration}
    {label : DTR.GeneralLabel}
    (hNoOverdue :
      GeneralNoOverdue config)
    (hStep :
      GeneralStep
        model
        config
        label
        config') :
    GeneralNoOverdue config' := by
  cases hStep with

  | assign hActor hBody hEvaluate =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        exact
          hNoOverdue
            _
            (Store.mem_of_lookup
              config.actors
              _
              _
              hActor)
            message
            hMessage

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  | trace hActor hBody =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        exact
          hNoOverdue
            _
            (Store.mem_of_lookup
              config.actors
              _
              _
              hActor)
            message
            hMessage

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  -- Stage I's local declaration rewrites one actor's valuation and copies its bag unchanged,
  -- so the `assign` proof is this arm's proof: the membership cases do not look at the
  -- valuation.
  | localDecl hActor hBody hEvaluate =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        exact
          hNoOverdue
            _
            (Store.mem_of_lookup
              config.actors
              _
              _
              hActor)
            message
            hMessage

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  -- Stage H's three step-into rules rewrite one actor's continuation fields and copy its
  -- `state` unchanged, so its bag is the bag this invariant was already proved for. The proof
  -- is the `trace` proof, and it is repeated rather than abstracted for the reason the `assign`
  -- and `trace` cases are not shared either: each case names its own rule's premises.
  | branchTrue hActor hBody hCondition =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        exact
          hNoOverdue
            _
            (Store.mem_of_lookup
              config.actors
              _
              _
              hActor)
            message
            hMessage

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  | branchFalse hActor hBody hCondition =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        exact
          hNoOverdue
            _
            (Store.mem_of_lookup
              config.actors
              _
              _
              hActor)
            message
            hMessage

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  | resume hActor hBody hFrames =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        exact
          hNoOverdue
            _
            (Store.mem_of_lookup
              config.actors
              _
              _
              hActor)
            message
            hMessage

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  | send hSender hBody hArguments hTarget hReceiver =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hReceiverNew | hSenderStore
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hReceiverNew

        subst runtimeEq

        rcases
            List.mem_append.mp hMessage with
          hOldMessage | hNewMessage
        · have hReceiverMem :=
            Store.mem_of_lookup
              _
              _
              _
              hReceiver

          rcases
              mem_update_cases
                hReceiverMem with
            hSelfSend | hOldMem
          · obtain ⟨_, receiverEq⟩ :=
              Prod.mk.inj hSelfSend

            subst receiverEq

            exact
              hNoOverdue
                _
                (Store.mem_of_lookup
                  config.actors
                  _
                  _
                  hSender)
                message
                hOldMessage

          · exact
              hNoOverdue
                _
                hOldMem
                message
                hOldMessage

        · obtain rfl :=
            List.mem_singleton.mp hNewMessage

          exact
            LogicalTime.le_after
              config.now
              _

      · rcases
            mem_update_cases
              hSenderStore with
          hSenderNew | hOld
        · obtain ⟨_, runtimeEq⟩ :=
            Prod.mk.inj hSenderNew

          subst runtimeEq

          exact
            hNoOverdue
              _
              (Store.mem_of_lookup
                config.actors
                _
                _
                hSender)
              message
              hMessage

        · exact
            hNoOverdue
              _
              hOld
              message
              hMessage

  | take hSelected hName hActor hIdleActor hDue hArrival hServer =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      rcases
          mem_update_cases
            hMem with
        hNew | hOld
      · obtain ⟨_, runtimeEq⟩ :=
          Prod.mk.inj hNew

        subst runtimeEq

        have hActorMem :=
          Store.mem_of_lookup
            config.actors
            _
            _
            hActor

        exact
          hNoOverdue
            _
            hActorMem
            message
            (by
              rw [hDue]

              rcases
                  List.mem_append.mp
                    hMessage with
                hEarlier | hLater
              · exact
                  List.mem_append.mpr
                    (Or.inl hEarlier)
              · exact
                  List.mem_append.mpr
                    (Or.inr
                      (List.mem_cons.mpr
                        (Or.inr hLater))))

      · exact
          hNoOverdue
            _
            hOld
            message
            hMessage

  | timeProgress hForward hQuiescent hSelected =>
      intro entry hMem message hMessage

      obtain ⟨name, runtime⟩ := entry

      have hEraseMem :
          (name, runtime.state) ∈
            eraseContinuations config.actors :=
        mem_eraseContinuations_of_mem
          config.actors
          name
          runtime
          hMem

      have hFuture :
          config.now < message.arrival :=
        arrival_future_of_readyActors_nil
          config.erase
          name
          runtime.state
          message
          hQuiescent
          hEraseMem
          hMessage

      exact
        earliestFutureArrivalOf_minimal
          (eraseContinuations config.actors)
          config.now
          name
          runtime.state
          message
          hEraseMem
          hMessage
          hFuture
          _
          hSelected

/--
The take-time alignment: a message the source actually takes arrives at exactly `now`.

The three-link chain the forward core lemma's `hEventTime` premise waited for. `hArrival` ties
the taken message to the selection's `logicalTime`; `selectedActor_ne_fabricated` +
`earliestDueArrival_sound` make that `logicalTime` **due** (at-or-before `now`) by exhibiting a
bag message that realizes it; and the no-overdue invariant supplies `now ≤ message.arrival` —
the taken message is in its actor's bag by `hDue`. Dueness and no-overdue close on equality.

This is a corollary **of the invariant**, not a restatement of a rule premise: the rule ties
the message to the selection, and only the invariant ties the selection to the clock.
-/
theorem generalNoOverdue_arrival_of_take
    {model : DTR.GeneralModel}
    {config : GeneralRuntimeConfiguration}
    (hNoOverdue :
      GeneralNoOverdue config)
    {actorName : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {selected :
      GlobalMultiStorePayloadActorPriority.ReadyActor}
    {message : DTR.GeneralMessage}
    {earlier later : DTR.GeneralMessageBag}
    (hSelected :
      GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected)
    (_hName :
      selected.actorName = actorName)
    (hActor :
      Store.lookup
          config.actors
          actorName =
        some actor)
    (hDue :
      actor.state.bag =
        earlier ++ message :: later)
    (hArrival :
      message.arrival = selected.logicalTime) :
    message.arrival = config.now := by
  have hMessageMem :
      message ∈ actor.state.bag := by
    rw [hDue]

    exact
      List.mem_append.mpr
        (Or.inr List.mem_cons_self)

  have hActorMem :=
    Store.mem_of_lookup
      config.actors
      _
      _
      hActor

  have hNotPast :
      config.now ≤ message.arrival :=
    hNoOverdue
      _
      hActorMem
      message
      hMessageMem

  obtain
      ⟨state, _, hDueArrival⟩ :=
    GeneralActorSelection.selectedActor_ne_fabricated
      hSelected

  obtain
      ⟨_, _, _, hDueLe⟩ :=
    earliestDueArrival_sound
      state.bag
      config.erase.now
      selected.logicalTime
      hDueArrival

  have hDue :
      selected.logicalTime ≤ config.now := by
    rw [
      GeneralRuntimeConfiguration.erase_now
    ] at hDueLe

    exact hDueLe

  rw [hArrival]

  exact
    Nat.le_antisymm
      hDue
      (hArrival ▸ hNotPast)

end DTR
end Relico
