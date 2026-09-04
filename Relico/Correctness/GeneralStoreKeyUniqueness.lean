/-
! # Reachable-state store-key uniqueness for the general family

The `hUniqueS` and `hUniqueT` premises of
`Correctness.generalConsume_forward_weak_of_fireRepresentative` say, in the spelling the consume
core reads them, that the store a step selects its actor or reactor from filters to exactly one
entry at that key. This module proves that every **reachable** configuration, on both sides of
the translation, satisfies the invariant those premises presuppose, and packages the two filter
equations in exactly that spelling.

## Why occurrence uniqueness, and why `Store.KeysUnique`

The premise is not lookup uniqueness and cannot be weakened to it. `Store.lookup` observes only
the first binding at a key, so a store carrying a shadowed second binding agrees with the honest
one under every lookup — F74's caveat, and the reason
`Correctness.GeneralStateCorrespondence` quantifies its per-actor components over membership
rather than resolution. A filter equation is strictly stronger: it pins how many entries carry
the key, so `[(k, v)]` filters to `[(k, v)]` while `[(k, v), (k, v)]` filters to both, equal
values notwithstanding.

The invariant is therefore stated as `Store.KeysUnique` — `(keys store).Nodup`, the notion
`Relico/Common/ActorTopology.lean` already defines and `DTR.GeneralModel.namesUniqueAndValid`
already demands of the topology. It is occurrence-exact: `Nodup` on the key list forbids a key
occurring twice whatever the values, which is exactly what the filter equations need and what
neither lookup agreement nor `Nodup` of whole entries gives — two entries at one key with
different values are distinct pairs, so entry-level `Nodup` would admit them. Nothing new is
defined at the Store level except bridges: one lemma taking `KeysUnique` plus a membership to
the filter equation, one taking `KeysUnique` through `Store.update`. The generic section is four
lemmas and no library, and it serves both families because both runtime stores are
`Store ActorName _` and every store-writing rule on either side goes through `Store.update`.

## How the invariant is obtained

Both initializers build their store as one `List.map` keyed by instance names, so initial
uniqueness is instance-name uniqueness — on the source, the `namesUniqueAndValid` clause of a
well-formed model; on the target, the `instanceNamesUnique` clause of a well-formed program,
which the compilation guard has already decided for any successfully compiled program. Every
rule that writes a store goes through `Store.update`, and `update` replaces the first binding
at a key or appends when the key is absent — either way one occurrence in means one occurrence
out — so preservation is one generic lemma applied once per update. The DTR `send` rule writes
twice, sender then receiver; two applications cover it with no distinctness side condition, and
the self-send case needs none because updating one key twice is still, in effect, one update.

Reachability itself had no formalization anywhere — every occurrence of the word in the tree is
docstring prose — so the smallest definition supporting the corollaries is introduced per
family: an inductive with an `initial` case and a `step` case, shaped like `Common.TauSteps`
minus the label filter, and consumed by a one-line induction.

## Why there is no α-transport theorem

`LF.generalStateAlphaEquiv` relates two states by equal tags, reactor-store membership
equivalence, pointwise `Store.lookup` agreement, and a queue permutation. **Neither reactor
clause can see occurrence multiplicity**: a store carrying `(k, r)` twice is
membership-equivalent to, and lookup-agrees with, one carrying it once, so key uniqueness is
not preserved by α and a transport theorem for it would be false rather than merely unproved.
The α definition's own docstring records that no key-uniqueness invariant is assumed or needed
for these runtime stores. α is not strengthened here, and nothing needs it to be.

The representative `hUniqueT` is about is instead to be **constructed with an identical reactor
store and only a reordered pending queue**. That choice is α-admissible — identical stores
satisfy both reactor clauses trivially, and the queue permutation is exactly what α exists to
permit (decision 0042) — and it is the choice the architecture already anticipates: the consume
core takes `hAlignedReactors : aligned.reactors = state.reactors` as a premise, routing
reactor-store facts through equality rather than through α, and the instant-block spine's
`consume` constructor constrains its representative through α alone, leaving the representative's
reactor store to the construction. Under that construction `before.reactors = aligned.reactors =
state.reactors`, so the eventual forward wrapper obtains `hUniqueT` from reachability of
`state` — `LF.generalStoreKeyUnique_of_reachable`, or `LF.generalStoreKeyUnique_of_tauSteps`
when the alignment spine is what is in hand — plus `LF.generalStoreKeyUnique_filter_of_lookup`,
transported along equalities and never across α. The source side needs nothing of the sort:
`hUniqueS` is stated at the take rule's own pre-configuration, so
`DTR.generalStoreKeyUnique_of_reachable` plus `DTR.generalStoreKeyUnique_filter_of_lookup`
discharges it directly.

## What this module does not do

No `.consume` transfer condition is stated or prepared — the forward wrapper still owes the
no-overdue/tag-alignment and kind-origin packages and stands behind the α′ cross-microstep and
F27-tie decisions, all outside this milestone. `Store.update`'s semantics, both runtime state
types, `GeneralStateCorrespondence`, and `generalStateAlphaEquiv` are untouched. No new
well-formedness clause is added on either side: every fact consumed here is a clause both
guards already decide.
-/
import Relico.Common.Store
import Relico.Common.ActorTopology
import Relico.Common.WeakTransition
import Relico.DTR.GeneralSemantics
import Relico.DTR.GeneralInitialization
import Relico.DTR.GeneralWellFormed
import Relico.LF.GeneralSemantics
import Relico.LF.GeneralInitialization
import Relico.LF.GeneralWellFormed

set_option autoImplicit false

namespace Relico

namespace Store

/-!
## Update equations, locally

`update_cons_eq` and `update_cons_ne` exist `private` in
`Relico/Correctness/GeneralWeakBisimulation.lean` and again in
`Relico/DTR/GeneralNoOverdue.lean`. Neither is de-privatised — duplicating a three-line lemma is
the house preference over widening an interface, and the two existing copies already justify the
convention by existing.
-/

/--
An update at the head key replaces the head binding.
-/
private theorem update_cons_eq
    {Key : Type}
    {Value : Type}
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
  simp [Store.update, hCandidate]

/--
An update at another key keeps the head binding and recurses.
-/
private theorem update_cons_ne
    {Key : Type}
    {Value : Type}
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
  simp [Store.update, hCandidate]

/-!
## The two bridges
-/

/--
Every key of an updated store is an old key or the updated one.

The keys-level companion of the pair-level `Store.mem_update`
(`Relico/LF/GeneralKindOrigin.lean`): that one splits a surviving *binding*, this one splits a
surviving *key*, which is what a `Nodup` argument can consume.
-/
private theorem mem_keys_update
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {value : Value}
    {name : Key}
    (hMem :
      name ∈
        Store.keys
          (Store.update store key value)) :
    name ∈ Store.keys store ∨
      name = key := by
  revert hMem
  induction store with

  | nil =>
      intro hMem

      rw [
        show
            Store.update
                ([] : Store Key Value)
                key
                value =
              [(key, value)] from
            rfl,
        Store.keys_cons
      ] at hMem

      rcases List.mem_cons.mp hMem with
        hEq | hNil

      · exact Or.inr hEq

      · exact
          absurd
            hNil
            (by simp [Store.keys])

  | cons head remaining IH =>
      intro hMem

      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · rw [
          update_cons_eq
            candidate
            currentValue
            remaining
            key
            value
            hCandidate,
          Store.keys_cons
        ] at hMem

        rcases List.mem_cons.mp hMem with
          hEq | hIn

        · exact Or.inr hEq

        · refine Or.inl ?_

          rw [Store.keys_cons]

          exact
            List.mem_cons_of_mem
              _
              hIn

      · rw [
          update_cons_ne
            candidate
            currentValue
            remaining
            key
            value
            hCandidate,
          Store.keys_cons
        ] at hMem

        rcases List.mem_cons.mp hMem with
          hEq | hIn

        · refine Or.inl ?_

          rw [Store.keys_cons]

          exact
            List.mem_cons.mpr
              (Or.inl hEq)

        · rcases IH hIn with
            hOld | hNew

          · refine Or.inl ?_

            rw [Store.keys_cons]

            exact
              List.mem_cons_of_mem
                _
                hOld

          · exact Or.inr hNew

/--
A key absent from a store's keys filters the store to nothing.

The nil half of the filter bridge. Membership in `keys` is exactly what a filter at that key
tests, so absence of the one is absence from the other.
-/
private theorem filter_eq_nil_of_notMem_keys
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {key : Key} :
    ∀ (store : Store Key Value),
      key ∉ Store.keys store →
      store.filter
          (fun entry =>
            decide (entry.1 = key)) =
        [] := by

  intro store
  induction store with

  | nil =>
      intro _

      rfl

  | cons head remaining IH =>
      intro hNotMem

      rcases head with
        ⟨candidate, value⟩

      rw [Store.keys_cons] at hNotMem

      have hNe :
          key ≠ candidate := by
        intro hEq

        exact
          hNotMem
            (List.mem_cons.mpr
              (Or.inl hEq))

      have hTail :
          key ∉ Store.keys remaining := by
        intro hIn

        exact
          hNotMem
            (List.mem_cons.mpr
              (Or.inr hIn))

      rw [
        List.filter_cons_of_neg
          (p := fun entry =>
            decide (entry.1 = key))
          (a := (candidate, value))
          (by
            intro hEqual

            exact
              hNe
                (decide_eq_true_iff.mp
                  hEqual).symm)
      ]

      exact IH hTail

/--
`Store.update` preserves key uniqueness.

The load-bearing preservation fact, and the reason the whole milestone is cheap: `update`
replaces the **first** binding at a key or appends when the key is absent, and under either
branch a store with at most one occurrence per key still has at most one occurrence per key.
The replace branch keeps the key count exactly (one occurrence in, one out, at the same
position); the append branch adds a key the store did not carry, which `Nodup` of the key list
admits precisely because it was absent.

No distinctness side conditions, because none are needed — and none would be available, since
the DTR `send` rule updates sender and receiver without knowing whether they are the same actor.
-/
theorem keysUnique_update
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {key : Key}
    {value : Value}
    (hUnique :
      Store.KeysUnique store) :
    Store.KeysUnique
      (Store.update
          store
          key
          value) := by

  revert hUnique
  induction store with

  | nil =>
      intro _

      rw [
        show
            Store.update
                ([] : Store Key Value)
                key
                value =
              [(key, value)] from
            rfl
      ]

      refine
        (Store.keysUnique_cons key value []).mpr
          ⟨?_, Store.keysUnique_empty⟩

      simp [Store.keys]

  | cons head remaining IH =>
      intro hUnique

      rcases head with
        ⟨candidate, currentValue⟩

      obtain ⟨hHeadNotMem, hTailUnique⟩ :=
        (Store.keysUnique_cons
            candidate
            currentValue
            remaining).mp
          hUnique

      by_cases hCandidate :
          candidate = key

      · rw [hCandidate] at hHeadNotMem

        rw [
          update_cons_eq
            candidate
            currentValue
            remaining
            key
            value
            hCandidate
        ]

        exact
          (Store.keysUnique_cons
              key
              value
              remaining).mpr
            ⟨hHeadNotMem, hTailUnique⟩

      · rw [
          update_cons_ne
            candidate
            currentValue
            remaining
            key
            value
            hCandidate
        ]

        refine
          (Store.keysUnique_cons
              candidate
              currentValue
              _).mpr
            ⟨?_, IH hTailUnique⟩

        intro hMem

        rcases
            mem_keys_update hMem with
          hOld | hNew

        · exact hHeadNotMem hOld

        · exact hCandidate hNew

/--
Under key uniqueness, an actual entry is the **only** entry at its key, in the exact spelling
the consume core's store premises read.

The filter bridge, and the reason the invariant is stated at occurrence strength. `Nodup` of the
key list says the key occurs once; that the occurring entry is *this* one is the membership
hypothesis; and a filter at a key that one entry carries is that entry alone. Lookup uniqueness
could not carry this step for the reason F74 records — two bindings at one key agree under every
lookup — which is why the premise set is `KeysUnique` plus membership and nothing weaker.
-/
theorem filter_eq_singleton_of_keysUnique_of_mem
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    {store : Store Key Value}
    {entry : Key × Value}
    (hUnique :
      Store.KeysUnique store)
    (hMember :
      entry ∈ store) :
    store.filter
        (fun candidate =>
          decide (candidate.1 = entry.1)) =
      [entry] := by

  revert hMember
  revert hUnique

  induction store with

  | nil =>
      intro _ hMember

      cases hMember

  | cons head remaining IH =>
      intro hUnique hMember

      rcases head with
        ⟨candidate, value⟩

      obtain ⟨hHeadNotMem, hTailUnique⟩ :=
        (Store.keysUnique_cons
            candidate
            value
            remaining).mp
          hUnique

      rcases List.mem_cons.mp hMember with
        hHere | hThere

      · subst hHere

        dsimp only

        rw [
          List.filter_cons_of_pos
            (p := fun entry =>
              decide (entry.1 = candidate))
            (a := (candidate, value))
            (by
              show
                decide (candidate = candidate) =
                  true

              exact decide_eq_true rfl)
        ]

        rw [
          filter_eq_nil_of_notMem_keys
            remaining
            hHeadNotMem
        ]

      · have hHeadNe :
            candidate ≠ entry.1 := by
          intro hEqual

          apply hHeadNotMem

          rw [hEqual]

          exact
            List.mem_map_of_mem
              hThere

        rw [
          List.filter_cons_of_neg
            (p := fun e =>
              decide (e.1 = entry.1))
            (a := (candidate, value))
            (by
              intro hEqual

              exact
                hHeadNe
                  (decide_eq_true_iff.mp
                    hEqual))
        ]

        exact IH hTailUnique hThere

end Store

namespace DTR

/--
The actor store of a source runtime configuration carries each actor name at most once.

Stated as `Store.KeysUnique` — occurrence-exact — because that is the strength the consume
core's `hUniqueS` premise reads and the strength `Store.update` preserves. See the module header
for why lookup uniqueness is not an acceptable weakening.
-/
def GeneralStoreKeyUnique
    (config : DTR.GeneralRuntimeConfiguration) :
    Prop :=
  Store.KeysUnique
    config.actors

/--
The initial configuration's actor store is key-unique.

The initializers build the actor store as one `List.map` keyed by instance names, so key
uniqueness is instance-name uniqueness — and that is `Store.KeysUnique model.topology`, the
first conjunct of the `namesUniqueAndValid` clause a well-formed model already satisfies. The
two key lists are the same list because `DTR.GeneralModel.topology` projects the same
`model.instances` under the same name function.

This is the only place source well-formedness enters the milestone, and it is genuinely required
here: nothing else in the source semantics forbids two instances of one name, and a model
admitting them would build a shadowed initial store no later theorem could repair.
-/
theorem generalStoreKeyUnique_initial
    {model : DTR.GeneralModel}
    (hWellFormed :
      model.wellFormed =
        true) :
    DTR.GeneralStoreKeyUnique
      (DTR.GeneralModel.initialState model) := by
  have hClause :
      model.namesUniqueAndValid =
        true :=
    DTR.GeneralModel.namesUniqueAndValid_of_wellFormed
      model
      hWellFormed

  unfold DTR.GeneralModel.namesUniqueAndValid at hClause

  simp only [
    Bool.and_eq_true,
    decide_eq_true_eq
  ] at hClause

  have hTopology :
      Store.KeysUnique
        model.topology :=
    hClause.left.left.left

  have hInitialKeys :
      Store.keys
          (DTR.GeneralModel.initialState model).actors =
        model.instances.map
          (fun actor =>
            actor.name) := by
    unfold DTR.GeneralModel.initialState
    unfold Store.keys
    rw [List.map_map]
    rfl

  have hTopologyKeys :
      Store.keys
          model.topology =
        model.instances.map
          (fun actor =>
            actor.name) := by
    unfold DTR.GeneralModel.topology
    unfold Store.keys
    rw [List.map_map]
    rfl

  unfold DTR.GeneralStoreKeyUnique
  unfold Store.KeysUnique

  rw [hInitialKeys, ← hTopologyKeys]

  exact hTopology

/--
Every source step preserves actor-store key uniqueness.

All five rules, and the accounting is: `assign`, `trace` and `take` write one actor through one
`Store.update`; `send` writes two, sender then receiver — the receiver lookup already reads the
sender-updated store, and the double update needs no distinctness side condition, so the
self-send case is covered by the same two applications rather than by a special argument;
`timeProgress` touches no store at all. No premise beyond the step itself: preservation is a
fact about `Store.update`, not about the model.
-/
theorem generalStoreKeyUnique_of_step
    {model : DTR.GeneralModel}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {label : DTR.GeneralLabel}
    (hUnique :
      DTR.GeneralStoreKeyUnique config)
    (hStep :
      DTR.GeneralStep
        model
        config
        label
        config') :
    DTR.GeneralStoreKeyUnique config' := by
  unfold DTR.GeneralStoreKeyUnique at hUnique ⊢

  cases hStep with

  | assign _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | trace _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | send _ _ _ _ _ =>
      dsimp only

      exact
        Store.keysUnique_update
          (Store.keysUnique_update hUnique)

  -- Stage H's three step-into rules each `Store.update` one existing key, so the key set is the
  -- one uniqueness was proved for. Nothing about the argument depends on which fields the update
  -- rewrites, which is why these three read exactly like `assign`.
  | branchTrue _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | branchFalse _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | resume _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | take _ _ _ _ _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | timeProgress _ _ _ =>
      dsimp only

      exact hUnique

/--
Reachability of a source runtime configuration: finite execution from the canonical initial
configuration.

No reachability predicate existed anywhere in the tree — every occurrence of the word is
docstring prose — so this is the smallest definition that supports the corollary below: one
`initial` case, one `step` case, and an induction that consumes exactly those two. Shaped like
`Common.TauSteps` minus the label filter, because reachability here does not care what a step
observes, only that it happened.
-/
inductive GeneralReachable
    (model : DTR.GeneralModel) :
    DTR.GeneralRuntimeConfiguration →
    Prop where

  | initial :
      GeneralReachable
        model
        (DTR.GeneralModel.initialState model)

  | step
      {config config' : DTR.GeneralRuntimeConfiguration}
      {label : DTR.GeneralLabel}
      (hReachable :
        GeneralReachable model config)
      (hStep :
        DTR.GeneralStep
          model
          config
          label
          config') :
      GeneralReachable model config'

/--
Every reachable source configuration has a key-unique actor store.

The one-line induction over `GeneralReachable`: the initial case is the initializer theorem,
the step case is preservation. Model well-formedness enters only through the initial case, which
is the only place it is needed.

This is the theorem a future forward `.consume` wrapper reads for `hUniqueS`: the take rule's
pre-configuration is reachable by construction, and the filter corollary below turns this
invariant into the premise's own equation.
-/
theorem generalStoreKeyUnique_of_reachable
    {model : DTR.GeneralModel}
    (hWellFormed :
      model.wellFormed =
        true)
    {config : DTR.GeneralRuntimeConfiguration}
    (hReachable :
      DTR.GeneralReachable model config) :
    DTR.GeneralStoreKeyUnique config := by
  induction hReachable with

  | initial =>
      exact
        DTR.generalStoreKeyUnique_initial
          hWellFormed

  | step _ hStep IH =>
      exact
        DTR.generalStoreKeyUnique_of_step
          IH
          hStep

/--
The `hUniqueS` premise's own equation, from the invariant and an actor-store membership.

Exactly the spelling `Correctness.generalConsume_forward_weak_of_fireRepresentative` reads: the
store filtered at the actor's name is the one pair that actor names. Membership rather than
lookup, because membership is the stronger fact and the invariant is stated to be consumed at
that strength.
-/
theorem generalStoreKeyUnique_filter_of_mem
    {config : DTR.GeneralRuntimeConfiguration}
    (hUnique :
      DTR.GeneralStoreKeyUnique config)
    {actorName : ActorName}
    {actor : DTR.GeneralActorRuntime}
    (hMember :
      (actorName, actor) ∈
        config.actors) :
    config.actors.filter
        (fun entry =>
          decide (entry.1 = actorName)) =
      [(actorName, actor)] :=
  Store.filter_eq_singleton_of_keysUnique_of_mem
    hUnique
    hMember

/--
The lookup-shaped companion of the filter corollary.

`DTR.GeneralStep.take` resolves its actor through `Store.lookup`, so this is the form a caller
holding a take rule's own premise reads directly; `Store.mem_of_lookup` is the bridge from the
weaker fact, and it is sound in this direction only — which is the entire reason the invariant
is membership-shaped.
-/
theorem generalStoreKeyUnique_filter_of_lookup
    {config : DTR.GeneralRuntimeConfiguration}
    (hUnique :
      DTR.GeneralStoreKeyUnique config)
    {actorName : ActorName}
    {actor : DTR.GeneralActorRuntime}
    (hLookup :
      Store.lookup
          config.actors
          actorName =
        some actor) :
    config.actors.filter
        (fun entry =>
          decide (entry.1 = actorName)) =
      [(actorName, actor)] :=
  DTR.generalStoreKeyUnique_filter_of_mem
    hUnique
    (Store.mem_of_lookup
      config.actors
      actorName
      actor
      hLookup)

end DTR

namespace LF

/--
The `instanceNamesUnique` clause of program well-formedness, as a `Nodup` fact.

A local copy of an extraction that exists `private` in
`Relico/Correctness/GeneralCorrespondence.lean` and again in
`Relico/LF/GeneralKindOrigin.lean` — neither is de-privatised, and duplicating a four-line
Bool case split is the house preference over widening either interface. The proof is the
clause's own `cases … <;> simp`, which works because the conclusion mentions the clause: in the
`true` case the premise's conjunct is `true` and simp peels it, in the `false` case the premise
reduces to `false = true`.
-/
private theorem instanceNamesUnique_of_wellFormed
    (program : LF.GeneralProgram)
    (hWellFormed :
      program.wellFormed =
        true) :
    program.instanceNamesUnique =
      true := by
  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.instanceNamesUnique <;>
    simp

/--
The reactor store of a target runtime state carries each instance name at most once.

The target mirror of `DTR.GeneralStoreKeyUnique`, same notion, same strength, same reason: the
consume core's `hUniqueT` premise reads occurrence-exact filtering.
-/
def GeneralStoreKeyUnique
    (state : LF.GeneralRuntimeState) :
    Prop :=
  Store.KeysUnique
    state.reactors

/--
The initial state's reactor store is key-unique.

The target mirror of the source initializer theorem, and the one place target well-formedness
enters: `LF.GeneralProgram.initialState` builds the reactor store as one `List.map` keyed by
instance names, so key uniqueness is the `instanceNamesUnique` clause — which the compilation
guard decides, so a caller holding a successfully compiled program reads this off
`Translation.compileGeneralModel_wellFormed` and nothing else. No compiler premise is taken
here because none is needed: the guard's verdict is already on the program.
-/
theorem generalStoreKeyUnique_initial
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed =
        true) :
    LF.GeneralStoreKeyUnique
      (LF.GeneralProgram.initialState program) := by
  have hNames :
      (program.instances.map
        (fun reactorInstance =>
          reactorInstance.name)).Nodup :=
    of_decide_eq_true
      (instanceNamesUnique_of_wellFormed
        program
        hWellFormed)

  have hKeys :
      Store.keys
          (LF.GeneralProgram.initialState program).reactors =
        program.instances.map
          (fun reactorInstance =>
            reactorInstance.name) := by
    unfold LF.GeneralProgram.initialState
    unfold Store.keys
    rw [List.map_map]
    rfl

  unfold LF.GeneralStoreKeyUnique
  unfold Store.KeysUnique

  rw [hKeys]

  exact hNames

/--
Every target step preserves reactor-store key uniqueness.

All seven rules: `assign`, `trace`, `schedule`, `setPort` and `fire` each write one reactor
through one `Store.update` — `fire` at the fired event's target — and `microstepAdvance` and
`timeAdvance` touch no store at all. One generic lemma per update, no premises: the target's
store discipline is the same fact about `Store.update` the source's is.
-/
theorem generalStoreKeyUnique_of_step
    {program : LF.GeneralProgram}
    {state state' : LF.GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hUnique :
      LF.GeneralStoreKeyUnique state)
    (hStep :
      LF.GeneralStep
        program
        state
        label
        state') :
    LF.GeneralStoreKeyUnique state' := by
  unfold LF.GeneralStoreKeyUnique at hUnique ⊢

  cases hStep with

  | assign _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | trace _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | schedule _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | setPort _ _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  -- The three target step-into rules update one existing reactor key, exactly as the four
  -- statement rules above do.
  | branchTrue _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | branchFalse _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | resume _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | fire _ _ _ _ _ _ =>
      dsimp only

      exact Store.keysUnique_update hUnique

  | microstepAdvance _ _ _ =>
      dsimp only

      exact hUnique

  | timeAdvance _ _ =>
      dsimp only

      exact hUnique

/--
The invariant survives a τ closure.

The lift the future forward wrapper actually consumes: the consume core's alignment premise is
`Common.TauSteps`, and every τ step — including the store-writing body-execution rules the
alignment may contain — preserves the invariant by the step theorem, so the closure does too.
The label filter plays no role, which is why the induction has no case on it.
-/
theorem generalStoreKeyUnique_of_tauSteps
    {program : LF.GeneralProgram}
    {state state' : LF.GeneralRuntimeState}
    (hUnique :
      LF.GeneralStoreKeyUnique state)
    (hSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        state') :
    LF.GeneralStoreKeyUnique state' := by
  revert hUnique

  induction hSteps with

  | refl current =>
      intro hUniqueCurrent

      exact hUniqueCurrent

  | cons headStep headIsTau remainingSteps IH =>
      intro hUniqueStep

      exact
        IH
          (LF.generalStoreKeyUnique_of_step
            hUniqueStep
            headStep)

/--
Reachability of a target runtime state: finite execution from the canonical initial state.

The target mirror of `DTR.GeneralReachable`, introduced for the same reason — no reachability
predicate existed — and with the same shape, so the two corollaries below read symmetrically.
-/
inductive GeneralReachable
    (program : LF.GeneralProgram) :
    LF.GeneralRuntimeState →
    Prop where

  | initial :
      GeneralReachable
        program
        (LF.GeneralProgram.initialState program)

  | step
      {state state' : LF.GeneralRuntimeState}
      {label : LF.GeneralLabel}
      (hReachable :
        GeneralReachable program state)
      (hStep :
        LF.GeneralStep
          program
          state
          label
          state') :
      GeneralReachable program state'

/--
Every reachable target state has a key-unique reactor store.

Program well-formedness enters only through the initial case. A caller holding a compiled
program obtains it from `Translation.compileGeneralModel_wellFormed`; the step cases need
nothing, because preservation is a fact about `Store.update`.

**This, not an α-transport theorem, is how the future forward wrapper should reach
`hUniqueT`'s store** — see the module header. The representative the premise is stated at is to
be constructed with an identical reactor store, so reachability of the real state plus the
alignment's own reactor equality carries the invariant to it without ever crossing α.
-/
theorem generalStoreKeyUnique_of_reachable
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed =
        true)
    {state : LF.GeneralRuntimeState}
    (hReachable :
      LF.GeneralReachable program state) :
    LF.GeneralStoreKeyUnique state := by
  induction hReachable with

  | initial =>
      exact
        LF.generalStoreKeyUnique_initial
          hWellFormed

  | step _ hStep IH =>
      exact
        LF.generalStoreKeyUnique_of_step
          IH
          hStep

/--
The `hUniqueT` premise's own equation, from the invariant and a reactor-store membership.

Exactly the spelling `Correctness.generalConsume_forward_weak_of_fireRepresentative` reads: the
store filtered at the fired event's target is the one pair that target names.
-/
theorem generalStoreKeyUnique_filter_of_mem
    {state : LF.GeneralRuntimeState}
    (hUnique :
      LF.GeneralStoreKeyUnique state)
    {instanceName : ActorName}
    {reactor : LF.GeneralReactorRuntime}
    (hMember :
      (instanceName, reactor) ∈
        state.reactors) :
    state.reactors.filter
        (fun entry =>
          decide (entry.1 = instanceName)) =
      [(instanceName, reactor)] :=
  Store.filter_eq_singleton_of_keysUnique_of_mem
    hUnique
    hMember

/--
The lookup-shaped companion of the filter corollary.

The consume core resolves its representative's reactor through `Store.lookup`
(`hReactorBefore`), and `LF.GeneralStep.fire` does the same, so this is the form those callers
read directly.
-/
theorem generalStoreKeyUnique_filter_of_lookup
    {state : LF.GeneralRuntimeState}
    (hUnique :
      LF.GeneralStoreKeyUnique state)
    {instanceName : ActorName}
    {reactor : LF.GeneralReactorRuntime}
    (hLookup :
      Store.lookup
          state.reactors
          instanceName =
        some reactor) :
    state.reactors.filter
        (fun entry =>
          decide (entry.1 = instanceName)) =
      [(instanceName, reactor)] :=
  LF.generalStoreKeyUnique_filter_of_mem
    hUnique
    (Store.mem_of_lookup
      state.reactors
      instanceName
      reactor
      hLookup)

end LF

end Relico
