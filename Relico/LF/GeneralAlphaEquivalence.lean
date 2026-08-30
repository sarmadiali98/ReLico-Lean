/-
! # The light within-tag quotient: α-equivalence and the lifted step relation

Decision 0042 (`docs/decisions/0042-within-tag-partial-quotient.md`), landed 2026-08-30 after the
F86 architecture audit: among events targeting **distinct** reactors at one identical full
superdense tag, no target order is claimed, because none is real (F76's over-specification
measurement); among events targeting **one** reactor, order is preserved (F80's `lfc`
measurement). This module is that decision as a *defined system*, in the light encoding chosen
over a `Quotient`-typed one: raw states, raw `LF.GeneralStep`, and a lifted relation
`LF.GeneralStepModulo` whose steps may begin and end at α-equivalent representatives.

Three design commitments, each forced mechanically rather than chosen for taste:

**No congruence is claimed or needed.** α-equivalence is *not* a congruence of `GeneralStep`
and never can be: the scheduler seeds from the queue head, so two α-equivalent queues can
expose different next observable `.consume` labels. This is exactly why the lifted relation
exists — a step of the quotient system is *some* representative's step, and no
well-definedness proof is owed. That is also why the light encoding needs no bridge from
`fire_execution_commute_of_adjacent_queue_swap`'s final agreement: the transfer conditions this
layer serves quantify over representatives and consume each execution's *own* raw final, so the
two finals of a commuted pair never have to be identified with each other. What the commutation
theorem contributes is the *starting-state* bridge — the swapped partner is α-equivalent to the
original — which is `generalStateAlphaEquiv_swapPartner` below.

**The store component is a conjunction: membership equivalence and lookup equivalence.** Each
half preserves what one of the two consumers of a runtime state reads. The correspondence
relation this layer must carry (`Correctness.GeneralStateCorrespondence`) quantifies its
per-actor components over *membership* in the reactor store, and `Store.mem_of_lookup`'s own
docstring records why a lookup-shaped relation is unsound in that position: a shadowed binding
is constrained too. Conversely, `GeneralStep` reads the store only through `Store.lookup`
(fire's reactor, idleness and reaction premises), so membership alone would let the lifted
relation below select a representative whose operationally visible reactor state differs —
`[(k, rA), (k, rB)]` and `[(k, rB), (k, rA)]` are membership-equivalent with different
lookups. Neither half implies the other on shadowed stores; the α relation states both, and no
key-uniqueness invariant is assumed to bridge them. The commutation theorem's final agreement
supplies exactly the lookup half, which is why the finals bridge below still carries a recorded
gap on the membership half.

**The queue generator is positional and duplicate-safe.** One admissible swap exchanges two
*adjacent occurrences* with identical full tags and distinct targets. No `Nodup`, no
`first ∉ earlier` exclusion: that exclusion belongs to the *fire* theorem's scheduler-side
argument, not to the queue relation — a queue may legally hold duplicate events, and a swap
moves two occurrences without merging or dropping any. The closure is a hand-rolled inductive
(Lean core in this toolchain has no `EqvGen`), symmetric by construction, and each of its
members is a `List.Perm`, which is the formal carrier of multiplicity.

Out of scope, by the standing boundaries: any widening to same-logical-time-across-microsteps
ordering (the frozen α′ question — the generator below requires *full tag* equality), any
reordering of same-reactor events, any change to `GeneralStep`, `Common.TauSteps`,
`Common.WeakStep`, the label alphabet, `isTau`, or the observable projection, and both `.consume`
transfer conditions, which this layer exists to serve but does not state.
-/
import Relico.Common.WeakTransition
import Relico.LF.GeneralSemantics

namespace Relico
namespace LF

/-!
## Admissible queue swaps
-/

/--
One admissible adjacent swap of decision 0042's partial quotient.

Two **adjacent occurrences** — spelled as arbitrary splits around them, so that the relation is
about positions and never about values — with **identical full superdense tags** and
**distinct target reactors** are exchanged. Each conjunct is load-bearing: tag equality is the
decision's "at one logical tag" read exactly (the frozen α′ question is precisely whether this
should widen to logical time only — it has not); target distinctness is the decision's
"independent" clause, and it is what keeps same-reactor declaration order untouched (F80).

Duplicate occurrences are untouched by this definition: a swap of two positions keeps every
occurrence, so a queue `[e, e]` with `e.target ≠ e.target` impossible is simply never swapped
against itself, while `[e₁, e₂]` with equal tags and equal targets is refused by `hDistinct`.
No `Nodup` appears anywhere.
-/
def generalQueueSwapStep
    (pending pending' : GeneralEventQueue) :
    Prop :=
  ∃ earlier : GeneralEventQueue,
    ∃ first second : GeneralPendingEvent,
      ∃ rest : GeneralEventQueue,
        pending =
            earlier ++ first :: second :: rest ∧
          pending' =
            earlier ++ second :: first :: rest ∧
            first.tag = second.tag ∧
            first.target ≠ second.target

/--
An admissible swap is its own inverse.

The same splits witness the reverse step: tag equality and target distinctness are symmetric,
and the two queue equations swap roles. Symmetry at the generator level is what keeps the
closure honest about duplicates — nothing directional survives into the equivalence.
-/
theorem generalQueueSwapStep.symm
    {pending pending' : GeneralEventQueue}
    (hSwap :
      generalQueueSwapStep
        pending
        pending') :
    generalQueueSwapStep
      pending'
      pending := by
  obtain
      ⟨earlier, first, second, rest, hLeft, hRight, hTag, hDistinct⟩ :=
    hSwap

  exact
    ⟨earlier,
      second,
      first,
      rest,
      hRight,
      hLeft,
      hTag.symm,
      hDistinct.symm⟩

/--
An admissible swap is a permutation — the formal multiplicity carrier.

Length- and occurrence-preserving by construction; recorded because the closure below is
transported along this to give every α-equivalent queue pair a `List.Perm`, which is what the
correspondence-side β-(i) machinery consumes. `List.Perm.swap` exchanges the two middle events
and `List.Perm.append` carries the untouched prefix.
-/
theorem generalQueueSwapStep.perm
    {pending pending' : GeneralEventQueue}
    (hSwap :
      generalQueueSwapStep
        pending
        pending') :
    List.Perm
      pending
      pending' := by
  obtain
      ⟨earlier, first, second, rest, hLeft, hRight, _, _⟩ :=
    hSwap

  subst hLeft
  subst hRight

  exact
    List.Perm.append
      (List.Perm.refl earlier)
      (List.Perm.swap
        second
        first
        rest)

/--
An admissible swap leaves every reactor's event subsequence literally identical.

This is the same-reactor order preservation of decision 0042, at the generator level, in its
strongest form: not merely "relative order preserved" but *equality* of the filtered
projection. The two swapped events have distinct targets, so at most one of them targets any
given reactor; the one that does (if either) keeps its position among that reactor's events,
because the events around it that fail the filter are invisible to the projection. A blanket
"same logical time commutes" rule would fail exactly here — it could not say which filter is
preserved.
-/
theorem generalQueueSwapStep.filter_target
    (reactor : ActorName)
    {pending pending' : GeneralEventQueue}
    (hSwap :
      generalQueueSwapStep
        pending
        pending') :
    pending.filter
        (fun event =>
          decide (event.target = reactor)) =
      pending'.filter
        (fun event =>
          decide (event.target = reactor)) := by
  obtain
      ⟨earlier, first, second, rest, hLeft, hRight, _, hDistinct⟩ :=
    hSwap

  subst hLeft
  subst hRight

  by_cases hFirst : first.target = reactor

  · have hSecond :
        second.target ≠ reactor := by
      intro hEqual

      exact
        hDistinct
          (hFirst.trans hEqual.symm)

    simp [List.filter_append, hFirst, hSecond]

  · by_cases hSecond : second.target = reactor

    · simp [List.filter_append, hFirst, hSecond]

    · simp [List.filter_append, hFirst, hSecond]

/-!
## The generated queue equivalence
-/

/--
The equivalence generated by admissible swaps — the queue half of decision 0042.

Hand-rolled rather than taken from a library because this toolchain's core has no `EqvGen`, and
the shape is deliberately the one `EqvGen` would have: `refl` for identity, `rel` to embed one
admissible swap, `symm` and `trans` to close. Symmetry lives in the relation itself, so no
separate "symmetric closure" step exists to get wrong, and duplicates are legal throughout —
the generator moves positions, never values.

The equivalence laws are the constructors `refl`, `symm` and `trans` themselves; what is proved
below is what the laws do *not* give for free: every member is a `List.Perm` (multiplicity),
and every member preserves each reactor's filtered event subsequence (same-reactor order, over
the whole closure and not just one swap).
-/
inductive generalQueueAlphaEquiv :
    GeneralEventQueue →
    GeneralEventQueue →
    Prop where

  | refl
      (pending : GeneralEventQueue) :
      generalQueueAlphaEquiv
        pending
        pending

  | rel
      {pending pending' : GeneralEventQueue}
      (hSwap :
        generalQueueSwapStep
          pending
          pending') :
      generalQueueAlphaEquiv
        pending
        pending'

  | symm
      {pending pending' : GeneralEventQueue}
      (hEquiv :
        generalQueueAlphaEquiv
          pending
          pending') :
      generalQueueAlphaEquiv
        pending'
        pending

  | trans
      {pending middle pending' : GeneralEventQueue}
      (hLeft :
        generalQueueAlphaEquiv
          pending
          middle)
      (hRight :
        generalQueueAlphaEquiv
          middle
          pending') :
      generalQueueAlphaEquiv
        pending
        pending'

/--
Every α-equivalent queue pair is a permutation — multiplicity over the whole closure.

Each constructor preserves `List.Perm`: identity trivially, one swap by
`generalQueueSwapStep.perm`, symmetry and transitivity by `List.Perm`'s own closure. This is
the formal statement that the quotient never merges or drops occurrences, and it is what
carries membership facts (and, through β-(i)'s permutation clauses, occurrence counts) across
an α-exchange.
-/
theorem generalQueueAlphaEquiv.perm
    {pending pending' : GeneralEventQueue}
    (hEquiv :
      generalQueueAlphaEquiv
        pending
        pending') :
    List.Perm
      pending
      pending' := by
  induction hEquiv with

  | refl queue =>
      exact
        List.Perm.refl
          queue

  | rel hSwap =>
      exact
        generalQueueSwapStep.perm
          hSwap

  | symm _ inductionHypothesis =>
      exact
        inductionHypothesis.symm

  | trans _ _ inductionLeft inductionRight =>
      exact
        inductionLeft.trans
          inductionRight

/--
α-equivalence preserves each reactor's event subsequence over the whole closure.

The closure-level form of `generalQueueSwapStep.filter_target`: one swap preserves the filtered
projection *as a list*, so equality survives symmetry (as `Eq.symm`) and transitivity (as
`Eq.trans`), and induction over the derivation lifts the fact from single swaps to every
α-equivalent pair. This is the theorem a future transfer condition cites when it must know that
the quotient reorders nothing a single reactor can observe — same-target order and multiplicity
at once.
-/
theorem generalQueueAlphaEquiv.filter_target
    (reactor : ActorName)
    {pending pending' : GeneralEventQueue}
    (hEquiv :
      generalQueueAlphaEquiv
        pending
        pending') :
    pending.filter
        (fun event =>
          decide (event.target = reactor)) =
      pending'.filter
        (fun event =>
          decide (event.target = reactor)) := by
  induction hEquiv with

  | refl queue =>
      rfl

  | rel hSwap =>
      exact
        generalQueueSwapStep.filter_target
          reactor
          hSwap

  | symm _ inductionHypothesis =>
      exact
        inductionHypothesis.symm

  | trans _ _ inductionLeft inductionRight =>
      exact
        inductionLeft.trans
          inductionRight

/-!
## α-equivalence of runtime states
-/

/--
Two runtime states are α-equivalent when they differ only as decision 0042 permits.

Four clauses, reading the three fields of `GeneralRuntimeState` (the store contributes two):

- **Tags are equal** — the quotient moves nothing across logical time, so no `timeAdvance`
  behaviour changes; the generator's tag conjunct already forces this locally, and the state
  clause makes it global.

- **Reactor stores agree on membership** — every `(name, reactor)` entry of one is an entry of
  the other. This is what the correspondence this layer must carry reads:
  `Correctness.GeneralStateCorrespondence` quantifies its per-actor components over membership
  (the same reason `Store.mem_of_lookup` exists and the same shadowed-binding discipline its
  docstring records), so without this half the transport below is false rather than merely
  hard — two stores can agree under every lookup while one carries a shadowed entry the other
  lacks.

- **Reactor stores agree under every `Store.lookup`** — the first binding for each key is the
  same in both. This is what `GeneralStep` reads: every premise of `fire` resolves its reactor,
  its idleness and its reaction through `Store.lookup`, so without this half the lifted
  relation below could select a representative whose *operationally visible* reactor state
  differs from the state being stepped from — `[(k, rA), (k, rB)]` and `[(k, rB), (k, rA)]`
  are membership-equivalent with different lookups, and a step fired from the second is a
  behaviour no approved queue reordering of the first produces. The two halves are
  independent: neither implies the other on stores with shadowed bindings, and the reactor
  component is their conjunction precisely because the α relation must preserve what *both*
  consumers of a state observe.

- **Pending queues are α-equivalent** — the generated swap closure above.

No key-uniqueness invariant is assumed or needed: none is proved for these runtime stores, and
the lifted relation's ∃ ranges over arbitrary representatives, so a reachability invariant
would not tame it without being baked into the relation itself. No scheduler content, no
selection function — the lifted step relation below is where the scheduler's
representative-sensitivity is confined.
-/
def generalStateAlphaEquiv
    (state state' : GeneralRuntimeState) :
    Prop :=
  state.currentTag = state'.currentTag ∧
    (∀ (name : ActorName)
        (reactor : GeneralReactorRuntime),
      (name, reactor) ∈ state.reactors ↔
        (name, reactor) ∈ state'.reactors) ∧
    (∀ name : ActorName,
      Store.lookup
          state.reactors
          name =
        Store.lookup
          state'.reactors
          name) ∧
    generalQueueAlphaEquiv
      state.pending
      state'.pending

/--
α-equivalence is reflexive.
-/
theorem generalStateAlphaEquiv.refl
    (state : GeneralRuntimeState) :
    generalStateAlphaEquiv
      state
      state :=
  ⟨rfl,
   fun _ _ => Iff.rfl,
   fun _ => rfl,
   generalQueueAlphaEquiv.refl state.pending⟩

/--
α-equivalence is symmetric.
-/
theorem generalStateAlphaEquiv.symm
    {state state' : GeneralRuntimeState}
    (hEquiv :
      generalStateAlphaEquiv
        state
        state') :
    generalStateAlphaEquiv
      state'
      state := by
  obtain ⟨hTag, hStoreMem, hStoreLookup, hQueue⟩ :=
    hEquiv

  exact
    ⟨hTag.symm,
     fun name reactor =>
       (hStoreMem name reactor).symm,
     fun name =>
       (hStoreLookup name).symm,
     hQueue.symm⟩

/--
α-equivalence is transitive.
-/
theorem generalStateAlphaEquiv.trans
    {state middle state' : GeneralRuntimeState}
    (hLeft :
      generalStateAlphaEquiv
        state
        middle)
    (hRight :
      generalStateAlphaEquiv
        middle
        state') :
    generalStateAlphaEquiv
      state
      state' := by
  obtain ⟨hTagLeft, hStoreMemLeft, hStoreLookupLeft, hQueueLeft⟩ :=
    hLeft

  obtain ⟨hTagRight, hStoreMemRight, hStoreLookupRight, hQueueRight⟩ :=
    hRight

  exact
    ⟨hTagLeft.trans hTagRight,
     fun name reactor =>
       Iff.trans
         (hStoreMemLeft name reactor)
         (hStoreMemRight name reactor),
     fun name =>
       hStoreLookupLeft name |>.trans
         (hStoreLookupRight name),
     hQueueLeft.trans hQueueRight⟩

/-!
## The bridge from the execution-commutation theorem
-/

/--
The queue-swap partner of a state is α-equivalent to it — the starting-state half of
`GeneralStep.fire_execution_commute_of_adjacent_queue_swap`, restated in the quotient's own
terms.

The partner is the state the commutation theorem fires `second`-first from: same tag, same
reactor store, pending `earlier ++ second :: first :: rest`. All four clauses of
α-equivalence are immediate — the tag and the store are *literally* the same fields (so both
the membership and the lookup halves hold by reflexivity), and the queues differ by exactly one
admissible swap, the generator's own archetypal case. This is the bridge a future `.consume`
transfer condition uses to move from "the target's queue-first event" to "an α-representative
whose queue-first event is the matched one": F76's selection divergence is repaired by stepping
to the partner, and this theorem says that step costs nothing.

What is deliberately **not** here: a bridge identifying the two *finals* of the commuted
executions. The commutation theorem's final agreement gives per-key lookup equality, which is
exactly the lookup half of α's store component — but not the membership half, which needs key
uniqueness to follow from lookup agreement and is not available for these stores. Under the
light encoding this costs nothing: the lifted relation below quantifies over representatives
directly, so each execution is consumed at its own raw final and no well-definedness of finals
is owed. The gap is recorded here so a future full-quotient layer cannot mistake it for proved.
-/
theorem generalStateAlphaEquiv_swapPartner
    (state : GeneralRuntimeState)
    (first second : GeneralPendingEvent)
    (earlier rest : GeneralEventQueue)
    (hQueue :
      state.pending =
        earlier ++ first :: second :: rest)
    (hTag :
      first.tag = second.tag)
    (hDistinct :
      first.target ≠ second.target) :
    generalStateAlphaEquiv
      state
      {
        currentTag := state.currentTag

        reactors := state.reactors

        pending := earlier ++ second :: first :: rest
      } := by
  refine
    ⟨rfl,
     fun _ _ => Iff.rfl,
     fun _ => rfl,
     generalQueueAlphaEquiv.rel
       ⟨earlier,
        first,
        second,
        rest,
        hQueue,
        rfl,
        hTag,
        hDistinct⟩⟩

/-!
## The lifted step relation
-/

/--
One step of the quotient system: some representative's raw step.

The entire light encoding in one definition. A `GeneralStepModulo program state label state'`
holds when α-representatives of `state` and `state'` are connected by a raw `GeneralStep`.
No representative is canonical, none is recorded, and no step of the raw system is altered —
the raw relation is a *premise* here, never a conclusion. Because the relation is
∃-shaped over representatives, it needs no congruence proof to exist, which is the point: the
scheduler's representative-sensitivity (two α-equivalent queues can expose different next
observable labels) makes `GeneralStep` genuinely non-congruent, and the light encoding is how
decision 0042 is represented *without* paying that false obligation.

Orientation follows the commissioning instruction: the representatives are existentially
bound on the left of each α-equivalence, which the relation's symmetry makes immaterial.

`Common.LabeledTransition` conformance is definitional — the relation has the
`State → Label → State → Prop` shape the generic machinery takes — so
`TauSteps (GeneralStepModulo program) isTau` and `WeakStep (GeneralStepModulo program) isTau`
instantiate at this parameter with the *unchanged* `LF.GeneralLabel.isTau` and the unchanged
observable projection; the two lemmas below are the raw-to-modulo liftings that keep the raw
weak-transition theorems reusable against the lifted system.
-/
def GeneralStepModulo
    (program : GeneralProgram)
    (state : GeneralRuntimeState)
    (label : GeneralLabel)
    (state' : GeneralRuntimeState) :
    Prop :=
  ∃ before after : GeneralRuntimeState,
    generalStateAlphaEquiv before state ∧
      generalStateAlphaEquiv after state' ∧
        GeneralStep
          program
          before
          label
          after

/--
Every raw step is a modulo step, via reflexivity on both ends.
-/
theorem GeneralStepModulo.of_raw
    {program : GeneralProgram}
    {state state' : GeneralRuntimeState}
    {label : GeneralLabel}
    (hStep :
      GeneralStep
        program
        state
        label
        state') :
    GeneralStepModulo
      program
      state
      label
      state' :=
  ⟨state, state', generalStateAlphaEquiv.refl state, generalStateAlphaEquiv.refl state', hStep⟩

/--
Raw internal closures lift to modulo internal closures.

`Common.TauSteps.mono` over `GeneralStepModulo.of_raw`: the generic closure machinery is reused,
not restated, and `isTau` — the same `LF.GeneralLabel.isTau` the raw system uses — passes
through unchanged, so a τ of the raw system is a τ of the quotient system by construction.
-/
theorem GeneralStepModulo.tauSteps_of_raw
    {program : GeneralProgram}
    {state state' : GeneralRuntimeState}
    (hSteps :
      Common.TauSteps
        (GeneralStep program)
        GeneralLabel.isTau
        state
        state') :
    Common.TauSteps
      (GeneralStepModulo program)
      GeneralLabel.isTau
      state
      state' :=
  Common.TauSteps.mono
    (fun _ _ _ hStep =>
      GeneralStepModulo.of_raw hStep)
    hSteps

/--
Raw weak transitions lift to modulo weak transitions.

`Common.WeakStep.mono` over `GeneralStepModulo.of_raw` — the visible step and both τ paddings
lift together, so every raw `WeakStep` theorem transfers to the lifted system unchanged. The
converse is deliberately absent: a modulo weak step may switch representatives between
segments, and that is the quotient's semantics, not an accident to be undone.
-/
theorem GeneralStepModulo.weakStep_of_raw
    {program : GeneralProgram}
    {state state' : GeneralRuntimeState}
    {label : GeneralLabel}
    (hWeak :
      Common.WeakStep
        (GeneralStep program)
        GeneralLabel.isTau
        state
        label
        state') :
    Common.WeakStep
      (GeneralStepModulo program)
      GeneralLabel.isTau
      state
      label
      state' :=
  Common.WeakStep.mono
    (fun _ _ _ hStep =>
      GeneralStepModulo.of_raw hStep)
    hWeak

end LF
end Relico
