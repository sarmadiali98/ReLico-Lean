/-
! # The instant-block abstraction for the `.consume` correspondence

The theorem-level treatment of the F76/F86 scheduler divergence, as approved on 2026-08-30
after three read-only audits: correctness for the general family is **instant-block weak
correspondence**, not unrestricted per-observable-step weak bisimulation. One block drains one
logical instant — every `.consume` belonging to logical time `t`, including the events that
zero-delay sends generate at later microsteps of `t` — and the only order the two sides must
agree on is the order **within one reactor**; how independent reactors interleave inside the
instant is unobserved, which is exactly what LF's own semantics guarantees (F76's
over-specification finding, confirmed from our own two definitions in F77: ports and state are
fixed at a tag; the interleaving is not) and what the paper's own Theorem 1 absorption sentence
claims (P24).

This module is the **abstraction layer only** — the block relations, the occurrence spine, the
per-reactor match, and the basic facts later proofs will need. Neither transfer direction is
stated, and the three mechanical invariants the eventual transfer requires (no-overdue
tag-alignment, kind-origin, reachable-state store-key uniqueness) are not attempted here.

Three design commitments, each forced by one of the audits rather than chosen:

**The target block's execution object is an indexed spine over the actual fired events.**
`LF.GeneralLabel.consume` carries only `(target, kind)` — no payload, no tag, no event identity
— and two pending events with the same target and kind but different payloads are
label-indistinguishable (F78's measurement, one level up). A block stated over label lists
alone therefore cannot guarantee that its correspondence witnesses are the events that actually
executed; a witness could pair a label with a same-kind event that never fired. The spine below
makes the occurrence list **data** indexing a `Prop`, and each `consume` constructor carries the
raw `LF.GeneralStep.fire` premises for its own event — the event is the constructor's binder,
so every indexed occurrence is an actual fire by construction. This follows the repository's
own `Common.WeakSteps` pattern (a `Prop` indexed by a label list) rather than eliminating a
`Prop` proof into data, which Lean forbids for non-subsingleton proofs anyway.

**Both endpoints are all-idle.** Queue/bag quiescence alone is not a maximal drain: every τ
body rule on both sides is premised only on a store lookup and an active-body head, so a
mid-body actor can satisfy "no due message" while its own next statement is a zero-delay send
that would generate same-instant work the block had already declared finished. Both block
predicates therefore end at: same logical time, no remaining instant work in the
bag/queue, **and** every runtime entry idle (`activeBody.isEmpty`). The maximality theorems
below make that endpoint's meaning precise: from such a state, the only step either semantics
offers is the logical-time advance that starts the next block.

**Matching is per reactor, not global.** A single ordered occurrence list shared by both sides
would force the two executions into the same global interleaving — refuted by the approved
semantics, which exists precisely to free the interleaving. `generalConsumeBlockMatch` relates
the two sides only through `Forall2 (GeneralConsumeMatch actor)` on each actor's own filtered
extractions, so cross-reactor interleaving is unconstrained while same-reactor order and
multiplicity are positional facts of the pairing. `List.Forall₂` does not exist in this
toolchain's core, so the five-line twin lives here.

Out of scope, by the standing boundaries: the F27 same-actor tie (the match deliberately does
not weaken same-reactor order, so that question stays visible where it lives), α′-style
cross-microstep widening (the spine reaches later microsteps by the τ alignment its entries
carry, not by quotienting), and any change to `GeneralStepModulo`, α-equivalence, or either
scheduler.
-/
import Relico.Correctness.GeneralWeakBisimulation
import Relico.Common.WeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/-!
## A local `Forall₂`

Lean core in this toolchain (4.32.1) has no `List.Forall₂`, and the block match needs exactly
that relation: a positional, order- and multiplicity-preserving pairing of two lists under a
binary relation. Rather than reach for anything stronger, the twin is stated here in full —
two constructors, nothing else — with the three inversion/counting facts the match's basic
lemmas consume.
-/

/--
A positional pairing of two lists under a binary relation: element `i` of the left with
element `i` of the right, same order, same length, duplicates distinct.

This toolchain's core has no `List.Forall₂`, so this is the smallest twin: two constructors,
and the discipline (order, multiplicity, length) is the induction principle rather than a
separate theorem.
-/
inductive Forall2
    {α β : Type}
    (R : α → β → Prop) :
    List α →
    List β →
    Prop where

  | nil :
      Forall2
        R
        []
        []

  | cons
      {left : α}
      {right : β}
      {leftRest : List α}
      {rightRest : List β}
      (hHead : R left right)
      (hRest :
        Forall2
          R
          leftRest
          rightRest) :
      Forall2
        R
        (left :: leftRest)
        (right :: rightRest)

/--
A pairing of the empty list forces the other side empty.
-/
theorem Forall2.eq_nil_of_left_nil
    {α β : Type}
    {R : α → β → Prop}
    {right : List β}
    (hPair :
      Forall2
        R
        []
        right) :
    right = [] := by

  cases hPair

  rfl

/--
Pairing a cons on the left forces a cons on the right, and splits the pairing.
-/
theorem Forall2.cons_inv
    {α β : Type}
    {R : α → β → Prop}
    {left : α}
    {leftRest : List α}
    {right : List β}
    (hPair :
      Forall2
        R
        (left :: leftRest)
        right) :
    ∃ (head : β)
      (rest : List β),
      right = head :: rest ∧
        R left head ∧
          Forall2
            R
            leftRest
            rest := by

  cases hPair with

  | cons hHead hRest =>
      exact
        ⟨_,
         _,
         rfl,
         hHead,
         hRest⟩

/--
A pairing preserves length — the counting fact behind per-reactor multiplicity.
-/
theorem Forall2.length
    {α β : Type}
    {R : α → β → Prop}
    {left : List α}
    {right : List β}
    (hPair :
      Forall2
        R
        left
        right) :
    left.length =
      right.length := by

  induction hPair with

  | nil =>
      rfl

  | cons _ _ IH =>
      simp only [
        List.length_cons
      ]

      exact
        congrArg
          (fun n =>
            n + 1)
          IH

/-!
## Pure extractions and projections

Everything in this section is an ordinary function on data. The source side extracts from
label data (the DTR `.consume` label carries the whole message); the target side projects
from the spine's occurrence index. No proof is ever eliminated into data.
-/

/--
The per-label filter behind `sourceConsumesAt`, named so that the extraction's algebra
(distribution over append, the two-consume swap) can state and compose equalities about the
*same* function instead of repeating an anonymous lambda.

A consume label at this actor keeps its message; every other label — consumes at other actors,
τ, time-advances — contributes nothing.
-/
def sourceConsumeFilter
    (actor : ActorName)
    (label : DTR.GeneralLabel) :
    Option DTR.GeneralMessage :=
  match label with
  | .consume receiver message =>
      if actor = receiver then
        some message
      else
        none
  | _ =>
      none

/--
This actor's consumed messages, in order, from the source block's label list.

A pure `filterMap`: order and duplicates are those of the label list, which is what makes the
per-reactor pairing below positional.
-/
def sourceConsumesAt
    (actor : ActorName)
    (labels : List DTR.GeneralLabel) :
    List DTR.GeneralMessage :=
  labels.filterMap
    (sourceConsumeFilter actor)

/--
This reactor's fired events, in order, from the target block's occurrence index.

A pure filter on the event data — the spine's index already *is* the actual fired events, so
this extraction needs no execution premise at all.
-/
def targetConsumesAt
    (reactor : ActorName)
    (events : List LF.GeneralPendingEvent) :
    List LF.GeneralPendingEvent :=
  events.filter
    (fun event =>
      decide (event.target = reactor))

/--
The observable label list a target occurrence index projects to.

The target block's observables, derived from data: each actual fired event contributes exactly
its `.consume` label. This is the projection the spine's `weakSteps` theorem connects to a real
modulo execution.
-/
def blockLabels
    (events : List LF.GeneralPendingEvent) :
    List LF.GeneralLabel :=
  events.map
    (fun event =>
      LF.GeneralLabel.consume
        event.target
        event.kind)

/--
Every projected label is a consume label.

Definitional (`blockLabels` maps into the `consume` constructor), but stated because the
eventual transfer quantifies over the projected list and will want the shape without
re-deriving it from the map.
-/
theorem blockLabels_mem_consume
    {events : List LF.GeneralPendingEvent}
    {label : LF.GeneralLabel}
    (hMem :
      label ∈ blockLabels events) :
    ∃ target kind,
      label =
        LF.GeneralLabel.consume
          target
          kind := by
  obtain ⟨event, _, rfl⟩ :=
    List.mem_map.mp hMem

  exact
    ⟨event.target, event.kind, rfl⟩

/-!
## Small list facts, privately

Generic helpers the block lemmas consume, none of which core states in the shapes needed:
the filter-split that locates an element's occurrence inside the list its filter heads, and
the all-false filter collapse. They live here privately rather than in `Relico/Common/`
because each was written for one consumer in this file — the standing rule against
speculative infrastructure applies to list lemmas too. The global consume-count equality the
design sketched is deliberately absent: per-reactor lengths (`generalConsumeBlockMatch.length_eq`)
are what the block induction consumes, and a global count would need finite-actor reasoning
the design audit explicitly declined to complicate the definition with.
-/

/--
`filterMap` distributes over append.
-/
private theorem filterMap_append
    {α β : Type}
    (f : α → Option β)
    (left right : List α) :
    (left ++ right).filterMap f =
      left.filterMap f ++
        right.filterMap f := by

  induction left with

  | nil =>
      rfl

  | cons head tail IH =>
      cases hHead : f head with

      | none =>
          simp only [
            List.cons_append,
            List.filterMap,
            hHead
          ]

          exact IH

      | some b =>
          simp only [
            List.cons_append,
            List.filterMap,
            hHead
          ]

          exact
            congrArg
              (fun l =>
                b :: l)
              IH

/--
A filter whose result heads with `x` splits the list around `x`'s occurrence.

The occurrence-locating fact the global consume-count induction runs on: the prefix is all
`false` under the predicate, and the suffix's filter is the tail of the result. Occurrence
reasoning, not value reasoning — a duplicate of `x` in the prefix is excluded by the `false`
clause, which is what keeps the count honest.
-/
private theorem filter_split
    {α : Type}
    (p : α → Bool)
    {l : List α}
    {x : α}
    {xs : List α}
    (hFilter :
      l.filter p = x :: xs) :
    ∃ pre post : List α,
      l = pre ++ x :: post ∧
        (∀ y ∈ pre, p y = false) ∧
          post.filter p = xs := by

  induction l with

  | nil =>
      cases hFilter

  | cons head tail IH =>
      by_cases hHead :
        p head = true

      · rw [
          List.filter_cons_of_pos
            (p := p)
            (a := head)
            hHead
        ] at hFilter

        injection hFilter with hEq hRest

        subst hEq

        refine
          ⟨[],
           tail,
           rfl,
           fun y hMem =>
             by simp at hMem,
           hRest⟩

      · rw [
          List.filter_cons_of_neg
            (p := p)
            (a := head)
            hHead
        ] at hFilter

        obtain
            ⟨pre, post, hSplit, hPre, hPost⟩ :=
          IH hFilter

        refine
          ⟨head :: pre,
           post,
           by rw [List.cons_append, hSplit],
           by
             intro y hMem

             rcases
               List.mem_cons.mp hMem with
               hEq | hIn
             · rw [hEq]

               exact
                 (Bool.not_eq_true
                     (p head)).mp
                   hHead
             · exact
                 hPre y hIn,
           hPost⟩

/--
A list whose every element fails the predicate filters to nothing.
-/
private theorem filter_nil_of_forall_false
    {α : Type}
    (p : α → Bool)
    {l : List α}
    (hAll :
      ∀ y ∈ l, p y = false) :
    l.filter p = [] := by

  induction l with

  | nil =>
      rfl

  | cons head tail IH =>
      rw [
        List.filter_cons_of_neg
          (p := p)
          (a := head)
          (by
            rw [
              hAll head
                List.mem_cons_self
            ]

            intro hEqual

            exact
              Bool.noConfusion
                hEqual)
      ]

      exact
        IH
          (fun y hMem =>
            hAll y
              (List.mem_cons_of_mem
                _
                hMem))

/-!
## τ steps and logical time

Two facts the spine's time theorems compose, stated here because the semantics modules own
the step-level versions and the block layer owns their closure over `TauSteps`.
-/

/--
An internal LF label is the τ label.

The two-constructor elimination of `LF.GeneralLabel.isTau`: the classification is total over
the three labels, and only `tau` passes it.
-/
private theorem label_eq_tau_of_isTau
    {label : LF.GeneralLabel}
    (hTau :
      LF.GeneralLabel.isTau label) :
    label =
      LF.GeneralLabel.tau := by

  cases label with

  | tau =>
      rfl

  | timeAdvance before after =>
      exact
        absurd
          hTau
          (LF.GeneralLabel.not_isTau_timeAdvance
            before
            after)

  | consume target kind =>
      exact
        absurd
          hTau
          (LF.GeneralLabel.not_isTau_consume
            target
            kind)

/--
A τ closure preserves logical time — `LF.GeneralStep.now_eq_of_tau` lifted to `TauSteps`.

P24's discipline at the closure level: internal activity may move microsteps but never the
logical time, which is what keeps a block inside its instant. Stated on `currentTag.time`
directly because that is the form the spine's theorems consume.
-/
private theorem tauSteps_time_eq
    {program : LF.GeneralProgram}
    {state state' : LF.GeneralRuntimeState}
    (hSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        state') :
    state'.currentTag.time =
      state.currentTag.time := by

  induction hSteps with

  | refl current =>
      rfl

  | cons headStep headIsTau remainingSteps IH =>
      have hLabelTau :=
        label_eq_tau_of_isTau
          headIsTau

      rw [hLabelTau] at headStep

      exact
        IH.trans
          (LF.GeneralStep.now_eq_of_tau
            headStep)

/-!
## The target occurrence spine

The target block's execution object. The occurrence list is an **index** of the `Prop`, in the
`Common.WeakSteps` pattern, so labels and per-reactor extractions are ordinary functions of
data and no proof is ever eliminated. Each `consume` constructor carries the raw fire premises
for its own `event` binder — the actual-event guarantee is structural, not a theorem about
label recovery.
-/

/--
The state a raw `fire` produces, as a function of the fire's own ingredients.

The spine's `consume` constructor continues from exactly this state, and the actual-event and
weak-step theorems below apply `LF.GeneralStep.fire` to exactly these arguments — the function
exists so both mention the same value without writing the literal twice.
-/
def fireResult
    (rep : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (earlier' later' : LF.GeneralEventQueue)
    (reactorRT : LF.GeneralReactorRuntime)
    (reaction : LF.GeneralReaction) :
    LF.GeneralRuntimeState :=
  {
    currentTag := rep.currentTag

    reactors :=
      Store.update
        rep.reactors
        event.target
        {
          valuation :=
            LF.bindReactionParameters
              reaction.parameters
              event.payload
              reactorRT.valuation

          activeBody := reaction.body
          frames := []
        }

    pending := earlier' ++ later'
  }

/--
One instant's drain of the target system, as the **actual fired events** in fire order.

`nil` is the maximal empty block: nothing at this instant remains — every pending event is
strictly future and every reactor idle — so the block at a quiescent state is the empty
occurrence list. `consume` is one fire plus the rest: from the real state `before`, a raw τ
alignment reaches `aligned` (this is where microstep advances and body execution live — τ, and
inside the block), an α-representative `rep` of `aligned` supplies the fire premises
(`hEarliest` … `hReaction` are `LF.GeneralStep.fire`'s own six, at `rep`, with `event` as the
constructor's binder), the fire produces `fireResult rep event …`, and the tail drains the
rest of the instant from there.

Why the index is the occurrence list and not the label list: the label `.consume event.target
event.kind` under-determines the event (F78), so the spine indexes by the events themselves and
`blockLabels` projects. Why the fire premises are carried flat rather than in a witness
structure: `cases` on the spine then binds exactly the premises the transfer will consume, in
the repository's established flat-constructor style; a structure would only rename them.

What the constructor does **not** constrain: the alignment's length (zero or more τ steps),
the representative's queue arrangement (α's own discipline), and everything about other
reactors' interleaving — the block observes per-reactor order through its index and nothing
else.
-/
inductive GeneralInstantBlockSpine
    (program : LF.GeneralProgram)
    (t : LogicalTime) :
    LF.GeneralRuntimeState →
    List LF.GeneralPendingEvent →
    LF.GeneralRuntimeState →
    Prop where

  | nil
      {state : LF.GeneralRuntimeState}
      (hTime :
        state.currentTag.time = t)
      (hFuture :
        ∀ event ∈ state.pending,
          t < event.tag.time)
      (hIdle :
        ∀ entry ∈ state.reactors,
          LF.GeneralReactorRuntime.idle
            entry.2 =
            true) :
      GeneralInstantBlockSpine
        program
        t
        state
        []
        state

  | consume
      {before aligned rep : LF.GeneralRuntimeState}
      (event : LF.GeneralPendingEvent)
      (events : List LF.GeneralPendingEvent)
      (hTime :
        before.currentTag.time = t)
      (hAlign :
        Common.TauSteps
          (LF.GeneralStep program)
          LF.GeneralLabel.isTau
          before
          aligned)
      (hAlpha :
        LF.generalStateAlphaEquiv
          rep
          aligned)
      (hEarliest :
        LF.GeneralRuntimeState.earliestPendingEvent?
            rep =
          some event)
      (hTag :
        event.tag = rep.currentTag)
      {earlier' later' : LF.GeneralEventQueue}
      {reactorRT : LF.GeneralReactorRuntime}
      {reaction : LF.GeneralReaction}
      (hQueue :
        rep.pending =
          earlier' ++ event :: later')
      (hReactor :
        Store.lookup
            rep.reactors
            event.target =
          some reactorRT)
      (hIdleRT :
        reactorRT.idle = true)
      (hReaction :
        LF.GeneralProgram.reactionFor?
            program
            event.target
            event.kind =
          some reaction)
      {finish : LF.GeneralRuntimeState}
      (hTail :
        GeneralInstantBlockSpine
          program
          t
          (fireResult
            rep
            event
            earlier'
            later'
            reactorRT
            reaction)
          events
          finish) :
      GeneralInstantBlockSpine
        program
        t
        before
        (event :: events)
        finish

namespace GeneralInstantBlockSpine

/--
One spine entry is a weak transition of the modulo system, at exactly its own consume label.

The per-entry packaging the eventual transfer will apply once per occurrence: the raw τ
alignment lifts into the quotient system by `GeneralStepModulo.tauSteps_of_raw`, the fire
itself becomes the visible modulo step (the representative on the pre-side, reflexivity on the
post-side — the light quotient consumes each execution at its own raw final), and the suffix
is empty. This is `generalConsume_forward_weak_of_fireRepresentative`'s step construction with
the correspondence parts removed — the transfer adds those around it.
-/
theorem weakStep_consume
    {program : LF.GeneralProgram}
    {before aligned rep : LF.GeneralRuntimeState}
    {event : LF.GeneralPendingEvent}
    {earlier' later' : LF.GeneralEventQueue}
    {reactorRT : LF.GeneralReactorRuntime}
    {reaction : LF.GeneralReaction}
    (hAlign :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        before
        aligned)
    (hAlpha :
      LF.generalStateAlphaEquiv
        rep
        aligned)
    (hEarliest :
      LF.GeneralRuntimeState.earliestPendingEvent?
          rep =
        some event)
    (hTag :
      event.tag = rep.currentTag)
    (hQueue :
      rep.pending =
        earlier' ++ event :: later')
    (hReactor :
      Store.lookup
          rep.reactors
          event.target =
        some reactorRT)
    (hIdleRT :
      reactorRT.idle = true)
    (hReaction :
      LF.GeneralProgram.reactionFor?
          program
          event.target
          event.kind =
        some reaction) :
    Common.WeakStep
      (LF.GeneralStepModulo program)
      LF.GeneralLabel.isTau
      before
      (LF.GeneralLabel.consume
        event.target
        event.kind)
      (fireResult
        rep
        event
        earlier'
        later'
        reactorRT
        reaction) :=
  Common.WeakStep.visible
    (LF.GeneralLabel.not_isTau_consume
      event.target
      event.kind)
    (LF.GeneralStepModulo.tauSteps_of_raw
      hAlign)
    ⟨rep,
     fireResult
       rep
       event
       earlier'
       later'
       reactorRT
       reaction,
     hAlpha,
     LF.generalStateAlphaEquiv.refl
       (fireResult
         rep
         event
         earlier'
         later'
         reactorRT
         reaction),
     LF.GeneralStep.fire
       hEarliest
       hTag
       hQueue
       hReactor
       hIdleRT
       hReaction⟩
    (Common.TauSteps.refl
      (fireResult
        rep
        event
        earlier'
        later'
        reactorRT
        reaction))

/--
A spine is a real modulo execution whose observable labels are the occurrence projection.

The soundness of the label projection: inducting over the spine, each `consume` entry is one
modulo weak step at its own label (`weakStep_consume`), so the whole spine is a
`Common.WeakSteps` at exactly `blockLabels events` — the derived labels are not a claim about
the execution, they are the execution's labels.
-/
theorem weakSteps
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hSpine :
      GeneralInstantBlockSpine
        program
        t
        state
        occurrences
        finish) :
    Common.WeakSteps
      (LF.GeneralStepModulo program)
      LF.GeneralLabel.isTau
      state
      (blockLabels occurrences)
      finish := by

  induction hSpine with

  | nil hTime hFuture hIdle =>
      exact
        Common.WeakSteps.refl
          _

  | consume event events hTime hAlign hAlpha hEarliest hTag hQueue hReactor hIdleRT hReaction hTail IH =>
      exact
        Common.WeakSteps.cons
          (weakStep_consume
            hAlign
            hAlpha
            hEarliest
            hTag
            hQueue
            hReactor
            hIdleRT
            hReaction)
          IH

/--
Every indexed occurrence is an **actual raw fire** — the F78 soundness of the spine.

For each occurrence there exist the representative, the queue splits, the reactor runtime and
the reaction of a real `LF.GeneralStep.fire` whose event is definitionally that occurrence
(the last conjunct is the fire derivation itself, applied to the premises the constructor
carries). Not merely an event with the same target and kind: the full `GeneralPendingEvent`
is the fire's own binder. A witness that paired a label with a never-fired same-kind event
cannot satisfy this, because the spine never contained it.
-/
theorem fire_of_mem
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hSpine :
      GeneralInstantBlockSpine
        program
        t
        state
        occurrences
        finish)
    {event : LF.GeneralPendingEvent}
    (hMem :
      event ∈ occurrences) :
    ∃ (rep : LF.GeneralRuntimeState)
      (earlier' later' : LF.GeneralEventQueue)
      (reactorRT : LF.GeneralReactorRuntime)
      (reaction : LF.GeneralReaction),
      LF.GeneralRuntimeState.earliestPendingEvent?
          rep =
        some event ∧
        event.tag = rep.currentTag ∧
        rep.pending =
          earlier' ++ event :: later' ∧
        Store.lookup
            rep.reactors
            event.target =
          some reactorRT ∧
        reactorRT.idle = true ∧
        LF.GeneralProgram.reactionFor?
            program
            event.target
            event.kind =
          some reaction ∧
        LF.GeneralStep
          program
          rep
          (LF.GeneralLabel.consume
            event.target
            event.kind)
          (fireResult
            rep
            event
            earlier'
            later'
            reactorRT
            reaction) := by

  induction hSpine with

  | nil hTime hFuture hIdle =>
      cases hMem

  | consume headEvent events hTime hAlign hAlpha hEarliest hTag hQueue hReactor hIdleRT hReaction hTail IH =>
      rcases
        List.mem_cons.mp hMem with
        rfl | hIn
      · exact
          ⟨_,
           _,
           _,
           _,
           _,
           hEarliest,
           hTag,
           hQueue,
           hReactor,
           hIdleRT,
           hReaction,
           LF.GeneralStep.fire
             hEarliest
             hTag
             hQueue
             hReactor
             hIdleRT
             hReaction⟩
      · exact IH hIn

/--
The spine ends at the logical time it started at — the block never crosses instants.

Induction over the spine: the `nil` case is its own `hTime`, and the `consume` case's fire
preserves the representative's tag, so the tail inherits the anchor. The step-level content —
that τ steps do not move logical time and `timeAdvance` is the only rule that does — is the
P24 discipline the semantics modules already own; nothing here re-derives it.
-/
theorem time_invariant
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hSpine :
      GeneralInstantBlockSpine
        program
        t
        state
        occurrences
        finish) :
    finish.currentTag.time = t := by

  induction hSpine with

  | nil hTime hFuture hIdle =>
      exact hTime

  | consume event events hTime hAlign hAlpha hEarliest hTag hQueue hReactor hIdleRT hReaction hTail IH =>
      exact IH

/--
Every fired occurrence sits at the block's logical time.

The chain is entirely step-level facts composed: the fire premise pins the event's tag to the
representative's tag, α-equivalence pins the representative's tag to the aligned state's, the
τ alignment preserves logical time (`now_eq_of_tau`, lifted here to `TauSteps`), and the
constructor's `hTime` pins the alignment's start to `t`. Zero-delay chains stay inside the
block precisely because their events satisfy this theorem.
-/
theorem event_time_of_mem
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hSpine :
      GeneralInstantBlockSpine
        program
        t
        state
        occurrences
        finish)
    {event : LF.GeneralPendingEvent}
    (hMem :
      event ∈ occurrences) :
    event.tag.time = t := by

  induction hSpine with

  | nil hTime hFuture hIdle =>
      cases hMem

  | consume headEvent events hTime hAlign hAlpha hEarliest hTag hQueue hReactor hIdleRT hReaction hTail IH =>
      rcases
        List.mem_cons.mp hMem with
        rfl | hIn
      · rw [
          hTag,
          hAlpha.1,
          tauSteps_time_eq
            hAlign,
          hTime
        ]
      · exact IH hIn

end GeneralInstantBlockSpine

/-!
## The source block

The source side needs no spine: `DTR.GeneralLabel.consume` carries the whole message, so the
ordinary `Common.WeakSteps` label list — already data, already indexed — *is* the execution
object, and the message facts are pattern-matched out of the labels.
-/

/--
One instant's drain of the source system, as an ordinary finite weak execution.

The label list is the observable content (τ steps hide inside the weak-step machinery, exactly
as `Common.WeakSteps` draws that line). The interior conjunct demands that every visible label
be a consume whose message arrived at `t` — under the block's time discipline that is no
restriction at all (a take's message is due at `now`, and the block never leaves `t`), but
stating it keeps the block self-contained: the match's counting and the eventual transfer read
it off the predicate rather than re-deriving it from selection semantics.

The endpoint is **maximal** in the sense the maximality theorem below makes precise: same
logical time, no ready actor, and every actor idle — the strongest state-level "nothing at
`t` remains or will be generated" the configuration can express.
-/
def generalInstantBlock_source
    (model : DTR.GeneralModel)
    (t : LogicalTime)
    (config config' : DTR.GeneralRuntimeConfiguration)
    (labels : List DTR.GeneralLabel) :
    Prop :=
  config.now = t ∧
    Common.WeakSteps
      (DTR.GeneralStep model)
      DTR.GeneralLabel.isTau
      config
      labels
      config' ∧
    (∀ label ∈ labels,
      ∃ receiver message,
        label =
          DTR.GeneralLabel.consume
            receiver
            message ∧
          message.arrival = t) ∧
    config'.now = t ∧
    DTR.GeneralConfiguration.readyActors
      config'.erase =
      [] ∧
    ∀ entry ∈ config'.actors,
      DTR.GeneralActorRuntime.idle
        entry.2 =
        true

/-!
## The target block

A thin wrapper around the spine — the execution object *is* the spine; the wrapper exists only
to hold the two endpoint facts that the spine's `nil` case already carries at the end state
but that the source predicate states symmetrically, so the two block relations read alike.

The per-message arrival fact ("every consumed message arrived at `t`") is the source block's
own interior conjunct, stated per label; it is read off the predicate rather than re-proved.
-/

/--
One instant's drain of the target system.

The spine is the content; the wrapper adds nothing it does not guarantee — start time is the
spine's constructor discipline (each `consume` anchors its `before` at `t`, `nil` its state),
and the end conditions are exactly the `nil` constructor's own. Stated through the wrapper so
later proofs name one block predicate per side.
-/
def generalInstantBlock_target
    (program : LF.GeneralProgram)
    (t : LogicalTime)
    (state finish : LF.GeneralRuntimeState)
    (occurrences : List LF.GeneralPendingEvent) :
    Prop :=
  state.currentTag.time = t ∧
    GeneralInstantBlockSpine
      program
      t
      state
      occurrences
      finish

/-!
## The block match

Per reactor, `Forall2 (GeneralConsumeMatch actor)` between the pure extractions. Nothing
global — that is the design's point.
-/

/--
The observable equivalence of a source block and a target block: per-reactor positional
pairing of consumed messages with actually-fired events.

For every actor, the messages its consume labels carried (in source order) pair, element by
element, with the events its reactors actually fired (in target order) under
`GeneralConsumeMatch actor` — which pins target, logical time, and compiled payload per pair.
Cross-reactor interleaving is unconstrained, because no conjunct mentions two actors;
same-reactor order and multiplicity are positional facts of the pairing; and the kind bridge
stays out of the relation entirely (F78: kind is a property of the fired event, and the match
takes the event as it was fired).
-/
def generalConsumeBlockMatch
    (sourceLabels : List DTR.GeneralLabel)
    (targetOccurrences : List LF.GeneralPendingEvent) :
    Prop :=
  ∀ actor : ActorName,
    Forall2
      (GeneralConsumeMatch actor)
      (sourceConsumesAt
        actor
        sourceLabels)
      (targetConsumesAt
        actor
        targetOccurrences)

namespace generalConsumeBlockMatch

/--
The empty source block matches the empty occurrence list.

The base case of every block induction: no actor has any consume, and `Forall2` is nil-nil.
-/
theorem nil :
    generalConsumeBlockMatch [] [] :=
  fun _ =>
    Forall2.nil

/--
Per actor, the two extractions have equal length.

Multiplicity's counting half, per reactor. Immediate from `Forall2.length`.
-/
theorem length_eq
    {sourceLabels : List DTR.GeneralLabel}
    {targetOccurrences : List LF.GeneralPendingEvent}
    (hMatch :
      generalConsumeBlockMatch
        sourceLabels
        targetOccurrences)
    (actor : ActorName) :
    (sourceConsumesAt
        actor
        sourceLabels).length =
      (targetConsumesAt
        actor
        targetOccurrences).length :=
  Forall2.length
    (hMatch actor)

/--
The source extraction distributes over append — `filterMap_append` at the extraction's own
granularity, so the swap lemma can be applied to an appended pair without unfolding.
-/
private theorem sourceConsumesAt_append
    (actor : ActorName)
    (left right : List DTR.GeneralLabel) :
    sourceConsumesAt
        actor
        (left ++ right) =
      sourceConsumesAt
        actor
        left ++
        sourceConsumesAt
        actor
        right := by

  unfold sourceConsumesAt

  exact
    filterMap_append
      _
      _
      _

/--
Swapping two adjacent **source** consume labels at different actors leaves every actor's
extraction unchanged — the extraction-local core of the transposition lemma.

Distinctness is load-bearing: if the two labels belonged to the same actor, the swap would
reverse that actor's own consume order, which is semantic and must not be free. Under
distinctness, each actor's extraction sees at most one of the two labels, and a `none`
contribution is position-independent.
-/
private theorem sourceConsumesAt_of_two_consumes
    (actor receiverFirst receiverSecond : ActorName)
    (messageFirst messageSecond : DTR.GeneralMessage)
    (rest : List DTR.GeneralLabel)
    (hDistinct :
      receiverFirst ≠ receiverSecond) :
    sourceConsumesAt
        actor
        (DTR.GeneralLabel.consume
            receiverFirst
            messageFirst ::
          DTR.GeneralLabel.consume
              receiverSecond
              messageSecond ::
          rest) =
      sourceConsumesAt
        actor
        (DTR.GeneralLabel.consume
            receiverSecond
            messageSecond ::
          DTR.GeneralLabel.consume
              receiverFirst
              messageFirst ::
          rest) := by

  unfold sourceConsumesAt

  by_cases hFirst :
    actor = receiverFirst

  · have hSecond :
        ¬(actor = receiverSecond) := by
      intro hEqual

      exact
        hDistinct
          (hFirst.symm.trans hEqual)

    simp only [
      List.filterMap,
      sourceConsumeFilter,
      if_pos hFirst,
      if_neg hSecond
    ]

  · by_cases hSecond :
      actor = receiverSecond

    · simp only [
        List.filterMap,
        sourceConsumeFilter,
        if_neg hFirst,
        if_pos hSecond
      ]

    · simp only [
        List.filterMap,
        sourceConsumeFilter,
        if_neg hFirst,
        if_neg hSecond
      ]

/--
Swapping two adjacent **source** labels that consumed at different actors preserves the match.

The freedom the quotient grants, as a theorem: the target side is untouched — its occurrences
are the actual fires — while the source's interleaving may be any adjacent transposition of
consumes belonging to different actors. The extraction equality reduces to the two-consume
lemma inside the append split; same-actor swaps are deliberately not licensed.
-/
theorem of_source_swap
    {sourceLabels rest : List DTR.GeneralLabel}
    {targetOccurrences : List LF.GeneralPendingEvent}
    {first second : DTR.GeneralLabel}
    {receiverFirst receiverSecond : ActorName}
    {messageFirst messageSecond : DTR.GeneralMessage}
    (hFirst :
      first =
        DTR.GeneralLabel.consume
          receiverFirst
          messageFirst)
    (hSecond :
      second =
        DTR.GeneralLabel.consume
          receiverSecond
          messageSecond)
    (hDistinct :
      receiverFirst ≠
        receiverSecond)
    (hMatch :
      generalConsumeBlockMatch
        (sourceLabels ++
          first :: second :: rest)
        targetOccurrences) :
    generalConsumeBlockMatch
      (sourceLabels ++
        second :: first :: rest)
      targetOccurrences := by

  subst hFirst

  subst hSecond

  intro actor

  have hExtraction :
      sourceConsumesAt
          actor
          (sourceLabels ++
            DTR.GeneralLabel.consume
                receiverSecond
                messageSecond ::
              DTR.GeneralLabel.consume
                  receiverFirst
                  messageFirst ::
              rest) =
        sourceConsumesAt
          actor
          (sourceLabels ++
            DTR.GeneralLabel.consume
                receiverFirst
                messageFirst ::
              DTR.GeneralLabel.consume
                  receiverSecond
                  messageSecond ::
              rest) := by
    rw [
      sourceConsumesAt_append,
      sourceConsumesAt_append
    ]

    exact
      congrArg
        (fun l =>
          sourceConsumesAt
              actor
              sourceLabels ++
            l)
        (sourceConsumesAt_of_two_consumes
            actor
            receiverFirst
            receiverSecond
            messageFirst
            messageSecond
            rest
            hDistinct).symm

  rw [hExtraction]

  exact hMatch actor

end generalConsumeBlockMatch

/-!
## Maximal endpoints

What the all-idle end conditions mean: from a block's end state, the **only** step either
semantics offers is the logical-time advance that starts the next block. Every τ body rule is
premised on an active-body head (killed by idleness), every take/fire needs instant work
(killed by no-ready-actor / future-only-pending), and the two time rules are the remainder.
These are the theorems a future transfer cites for "the block ended because the instant did".
-/

/--
The maximality content at a quiescent-and-idle **source** state: the only step is the
observable time advance.

Stated standalone (no spine induction, no shadowed indices) because the argument is purely
about the state the end conditions describe. Each τ body rule is killed by unfolding `idle`
to `activeBody.isEmpty` and rewriting with the rule's own body premise — the successor body
is a cons, whose `isEmpty` is definitionally `false`; `take` is killed by the cohort bridge
`DTR.GeneralActorSelection.selectedActor_eq_none_of_cohort_nil`; `timeProgress` is the
survivor.
-/
private theorem generalInstantBlock_source_nil_maximal
    {model : DTR.GeneralModel}
    {config config'' : DTR.GeneralRuntimeConfiguration}
    (hQuiescent :
      DTR.GeneralConfiguration.readyActors
        config.erase =
      [])
    (hIdle :
      ∀ entry ∈ config.actors,
        DTR.GeneralActorRuntime.idle
          entry.2 =
        true)
    {label : DTR.GeneralLabel}
    (hStep :
      DTR.GeneralStep
        model
        config
        label
        config'') :
    ∃ before after : LogicalTime,
      label =
        DTR.GeneralLabel.timeAdvance
          before
          after := by

  cases hStep with

  | assign hActor hBody hEvaluate =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          config.actors
          _
          _
          hActor

      have hIdleEntry := hIdle _ hMem

      unfold DTR.GeneralActorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | trace hActor hBody =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          config.actors
          _
          _
          hActor

      have hIdleEntry := hIdle _ hMem

      unfold DTR.GeneralActorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | send hSender hBody hArguments hTarget hReceiver =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          config.actors
          _
          _
          hSender

      have hIdleEntry := hIdle _ hMem

      unfold DTR.GeneralActorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  -- Stage H's step-into rules are unreachable here for the same reason the three above are, and
  -- the two branch rules by the same conjunct: a conditional head makes `activeBody.isEmpty`
  -- false. `resume` is refuted by the *other* conjunct, which is what the stage H redesign of
  -- `idle` bought: an empty active body over a non-empty frame stack is not idle.
  | branchTrue hActor hBody hCondition =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          config.actors
          _
          _
          hActor

      have hIdleEntry := hIdle _ hMem

      unfold DTR.GeneralActorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | branchFalse hActor hBody hCondition =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          config.actors
          _
          _
          hActor

      have hIdleEntry := hIdle _ hMem

      unfold DTR.GeneralActorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | resume hActor hBody hFrames =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          config.actors
          _
          _
          hActor

      have hIdleEntry := hIdle _ hMem

      unfold DTR.GeneralActorRuntime.idle at hIdleEntry

      rw [
        hBody,
        hFrames
      ] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | take hSelected hName hActor hIdleActor hDue hArrival hServer =>
      exfalso

      have hNone :
          DTR.GeneralActorSelection.selectedActor
              model
              config.erase =
            none :=
        DTR.GeneralActorSelection.selectedActor_eq_none_of_cohort_nil
          model
          config.erase
          hQuiescent

      rw [hNone] at hSelected

      simp at hSelected

  | timeProgress hForward hQuiescent hSelected =>
      exact
        ⟨_,
         _,
         rfl⟩

/--
From a source block's end state, the only next step is the observable time advance.

`take` is unreachable (selection answers `none` on an empty cohort — the landed
`selectedActor_eq_none_of_cohort_nil` bridge); every τ body rule is unreachable (each needs a
cons active body, and every actor is idle); `timeProgress` remains, which is observable and
belongs to the next block.
-/
theorem generalInstantBlock_source_maximal
    {model : DTR.GeneralModel}
    {t : LogicalTime}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {labels : List DTR.GeneralLabel}
    (hBlock :
      generalInstantBlock_source
        model
        t
        config
        config'
        labels)
    {config'' : DTR.GeneralRuntimeConfiguration}
    {label : DTR.GeneralLabel}
    (hStep :
      DTR.GeneralStep
        model
        config'
        label
        config'') :
    ∃ before after : LogicalTime,
      label =
        DTR.GeneralLabel.timeAdvance
          before
          after := by

  obtain
      ⟨_, _, _, _, hQuiescent, hIdle⟩ :=
    hBlock

  exact
    generalInstantBlock_source_nil_maximal
      hQuiescent
      hIdle
      hStep

/--
The maximality content at a future-only-and-idle **target** state: the only raw step is the
observable time advance.

Standalone, like its source twin. `fire` and `microstepAdvance` are killed by the same
selection fact — the selected earliest event must sit at the current tag (each rule's own tag
premise), but `LF.earliestPendingEvent?_mem` places it in the pending list, where the end
condition makes every event strictly future; the four τ body rules are killed by idleness,
exactly as on the source side; `timeAdvance` is the survivor.
-/
private theorem generalInstantBlock_target_nil_maximal
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {state finish' : LF.GeneralRuntimeState}
    (hTime :
      state.currentTag.time = t)
    (hFuture :
      ∀ event ∈ state.pending,
        t < event.tag.time)
    (hIdle :
      ∀ entry ∈ state.reactors,
        LF.GeneralReactorRuntime.idle
          entry.2 =
        true)
    {label : LF.GeneralLabel}
    (hStep :
      LF.GeneralStep
        program
        state
        label
        finish') :
    ∃ before after : LogicalTime,
      label =
        LF.GeneralLabel.timeAdvance
          before
          after := by

  cases hStep with

  | assign hReactor hBody hEvaluate =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | trace hReactor hBody =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | schedule hReactor hBody hArguments =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | setPort hReactor hBody hArguments hConnection =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  -- The target step-into rules are unreachable here for the same reasons their source mirrors
  -- are: a conditional head refutes `activeBody.isEmpty`, and `resume` is refuted by the frame
  -- conjunct of the stage H `idle`.

  | branchTrue hReactor hBody hCondition =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | branchFalse hReactor hBody hCondition =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [hBody] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | resume hReactor hBody hFrames =>
      exfalso

      have hMem :=
        Store.mem_of_lookup
          state.reactors
          _
          _
          hReactor

      have hIdleEntry := hIdle _ hMem

      unfold LF.GeneralReactorRuntime.idle at hIdleEntry

      rw [
        hBody,
        hFrames
      ] at hIdleEntry

      exact
        Bool.noConfusion
          hIdleEntry

  | fire hSelected hTag hQueue hReactor hIdleRT hReaction =>
      exfalso

      have hMem :=
        LF.GeneralRuntimeState.earliestPendingEvent?_mem
          state
          _
          hSelected

      have hFutureEvent :=
        hFuture _ hMem

      rw [hTag] at hFutureEvent

      rw [hTime] at hFutureEvent

      exact
        Nat.lt_irrefl
          _
          hFutureEvent

  | microstepAdvance hSelected hTag hAdvance =>
      exfalso

      have hMem :=
        LF.GeneralRuntimeState.earliestPendingEvent?_mem
          state
          _
          hSelected

      have hFutureEvent :=
        hFuture _ hMem

      rw [hTag] at hFutureEvent

      rw [hTime] at hFutureEvent

      exact
        Nat.lt_irrefl
          _
          hFutureEvent

  | timeAdvance hSelected hForward =>
      exact
        ⟨_,
         _,
         rfl⟩

/--
From a target block's end state, the only next **raw** step is the observable time advance.

`fire` and `microstepAdvance` are unreachable: both are premised on the selected earliest
event, which at a future-only pending queue cannot sit at the current tag, because
`LF.earliestPendingEvent?_mem` would place that event in the pending list, where every
event's time is strictly future. The four τ body rules are unreachable by idleness, as on the
source side. `timeAdvance` remains — next block's entry.
-/
theorem GeneralInstantBlockSpine.maximal
    {program : LF.GeneralProgram}
    {t : LogicalTime}
    {state finish : LF.GeneralRuntimeState}
    {occurrences : List LF.GeneralPendingEvent}
    (hSpine :
      GeneralInstantBlockSpine
        program
        t
        state
        occurrences
        finish)
    {finish' : LF.GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hStep :
      LF.GeneralStep
        program
        finish
        label
        finish') :
    ∃ before after : LogicalTime,
      label =
        LF.GeneralLabel.timeAdvance
          before
          after := by

  induction hSpine with

  | nil hTime hFuture hIdle =>
      exact
        generalInstantBlock_target_nil_maximal
          hTime
          hFuture
          hIdle
          hStep

  | consume event events hTime hAlign hAlpha hEarliest hTag hQueue hReactor hIdleRT hReaction hTail IH =>
      exact
        IH hStep

end Correctness
end Relico
