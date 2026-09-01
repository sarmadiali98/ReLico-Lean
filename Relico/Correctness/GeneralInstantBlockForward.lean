/-
! # Forward instant-block transfer, general family

The forward half of the instant-block correspondence approved on 2026-08-30: one source instant block
is answered by one target execution over the light within-tag quotient, with the two sides related
per reactor.

## What this module composes, and what it assumes

Two things are already proved and are used unchanged:

* `Correctness.generalTauSteps_forward_raw` crosses the τ segments. Every `Common.WeakStep` of the
  source block carries a τ prefix and a τ suffix, and nothing crossed them before
  `Relico/Correctness/GeneralStatementForward.lean`.
* `Correctness.generalConsume_forward_weak_of_fireRepresentative` crosses a visible `.consume`. It is
  the **core lemma**, not the transfer clause: its own docstring records that the α-representative at
  which the target's `fire` premises hold is a *premise* there, being the honest residue of the frozen
  α′ question.

That residue is why this module's `.consume` answer is a **premise** rather than a construction. It is
quantified over the block's own steps — `hConsumeAnswer` below — in exactly the shape the core lemma
produces, so a caller who can supply representatives discharges it by applying the core lemma once per
occurrence and nothing else. Faking it here, by picking a representative or by promoting one with an
exact-tag quotient, would silently claim the frozen question was settled.

## Why the target occurrences are existential

`Correctness.generalConsumeBlockMatch` is produced for the constructed occurrence list, not consumed as
a premise, and the reason is structural rather than a matter of taste. The source block's label list and
the target block's occurrence list may legitimately differ in **cross-reactor interleaving** — that
freedom *is* the approved semantics, and `generalConsumeBlockMatch` mentions no two actors precisely so
that it does not constrain it. A statement taking both lists as given therefore cannot walk them
simultaneously in a `Common.WeakSteps` induction: the two orders need not agree globally. Aligning them
with an extra premise would re-specify the very interleaving the block semantics exists to free.

**This does not settle F27, and must not be read as doing so.** F27 asks whether an *arbitrary*
admissible source order is matchable — the source's `take` rule admits any of several equally-early
messages in one bag, and nothing derives that the target's single forced order is among them. What is
produced here is a match for the occurrence list this transfer *itself* constructs, which follows the
source's own order by construction. The F27 question stays open, where it lives
(`Relico/Correctness/GeneralSameReactorOrder.lean`, classification C), and no theorem here weakens
same-reactor order to reach its conclusion.

## Why store-key uniqueness is carried by the answer

`Common.TauSteps` over `LF.GeneralStepModulo` cannot preserve `LF.GeneralStoreKeyUnique`: a modulo step
may begin and end at α-equivalent representatives, and α's reactor conjuncts are membership- and
lookup-shaped, so they cannot see occurrence multiplicity. Transporting the invariant across them would
be unsound, and is forbidden. Consequently the target invariant is **re-established by the answer** at
each occurrence rather than propagated through it, and the τ segments are crossed in the *raw* system
(`generalTauSteps_forward_raw`) where `LF.generalStoreKeyUnique_of_tauSteps` does apply. The lift into
the quotient happens only when a segment is spliced into a `Common.WeakStep`.

Nothing here uses α to repair same-reactor ordering, transports store-key uniqueness through
`LF.generalStateAlphaEquiv`, revisits the kind-origin or routing decisions, or adds a well-formedness
clause.
-/
import Relico.Correctness.GeneralInstantBlock
import Relico.Correctness.GeneralStatementForward

set_option autoImplicit false

namespace Relico
namespace Correctness

/-!
## Two small facts the composition needs

Neither is stated anywhere: the source's τ-closure preservation of actor-store key uniqueness (the
target's twin exists as `LF.generalStoreKeyUnique_of_tauSteps`, the source's does not), and the padding
of a visible weak step by τ closures on both ends.
-/

/--
Source actor-store key uniqueness survives a τ closure.

The mirror of `LF.generalStoreKeyUnique_of_tauSteps`, which exists, for the side that has only the
per-step theorem. Needed because each source `Common.WeakStep` reaches its visible `take` through a τ
prefix, and the `.consume` answer wants the invariant at the `take`'s own pre-configuration rather than
at the block's start.

The label filter plays no role — `DTR.generalStoreKeyUnique_of_step` is stated for any label — which is
why the induction has no case on it.
-/
private theorem generalStoreKeyUnique_of_sourceTauSteps
    {model : DTR.GeneralModel}
    {config config' : DTR.GeneralRuntimeConfiguration}
    (hUnique :
      DTR.GeneralStoreKeyUnique config)
    (hSteps :
      Common.TauSteps
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        config') :
    DTR.GeneralStoreKeyUnique config' := by
  revert hUnique

  induction hSteps with

  | refl current =>
      intro hUniqueCurrent

      exact hUniqueCurrent

  | cons headStep headIsTau remainingSteps IH =>
      intro hUniqueStep

      exact
        IH
          (DTR.generalStoreKeyUnique_of_step
            hUniqueStep
            headStep)

/--
A visible weak step absorbs a τ closure on either end.

The splice this module's `.consume` case performs. The source's own weak step already pads its `take`
with τ segments, and the answer's weak step already pads its `fire` with the alignment and the
quotient's own reflexivity, so composing the two means concatenating four τ segments around one visible
step rather than nesting weak steps.

`cases` on the middle step rather than `induction`: `Common.WeakStep` has no premise of its own type.
The `tau` alternative is refuted by `hVisible`, which is why the visibility hypothesis is taken
explicitly instead of being recovered from the label — the caller has it either way, and taking it keeps
this lemma independent of which labels a family calls internal.

Generic in the step relation and the τ predicate: nothing here is about the general family, and stating
it at one instantiation would invite a second copy for the backward direction.
-/
private theorem weakStep_padTau
    {State : Type}
    {Label : Type}
    {step : Common.LabeledTransition State Label}
    {isTau : Label → Prop}
    {source before after target : State}
    {label : Label}
    (hVisible :
      ¬ isTau label)
    (hPrefix :
      Common.TauSteps
        step
        isTau
        source
        before)
    (hMiddle :
      Common.WeakStep
        step
        isTau
        before
        label
        after)
    (hSuffix :
      Common.TauSteps
        step
        isTau
        after
        target) :
    Common.WeakStep
      step
      isTau
      source
      label
      target := by

  cases hMiddle with

  | tau hTau _ =>
      exact
        absurd
          hTau
          hVisible

  | visible _ hInnerPrefix hStep hInnerSuffix =>
      exact
        Common.WeakStep.visible
          hVisible
          (Common.TauSteps.trans
            hPrefix
            hInnerPrefix)
          hStep
          (Common.TauSteps.trans
            hInnerSuffix
            hSuffix)

/-!
## The per-reactor match, built one occurrence at a time

`generalConsumeBlockMatch` is a `∀ actor` of `Forall2` over two `filterMap`/`filter` extractions, so
extending it by one paired occurrence is a case split on whether that actor is the consuming one. Both
branches are decided by a single fact — the answer's `GeneralConsumeMatch` says the event targets the
label's receiver — so the two extractions cannot disagree about which of them keeps the new element.
-/

/--
Extending a block match by one matched occurrence.

The step case of the transfer's match construction. For the consuming actor both extractions grow by
one and the new pair is the answer's own `GeneralConsumeMatch`; for every other actor both extractions
are unchanged, because `event.target = receiver` decides the target-side filter exactly as
`actor = receiver` decides the source-side one.

**No cross-reactor content.** The lemma quantifies over one actor at a time, so it says nothing about
how this occurrence is ordered against another reactor's — which is the property the block match exists
to leave free.
-/
private theorem generalConsumeBlockMatch_cons
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    {event : LF.GeneralPendingEvent}
    {labels : List DTR.GeneralLabel}
    {occurrences : List LF.GeneralPendingEvent}
    (hMatch :
      GeneralConsumeMatch
        receiver
        message
        event)
    (hRest :
      generalConsumeBlockMatch
        labels
        occurrences) :
    generalConsumeBlockMatch
      (DTR.GeneralLabel.consume
          receiver
          message ::
        labels)
      (event :: occurrences) := by

  intro actor

  have hTarget :
      event.target = receiver :=
    hMatch.1

  by_cases hActor :
      actor = receiver

  · subst hActor

    have hSource :
        sourceConsumesAt
            actor
            (DTR.GeneralLabel.consume
                actor
                message ::
              labels) =
          message ::
            sourceConsumesAt
              actor
              labels := by
      unfold sourceConsumesAt

      rw [
        List.filterMap_cons
      ]

      simp [
        sourceConsumeFilter
      ]

    have hTargetList :
        targetConsumesAt
            actor
            (event :: occurrences) =
          event ::
            targetConsumesAt
              actor
              occurrences := by
      unfold targetConsumesAt

      rw [
        List.filter_cons_of_pos
          (by
            simp [hTarget])
      ]

    rw [
      hSource,
      hTargetList
    ]

    exact
      Forall2.cons
        hMatch
        (hRest actor)

  · have hSource :
        sourceConsumesAt
            actor
            (DTR.GeneralLabel.consume
                receiver
                message ::
              labels) =
          sourceConsumesAt
            actor
            labels := by
      unfold sourceConsumesAt

      rw [
        List.filterMap_cons
      ]

      simp [
        sourceConsumeFilter,
        hActor
      ]

    have hTargetList :
        targetConsumesAt
            actor
            (event :: occurrences) =
          targetConsumesAt
            actor
            occurrences := by
      unfold targetConsumesAt

      rw [
        List.filter_cons_of_neg
          (by
            simp [
              hTarget,
              Ne.symm hActor
            ])
      ]

    rw [
      hSource,
      hTargetList
    ]

    exact hRest actor

/-!
## Endpoint transport, the forward direction

**This section corrects an earlier claim in this module's own history.** The transfer below concludes a
`Common.WeakSteps` rather than a `Correctness.GeneralInstantBlockSpine`, and the docstring of
`generalInstantBlock_forward_of_source` recorded that the obstacle was the *endpoint transport*, with the
`hFuture` half — "no ready source actor implies every pending target event is strictly future" — named as
genuine unproved work.

That was wrong, and the reason it was wrong is worth stating. `GeneralPendingAgrees` has accessors in
**both** directions (`generalPendingAgrees_message_of_event` and `..._event_of_message`), so both
transports go through; the earlier assessment was made before the backward direction's readiness layer
made the pairing's symmetry obvious. Both halves are proved below.

**What actually blocks the spine is different, and it is structural.** `GeneralInstantBlockSpine`'s
`consume` constructor carries `LF.GeneralStep.fire`'s six premises at an α-representative — the alignment,
the α-exchange, the earliest-event selection, the tag anchor, the queue split, and the reaction lookup.
The transfer's answer premise returns a `Common.WeakStep`, which is a `Prop` carrying **none** of them:
a weak step says a transition exists, not which event it fired or at which representative. So a spine
cannot be recovered from what the answer gives, and the gap is not an unproved lemma but a premise that
would have to return different data. Whoever closes it should strengthen the answer premise to return the
spine entry, not attempt an inversion — `GeneralInstantBlockSpine.weakSteps` runs spine to execution and
has no converse for exactly this reason.

The two transports below are what remains of the earlier "deferred" item, and they are done.
-/

/--
A compiled body is empty when its source body is.

The easy direction of the emptiness correspondence, and the one the forward idleness transport needs.
`Translation.compileGeneralBody` sends `[]` to `.ok []` outright, so a successful compilation of an empty
source body has an empty target body.

Its converse — an empty compiled body forces an empty source body — is
`compileGeneralBody_eq_nil` in `Relico/Correctness/GeneralInstantBlockBackward.lean`, which needs a case
split on the statement compiler because the implication runs against the compiler's direction. That
asymmetry in cost is why the two live apart rather than as one iff.
-/
private theorem compileGeneralBody_nil_eq
    {env : Translation.GeneralOutputPortEnv}
    {context : Translation.GeneralBodyContext}
    {index : Nat}
    {target : LF.GeneralBody}
    (hCompiled :
      Translation.compileGeneralBody
          env
          context
          index
          [] =
        .ok target) :
    target = [] := by

  unfold Translation.compileGeneralBody at hCompiled

  simp at hCompiled

  exact hCompiled

/--
An idle actor's reactor is idle.

The `hIdle` half of forward endpoint transport, and the mirror of
`Correctness.generalActorIdle_of_reactorIdle`. Idleness is `activeBody.isEmpty` on both sides and the
correspondence's `continuation` field compiles one into the other, so `compileGeneralBody_nil_eq` closes
it.

No well-formedness premise and no appeal to the model: emptiness of a compiled body is a fact about the
compiler alone.
-/
theorem generalReactorIdle_of_actorIdle
    {env : Translation.GeneralOutputPortEnv}
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {reactor : LF.GeneralReactorRuntime}
    {pending : LF.GeneralEventQueue}
    (hCorresponds :
      GeneralActorCorresponds
        env
        name
        actor
        reactor
        pending)
    (hIdle :
      DTR.GeneralActorRuntime.idle actor = true) :
    LF.GeneralReactorRuntime.idle reactor = true := by

  obtain ⟨context, index, hCompiled, _⟩ :=
    hCorresponds.continuation

  have hSourceNil :
      actor.activeBody = [] := by
    unfold DTR.GeneralActorRuntime.idle at hIdle

    exact
      List.isEmpty_iff.mp hIdle

  rw [hSourceNil] at hCompiled

  unfold LF.GeneralReactorRuntime.idle

  rw [
    compileGeneralBody_nil_eq
      hCompiled
  ]

  rfl

/--
**Every pending target event is strictly future when the source has no ready actor.**

The `hFuture` half of forward endpoint transport, and the one this module previously recorded as unproved.
The chain is the mirror of `Correctness.generalQuiescent_of_pendingFuture`, run through the pairing's other
accessor: `pendingTargeted` names the event's actor, `reactorOfActor` supplies its pairing,
`generalPendingAgrees_message_of_event` turns the event into a source message *at the event's own arrival*,
and a message due at or before the clock would put its actor in the readiness cohort — which
`hReady` says is empty.

So the two endpoint transports are symmetric after all, and the asymmetry recorded earlier was an artefact
of which accessor had been used at the time, not of the relation. What remains asymmetric is the *spine
structure*, for the reason given in this section's header.

Stated over `state.currentTag.time` rather than a separate instant so that it composes directly with
`GeneralInstantBlockSpine.nil`'s `hFuture` after one rewrite by the block's own time premise.
-/
theorem generalPendingFuture_of_quiescent
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hReady :
      DTR.GeneralConfiguration.readyActors config.erase =
        []) :
    ∀ event ∈ state.pending,
      state.currentTag.time < event.tag.time := by

  intro event hEvent

  -- `by_contra` is not available here (no Mathlib in this project), so the excluded middle is taken
  -- explicitly on the order itself. `Nat.lt_or_ge` is total, so the split is exhaustive.
  rcases Nat.lt_or_ge
      state.currentTag.time
      event.tag.time with
    hFuture |
      hDue

  · exact hFuture

  exfalso

  obtain ⟨actor, hActorMember⟩ :=
    hCorrespondence.pendingTargeted
      event
      hEvent

  obtain ⟨_, _, _, _, hPair⟩ :=
    hCorrespondence.reactorOfActor
      event.target
      actor
      hActorMember

  obtain ⟨message, hMessageMember, hArrival⟩ :=
    generalPendingAgrees_message_of_event
      event.target
      actor.state.bag
      state.pending
      hPair.messages
      event
      hEvent
      rfl

  -- The message is due, so its actor belongs to the cohort the premise says is empty.
  obtain ⟨arrival, hEarliest⟩ :=
    DTR.earliestDueArrival_complete
      actor.state.bag
      config.now
      message
      hMessageMember
      (by
        -- `logicalTime` reads `state.currentTag.time = config.now`, so the clock is rewritten BACKWARDS
        -- here: the goal mentions `config.now` and `hDue` is stated at the target's tag.
        rw [
          hArrival,
          ← hCorrespondence.logicalTime
        ]

        exact hDue)

  have hCohortMember :
      (
        {
          actorName := event.target
          logicalTime := arrival
        } :
          DTR.GlobalMultiStorePayloadActorPriority.ReadyActor
      ) ∈
        DTR.GeneralConfiguration.readyActors config.erase :=
    DTR.readyActors_complete
      config.erase
      event.target
      actor.state
      arrival
      (by
        rw [
          DTR.GeneralRuntimeConfiguration.erase_actors
        ]

        exact
          DTR.mem_eraseContinuations_of_mem
            config.actors
            event.target
            actor
            hActorMember)
      (by
        unfold DTR.GeneralActorState.dueArrival

        rw [
          DTR.GeneralRuntimeConfiguration.erase_now
        ]

        exact hEarliest)

  rw [hReady] at hCohortMember

  cases hCohortMember

/-!
## The transfer

One induction over `Common.WeakSteps`, with the visible case delegated to the answer premise and the
two τ paddings crossed by `generalTauSteps_forward_raw`.

The τ crossings are deliberately **raw**: `LF.generalStoreKeyUnique_of_tauSteps` is stated for
`LF.GeneralStep`, and it has no modulo counterpart because none is sound — a modulo step may switch
α-representatives and α cannot see occurrence multiplicity. Each raw segment is lifted into the quotient
only at the moment it is spliced around a visible step.
-/

/--
**Forward instant-block transfer.** A source instant block's step sequence is answered by a target
execution of the quotient system, whose observable labels are the projection of the events it actually
fired, with the correspondence at both endpoints and a per-reactor match.

Read the premises in three groups.

**The compiled-program facts** — `hCompiled`, `hRoutes`, `hEnvNodup`, `hNames` — are what
`generalTauSteps_forward` already consumed, and are accepted-program facts rather than new obligations.

**`hConsumeLabels`** is `generalInstantBlock_source`'s own label-shape conjunct, weakened to what this
proof uses: every label of the block is a `.consume`. It is what refutes `Common.WeakStep.tau` in the
induction, so a τ label cannot enter the block and quietly vanish from the projected trace. The
arrival-time half of that conjunct is not needed here and is not asked for.

**`hConsumeAnswer` is the α′ residue, quantified over the block's own steps.** Its shape is exactly what
`generalConsume_forward_weak_of_fireRepresentative` produces, so a caller discharges it by applying that
core lemma once per occurrence: given a corresponding pair with both stores key-unique and a source
`.consume` step, it returns the fired event, the target's weak step at that event's own label, the match,
the post-state correspondence, and the target invariant re-established. The last of those is included
because it **cannot** be propagated: the answer's weak step is a modulo step, and transporting key
uniqueness across α is unsound. The representative package that the core lemma takes as a premise is
therefore still a premise here — this theorem composes the block, it does not settle the frozen α′
question.

**`generalConsumeBlockMatch` is produced, not consumed, and this does not settle F27.** The match is
built for the occurrence list this transfer constructs, which follows the source's own order. F27 asks
the different question of whether an *arbitrary* admissible source order is matchable — the source's
`take` admits any equally-early message of a bag — and nothing here answers it. Its classification stays
where it lives.

Nothing in the proof uses α to reorder same-reactor consumes, transports store-key uniqueness through
`LF.generalStateAlphaEquiv`, or touches either scheduler.
-/
theorem generalInstantBlock_forward
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {labels : List DTR.GeneralLabel}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
                  model.classes
                  candidateClass =
                .ok candidateEnv) →
          (List.map
            (fun candidateEntry =>
              candidateEntry.outputPort.value)
            candidateEnv).Nodup)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup)
    (hConsumeAnswer :
      ∀ (stepConfig stepConfig' : DTR.GeneralRuntimeConfiguration)
        (stepState : LF.GeneralRuntimeState)
        (receiver : ActorName)
        (message : DTR.GeneralMessage),
        GeneralStateCorrespondence
          model
          stepConfig
          stepState →
        DTR.GeneralStoreKeyUnique stepConfig →
        LF.GeneralStoreKeyUnique stepState →
        DTR.GeneralStep
          model
          stepConfig
          (DTR.GeneralLabel.consume
            receiver
            message)
          stepConfig' →
        ∃ (stepState' : LF.GeneralRuntimeState)
          (event : LF.GeneralPendingEvent),
          Common.WeakStep
              (LF.GeneralStepModulo program)
              LF.GeneralLabel.isTau
              stepState
              (LF.GeneralLabel.consume
                event.target
                event.kind)
              stepState' ∧
            GeneralConsumeMatch
              receiver
              message
              event ∧
            GeneralStateCorrespondence
              model
              stepConfig'
              stepState' ∧
            LF.GeneralStoreKeyUnique stepState')
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hConsumeLabels :
      ∀ label ∈ labels,
        ∃ (receiver : ActorName)
          (message : DTR.GeneralMessage),
          label =
            DTR.GeneralLabel.consume
              receiver
              message)
    (hBlock :
      Common.WeakSteps
        (DTR.GeneralStep model)
        DTR.GeneralLabel.isTau
        config
        labels
        config') :
    ∃ (occurrences : List LF.GeneralPendingEvent)
      (state' : LF.GeneralRuntimeState),
      Common.WeakSteps
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          (blockLabels occurrences)
          state' ∧
        generalConsumeBlockMatch
          labels
          occurrences ∧
        GeneralStateCorrespondence
          model
          config'
          state' ∧
        LF.GeneralStoreKeyUnique state' := by

  induction hBlock generalizing state with

  | refl current =>
      exact
        ⟨[],
         state,
         Common.WeakSteps.refl state,
         generalConsumeBlockMatch.nil,
         hCorrespondence,
         hUniqueT⟩

  | @cons stepSource stepMiddle stepAfter label remainingLabels headStep remainingSteps IH =>

      -- The head label is a consume, which is what makes the τ alternative of the weak step impossible.
      obtain ⟨receiver, message, rfl⟩ :=
        hConsumeLabels
          _
          List.mem_cons_self

      cases headStep with

      | tau hTau _ =>
          exact
            absurd
              hTau
              (DTR.GeneralLabel.not_isTau_consume
                receiver
                message)

      | visible _ hPrefix hTakeStep hSuffix =>

          -- The τ prefix, crossed in the raw target system so the target invariant survives it.
          obtain ⟨stateBefore, hRawPrefix, hCorrespondenceBefore⟩ :=
            generalTauSteps_forward_raw
              hCompiled
              hRoutes
              hEnvNodup
              hNames
              hCorrespondence
              hUniqueS
              hUniqueT
              hPrefix

          have hUniqueSBefore :
              DTR.GeneralStoreKeyUnique _ :=
            generalStoreKeyUnique_of_sourceTauSteps
              hUniqueS
              hPrefix

          have hUniqueTBefore :
              LF.GeneralStoreKeyUnique stateBefore :=
            LF.generalStoreKeyUnique_of_tauSteps
              hUniqueT
              hRawPrefix

          -- The visible consume, by the answer premise.
          obtain
              ⟨stateAfter,
               event,
               hAnswerStep,
               hAnswerMatch,
               hCorrespondenceAfter,
               hUniqueTAfter⟩ :=
            hConsumeAnswer
              _
              _
              stateBefore
              receiver
              message
              hCorrespondenceBefore
              hUniqueSBefore
              hUniqueTBefore
              hTakeStep

          have hUniqueSAfter :
              DTR.GeneralStoreKeyUnique _ :=
            DTR.generalStoreKeyUnique_of_step
              hUniqueSBefore
              hTakeStep

          -- The τ suffix, again raw.
          obtain ⟨stateMiddle, hRawSuffix, hCorrespondenceMiddle⟩ :=
            generalTauSteps_forward_raw
              hCompiled
              hRoutes
              hEnvNodup
              hNames
              hCorrespondenceAfter
              hUniqueSAfter
              hUniqueTAfter
              hSuffix

          have hUniqueSMiddle :
              DTR.GeneralStoreKeyUnique stepMiddle :=
            generalStoreKeyUnique_of_sourceTauSteps
              hUniqueSAfter
              hSuffix

          have hUniqueTMiddle :
              LF.GeneralStoreKeyUnique stateMiddle :=
            LF.generalStoreKeyUnique_of_tauSteps
              hUniqueTAfter
              hRawSuffix

          -- The rest of the block, from the corresponding intermediate pair.
          obtain
              ⟨tailOccurrences,
               stateFinal,
               hTailSteps,
               hTailMatch,
               hCorrespondenceFinal,
               hUniqueTFinal⟩ :=
            IH
              hCorrespondenceMiddle
              hUniqueSMiddle
              hUniqueTMiddle
              (fun label hLabel =>
                hConsumeLabels
                  label
                  (List.mem_cons_of_mem
                    _
                    hLabel))

          refine
            ⟨event :: tailOccurrences,
             stateFinal,
             Common.WeakSteps.cons
               (weakStep_padTau
                 (LF.GeneralLabel.not_isTau_consume
                   event.target
                   event.kind)
                 (LF.GeneralStepModulo.tauSteps_of_raw
                   hRawPrefix)
                 hAnswerStep
                 (LF.GeneralStepModulo.tauSteps_of_raw
                   hRawSuffix))
               hTailSteps,
             generalConsumeBlockMatch_cons
               hAnswerMatch
               hTailMatch,
             hCorrespondenceFinal,
             hUniqueTFinal⟩

/--
The transfer against the block predicate itself.

`generalInstantBlock_source` is `generalInstantBlock_forward`'s premises repackaged: its second conjunct
is the step sequence and its third is the label-shape fact, so this corollary only projects and forgets.

What it forgets is worth naming. The block predicate also carries `config.now = t`, `config'.now = t`,
and the endpoint quiescence (`readyActors config'.erase = []` and every actor idle); **none of them is
used**, and none is passed on.

**An earlier version of this docstring said the obstacle was the endpoint transport, and named the
`hFuture` half as an unproved obligation. That was wrong.** Both halves are proved, above:
`generalPendingFuture_of_quiescent` and `generalReactorIdle_of_actorIdle`. The pairing has accessors in
both directions, so the transport is symmetric; the earlier assessment was made before the backward
direction's readiness layer made that obvious.

**What actually blocks a full `generalInstantBlock_target` is the spine's data, not its endpoint.**
`GeneralInstantBlockSpine`'s `consume` constructor carries `LF.GeneralStep.fire`'s six premises at an
α-representative, while this theorem's `hConsumeAnswer` returns a `Common.WeakStep` — a `Prop` that says a
transition exists and records neither which event fired nor at which representative.
`GeneralInstantBlockSpine.weakSteps` runs spine to execution and has no converse for exactly that reason.
Closing the gap means **strengthening the answer premise to return the spine entry**, not proving another
transport lemma; that is separate work, and the transports it would have needed are now in hand.
-/
theorem generalInstantBlock_forward_of_source
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {t : LogicalTime}
    {config config' : DTR.GeneralRuntimeConfiguration}
    {state : LF.GeneralRuntimeState}
    {labels : List DTR.GeneralLabel}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hEnvNodup :
      ∀ candidate ∈ model.instances,
        ∀ candidateEnv : Translation.GeneralOutputPortEnv,
          (∃ candidateClass : DTR.GeneralReactiveClass,
            model.class? candidate.className =
                some candidateClass ∧
              Translation.outputPortEnvOf
                  model.classes
                  candidateClass =
                .ok candidateEnv) →
          (List.map
            (fun candidateEntry =>
              candidateEntry.outputPort.value)
            candidateEnv).Nodup)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup)
    (hConsumeAnswer :
      ∀ (stepConfig stepConfig' : DTR.GeneralRuntimeConfiguration)
        (stepState : LF.GeneralRuntimeState)
        (receiver : ActorName)
        (message : DTR.GeneralMessage),
        GeneralStateCorrespondence
          model
          stepConfig
          stepState →
        DTR.GeneralStoreKeyUnique stepConfig →
        LF.GeneralStoreKeyUnique stepState →
        DTR.GeneralStep
          model
          stepConfig
          (DTR.GeneralLabel.consume
            receiver
            message)
          stepConfig' →
        ∃ (stepState' : LF.GeneralRuntimeState)
          (event : LF.GeneralPendingEvent),
          Common.WeakStep
              (LF.GeneralStepModulo program)
              LF.GeneralLabel.isTau
              stepState
              (LF.GeneralLabel.consume
                event.target
                event.kind)
              stepState' ∧
            GeneralConsumeMatch
              receiver
              message
              event ∧
            GeneralStateCorrespondence
              model
              stepConfig'
              stepState' ∧
            LF.GeneralStoreKeyUnique stepState')
    (hCorrespondence :
      GeneralStateCorrespondence
        model
        config
        state)
    (hUniqueS :
      DTR.GeneralStoreKeyUnique config)
    (hUniqueT :
      LF.GeneralStoreKeyUnique state)
    (hBlock :
      generalInstantBlock_source
        model
        t
        config
        config'
        labels) :
    ∃ (occurrences : List LF.GeneralPendingEvent)
      (state' : LF.GeneralRuntimeState),
      Common.WeakSteps
          (LF.GeneralStepModulo program)
          LF.GeneralLabel.isTau
          state
          (blockLabels occurrences)
          state' ∧
        generalConsumeBlockMatch
          labels
          occurrences ∧
        GeneralStateCorrespondence
          model
          config'
          state' ∧
        LF.GeneralStoreKeyUnique state' := by

  obtain ⟨_, hSteps, hLabels, _, _, _⟩ :=
    hBlock

  refine
    generalInstantBlock_forward
      hCompiled
      hRoutes
      hEnvNodup
      hNames
      hConsumeAnswer
      hCorrespondence
      hUniqueS
      hUniqueT
      ?_
      hSteps

  intro label hLabel

  obtain ⟨receiver, message, hLabelShape, _⟩ :=
    hLabels
      label
      hLabel

  exact
    ⟨receiver,
     message,
     hLabelShape⟩

end Correctness

end Relico
