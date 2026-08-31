/-
! # F27, same-reactor consume order: the source is free where the target is forced

Milestone C7's remaining decision. The question is whether, within one logical instant, the order
in which the source takes messages addressed to **one** actor is compatible with the order in which
the target can fire the corresponding events at **one** reactor. Cross-reactor order is not at issue
here — decision 0042's partial quotient already frees it, and `generalQueueSwapStep` deliberately
requires distinct targets. This module is about the same-reactor case that quotient explicitly
preserves.

## The answer, in one paragraph

The two selectors have **different strengths**, and the asymmetry is one-directional. The target's
`LF.GeneralRuntimeState.earliestPendingEvent?` is a *function of the state*, so
`LF.GeneralStep.fire`'s `hSelected` pins one event outright: at any state, the fired event — and
with it the `.consume` label — is uniquely determined. The source's
`DTR.GeneralActorSelection.selectedActor` fixes only an actor **and a logical time**, and
`DTR.GeneralStep.take`'s `hDue` reaches *any* position of that actor's bag through
`earlier ++ message :: later`; every message whose arrival equals the selected time is therefore
takeable. So where two messages for one actor share an arrival, the source branches and the target
does not. `LF.GeneralStep.fire`'s own docstring already says this — *"This is tighter than the
source"* — and this module is that sentence made into two theorems.

The consequence for the block transfer is that the source's admissible same-reactor orders are a
**superset** of the target's single order, never a conflicting one. That rules out a genuine
counterexample: the target's forced order is always one the source can realize, because the source
can realize every order. What it does not do is make the per-reactor pairing *derivable*, since the
source execution actually under transfer may be one of the others.

## Why this is classification C, not B and not D

**Not D.** A counterexample would need a source execution whose same-reactor order the target cannot
produce. Time-order agreement is already the landed no-overdue/tag-alignment invariant, and within
one time the source is free, so no source order is forced against the target. The obstruction is
source nondeterminism, not disagreement.

**Not B.** The natural static condition — no reactor receiving two same-arrival messages in one
instant — is exactly decision 0042's rejected alternative (d), and it would refuse `fan-in`, whose
three `@priority`-ordered sensors all send `collect` with zero delay at time 1 and so hand
`gateway0` three arrival-1 messages with payloads 10, 20 and 30. `fan-in` is one of the four
fixtures eligible for everything, and 0042 names it as one of the two corpus models where actor
priority is irreducible. A condition that refuses it is not a fragment restriction but a retreat
from the delivered scope.

**C.** The per-reactor pairing is a **premise** of the forward block transfer, and the premise
already exists: `Correctness.generalConsumeBlockMatch`, per-reactor `Forall2 (GeneralConsumeMatch
actor)` over the two pure extractions. No new predicate is introduced, because introducing one
would duplicate that definition at a different granularity — and the pairing is already
occurrence-sensitive (positional, so multiplicity and same-reactor order are both facts of the
`Forall2`), already same-reactor only (no conjunct mentions two actors), and already F78-safe (the
kind is read off the event as fired, never mapped from a payload). What F27 settles is its
**status**: it is assumed, and `takeConsumeLabel_branches` below is why it must be, while
`consumeLabel_unique_of_step` is why the assumption is about the source and not the target.

The premise is satisfiable rather than vacuous, and the reason it is satisfiable is **not** a reason
it can be dropped. The two transfer directions consume this result differently, and conflating them
is the mistake to avoid:

**Forward, DTR → LF.** A particular source block is *given*. The source may have chosen a
same-reactor order different from the one the target's scheduler forces, and forward transfer can
neither reconstruct nor replace the source execution it was handed. So forward transfer must
**require or establish `generalConsumeBlockMatch` for that particular source block and target
block** — F27 is a genuine execution-specific compatibility premise there. Source freedom does not
remove this premise; it is what creates the need for it.

**Backward, LF → DTR.** A particular target block is *given*, and here the freedom is a
constructive asset. Every target-forced same-reactor order is one of the source-admissible orders, so
the backward proof can *build* a source block that consumes messages in the target's per-reactor
occurrence order, using `take_of_split` to reach each message wherever it sits in the bag. Backward
transfer should therefore not need an independent F27 ordering assumption merely to choose the source
consume order, provided the other correspondence and precondition obligations are met.

## The six shapes, decided against the actual definitions

1. **Two already-pending source messages to one actor at one arrival.** Source: both takeable,
   `takeConsumeLabel_branches`. Target: one label, `consumeLabel_unique_of_step`. Not forced on the
   source; forced on the target.
2. **Two target events to one reactor at the exact same full tag.** Target order is forced —
   `LF.selectEarliestEvent` keeps its incumbent when `Tag.PrecedesOrEqual` holds, which at equal tags
   it does by reflexivity, so the fold returns the queue-earliest of the tied events and insertion
   order decides. F80 measured that real `lfc` also orders same-reactor reactions, so this forcing is
   faithful rather than an artefact — which is exactly why 0042's quotient preserves it.
3. **Two target events to one reactor at one time but different microsteps.** Forced, and forced
   *twice over*: the microstep conjunct of `Tag.PrecedesOrEqual` orders them, and they cannot even be
   at the current tag simultaneously, so `LF.GeneralStep.fire`'s `hTag` admits only the earlier one
   until `microstepAdvance` moves the tag. The source cannot see microsteps at all (`LogicalTime` has
   no microstep component), so it treats both as one instant and branches.
4. **Zero-delay same-reactor chain.** A body's `setPort`/`schedule` at delay zero produces
   `LF.Tag.schedule tag ⟨0⟩ = ⟨tag.time, tag.microstep + 1⟩`, strictly later, so the created event
   cannot tie with the event being consumed — case 3, and causally ordered. No new freedom.
5. **Two distinct senders into one receiver at one logical time.** Case 2 if their delays coincide,
   case 3 otherwise. This is the `fan-in` shape (see `takeConsumeLabel_branches`).
6. **Self-send plus external send to one reactor at one logical time.** Same two cases; the kinds
   differ (`.logicalAction` versus `.inputPort`) but neither selector consults the kind, so the shape
   adds nothing beyond 2 and 3. Worth stating because it is where a payload-to-kind shortcut would be
   tempting, and F78 forbids one.

In every shape the target's order is forced and the source's is free. No shape produces a source
order the target cannot realize, which is the absence of a counterexample; no shape lets the source
order be *derived*, which is why the pairing is a premise.

## Scope

Nothing here changes a semantics. Neither selector is touched, α and `LF.GeneralStepModulo` are
untouched (widening α to swap same-target events is exactly what 0042's partial quotient forbids,
because F80 measured that real `lfc` *does* order same-reactor reactions), no well-formedness clause
is added, and no block-transfer theorem is stated.
-/
import Relico.DTR.GeneralSemantics
import Relico.LF.GeneralSemantics
import Relico.Correctness.GeneralInstantBlock

set_option autoImplicit false

namespace Relico

namespace LF

/-!
## The target is forced

Two theorems. The first makes case 2 of the header concrete — at an exact tag tie the fold keeps its
incumbent, so queue insertion order decides — and the second is the uniqueness statement that is the
target's whole contribution to F27: at a fixed state there is nothing to choose.
-/

/--
At an exact tag tie the scheduler keeps the incumbent, so insertion order decides.

Case 2 of the header, as a theorem rather than as prose. `LF.selectEarliestEvent` keeps its
incumbent whenever `LF.Tag.PrecedesOrEqual best.tag candidate.tag` holds, and at equal tags it holds
by reflexivity — so of two same-full-tag events aimed at one reactor, the fold returns whichever the
queue holds earlier, and the later one waits.

This is the ordering F80 measured real `lfc` to have (declaration order among same-reactor
reactions) and therefore the one decision 0042's *partial* quotient deliberately preserves rather
than quotienting away. Widening α to permit same-target swaps would erase exactly this fact, which is
why `generalQueueSwapStep` requires distinct targets.
-/
theorem selectEarliestEvent_keeps_incumbent_of_tagTie
    {best candidate : LF.GeneralPendingEvent}
    (remaining : LF.GeneralEventQueue)
    (hTie :
      best.tag = candidate.tag) :
    LF.selectEarliestEvent
        best
        (candidate :: remaining) =
      LF.selectEarliestEvent
        best
        remaining :=
  LF.selectEarliestEvent_cons_of_precedesOrEqual
    remaining
    (by
      rw [hTie]

      exact
        LF.Tag.precedesOrEqual_refl
          candidate.tag)

/--
At one state, every `.consume` step carries the same label.

`LF.GeneralStep.fire` is the only rule producing `.consume`, and its `hSelected` premise is an
equation on `LF.GeneralRuntimeState.earliestPendingEvent?` — a function of the state — so two fire
steps from one state select the *same* event, and the label is `.consume event.target event.kind`
of that one event. Same-reactor order is therefore not merely constrained on the target, it is
determined.

Stated on the label rather than on the successor state deliberately. The successor is determined
too, but by more than the scheduler — the reaction lookup and the parameter binding also enter, and
a caller reasoning about block order wants the observable, which is what the block extractions
read.

Note what this does **not** say: that the state has a `.consume` step at all. Enablement needs the
tag to match, the reactor to be idle, and a reaction to exist; a queue whose earliest event has no
matching reaction deadlocks by design (F64). This is a uniqueness statement, so both steps are
hypotheses.
-/
theorem consumeLabel_unique_of_step
    {program : LF.GeneralProgram}
    {state stateFirst stateSecond : GeneralRuntimeState}
    {targetFirst targetSecond : ActorName}
    {kindFirst kindSecond : LF.GeneralEventKind}
    (hFirst :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume
          targetFirst
          kindFirst)
        stateFirst)
    (hSecond :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume
          targetSecond
          kindSecond)
        stateSecond) :
    targetFirst = targetSecond ∧
      kindFirst = kindSecond := by

  cases hFirst with

  | fire hSelectedFirst _ _ _ _ _ =>

      cases hSecond with

      | fire hSelectedSecond _ _ _ _ _ =>

          rw [
            hSelectedFirst
          ] at hSelectedSecond

          obtain rfl :=
            Option.some.inj hSelectedSecond

          exact ⟨rfl, rfl⟩

end LF

namespace DTR

/-!
## The source is free

Two theorems. The first is `DTR.GeneralStep.take` restated as an availability fact — *any* position
of the selected actor's bag at the selected time is takeable — and the second spends it twice to
exhibit the branch.
-/

/--
Any due message of the selected actor is takeable, wherever it sits in the bag.

The `take` constructor read as an availability statement. It is `take` itself and carries no
content beyond it; it exists so that the branching theorem below can apply the rule twice without
restating seven premises twice, and so that the availability reading — the one F27 is about — has a
name.

`hDue` is the load-bearing premise and the reason this reads as freedom rather than as determinism:
the bag is split as `earlier ++ message :: later`, so the rule reaches every position.
`DTR.earliestDueArrival` scans the whole bag for the minimum arrival, so a rule that took the head
instead would have been a silent defect — and it is precisely that generality which leaves the
same-arrival choice open.

**This is the backward direction's constructive asset.** Given a target block, backward transfer can
build a source block consuming in the target's per-reactor occurrence order, reaching each message
wherever it sits by instantiating `earlier`/`later` accordingly. It buys the forward direction
nothing, for the reason the header gives: forward is handed a source block it cannot rechoose.
-/
theorem take_of_split
    {model : DTR.GeneralModel}
    {config : GeneralRuntimeConfiguration}
    {actorName : ActorName}
    {actor : GeneralActorRuntime}
    {selected :
      GlobalMultiStorePayloadActorPriority.ReadyActor}
    {message : DTR.GeneralMessage}
    {earlier later : DTR.GeneralMessageBag}
    {server : DTR.GeneralMessageServer}
    (hSelected :
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected)
    (hName :
      selected.actorName = actorName)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hIdle :
      actor.idle = true)
    (hDue :
      actor.state.bag =
        earlier ++ message :: later)
    (hArrival :
      message.arrival = selected.logicalTime)
    (hServer :
      DTR.GeneralModel.messageServerFor?
          model
          actorName
          message.messageName =
        some server) :
    GeneralStep
      model
      config
      (DTR.GeneralLabel.consume
        actorName
        message)
      {
        now := config.now
        actors :=
          Store.update
            config.actors
            actorName
            {
              state :=
                {
                  valuation :=
                    bindParameters
                      server.parameters
                      message.payload
                      actor.state.valuation
                  bag := earlier ++ later
                }
              activeBody := server.body
            }
      } :=
  GeneralStep.take
    hSelected
    hName
    hActor
    hIdle
    hDue
    hArrival
    hServer

/--
**F27's non-derivability, as a theorem.** When the selected actor's bag holds two messages at the
selected time, the source has a `.consume` step for **each** of them.

This is what makes the per-reactor pairing a premise rather than a conclusion. The target, by
`LF.consumeLabel_unique_of_step`, offers one label at its state; the source offers at least two, and
nothing in the source semantics prefers either. A forward transfer that had to answer *every* source
step would therefore have to answer a step whose label the target cannot produce — not because the
target disagrees, but because the source branched.

The two decompositions are the same bag read two ways: `pre ++ first :: mid ++ second :: post`
splits at `first` as written, and at `second` by re-associating the prefix to
`(pre ++ first :: mid) ++ second :: post`. That is why the hypothesis is a single three-way split
rather than two independent ones — two independent splits of one bag would be a weaker statement
that could not be instantiated without proving they describe the same list.

Both messages need a resolvable message server, because `take` refuses without one; they may be
different servers, and usually are, since two messages to one actor generally name different
message servers. Nothing here requires the two messages to be distinct: if they are equal, the two
steps are the same step and the theorem is true but says nothing, which is the honest treatment of
duplicate occurrences — no fake uniqueness is assumed and no occurrence is collapsed.

The `fan-in` fixture is the concrete shape, and it is the *same-full-tag* one. Its three
`@priority`-ordered sensors each schedule `self.sample() after(1)` from their constructor, so three
sample events sit at tag `(1, 0)`; each firing runs `gateway.collect(reading)` with zero delay, and
`LF.Tag.schedule` at delay zero advances the microstep, so all three `collect` events land at tag
`(1, 1)` — one reactor, one full tag, three events. Source-side, `gateway0`'s bag then holds three
arrival-1 messages carrying 10, 20 and 30. The target's order among the three is fixed by
`LF.selectEarliestEvent` keeping its incumbent on a tie, hence by queue insertion order, hence by
the order the sensors fired; the source may take the three in any order at all. Since
`GeneralConsumeMatch` pins the compiled payload, those orders are observably different, and the
pairing distinguishes them.
-/
theorem takeConsumeLabel_branches
    {model : DTR.GeneralModel}
    {config : GeneralRuntimeConfiguration}
    {actorName : ActorName}
    {actor : GeneralActorRuntime}
    {selected :
      GlobalMultiStorePayloadActorPriority.ReadyActor}
    {first second : DTR.GeneralMessage}
    {pre mid post : DTR.GeneralMessageBag}
    {serverFirst serverSecond : DTR.GeneralMessageServer}
    (hSelected :
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected)
    (hName :
      selected.actorName = actorName)
    (hActor :
      Store.lookup config.actors actorName =
        some actor)
    (hIdle :
      actor.idle = true)
    (hDue :
      actor.state.bag =
        pre ++ first :: (mid ++ second :: post))
    (hFirstArrival :
      first.arrival = selected.logicalTime)
    (hSecondArrival :
      second.arrival = selected.logicalTime)
    (hFirstServer :
      DTR.GeneralModel.messageServerFor?
          model
          actorName
          first.messageName =
        some serverFirst)
    (hSecondServer :
      DTR.GeneralModel.messageServerFor?
          model
          actorName
          second.messageName =
        some serverSecond) :
    (∃ configFirst,
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume
          actorName
          first)
        configFirst) ∧
    (∃ configSecond,
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume
          actorName
          second)
        configSecond) := by

  have hSecondDue :
      actor.state.bag =
        (pre ++ first :: mid) ++ second :: post := by
    rw [hDue]

    simp

  exact
    ⟨⟨_,
      take_of_split
        hSelected
        hName
        hActor
        hIdle
        hDue
        hFirstArrival
        hFirstServer⟩,
     ⟨_,
      take_of_split
        hSelected
        hName
        hActor
        hIdle
        hSecondDue
        hSecondArrival
        hSecondServer⟩⟩

end DTR

namespace Correctness

/-!
## What the block transfer inherits

No new predicate. `generalConsumeBlockMatch` is already the per-reactor, occurrence-sensitive,
same-reactor-only, F78-safe pairing F27 needs, and the settled result is that it is a **forward
premise**: forward transfer is handed a source block and must require or establish the pairing for
that block against the target block. Backward transfer is the other way round and does not need an
independent F27 ordering assumption to pick its source order, because it constructs that order from
the target's occurrences via `DTR.take_of_split`.

The theorem below records the one property of the premise a future forward wrapper has to know
beyond its statement: it is satisfiable, and satisfiable at every reactor simultaneously.
-/

/--
The F27 premise is satisfiable: an empty block pairs with an empty occurrence list.

Thin, and deliberately so — it is `generalConsumeBlockMatch.nil` under a name that says why this
module cites it. `docs/STAGE_G_FINDINGS.md` F66 part 5 is a finding about a relation conjunct that
was trivially true at the initial state and load-bearing after a step, and F86 is that trap's mirror
image; a milestone that settled F27 by making the pairing a premise without ever exhibiting the
premise satisfied would be inviting the same defect a third time.

Satisfiability at the interesting shape is not stated here, because stating it would require
exhibiting a block, which is block transfer's job and out of this milestone's scope. What
`DTR.takeConsumeLabel_branches` and `LF.consumeLabel_unique_of_step` establish between them is that
the interesting case *is* satisfiable — the target's order is forced and the source can realize every
order, so the source can realize that one. Note the direction of that argument: it shows the pairing
is inhabited, which is what the **backward** construction exploits. It does not let the **forward**
direction discharge the premise, since forward does not get to choose the source order it is given.
-/
theorem generalConsumeBlockMatch_satisfiable :
    generalConsumeBlockMatch
      []
      [] :=
  generalConsumeBlockMatch.nil

end Correctness

end Relico
