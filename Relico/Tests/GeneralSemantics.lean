import Relico.Common.WeakTransition
import Relico.DTR.GeneralSemantics
import Relico.LF.GeneralSemantics
import Relico.Correctness.GeneralCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GeneralSemantics

/-!
# Compile-time pins for the two general step relations

`docs/STAGE_G_DESIGN.md` §13, obligation G2a-iii. `Relico/DTR/GeneralSemantics.lean` and
`Relico/LF/GeneralSemantics.lean` declare the two step relations, their scheduler and lookup functions, and
the inversion lemmas. This module pins what those theorems are structurally unable to see.

The standard every pin below is held to is `docs/STAGE_F_FINDINGS.md` F60's: **a pin earns its place only if
some specific wrong implementation fails it.** That is why the section "What is deliberately not pinned" at
the end is as long as it is — several obvious-looking assertions are invariant under the very thing they
would appear to check, and F60 records one that shipped.

## The headline is P24's zero-delay case, and it is pinned as a witness rather than as arithmetic

`Relico/LF/GeneralSemantics.lean`'s module docstring promises that this file "pins the zero-delay case as a
regression so the two halves cannot be silently re-merged". Tests 6 through 10 are that promise.

The chain is three steps and it is the whole of P24 made checkable. A `schedule` with **zero** delay enqueues
an event at the same logical time and the next microstep (test 6). Reaching that event is a
`microstepAdvance`, which carries `.tau` (test 7), and `now` is therefore unchanged across it (test 8) even
though the state itself has changed (test 9). Contrast a **positive** delay: the same three steps produce a
`timeAdvance` label carrying two distinct times (test 10).

Merge the two advance rules back into one — which is exactly the single observable `TIME PROGRESS` the
paper's Table II implies, and exactly what makes its Theorem 1 false — and tests 7 and 8 stop compiling,
because there is no longer a τ-labelled step to build or a τ-labelled hypothesis to feed
`now_eq_of_tau`. That is the regression this file exists to catch.

Note the direction the states are written in. Each post-state below is a **hand-written literal**, and the
step is then proved to relate the two. Deriving the post-state from the rule would make every one of these
`rfl` by construction and would pin nothing — the wrong `Store.update`, the wrong tag, the wrong queue
position would all still pass.

## The scheduler's tie-break is pinned, because the fold is where it could be lost

Tests 1 through 5. `LF.selectEarliestEvent` keeps its incumbent on a tie, which
`LF.GeneralEventQueue`'s docstring specifies as the insertion-order tie-break. That convention lives in
exactly one character — the `≤` inside `PrecedesOrEqual` rather than a `<` — and no theorem in the module
sees it: `selectEarliestEvent_precedesOrEqual_of_mem` is satisfied by *either* choice, since both return a
minimal element. Test 3 is the only instrument that distinguishes them.

Test 2 matters for a different reason: it puts the earliest event in the queue's **tail**, so a scheduler
that returned the head would fail it. That is not a hypothetical wrong implementation. It is the defect
`Relico/DTR/GeneralSemantics.lean`'s `take` docstring records on the source side, where a head-only rule
would have been stuck exactly where the state layer says an actor may run.

## Declaration order, not priority, resolves a trigger

Test 11. Two reactions triggered by one action, the first declared carrying the *worse* priority. A lookup
that consulted `GeneralReaction.priority` returns the second; `findReactionForKind?` returns the first. Stage
F established that reaction declaration order is observable in the target and that nothing in this family
sorts a reaction list, and G3 made a populated LF reaction priority a well-formedness *violation* — so a
lookup that quietly honoured the field would contradict a property the guard now enforces.

The two reactions below are therefore, deliberately, reactions that no accepted program contains. That is
sound because the claim under test is about a *lookup* over a reaction list, and `findReactionForKind?` is
total: it does not ask whether the list came from a well-formed program. The tempting repair — setting both
literals to `none` so the witnesses satisfy the new conjunct — would make this test **vacuous**, which is
exactly the failure mode F60 records and the reason the `decide` pin below exists.

## The generic weak-transition machinery is instantiated, not merely said to be instantiable

The last five pins. Both step relations' docstrings claim, citing `docs/STAGE_G_FINDINGS.md` F70, that G2c
may instantiate `Common.TauSteps` and `Common.WeakStep` at them rather than restate either. That was a claim
about future work with nothing checking it, which is the shape `docs/STAGE_E_FINDINGS.md` F53 records: three
"by construction" claims that outlived the findings refuting them. Each of the five is an elaboration check
against a different specific mistake — the index order, a `Bool`-valued `isTau`, and a τ set that swallowed
`timeAdvance`. The `visible` pins are built with the constructor rather than `Common.WeakStep.of_step`,
because `of_step` splits classically on the τ classification and so elaborates whichever way that
classification goes, making it invariant under the thing being pinned.
-/

/-! ## Shared names -/

def probeName : ActorName :=
  ActorName.mk "probe"

def hubName : ActorName :=
  ActorName.mk "hub"

def pingActionName : ActionName :=
  ActionName.mk "ping"

def readingPortName : PortName :=
  PortName.mk "reading"

def firstReactionName : ReactionName :=
  ReactionName.mk "reaction_first"

def secondReactionName : ReactionName :=
  ReactionName.mk "reaction_second"

def zeroDelay : Delay :=
  { value := 0 }

def positiveDelay : Delay :=
  { value := 3 }

/-! ## The scheduler -/

def eventAtOne : LF.GeneralPendingEvent :=
  {
    target := probeName
    kind :=
      LF.GeneralEventKind.logicalAction
        pingActionName
    tag :=
      {
        time := 1
        microstep := 0
      }
  }

def eventAtFive : LF.GeneralPendingEvent :=
  {
    target := hubName
    kind :=
      LF.GeneralEventKind.inputPort
        readingPortName
    tag :=
      {
        time := 5
        microstep := 0
      }
  }

/--
Two events at one tag, distinguishable only by target, so a tie-break can be *observed* rather than merely
asserted.
-/
def tiedProbeEvent : LF.GeneralPendingEvent :=
  {
    target := probeName
    kind :=
      LF.GeneralEventKind.logicalAction
        pingActionName
    tag :=
      {
        time := 2
        microstep := 0
      }
  }

def tiedHubEvent : LF.GeneralPendingEvent :=
  {
    target := hubName
    kind :=
      LF.GeneralEventKind.inputPort
        readingPortName
    tag :=
      {
        time := 2
        microstep := 0
      }
  }

/--
A state carrying a given queue, with no reactors and the clock at the origin.

The scheduler consults neither the reactors nor the current tag — it folds the queue — so leaving both
trivial keeps each pin below about the one thing it is pinning.
-/
def queueState
    (pending : LF.GeneralEventQueue) :
    LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 0
        microstep := 0
      }
    reactors := []
    pending := pending
  }

/- Test 1: an empty queue selects nothing. -/
example :
    LF.GeneralRuntimeState.earliestPendingEvent?
        (queueState []) =
      none := by
  rfl

/- Test 2: the earliest event is found in the TAIL. A head-only scheduler fails here, which is the defect
   the source-side `take` docstring records. -/
example :
    LF.GeneralRuntimeState.earliestPendingEvent?
        (queueState
          [
            eventAtFive,
            eventAtOne
          ]) =
      some eventAtOne := by
  decide

/- Test 3: and it is still found when it is already the head, so test 2 is not passing by always
   returning the last element. -/
example :
    LF.GeneralRuntimeState.earliestPendingEvent?
        (queueState
          [
            eventAtOne,
            eventAtFive
          ]) =
      some eventAtOne := by
  decide

/- Test 4: at a tie the INCUMBENT wins, which is the insertion-order tie-break. A fold written
   `if candidate ≼ best then candidate else best` — or a `PrecedesOrEqual` whose second disjunct used `<`
   instead of `≤` — returns `tiedHubEvent` and fails here. No theorem in the module sees this: the
   minimality theorem is satisfied by either choice. -/
example :
    LF.GeneralRuntimeState.earliestPendingEvent?
        (queueState
          [
            tiedProbeEvent,
            tiedHubEvent
          ]) =
      some tiedProbeEvent := by
  decide

/- Test 5: reversing the two reverses the answer, so test 4 pins QUEUE POSITION and not some property of
   the probe event. A scheduler that preferred one reactor over another at equal tags — an actor priority
   the target language does not have — fails one of these two. -/
example :
    LF.GeneralRuntimeState.earliestPendingEvent?
        (queueState
          [
            tiedHubEvent,
            tiedProbeEvent
          ]) =
      some tiedHubEvent := by
  decide

/-! ## P24: the split time-progress rule -/

/--
A program with nothing in it.

Neither advance rule has a premise that mentions `program` — they read the queue and the tag and nothing
else — so the witnesses below need no reactors, and supplying some would only invite a reader to think the
rules consulted them.
-/
def emptyProgram : LF.GeneralProgram :=
  {
    reactors := []
    instances := []
    connections := []
  }

/- Test 6: the tag arithmetic that forces the split. A ZERO delay holds the logical time and advances the
   microstep... -/
example :
    LF.Tag.schedule
        {
          time := 5
          microstep := 0
        }
        zeroDelay =
      {
        time := 5
        microstep := 1
      } := by
  decide

/- ...while a POSITIVE delay advances the logical time and resets the microstep. An implementation that
   bumped the time in both cases, or the microstep in both, fails one of these two — and either way the two
   advance rules below would collapse into one. -/
example :
    LF.Tag.schedule
        {
          time := 5
          microstep := 0
        }
        positiveDelay =
      {
        time := 8
        microstep := 0
      } := by
  decide

/--
The event a zero-delay self-send made available: the *same* logical time as the sender's tag, one microstep
later.
-/
def microstepEvent : LF.GeneralPendingEvent :=
  {
    target := probeName
    kind :=
      LF.GeneralEventKind.logicalAction
        pingActionName
    tag :=
      {
        time := 5
        microstep := 1
      }
    payload := []
  }

/--
The state just before that event is reached. One event in the queue, so `earliestPendingEvent?` selects it
without a single tag comparison and the rules' `hSelected` premise closes by `rfl`.
-/
def microstepState : LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 5
        microstep := 0
      }
    reactors := []
    pending := [microstepEvent]
  }

/--
The state after, written out by hand rather than derived from the rule.

Deriving it would make the step below `rfl` by construction and pin nothing. Written this way, the wrong
destination tag, a dropped queue or a disturbed reactor store each fail to typecheck.
-/
def microstepNext : LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 5
        microstep := 1
      }
    reactors := []
    pending := [microstepEvent]
  }

/--
Test 7: reaching that event is a real step of the relation, and **its label is `.tau`**.

This is P24 made checkable. Merge the two advance rules back into the single observable `TIME PROGRESS` the
paper reads off Table II and this theorem stops typechecking, because the label it is annotated with no
longer exists on the merged rule.
-/
theorem microstepStep :
    LF.GeneralStep
      emptyProgram
      microstepState
      LF.GeneralLabel.tau
      microstepNext :=
  LF.GeneralStep.microstepAdvance
    (event := microstepEvent)
    rfl
    rfl
    (by decide)

/- Test 8: so logical time does not move across it. Proved by feeding the witness to the inversion lemma,
   which is what ties this pin to the theorem rather than to the arithmetic. -/
example :
    LF.GeneralRuntimeState.now microstepNext =
      LF.GeneralRuntimeState.now microstepState :=
  LF.GeneralStep.now_eq_of_tau
    microstepStep

/- Test 9: and yet the state DID change, so test 8 is not the empty observation that the step is a no-op.
   The tag advanced; only the part of it `now` reads stayed put. -/
example :
    microstepState ≠ microstepNext := by
  decide

/--
The contrasting event, from a positive delay: strictly later logical time.
-/
def timeEvent : LF.GeneralPendingEvent :=
  {
    target := probeName
    kind :=
      LF.GeneralEventKind.logicalAction
        pingActionName
    tag :=
      {
        time := 8
        microstep := 0
      }
    payload := []
  }

def timeState : LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 5
        microstep := 0
      }
    reactors := []
    pending := [timeEvent]
  }

def timeNext : LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 8
        microstep := 0
      }
    reactors := []
    pending := [timeEvent]
  }

/--
Test 10: the same shape of state, with the delay positive instead of zero, steps under an **observable**
label carrying both times.

Compare `microstepStep` directly above: same relation, same kind of premise, and the label differs. That
contrast is the entire content of P24, and it is now two theorems that must both continue to elaborate.
-/
theorem timeStep :
    LF.GeneralStep
      emptyProgram
      timeState
      (LF.GeneralLabel.timeAdvance 5 8)
      timeNext :=
  LF.GeneralStep.timeAdvance
    (event := timeEvent)
    rfl
    (by decide)

/- and the label's two times are genuinely ordered, read back off the witness through the inversion lemma
   rather than asserted. A rule that emitted `.timeAdvance after before` fails here. -/
example :
    (5 : LogicalTime) < 8 :=
  LF.GeneralStep.lt_of_timeAdvance
    timeStep

/-! ## Declaration order, not priority, resolves a trigger -/

/--
The reaction declared **first**, carrying the **worse** priority.
-/
def firstReaction : LF.GeneralReaction :=
  {
    name := firstReactionName
    trigger :=
      LF.GeneralTrigger.logicalAction
        pingActionName
    parameters := []
    body := []
    priority := some 9
  }

/--
The reaction declared **second**, carrying the **better** priority.
-/
def secondReaction : LF.GeneralReaction :=
  {
    name := secondReactionName
    trigger :=
      LF.GeneralTrigger.logicalAction
        pingActionName
    parameters := []
    body := []
    priority := some 1
  }

/- The instrument is only valid while the priorities run *against* declaration order. Pinned so that a later
   edit tidying these literals cannot quietly make test 11 vacuous — which is the failure mode F60 records.
   G3 gave that tidy-up a fresh motive: these two priorities are now well-formedness *violations*, so an
   author reading `reactionPrioritiesAbsent` may well reach for `none` here. This pin is what stops it. -/
example :
    firstReaction.priority = some 9 ∧
      secondReaction.priority = some 1 := by
  decide

/- Test 11: both reactions trigger on the same action, and the FIRST DECLARED one is returned. A lookup that
   consulted `GeneralReaction.priority` returns `secondReaction` and fails here. That is not a hypothetical:
   G3 made a populated LF reaction priority a well-formedness *violation*, so a lookup that honoured the
   field would contradict a property the guard now enforces. These two reactions sit in no
   `LF.GeneralProgram`, so nothing here evaluates `wellFormed` on them. -/
example :
    LF.findReactionForKind?
        [
          firstReaction,
          secondReaction
        ]
        (LF.GeneralEventKind.logicalAction
          pingActionName) =
      some firstReaction := by
  decide

/- Swapping the declaration order swaps the answer, so test 11 pins ORDER rather than something about
   `firstReaction` itself. This is the swap in which order and priority happen to agree, so a
   priority-consulting lookup passes it — which is precisely why the previous test is the load-bearing one
   and this one is only the control. -/
example :
    LF.findReactionForKind?
        [
          secondReaction,
          firstReaction
        ]
        (LF.GeneralEventKind.logicalAction
          pingActionName) =
      some secondReaction := by
  decide

/- A kind no trigger matches finds nothing rather than falling back on the first reaction. This is the
   lookup half of the deadlock G6 owes in writing: `fire` has no rule for an event whose target has no
   matching reaction, so such an event is never consumed and never discarded. -/
example :
    LF.findReactionForKind?
        [
          firstReaction,
          secondReaction
        ]
        (LF.GeneralEventKind.inputPort
          readingPortName) =
      none := by
  decide

/- And a startup trigger matches no pending event at all, which is why `reactionFor?` searches
   `messageReactions` and leaves `startupReaction` out. -/
example :
    LF.GeneralTrigger.matchesKind
        LF.GeneralTrigger.startup
        (LF.GeneralEventKind.logicalAction
          pingActionName) =
      false := by
  decide

/-! ## The source side has no internal time step -/

/--
An empty source model, the DTR counterpart of `emptyProgram`. `timeProgress` names no class or instance in
its premises, so the *model* still needs nothing populating — the configuration does, for **F74**'s reason
below.
-/
def emptyModel : DTR.GeneralModel :=
  {
    classes := []
    instances := []
  }

/-! ## Option A: internal trace steps -/

def sourceTraceActor : DTR.GeneralActorRuntime :=
  {
    state :=
      {
        valuation := []
        bag := []
      }
    activeBody := [DTR.GeneralStmt.trace "audit"]
    frames := []
  }

def sourceTraceConfig : DTR.GeneralRuntimeConfiguration :=
  {
    now := 3
    actors := [(probeName, sourceTraceActor)]
  }

def sourceTraceNext : DTR.GeneralRuntimeConfiguration :=
  {
    now := 3
    actors :=
      [
        (probeName,
          {
            state := sourceTraceActor.state
            activeBody := []
            frames := []
          })
      ]
  }

/- The source trace rule consumes only the continuation and is τ-labelled. -/
theorem sourceTraceStep :
    DTR.GeneralStep
      emptyModel
      sourceTraceConfig
      DTR.GeneralLabel.tau
      sourceTraceNext :=
  DTR.GeneralStep.trace
    (actorName := probeName)
    (actor := sourceTraceActor)
    (tag := "audit")
    (remaining := [])
    rfl
    rfl

example :
    sourceTraceNext.now = sourceTraceConfig.now :=
  DTR.GeneralStep.now_eq_of_tau sourceTraceStep

example :
    Store.lookup sourceTraceNext.actors probeName =
      some
        {
          state := sourceTraceActor.state
          activeBody := []
          frames := []
        } := by
  rfl

def targetTraceReactor : LF.GeneralReactorRuntime :=
  {
    valuation := []
    activeBody := [LF.GeneralStmt.trace "audit"]
    frames := []
  }

def targetTraceState : LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 3
        microstep := 0
      }
    reactors := [(probeName, targetTraceReactor)]
    pending := []
  }

def targetTraceNext : LF.GeneralRuntimeState :=
  {
    currentTag := targetTraceState.currentTag
    reactors :=
      [
        (probeName,
          {
            valuation := targetTraceReactor.valuation
            activeBody := []
            frames := []
          })
      ]
    pending := []
  }

/- The LF trace rule has the same τ/no-modeled-state behavior. -/
theorem targetTraceStep :
    LF.GeneralStep
      emptyProgram
      targetTraceState
      LF.GeneralLabel.tau
      targetTraceNext :=
  LF.GeneralStep.trace
    (instanceName := probeName)
    (reactor := targetTraceReactor)
    (tag := "audit")
    (remaining := [])
    rfl
    rfl

example :
    targetTraceNext.currentTag = targetTraceState.currentTag :=
  rfl

example :
    LF.GeneralRuntimeState.now targetTraceNext =
      LF.GeneralRuntimeState.now targetTraceState :=
  LF.GeneralStep.now_eq_of_tau targetTraceStep

example :
    targetTraceNext.pending = targetTraceState.pending :=
  rfl

example :
    ∀ event : LF.GeneralPendingEvent,
      event ∈ targetTraceNext.pending →
        event ∈ targetTraceState.pending ∨
          LF.Tag.PrecedesOrEqual
            targetTraceState.currentTag
            event.tag :=
  LF.GeneralStep.tau_pending_not_past targetTraceStep

example :
    targetTraceNext.pending = targetTraceState.pending ∨
      ∃ event : LF.GeneralPendingEvent,
        targetTraceNext.pending = targetTraceState.pending ++ [event] ∧
          LF.Tag.StrictlyPrecedes
            targetTraceState.currentTag
            event.tag :=
  LF.GeneralStep.tau_enqueue_strictly_future targetTraceStep

example :
    Store.lookup targetTraceNext.reactors probeName =
      some
        {
          valuation := targetTraceReactor.valuation
          activeBody := []
          frames := []
        } := by
  rfl

/-! ## Stage I: the target local declaration step -/

/--
The reactor under test: one `int temporary = 1;` declaration as its whole active body, an otherwise empty
valuation, no frames. The initialiser is a literal so the `hEvaluate` premise is `rfl` — the pin is about
the rule's plumbing, not about evaluation, which `assign`'s own tests already cover.
-/
def targetLocalDeclReactor : LF.GeneralReactorRuntime :=
  {
    valuation := []
    activeBody :=
      [
        LF.GeneralStmt.localDecl
          (VarName.mk "temporary")
          .int
          (LF.GeneralExpr.intLiteral 1)
      ]
    frames := []
  }

def targetLocalDeclState : LF.GeneralRuntimeState :=
  {
    currentTag :=
      {
        time := 3
        microstep := 0
      }
    reactors := [(probeName, targetLocalDeclReactor)]
    pending := []
  }

/--
The state after, hand-written rather than derived: the binding is in the valuation at the declared name,
the body is spent, the frames and the queue are untouched. A rule that forgot the binding, bound the wrong
name, kept the statement, or touched the queue each fails here by typechecking against the wrong literal.
-/
def targetLocalDeclNext : LF.GeneralRuntimeState :=
  {
    currentTag := targetLocalDeclState.currentTag
    reactors :=
      [
        (probeName,
          {
            valuation :=
              [
                (VarName.mk "temporary",
                  LF.GeneralValue.int 1)
              ]
            activeBody := []
            frames := []
          })
      ]
    pending := []
  }

/- The step itself: τ-labelled, `assign`-shaped, one rule application with `rfl` premises. -/
theorem targetLocalDeclStep :
    LF.GeneralStep
      emptyProgram
      targetLocalDeclState
      LF.GeneralLabel.tau
      targetLocalDeclNext :=
  LF.GeneralStep.localDecl
    (instanceName := probeName)
    (reactor := targetLocalDeclReactor)
    (name := VarName.mk "temporary")
    (declaredType := .int)
    (expression := LF.GeneralExpr.intLiteral 1)
    (remaining := [])
    (value := LF.GeneralValue.int 1)
    rfl
    rfl
    rfl

/- Test: logical time does not move, tying the new rule to the τ inversion lemma the same way the trace
   and conditional pins tie theirs. -/
example :
    LF.GeneralRuntimeState.now targetLocalDeclNext =
      LF.GeneralRuntimeState.now targetLocalDeclState :=
  LF.GeneralStep.now_eq_of_tau targetLocalDeclStep

/- Test: the binding really landed, at the declared name and nowhere else — the whole point of the rule,
   and the property a `trace`-shaped mis-implementation (drop the head, copy everything) would silently
   satisfy. -/
example :
    Store.lookup targetLocalDeclNext.reactors probeName =
      some
        {
          valuation :=
            [
              (VarName.mk "temporary",
                LF.GeneralValue.int 1)
            ]
          activeBody := []
          frames := []
        } := by
  rfl

/- The compiler/correspondence continuation fact is live on the same one-statement body. -/
def traceContinuationCompiles :
    Correctness.GeneralContinuationCompiles
      []
      [DTR.GeneralStmt.trace "audit"]
      [LF.GeneralStmt.trace "audit"] :=
  ⟨default,
   0,
   by rfl,
   by
     -- The one statement is a trace, so no path of this body reaches an external send and the site
     -- obligation is vacuous. This pin is the regression witness that the strengthened relation stays
     -- inhabited on a real compiled body; stage H made the obligation a path derivation, so the
     -- refutation is now one `cases` per constructor rather than one per index.
     intro _ _ _ _ hPath

     cases hPath with

     | @here _ position _ _ _ _ _ hDrop =>
         cases position <;> simp at hDrop

     | @thenBranch _ position _ _ _ _ _ _ _ _ hDrop _ =>
         cases position <;> simp at hDrop

     | @elseBranch _ position _ _ _ _ _ _ _ _ hDrop _ =>
         cases position <;> simp at hDrop⟩

example :
    Correctness.GeneralContinuationCompiles
      []
      []
      [] :=
  Correctness.generalContinuationCompiles_trace_tail
    traceContinuationCompiles

def futureMessageName : MsgName :=
  MsgName.mk "tick"

/--
The one message these configurations hold, arriving strictly after their clock.

**F74.** Before the repair this section ran on an empty configuration. `timeProgress` constrained `future`
only by `config.now < future`, so `now := 5 → 8` elaborated with no message at `8` — with no message
anywhere at all. That is the defect written as a witness: the source could advance to a time nothing was
waiting for, and could advance *past* a time something was. The repaired rule advances to
`DTR.GeneralConfiguration.nextArrival`, so a source time step now has to name the arrival it advances to,
and this message is it.

Its arrival is `8`, the tag time of `timeEvent` on the target side, so `sourceTimeStep` and `timeStep` carry
one label over one pair of times — the matched observable pair G2b's time case is about.
-/
def futureMessage : DTR.GeneralMessage :=
  {
    sender := hubName
    messageName := futureMessageName
    payload := []
    arrival := 8
  }

/--
A source configuration at time 5 whose single actor holds `futureMessage`.

Both premises about the bag are live here, and they read the same bag in opposite directions, which is the
point. `readyActors` is `[]` because `DTR.earliestDueArrival` keeps only messages with `arrival ≤ now` and
`8 ≤ 5` is false, so nothing is takeable and the clock *may* move. `nextArrival` is `some 8` because
`DTR.earliestFutureArrival` keeps exactly the complement, so the clock may move *only* to `8`. An empty bag
satisfies the first and refutes the second: under the repaired rule time cannot pass in a configuration with
nothing pending, which is what the target has always required of itself — `LF.GeneralStep.timeAdvance` needs
an event in the queue to advance to.
-/
def sourceConfig : DTR.GeneralRuntimeConfiguration :=
  {
    now := 5
    actors :=
      [
        (probeName,
          {
            state :=
              {
                valuation := []
                bag := [futureMessage]
              }
            activeBody := []
            frames := []
          })
      ]
  }

/--
The same actors at the advanced time. `timeProgress` copies the store, so this is `sourceConfig.actors`
rather than a second literal — a copy could drift and the rule would then simply not apply.
-/
def sourceNext : DTR.GeneralRuntimeConfiguration :=
  {
    now := 8
    actors := sourceConfig.actors
  }

/--
The **only** time step the source relation has, and it is `timeAdvance` — observable.

This is the far side of P24. `microstepStep` above is an LF step at a τ label with no logical-time motion;
there is no rule on this side that could match it, because `LogicalTime` has no microstep and this relation
advances the clock or does nothing. A reader tempted to give the source an internal time step to restore
Theorem 1 has to add a rule here, and this witness is what that reader's edit would sit beside.

**Three premises, since F74.** The third pins `future` to `nextArrival`, and it is the one a reader will be
tempted to drop as redundant — quiescence sounds like it should already forbid stepping over an arrival. It
does not: quiescence is about messages at or before `now`, `nextArrival` is about messages after it, and the
two ranges do not meet. Deleting the third premise makes this witness *easier*, not harder, which is why the
defect it records survived a whole commit.
-/
theorem sourceTimeStep :
    DTR.GeneralStep
      emptyModel
      sourceConfig
      (DTR.GeneralLabel.timeAdvance 5 8)
      sourceNext :=
  DTR.GeneralStep.timeProgress
    (by decide)
    (by decide)
    (by decide)

/- and the advance really is pinned to the bag, read back off the witness through the new inversion lemma
   rather than asserted. A rule that let the clock run to an arbitrary later time cannot prove this. -/
example :
    DTR.GeneralConfiguration.nextArrival
        sourceConfig.erase =
      some 8 :=
  DTR.GeneralStep.selected_of_timeAdvance
    sourceTimeStep

/- Its label is NOT internal: the source's time motion is always observable. Contrast `microstepStep`'s
   `.tau`. The two together are the whole reason the merged single `TIME PROGRESS` of the paper's Table II
   is unsound and the split is not. -/
example :
    ¬ DTR.GeneralLabel.isTau
        (DTR.GeneralLabel.timeAdvance 5 8) :=
  DTR.GeneralLabel.not_isTau_timeAdvance 5 8

/- and the LF observable time step's label is likewise not internal, so `timeStep` and `sourceTimeStep` are
   a matched observable pair while `microstepStep` stands alone. -/
example :
    ¬ LF.GeneralLabel.isTau
        (LF.GeneralLabel.timeAdvance 5 8) :=
  LF.GeneralLabel.not_isTau_timeAdvance 5 8

/- whereas the LF microstep step's label IS internal — the asymmetry stated as a fact about the two labels
   rather than about the rules that emit them. -/
example :
    LF.GeneralLabel.isTau LF.GeneralLabel.tau :=
  LF.GeneralLabel.isTau_tau

/-! ## Both relations instantiate the generic weak-transition machinery -/

/-
Each step relation's docstring states, citing F70, that G2c may **instantiate** `Common.TauSteps` and
`Common.WeakStep` at it rather than restate either. Until these five pins, that was a claim about future work
with nothing checking it — the same shape as the "by construction" claims F53 records, which outlived the
findings that refuted them. Every pin below is an elaboration check, and each fails under a different
specific mistake.

First: the partial application at a fixed program really is a `Common.LabeledTransition`. This is the F70
constraint itself, and it is the one pin that a *declaration* error breaks rather than a proof error — a
relation indexed `State → State → Label → Prop`, which is the order a reader would reach for if they thought
of a labelled step as "a step, labelled", does not inhabit this type.
-/
example :
    Common.LabeledTransition
      LF.GeneralRuntimeState
      LF.GeneralLabel :=
  LF.GeneralStep emptyProgram

example :
    Common.LabeledTransition
      DTR.GeneralRuntimeConfiguration
      DTR.GeneralLabel :=
  DTR.GeneralStep emptyModel

/- Second: a τ step closes into the internal-closure relation. `TauSteps.single` wants `isTau label` as a
   *proposition*, so an `isTau` returning `Bool` — which is how a reader coming from `matchesKind` next door
   would write it — fails here rather than three obligations later in G2c. -/
example :
    Common.TauSteps
      (LF.GeneralStep emptyProgram)
      LF.GeneralLabel.isTau
      microstepState
      microstepNext :=
  Common.TauSteps.single
    microstepStep
    LF.GeneralLabel.isTau_tau

/- Third, and this is P24 at the weak level: the microstep advance is absorbed into a weak step whose label is
   internal, so a bisimulation may match it with *nothing* on the source side. That is precisely the
   permission the paper's merged observable `TIME PROGRESS` would deny, and it is what makes the split sound
   rather than merely convenient. -/
example :
    Common.WeakStep
      (LF.GeneralStep emptyProgram)
      LF.GeneralLabel.isTau
      microstepState
      LF.GeneralLabel.tau
      microstepNext :=
  Common.WeakStep.tau
    LF.GeneralLabel.isTau_tau
    (Common.TauSteps.single
      microstepStep
      LF.GeneralLabel.isTau_tau)

/- Fourth and fifth: the two observable time steps are weak steps of the `visible` shape, one per language.
   Built with the constructor rather than through `Common.WeakStep.of_step`, deliberately — `of_step` decides
   the two cases with `classical` `by_cases` and so elaborates *whatever* the τ classification says, which
   would make it invariant under the very thing being pinned. `visible` demands `¬ isTau label` as an
   argument, so a τ set that wrongly swallowed `timeAdvance` fails these two and nothing else in the file
   would notice. -/
example :
    Common.WeakStep
      (LF.GeneralStep emptyProgram)
      LF.GeneralLabel.isTau
      timeState
      (LF.GeneralLabel.timeAdvance 5 8)
      timeNext :=
  Common.WeakStep.visible
    (LF.GeneralLabel.not_isTau_timeAdvance 5 8)
    (Common.TauSteps.refl timeState)
    timeStep
    (Common.TauSteps.refl timeNext)

example :
    Common.WeakStep
      (DTR.GeneralStep emptyModel)
      DTR.GeneralLabel.isTau
      sourceConfig
      (DTR.GeneralLabel.timeAdvance 5 8)
      sourceNext :=
  Common.WeakStep.visible
    (DTR.GeneralLabel.not_isTau_timeAdvance 5 8)
    (Common.TauSteps.refl sourceConfig)
    sourceTimeStep
    (Common.TauSteps.refl sourceNext)

end GeneralSemantics
end Tests
end Relico
