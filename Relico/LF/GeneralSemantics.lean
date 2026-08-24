import Relico.LF.GeneralEvaluation
import Relico.LF.GeneralRuntime
import Relico.LF.PendingNotPast

set_option autoImplicit false

namespace Relico
namespace LF

/-!
# The target step relation for the general family

Obligation G2a-iii, target side. `Relico/LF/GeneralRuntime.lean` holds the state a target program executes
in and the label a step carries; this module holds the **rules**, the scheduler that picks the next event,
and the trigger matching that decides which reaction a fired event runs. The split follows
`Relico/LF/DetailedMultiStorePayloadRuntime.lean` and its `…Semantics.lean` companion, and mirrors
`Relico/DTR/GeneralSemantics.lean` on the source side.

## Six rules where the source has four

The source's four rules are `assign`, `send`, `take` and `timeProgress`. Two of them split here.

`SEND` splits because the target has two send mechanisms and §III-E chooses between them by what the
statement *is*: a self-send becomes a `schedule` of a logical action, an external send becomes a `setPort`
that travels a connection. Both are τ, so the split is invisible in the label alphabet and visible only in
the rules.

`TIME PROGRESS` splits because a target tag has a microstep. **This is P24.** An advance that increases the
microstep and leaves the time alone is τ — it has no source counterpart, because `LogicalTime` has no
microstep to advance — while an advance that increases the time is observable and carries `.timeAdvance`.
The paper's Theorem 1 is false for a zero-delay send precisely because it reads a single observable
`TIME PROGRESS` off Table II; splitting the rule here is the repair, and `Relico/Tests/GeneralSemantics.lean`
pins the zero-delay case as a regression so the two halves cannot be silently re-merged.

Conditionals are absent on both sides: `LF.GeneralStmt` has no conditional and `LF.GeneralBody` is a flat
list, so stage G proves the conditional-free sub-fragment. `docs/STAGE_G_DESIGN.md` §7 states the
restriction and G6 owes its declaration.

## Why the scheduler lives here and not with the runtime state

`Relico/LF/GeneralRuntime.lean` records the decision under "What is deliberately absent": the selection of
the earliest pending event is scheduler work, its source-side counterpart is G1's `selectMinimum` in
`Relico/DTR/GeneralActorSelection.lean` — a scheduler module, not a runtime module — and adding a fourth
module to G2a-ii would have moved a job count the work plan predicts. So it is here, and it is deliberately
the *same shape* as G1's: an accumulator fold that keeps the incumbent on a tie.

Keeping the incumbent is not an arbitrary tie-break. `GeneralEventQueue`'s own docstring says the queue is
held in insertion order because "insertion order is the tie-break for events sharing a tag", and
`if best ≼ candidate then best else candidate` is exactly what preserves it — `PrecedesOrEqual` is
reflexive, so two events at one tag resolve to the earlier-inserted one.

The three facts a fold like this needs — decidability to compute, totality to know a minimum exists,
transitivity to know the computed one is least — were added to `namespace Tag` by G2a-ii *for this
module*. They are used here rather than restated.

## F72 governs every tag comparison below

`Tag.time` has type `LogicalTime`, which is an `abbrev` for `Nat` that `omega` does not see through, while
`Tag.microstep` is a bare `Nat` and is visible. Two fields of one structure therefore behave differently
inside one proof, and G1's source-side `omega` proofs are not the precedent they appear to be — its field
is declared `Nat`. Every time comparison here closes with an explicit `Nat` lemma. Recorded as **F72**.

## What is owed and deliberately not proved here

That no pending event is ever in the past. `Relico/LF/PendingNotPast.lean` proves this for the multi-store
family as an invariant preserved by its step relation, and the general-family analogue is a six-rule
induction that belongs with the correctness development rather than with the rules. What *is* proved here
is the one-rule fact underneath it — `schedules_not_past`, a direct consequence of
`Tag.precedesOrEqual_schedule` — and the two advance rules carry the ordering they need as an explicit
premise rather than borrowing it from an invariant that does not yet exist. Stating it as a premise is what
keeps the rules honest in the meantime: a rule that assumed an unproved invariant would look sound and be
unfalsifiable.
-/

namespace GeneralTrigger

/--
Whether a reaction's trigger fires on a given pending event.

`GeneralTrigger` has three constructors and `GeneralEventKind` has two, so this is the conversion
`Relico/LF/GeneralRuntime.lean` predicted would be owed "at the trigger-matching site in G2a-iii". Rather
than convert a kind into a trigger and compare, the two are matched directly: a conversion would need a
`GeneralTrigger` value for every kind and would leave `startup` as a case on the wrong side of a partial
function.

`startup` never matches. It fires once, before any event exists, and nothing enqueues it — which is why
`GeneralEventKind` has two constructors rather than reusing `GeneralTrigger`. A reaction triggered by
startup is therefore unreachable from a pending event, and the `fire` rule below cannot select it.

Note that `GeneralReaction.trigger` is **one** trigger, not a list. `Relico/LF/GeneralRuntime.lean`
anticipated "a trigger list is a disjunction"; the AST this family actually has does not have lists, so no
disjunction arises and the correction is worth stating rather than leaving the reader to notice. What the
real `lfc` accepts is wider than what this fragment emits, and G6 owes that restriction in writing.

The name comparisons are `decide (a = b)` rather than `a == b`, and that is the same discipline
`LF.findReactor?` records rather than a spelling preference. `DecidableEq` and `BEq` are derived
independently with no lawfulness bridge between them, and this function feeds `findReactionForKind?`,
`GeneralProgram.reactionFor?` and the `fire` rule, whose results G2b compares against a DTR-side lookup — so
one notion of equality has to hold along that whole chain. `decide` is `DecidableEq`'s `Bool` form and is
already the built idiom in this family, at `LF.GeneralBinaryOp.apply`.
-/
def matchesKind :
    LF.GeneralTrigger →
    LF.GeneralEventKind →
    Bool

  | .startup, _ =>
      false

  | .logicalAction actionName, .logicalAction eventName =>
      decide (actionName = eventName)

  | .logicalAction _, .inputPort _ =>
      false

  | .inputPort portName, .inputPort eventName =>
      decide (portName = eventName)

  | .inputPort _, .logicalAction _ =>
      false

/--
Startup triggers nothing that can be pending.
-/
@[simp]
theorem not_matchesKind_startup
    (kind : LF.GeneralEventKind) :
    matchesKind .startup kind = false := by
  cases kind with

  | logicalAction _ =>
      rfl

  | inputPort _ =>
      rfl

end GeneralTrigger

/--
The first reaction in a declaration list whose trigger fires on a given event.

**First match wins, and declaration order is what decides.** That is not a default: stage F established
that reaction declaration order is observable in the target — §III-D's whole mechanism is that *"the
`readingFromTemp` reaction is declared first, ensuring its message is processed first"* — and
`LF.GeneralProgram`'s docstring records that no function in this family sorts a reaction list. A lookup
that searched by priority, or that returned every match, would be a second ordering convention competing
with the one the printer honours.

Explicit recursion over `matchesKind` rather than `List.find?` over `BEq`, for the reason
`LF.findReactor?` records: `DecidableEq` and `BEq` are derived independently with no lawfulness bridge
between them, and the translation stage's structural theorems compare a DTR list against an LF list, so one
notion of equality has to hold throughout.
-/
def findReactionForKind? :
    List LF.GeneralReaction →
    LF.GeneralEventKind →
    Option LF.GeneralReaction

  | [], _ =>
      none

  | reaction :: remaining, kind =>
      if LF.GeneralTrigger.matchesKind reaction.trigger kind then
        some reaction
      else
        findReactionForKind?
          remaining
          kind

namespace GeneralProgram

/--
The reaction a named instance runs for a given event kind, when the instance, its reactor and a matching
reaction all exist.

The target-side counterpart of `DTR.GeneralModel.messageServerFor?`, and named once here for the same
reason: the `fire` rule and G2b's correspondence relation both need it, and spelling the composition out at
each use would be a second definition of one convention, free to drift from the other.

`messageReactions` is searched and `startupReaction` is not. A pending event is never a startup event, so
including the startup reaction could only ever produce a match that the runtime cannot reach — and
`GeneralTrigger.matchesKind` would refuse it anyway, which makes the exclusion belt *and* braces rather
than a load-bearing choice.
-/
def reactionFor?
    (program : LF.GeneralProgram)
    (target : ActorName)
    (kind : LF.GeneralEventKind) :
    Option LF.GeneralReaction :=
  match program.reactorOfInstance? target with

  | none =>
      none

  | some reactor =>
      LF.findReactionForKind?
        reactor.messageReactions
        kind

end GeneralProgram

/--
The first connection leaving a given instance through a given output port.

An external send in the target is a `setPort`, and where that value arrives is decided by the connection
list, not by the statement: a connection names a target instance, a target port, and a delay. This lookup
is what turns the statement into an addressed event.

First match wins, mirroring `findReactionForKind?`. A port with two outgoing connections would fan out in
real LF, and this fragment does not emit one — stage E's routing gives each send site its own port. Taking
the first match rather than all of them therefore restricts the fragment rather than mis-modelling it, and
that restriction is one of the three G6 owes in writing.

The two field tests are **nested** rather than combined with `∧`. Every lookup in this family — `findReactor?`,
`findInstance?`, `findReactionForKind?` — is explicit recursion over a single decidable equality, and
`LF.findReactor?`'s docstring records why `BEq` is avoided here: it is derived independently of `DecidableEq`
with no lawfulness bridge, and the translation stage's structural theorems need one notion of equality
throughout. Nesting keeps that discipline; `if A ∧ B` would introduce a conjunction instance no other lookup
in the family relies on, and `&&` would reach for `BEq`. The cost is the repeated tail call, which is
visible rather than hidden.
-/
def connectionFrom? :
    List LF.GeneralConnection →
    ActorName →
    PortName →
    Option LF.GeneralConnection

  | [], _, _ =>
      none

  | connection :: remaining, sourceInstance, sourcePort =>
      if connection.sourceInstance = sourceInstance then
        if connection.sourcePort = sourcePort then
          some connection
        else
          connectionFrom?
            remaining
            sourceInstance
            sourcePort
      else
        connectionFrom?
          remaining
          sourceInstance
          sourcePort

/--
The earlier of an incumbent event and a candidate, folded across a queue.

Deliberately the same shape as G1's `DTR.GeneralActorSelection.selectMinimum`: an accumulator carrying the
best event seen so far, replaced only when the candidate is *strictly* better. `PrecedesOrEqual` is
reflexive, so `if best ≼ candidate then best else candidate` keeps the incumbent whenever the two share a
tag — which is exactly the insertion-order tie-break `GeneralEventQueue`'s docstring specifies, since the
incumbent is always the earlier-inserted of the two.

The comparison is on tags only. Two events at one tag for different reactors are both eligible and the
queue order decides; nothing here consults the reactor, and nothing may, because a target that preferred one
reactor over another at equal tags would be implementing an actor priority the target language does not
have.

This is where G2a-ii's three additions to `namespace Tag` are spent: the `Decidable` instance makes the
`if` computable, and totality and transitivity are what let the theorems about this fold be stated at all.
-/
def selectEarliestEvent :
    LF.GeneralPendingEvent →
    LF.GeneralEventQueue →
    LF.GeneralPendingEvent

  | best, [] =>
      best

  | best, candidate :: remaining =>
      if
          LF.Tag.PrecedesOrEqual
            best.tag
            candidate.tag then
        selectEarliestEvent
          best
          remaining
      else
        selectEarliestEvent
          candidate
          remaining

/--
An exhausted queue leaves the incumbent.
-/
@[simp]
theorem selectEarliestEvent_nil
    (best : LF.GeneralPendingEvent) :
    selectEarliestEvent
        best
        [] =
      best := by
  rfl

/--
The fold keeps the incumbent when the incumbent is no later.

Stated as a rewrite rather than left to `simp` at each use, because the minimality theorem below cases on
this condition four times and the `if` has to be discharged the same way each time.
-/
theorem selectEarliestEvent_cons_of_precedesOrEqual
    {best candidate : LF.GeneralPendingEvent}
    (remaining : LF.GeneralEventQueue)
    (hPrecedes :
      LF.Tag.PrecedesOrEqual
        best.tag
        candidate.tag) :
    selectEarliestEvent
        best
        (candidate :: remaining) =
      selectEarliestEvent
        best
        remaining := by
  simp [selectEarliestEvent, hPrecedes]

/--
The fold takes the candidate when the incumbent is not no-later.
-/
theorem selectEarliestEvent_cons_of_not_precedesOrEqual
    {best candidate : LF.GeneralPendingEvent}
    (remaining : LF.GeneralEventQueue)
    (hNotPrecedes :
      ¬ LF.Tag.PrecedesOrEqual
          best.tag
          candidate.tag) :
    selectEarliestEvent
        best
        (candidate :: remaining) =
      selectEarliestEvent
        candidate
        remaining := by
  simp [selectEarliestEvent, hNotPrecedes]

/--
**The fold really does compute a minimum**: its result is no later than every event it walked past,
including the one it was seeded with.

This is the theorem the two advance rules rest on, and it is why it is proved here rather than deferred.
`microstepAdvance` and `timeAdvance` below are premised on *the computed earliest event* being strictly
after the current tag, and they conclude by moving the tag to it. If the fold could return a non-minimal
event, both rules could step over an event that was due — the target would skip work, and G2c would then
prove a bisimulation between the source and something that is not the target. Stating the premise on the
computed event and proving the computation correct is what closes that gap; a rule premised on "no event is
due" instead would be a second spelling of the same condition, free to drift from the fold.

The induction generalises over the accumulator, which is why the statement quantifies `best` inside the
goal rather than binding it as a parameter: `hMember` mentions both `best` and the queue, so `induction …
generalizing best` would have to revert a hypothesis that the motive then has to carry. Putting the two
binders under the `∀` is the shape `evaluateArguments_length` uses on the source side for the same reason.

Both of G2a-ii's order facts are spent here, one per branch. Transitivity carries the result past the event
the fold *rejected* — the rejected one is no earlier than the incumbent, and the result is no later than
the incumbent. Totality is what turns the `if`'s negative branch into a usable inequality: `¬ (best ≼
candidate)` is not, by itself, `candidate ≼ best`, and for a partial order it would not be.
-/
theorem selectEarliestEvent_precedesOrEqual_of_mem
    (queue : LF.GeneralEventQueue) :
    ∀ (best event : LF.GeneralPendingEvent),
      event ∈ best :: queue →
        LF.Tag.PrecedesOrEqual
          (selectEarliestEvent
            best
            queue).tag
          event.tag := by

  induction queue with

  | nil =>
      intro best event hMember

      have hEvent :
          event = best := by
        simpa using hMember

      rw [hEvent, selectEarliestEvent_nil]

      exact LF.Tag.precedesOrEqual_refl best.tag

  | cons candidate remaining inductionHypothesis =>
      intro best event hMember

      by_cases hPrecedes :
          LF.Tag.PrecedesOrEqual
            best.tag
            candidate.tag

      · rw [selectEarliestEvent_cons_of_precedesOrEqual
              remaining
              hPrecedes]

        rcases List.mem_cons.mp hMember with
          hIsBest |
          hInTail

        · rw [hIsBest]
          exact inductionHypothesis
            best
            best
            (List.mem_cons.mpr (Or.inl rfl))

        · rcases List.mem_cons.mp hInTail with
            hIsCandidate |
            hInRemaining

          · rw [hIsCandidate]
            exact LF.Tag.precedesOrEqual_trans
              (inductionHypothesis
                best
                best
                (List.mem_cons.mpr (Or.inl rfl)))
              hPrecedes

          · exact inductionHypothesis
              best
              event
              (List.mem_cons.mpr (Or.inr hInRemaining))

      · rw [selectEarliestEvent_cons_of_not_precedesOrEqual
              remaining
              hPrecedes]

        have hReverse :
            LF.Tag.PrecedesOrEqual
              candidate.tag
              best.tag := by
          rcases LF.Tag.precedesOrEqual_total
              best.tag
              candidate.tag with
            hForward |
            hBackward

          · exact absurd hForward hPrecedes

          · exact hBackward

        rcases List.mem_cons.mp hMember with
          hIsBest |
          hInTail

        · rw [hIsBest]
          exact LF.Tag.precedesOrEqual_trans
            (inductionHypothesis
              candidate
              candidate
              (List.mem_cons.mpr (Or.inl rfl)))
            hReverse

        · rcases List.mem_cons.mp hInTail with
            hIsCandidate |
            hInRemaining

          · rw [hIsCandidate]
            exact inductionHypothesis
              candidate
              candidate
              (List.mem_cons.mpr (Or.inl rfl))

          · exact inductionHypothesis
              candidate
              event
              (List.mem_cons.mpr (Or.inr hInRemaining))

namespace GeneralRuntimeState

/--
The pending event that fires next, or `none` when the queue is empty.

The target-side counterpart of `DTR.GeneralActorSelection.selectedActor`, down to the shape: a `match` on
the queue that seeds the fold with its head. An empty queue has no next event, which is the target's
terminated state — not an error, and not a time advance either, because there is nothing to advance to.

The queue is read straight off the state rather than passed in as a cohort. G1 made the same choice on the
source side and its module header records why: a cohort parameter lets a caller supply a set the
configuration does not license, and every theorem then carries a hypothesis tying the two back together.
-/
def earliestPendingEvent?
    (state : GeneralRuntimeState) :
    Option LF.GeneralPendingEvent :=
  match state.pending with

  | [] =>
      none

  | first :: rest =>
      some
        (LF.selectEarliestEvent
          first
          rest)

/--
An empty queue selects nothing.
-/
@[simp]
theorem earliestPendingEvent?_eq_none_of_nil
    (currentTag : LF.Tag)
    (reactors : Store ActorName LF.GeneralReactorRuntime) :
    earliestPendingEvent?
        {
          currentTag := currentTag
          reactors := reactors
          pending := []
        } =
      none := by
  rfl

/--
A non-empty queue selects the fold seeded with its head.

Stated so that the `fire` and advance rules can be unfolded at a concrete queue without re-deriving the
`match`, which is what `Relico/Tests/GeneralSemantics.lean` needs in order to pin the zero-delay case by
`decide` rather than by hand.
-/
@[simp]
theorem earliestPendingEvent?_eq_of_cons
    (currentTag : LF.Tag)
    (reactors : Store ActorName LF.GeneralReactorRuntime)
    (first : LF.GeneralPendingEvent)
    (rest : LF.GeneralEventQueue) :
    earliestPendingEvent?
        {
          currentTag := currentTag
          reactors := reactors
          pending := first :: rest
        } =
      some
        (LF.selectEarliestEvent
          first
          rest) := by
  rfl

end GeneralRuntimeState

/--
Bind a reaction's declared parameters to the payload of the event that triggered it.

The target-side counterpart of `DTR.bindParameters`, and the same shape — a fold that updates the reactor's
valuation, one name per value, stopping when either list runs out. What differs is the *left* list's type:
the source binds `List DTR.GeneralTypedParameter`, because a message server declares typed formals, while a
reaction here declares `parameters : List VarName` — an untyped name list, because `GeneralReaction`
records no formal types. The value list is `List LF.GeneralValue` on both sides, the event's payload.

Surplus on either side is dropped, not rejected, for the reason `DTR.bindParameters` records: a partiality
in the middle of the step relation would need a `none`-cannot-arise hypothesis on the `fire` rule for a case
well-formedness already excludes. The arity agreement is a fact to be proved from the well-formedness guard,
not a branch in the rule.

Untyped where the source is typed, so there is no `.name` projection — the `VarName` *is* the key. That is
the one place the target's thinner reaction record shows through into the semantics.
-/
def bindReactionParameters :
    List VarName →
    List LF.GeneralValue →
    LF.GeneralValuation →
    LF.GeneralValuation

  | [], _, valuation =>
      valuation

  | _ :: _, [], valuation =>
      valuation

  | parameter :: parameters, value :: values, valuation =>
      bindReactionParameters
        parameters
        values
        (Store.update valuation parameter value)

/--
A reaction declaring no parameters binds nothing.
-/
@[simp]
theorem bindReactionParameters_nil
    (payload : List LF.GeneralValue)
    (valuation : LF.GeneralValuation) :
    bindReactionParameters
        []
        payload
        valuation =
      valuation := by
  rfl


/--
The target step relation for the general family.

**Index order.** `State → Label → State`, for the reason `DTR.GeneralStep` records: `LabeledTransition` in
`Relico/Common/WeakTransition.lean` is declared `State → Label → State → Prop`, and G2c instantiates
`Common.TauSteps` and `Common.WeakStep` at both relations rather than restating either. Recorded as **F70**.

**Six rules against the source's four.** `assign` matches one-for-one. `SEND` becomes `schedule` and
`setPort`, chosen by §III-E on what the statement is rather than on any runtime condition, and both are τ.
`TAKE` becomes `fire`. `TIME PROGRESS` becomes `microstepAdvance`, which is **τ**, and `timeAdvance`, which
is observable — that split is P24.

**Both advance rules move the tag to the earliest pending event, and neither carries a quiescence premise
beyond that.** This is deliberate symmetry with the source, and it took reading `readyActorsOf`
(`Relico/DTR/GeneralState.lean:621`) to get right. That function walks a
`Store ActorName DTR.GeneralActorState` — actor *states*, which carry bags but not continuations, because
`GeneralRuntimeConfiguration.erase` drops them — so "ready" on the source side means "has a due message"
and nothing more. `DTR.GeneralStep.timeProgress` therefore permits the clock to advance while some actor
sits mid-body, and a target rule that forbade it would be *stricter* than the source: a source step would
exist with no target step to match it, and G2c's transfer condition would fail in the direction that matters.
So the premise here is the exact analogue — the earliest pending event is strictly beyond the current tag —
and the mid-body permissiveness is a property of both models rather than a divergence between them. It is
recorded as a finding rather than repaired here, because repairing it means changing the source relation
too, and that is not row 6's obligation.

**Records are written field by field, never with `{ state with … }`**, following `DTR.GeneralStep` and
`Relico/DTR/Semantics.lean`'s `Step`; a grep finds no `{ x with … }` anywhere under `Relico/`.
-/
inductive GeneralStep
    (program : LF.GeneralProgram) :
    GeneralRuntimeState →
    LF.GeneralLabel →
    GeneralRuntimeState →
    Prop

  /--
  `ASSIGN`. Evaluate the right-hand side in the reactor's own valuation and update it in place, dropping the
  statement from the continuation.

  Premised on evaluation succeeding, exactly as on the source side: an expression that fails to evaluate has
  no rule, so the reactor is stuck rather than assigning a default. Note that failure here is *not* the same
  set of expressions as on the source side once division enters — F67 measured that the general fragment's
  operator semantics is C++'s, and that `x / 0` is well-formed, printed, and undefined behaviour in the
  target with no guard anywhere. `LF.GeneralBinaryOp.apply` returns `none` there (`apply_div_zero`), so this
  rule makes the *model* stick where the emitted program would be undefined. That is a divergence between
  this relation and the C++ it stands for, not between this relation and the source's.
  -/
  | assign
      {state : GeneralRuntimeState}
      {instanceName : ActorName}
      {reactor : GeneralReactorRuntime}
      {target : VarName}
      {expression : LF.GeneralExpr}
      {remaining : LF.GeneralBody}
      {value : LF.GeneralValue}
      (hReactor :
        Store.lookup state.reactors instanceName = some reactor)
      (hBody :
        reactor.activeBody =
          LF.GeneralStmt.assign target expression :: remaining)
      (hEvaluate :
        LF.GeneralExpr.evaluate reactor.valuation expression = some value) :
      GeneralStep
        program
        state
        LF.GeneralLabel.tau
        {
          currentTag := state.currentTag
          reactors :=
            Store.update
              state.reactors
              instanceName
              {
                valuation :=
                  Store.update
                    reactor.valuation
                    target
                    value
                activeBody := remaining
              }
          pending := state.pending
        }

  /--
  `SEND`, self-send half: `schedule`. Evaluate the arguments and enqueue a logical-action event on the
  sending reactor itself, at the tag the delay produces.

  **`LF.Tag.schedule` is P24's `upd`.** A zero delay keeps the time and increments the microstep; a positive
  delay advances the time and resets the microstep. That is the whole of why `TIME PROGRESS` had to split:
  a source send with no delay makes a message available at the same logical time, and the target reaches it
  by a microstep that has no source counterpart.

  The target of the event is the *sender*, which is what makes this the self-send half. F56's repair is
  visible here only indirectly: it gave each send **site** its own action name, so two identical
  `schedule` statements in one body enqueue events with different `kind`s and cannot collapse into one.
  This rule takes the action name from the statement and so inherits that distinctness rather than
  re-establishing it.

  Appended to `pending`, not prepended, and here the order genuinely is read — unlike the source's message
  bag. `GeneralEventQueue`'s docstring makes insertion order the tie-break for events sharing a tag, and
  `selectEarliestEvent` keeps its incumbent precisely to honour it. Prepending would silently reverse the
  tie-break for every pair of same-tag events.

  τ. A message becoming available is not observable on either side; only its consumption is.
  -/
  | schedule
      {state : GeneralRuntimeState}
      {instanceName : ActorName}
      {reactor : GeneralReactorRuntime}
      {actionName : ActionName}
      {arguments : List LF.GeneralExpr}
      {delay : Delay}
      {remaining : LF.GeneralBody}
      {payload : List LF.GeneralValue}
      (hReactor :
        Store.lookup state.reactors instanceName = some reactor)
      (hBody :
        reactor.activeBody =
          LF.GeneralStmt.schedule actionName arguments delay :: remaining)
      (hArguments :
        LF.GeneralExpr.evaluateArguments
            reactor.valuation
            arguments =
          some payload) :
      GeneralStep
        program
        state
        LF.GeneralLabel.tau
        {
          currentTag := state.currentTag
          reactors :=
            Store.update
              state.reactors
              instanceName
              {
                valuation := reactor.valuation
                activeBody := remaining
              }
          pending :=
            state.pending ++
              [{
                target := instanceName
                kind :=
                  LF.GeneralEventKind.logicalAction
                    actionName
                tag :=
                  LF.Tag.schedule
                    state.currentTag
                    delay
                payload := payload
              }]
        }

  /--
  `SEND`, external half: `setPort`. Evaluate the arguments, follow the connection leaving that output port,
  and enqueue an input-port event on the connection's target.

  **The delay comes from the connection, not from the statement**, and `LF.GeneralStmt.setPort` has no delay
  field to take it from. `Relico/LF/GeneralSyntax.lean` records why: stage E gives every send site its own
  port "precisely so that each statement's delay has its own connection to sit on".

  **The same `LF.Tag.schedule` serves both send rules, and that is a measured fact about the printer rather
  than an assumption.** In real LF a zero-delay connection is dataflow — the downstream reaction runs at the
  *same* tag — while `after 0` is a one-microstep delay, so conflating the two would be a genuine
  mis-modelling. `LF.renderGeneralConnection` (`Relico/LF/GeneralCppPrinter.lean:1256`) emits
  `" after " ++ renderLfTime connection.delay` **unconditionally**, and `renderLfTime` renders a zero delay
  as `0 msec` rather than as nothing. Every connection this fragment prints therefore carries an explicit
  `after`, no connection is a zero-microstep dataflow connection, and one tag function is correct for both
  rules. Had the printer omitted `after` at zero, this rule would have needed to deliver at the current tag.

  **First connection wins, and a second connection on one output port is outside the fragment.**
  `connectionFrom?` returns the first match; real LF would fan out to all of them. Stage E's per-site
  routing means the translator never emits a second, so this restricts what the relation covers rather than
  mis-describing what it covers — one of the restrictions G6 owes in writing.

  τ, for the same reason as `schedule`.
  -/
  | setPort
      {state : GeneralRuntimeState}
      {instanceName : ActorName}
      {reactor : GeneralReactorRuntime}
      {portName : PortName}
      {arguments : List LF.GeneralExpr}
      {remaining : LF.GeneralBody}
      {payload : List LF.GeneralValue}
      {connection : LF.GeneralConnection}
      (hReactor :
        Store.lookup state.reactors instanceName = some reactor)
      (hBody :
        reactor.activeBody =
          LF.GeneralStmt.setPort portName arguments :: remaining)
      (hArguments :
        LF.GeneralExpr.evaluateArguments
            reactor.valuation
            arguments =
          some payload)
      (hConnection :
        LF.connectionFrom?
            program.connections
            instanceName
            portName =
          some connection) :
      GeneralStep
        program
        state
        LF.GeneralLabel.tau
        {
          currentTag := state.currentTag
          reactors :=
            Store.update
              state.reactors
              instanceName
              {
                valuation := reactor.valuation
                activeBody := remaining
              }
          pending :=
            state.pending ++
              [{
                target := connection.targetInstance
                kind :=
                  LF.GeneralEventKind.inputPort
                    connection.targetPort
                tag :=
                  LF.Tag.schedule
                    state.currentTag
                    connection.delay
                payload := payload
              }]
        }

  /--
  `TAKE`. The earliest pending event, if it is at the current tag, fires: it leaves the queue, its payload
  binds the matched reaction's parameters into the target reactor's valuation, and the reaction body becomes
  that reactor's continuation.

  **The event is chosen by the scheduler and removed by decomposition**, which is the source's `take` shape
  transposed. There it is `hSelected` on a `ReadyActor` plus `hDue : bag = earlier ++ message :: later` plus
  `hArrival` tying the two together; here `hSelected` already names the event itself, so the tie is `hTag`
  and no separate arrival premise is needed. The decomposition is what removes it. This is *tighter* than
  the source: the source's selection fixes only an actor and a time, leaving the choice among equally-early
  messages open, while here the fold picks a single event outright.

  **Premised on the reactor being idle.** Table I's `TAKE` requires the continuation to be `ε`, and the
  target must agree or the two sides' continuations diverge with nothing to notice. This is the premise
  that makes the continuation component of G2b's `R` do work.

  **The reaction is found by `reactionFor?`, so declaration order decides.** Stage F established that this
  is observable in the target and is §III-D's actual mechanism; a lookup that consulted
  `GeneralReaction.priority` instead would be reading a field G3 is about to make a well-formedness
  violation.

  A fired event whose reactor has no matching reaction has **no** step. The event stays queued and the tag
  cannot advance past it — the target deadlocks rather than dropping it. That is deliberate: F64 recorded
  that a never-firing reaction and an unmatched event are different things, and silently discarding the
  event would be the second of those disguised as the first.

  Observable, carrying `.consume` with the target reactor and the event kind. Note what the label does
  **not** carry: the payload. The source's `.consume` carries a whole `DTR.GeneralMessage`, payload
  included, so G2b's `ϕ` must drop it — the two label types agree on shape but not on content, which is
  exactly why they are two types.
  -/
  | fire
      {state : GeneralRuntimeState}
      {event : LF.GeneralPendingEvent}
      {earlier later : LF.GeneralEventQueue}
      {reactor : GeneralReactorRuntime}
      {reaction : LF.GeneralReaction}
      (hSelected :
        GeneralRuntimeState.earliestPendingEvent? state = some event)
      (hTag :
        event.tag = state.currentTag)
      (hQueue :
        state.pending = earlier ++ event :: later)
      (hReactor :
        Store.lookup state.reactors event.target = some reactor)
      (hIdle :
        reactor.idle = true)
      (hReaction :
        LF.GeneralProgram.reactionFor?
            program
            event.target
            event.kind =
          some reaction) :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume event.target event.kind)
        {
          currentTag := state.currentTag
          reactors :=
            Store.update
              state.reactors
              event.target
              {
                valuation :=
                  LF.bindReactionParameters
                    reaction.parameters
                    event.payload
                    reactor.valuation
                activeBody := reaction.body
              }
          pending := earlier ++ later
        }

  /--
  `TIME PROGRESS`, internal half. The earliest pending event shares the current logical time but sits at a
  later microstep, so the tag advances to it and **nothing is observable**.

  **This rule is the whole of P24.** The paper reads a single observable `TIME PROGRESS` off Table II and
  concludes Theorem 1; a zero-delay send in the source makes a message available at the same logical time,
  the target reaches it by exactly this step, and an observable label here would demand a source step that
  does not exist. Classifying it τ is what makes the repaired theorem true. `Relico/Tests/GeneralSemantics.lean`
  pins the zero-delay case so the two halves cannot be re-merged by a later edit.

  Premised on the *computed* earliest event, and `selectEarliestEvent_precedesOrEqual_of_mem` above is what
  makes that premise mean "no event is due": the fold's result is no later than every queued event, so an
  event strictly beyond the current tag guarantees none is at it.

  The time comparison is an equality on `Tag.time` and a strict inequality on `Tag.microstep`, kept apart on
  purpose. `Tag.time : LogicalTime` is invisible to `omega` while `Tag.microstep : Nat` is visible — two
  fields of one structure behaving differently inside one proof — so every consumer of this rule closes the
  time half with an explicit `Nat` lemma. Recorded as **F72**.
  -/
  | microstepAdvance
      {state : GeneralRuntimeState}
      {event : LF.GeneralPendingEvent}
      (hSelected :
        GeneralRuntimeState.earliestPendingEvent? state = some event)
      (hTime :
        event.tag.time = state.currentTag.time)
      (hMicrostep :
        state.currentTag.microstep < event.tag.microstep) :
      GeneralStep
        program
        state
        LF.GeneralLabel.tau
        {
          currentTag := event.tag
          reactors := state.reactors
          pending := state.pending
        }

  /--
  `TIME PROGRESS`, observable half. The earliest pending event is at a strictly later logical time, so the
  tag advances to it and the step carries `.timeAdvance`.

  The microstep of the destination is whatever the event's tag says, and this rule does not constrain it —
  `Tag.schedule` already set it to zero for every positive delay (`schedule_positive`), so constraining it
  here would restate a fact the tag arithmetic owns.

  The label's two components are `state.currentTag.time` and the event's, written as projections rather than
  through `GeneralRuntimeState.now`. `now` is a `@[simp]` unfolding of exactly this projection, so the two
  spellings are interchangeable in proofs; the projection is used because it keeps the label determined by
  the rule's own indices, which is what lets a `cases` on this rule read the label off without unfolding.
  -/
  | timeAdvance
      {state : GeneralRuntimeState}
      {event : LF.GeneralPendingEvent}
      (hSelected :
        GeneralRuntimeState.earliestPendingEvent? state = some event)
      (hForward :
        state.currentTag.time < event.tag.time) :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance
          state.currentTag.time
          event.tag.time)
        {
          currentTag := event.tag
          reactors := state.reactors
          pending := state.pending
        }


/-!
## Inversion

What a step's **label** already tells you about its endpoints, stated once so that G2b's cases do not
re-derive it. The section mirrors `Relico/DTR/GeneralSemantics.lean`'s, including its refusal to state a
structural iff-characterization: `GeneralStep`'s six rules are not separately named relations, so a
disjunction of six existentials would be a second spelling of the constructor list, free to drift from it.
`cases` delivers the structure; what it does not deliver is the tag arithmetic, so that is what is proved.

Two conventions are inherited from `Relico/DTR/GlobalMultiStorePayloadOneStep.lean`, where both are green.
Names in a `cases … with | ctor …` alternative bind the constructor's **explicit** fields only — implicit
data fields are auto-named and inaccessible even when the indices do not determine them — and an
existential witness for such a field is supplied as `_`. Unconsumed hypotheses are bound to `_` rather than
named, so `unusedVariables` has nothing to report and the warning count does not move.

The explicit-field counts, which the `cases` patterns below have to match exactly, are: `assign` 3,
`schedule` 3, `setPort` 4, `fire` 6, `microstepAdvance` 3, `timeAdvance` 2.
-/

/--
**A τ step does not move observable logical time — and that is P24 stated as a theorem.**

Four cases, and the fourth is the whole point. `assign`, `schedule` and `setPort` rebuild the state with
`currentTag := state.currentTag`, so they are `rfl`. `microstepAdvance` genuinely *changes* the tag, and this
theorem still holds of it, because `GeneralRuntimeState.now` projects the time and drops the microstep: its
premise says the earliest event shares the current time, so the advance is invisible to `now`.

That is exactly what the paper's Theorem 1 gets wrong and what P24 repairs. A microstep advance is a real
target step with no source counterpart; classifying it τ and proving that τ preserves `now` is what lets a
weak bisimulation absorb it. Had the rule been left observable, this theorem would be unstatable and the
zero-delay send would have no matching source step.
-/
theorem GeneralStep.now_eq_of_tau
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    (hStep :
      GeneralStep
        program
        state
        LF.GeneralLabel.tau
        next) :
    GeneralRuntimeState.now next =
      GeneralRuntimeState.now state := by

  cases hStep with

  | assign _ _ _ =>
      rfl

  | schedule _ _ _ =>
      rfl

  | setPort _ _ _ _ =>
      rfl

  | microstepAdvance _ hTime _ =>
      exact hTime

/--
**No τ step enqueues an event in the past.**

The one-rule fact underneath the pending-not-past invariant, and the reason
`Relico.LF.PendingNotPast` is imported: `LF.Tag.precedesOrEqual_schedule` discharges both send cases
outright, for zero and positive delay alike. The full invariant — that *every* queued event is at or after
the current tag, preserved by all six rules — is a six-rule induction that belongs with the correctness
development, and the two advance rules deliberately carry their ordering as a premise rather than borrowing
it from an invariant that does not yet exist.

Stated as a disjunction so that the two rules that leave the queue alone are `Or.inl` and need no arithmetic.
The proof of the two send cases follows `LF.ActionQueue.PendingNotPast.append_one` — note the namespace:
that theorem sits in `ActionQueue`, not in `Tag` alongside `precedesOrEqual_schedule` — reusing its
`simp only [List.mem_append, List.mem_singleton]` and its `rcases … with hExisting | hAdded`, because that is
the shape already green in this repository for an append-one queue. It diverges at the last line only:
`append_one` closes the added case with the `hNew` ordering premise it was *given*, whereas here there is no
such premise and the ordering is *derived* from `precedesOrEqual_schedule`. That difference is the whole
reason this statement can be proved one rule at a time while the full invariant cannot.

Restricted to τ deliberately. `fire` *removes* an event, so it can only shrink the queue, and it is the
advance rules that would need the full invariant to say anything — which is the point being deferred.
-/
theorem GeneralStep.tau_pending_not_past
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    (hStep :
      GeneralStep
        program
        state
        LF.GeneralLabel.tau
        next) :
    ∀ (event : LF.GeneralPendingEvent),
      event ∈ next.pending →
        event ∈ state.pending ∨
          LF.Tag.PrecedesOrEqual
            state.currentTag
            event.tag := by

  cases hStep with

  | assign _ _ _ =>
      intro event hEvent
      exact Or.inl hEvent

  | schedule _ _ _ =>
      intro event hEvent

      simp only [
        List.mem_append,
        List.mem_singleton
      ] at hEvent

      rcases hEvent with
        hExisting |
        hAdded

      · exact Or.inl hExisting

      · refine Or.inr ?_
        rw [hAdded]
        exact LF.Tag.precedesOrEqual_schedule
          state.currentTag
          _

  | setPort _ _ _ _ =>
      intro event hEvent

      simp only [
        List.mem_append,
        List.mem_singleton
      ] at hEvent

      rcases hEvent with
        hExisting |
        hAdded

      · exact Or.inl hExisting

      · refine Or.inr ?_
        rw [hAdded]
        exact LF.Tag.precedesOrEqual_schedule
          state.currentTag
          _

  | microstepAdvance _ _ _ =>
      intro event hEvent
      exact Or.inl hEvent

/--
A `.consume` step leaves the tag exactly where it was — not merely its time component.

Stronger than the τ statement above, and it has to be: firing happens *at* a tag, so a `fire` that moved the
microstep would let two events at one tag be separated by the firing of the first.
-/
theorem GeneralStep.tag_eq_of_consume
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume target kind)
        next) :
    next.currentTag = state.currentTag := by

  cases hStep with

  | fire _ _ _ _ _ _ =>
      rfl

/--
A `.consume` step's label names the event the scheduler selected, and that event is at the current tag.

The two `rfl`s in the witness are index unification doing the work an explicit premise does on the source
side. `DTR.GeneralStep.take` carries `hName : selected.actorName = actorName` because its selection fixes an
actor rather than a message; here the selected object *is* the event, so the label's components are the
event's own projections and the equations hold by construction.
-/
theorem GeneralStep.selected_of_consume
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume target kind)
        next) :
    ∃ event,
      GeneralRuntimeState.earliestPendingEvent? state =
          some event ∧
        event.target = target ∧
        event.kind = kind ∧
        event.tag = state.currentTag := by

  cases hStep with

  | fire hSelected hTag _ _ _ _ =>
      exact ⟨_, hSelected, rfl, rfl, hTag⟩

/--
A `.consume` step's target reactor exists and was idle.

The idleness is Table I's `TAKE` premise transposed, and it is what makes the continuation component of
G2b's `R` load-bearing rather than decorative.
-/
theorem GeneralStep.idle_of_consume
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume target kind)
        next) :
    ∃ reactor,
      Store.lookup state.reactors target =
          some reactor ∧
        reactor.idle = true := by

  cases hStep with

  | fire _ _ _ hReactor hIdle _ =>
      exact ⟨_, hReactor, hIdle⟩

/--
A `.consume` step removes exactly the fired event from the queue and changes nothing else about it.

The decomposition is what G2b needs in order to match this against the source's bag removal: both sides
split a list around the consumed item and rejoin the halves, so the two removals can be related without
either side committing to a position.
-/
theorem GeneralStep.pending_of_consume
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume target kind)
        next) :
    ∃ event earlier later,
      GeneralRuntimeState.earliestPendingEvent? state =
          some event ∧
        state.pending = earlier ++ event :: later ∧
        next.pending = earlier ++ later := by

  cases hStep with

  | fire hSelected _ hQueue _ _ _ =>
      exact ⟨_, _, _, hSelected, hQueue, rfl⟩

/--
A `.consume` step's label determines a matching reaction, found in declaration order.

The existential is over the reaction rather than over its body, because G2b has to relate the *whole*
reaction — its parameter list binds the payload and its body becomes the continuation.
-/
theorem GeneralStep.reaction_of_consume
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.consume target kind)
        next) :
    ∃ reaction,
      LF.GeneralProgram.reactionFor?
          program
          target
          kind =
        some reaction := by

  cases hStep with

  | fire _ _ _ _ _ hReaction =>
      exact ⟨_, hReaction⟩

/--
A `.timeAdvance` label's first component is the time the step started from.
-/
theorem GeneralStep.before_eq_of_timeAdvance
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance before after)
        next) :
    before =
      GeneralRuntimeState.now state := by

  cases hStep with

  | timeAdvance _ _ =>
      rfl

/--
A `.timeAdvance` label's second component is the time the step arrived at.
-/
theorem GeneralStep.now_eq_of_timeAdvance
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance before after)
        next) :
    GeneralRuntimeState.now next =
      after := by

  cases hStep with

  | timeAdvance _ _ =>
      rfl

/--
A `.timeAdvance` step strictly increases logical time.

The one place where the observable half of the split is distinguished from the internal half by arithmetic
rather than by label. `microstepAdvance` cannot satisfy this — its premise pins the time equal — so a
`.timeAdvance` label and a strict increase determine each other.
-/
theorem GeneralStep.lt_of_timeAdvance
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance before after)
        next) :
    before < after := by

  cases hStep with

  | timeAdvance _ hForward =>
      exact hForward

/--
A `.timeAdvance` step touches neither the reactors nor the queue.

Both are `rfl`, and both are worth stating: G2b's correspondence has a component per field, and a time
advance is the one step that must leave every component but the tag alone.
-/
theorem GeneralStep.reactors_eq_of_timeAdvance
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance before after)
        next) :
    next.reactors = state.reactors := by

  cases hStep with

  | timeAdvance _ _ =>
      rfl

/--
A `.timeAdvance` step leaves the pending queue untouched.
-/
theorem GeneralStep.pending_eq_of_timeAdvance
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance before after)
        next) :
    next.pending = state.pending := by

  cases hStep with

  | timeAdvance _ _ =>
      rfl

/--
A `.timeAdvance` step advances to the tag of the event the scheduler selected.

This is the theorem that ties the advance to the queue rather than to an arbitrary future time, and it is
where the difference from the source shows most plainly. `DTR.GeneralStep.timeProgress` advances to *any*
strictly later `future`, constrained only by no actor being ready; the target cannot, because a tag has to be
the tag of something. G2b therefore matches one source advance against one target advance by *choosing* the
source's `future` to be the target's event time — which is available in this direction and would not be if
the quantifiers ran the other way.
-/
theorem GeneralStep.selected_of_timeAdvance
    {program : LF.GeneralProgram}
    {state next : GeneralRuntimeState}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        program
        state
        (LF.GeneralLabel.timeAdvance before after)
        next) :
    ∃ event,
      GeneralRuntimeState.earliestPendingEvent? state =
          some event ∧
        next.currentTag = event.tag ∧
        before < event.tag.time := by

  cases hStep with

  | timeAdvance hSelected hForward =>
      exact ⟨_, hSelected, rfl, hForward⟩


end LF
end Relico
