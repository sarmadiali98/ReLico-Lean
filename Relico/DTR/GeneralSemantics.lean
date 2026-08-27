import Relico.DTR.GeneralEvaluation
import Relico.DTR.GeneralRuntime
import Relico.DTR.GeneralActorSelection

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
# The source step relation for the general family

Obligation G2a-iii, source side. `Relico/DTR/GeneralRuntime.lean` holds the state a program executes in and
the label a step carries; this module holds the **rules**, and the split follows
`Relico/DTR/DetailedMultiStorePayloadRuntime.lean` and its `…Semantics.lean` companion exactly.

## Four rules, read off the paper's Table I

Table I's rules are `ASSIGN`, `SEND`, `CONDITIONAL-T`, `CONDITIONAL-F`, `TAKE` and `TIME PROGRESS`.
`GeneralStmt` has no conditional, so four survive: `assign` and `send` carry τ, `take` carries `ms`, and
`timeProgress` carries `t`. The two missing conditional rules are **not** an omission — `DTR.GeneralBody`
is a flat statement list whose own docstring records that the stage admitting branching must change the
type, so what stage G proves is the conditional-free sub-fragment. `docs/STAGE_G_DESIGN.md` §7 states the
restriction and G6 owes its declaration.

## Why the relation is indexed state → label → state, in that order

Because `Common.LabeledTransition` is `State → Label → State → Prop`, and G2c must **instantiate**
`Common.TauSteps` and `Common.WeakStep` at this relation rather than restate either. An index order chosen
freely here would elaborate perfectly well and then fail two obligations later, at the point where the
instantiation is attempted. Recorded as **F70**.

## Why `take` reads the cohort through `erase`

`DTR.GeneralActorSelection.selectedActor` takes a `DTR.GeneralConfiguration` — the continuation-free
projection — because G1 was
built before continuations existed. `GeneralRuntimeConfiguration.erase` is exactly that projection, so the
cohort is `config.erase.readyActors` and the selection is
`GeneralActorSelection.selectedActor model config.erase`. This is
reuse rather than a workaround: a second cohort computation over the runtime configuration would be a
second definition of one convention, free to drift from the one G1 proved five theorems about.

## Why `take` is premised on an idle actor

Table I's `TAKE` is premised on the continuation being `ε`: an actor accepts a new message only when it has
no statements left to run. `GeneralActorRuntime.idle` is that test, and premising the rule on it is what
makes the continuation component of G2b's `R` do work. Without it an actor could accept a second message
mid-body and the two sides' continuations would diverge with nothing to notice.
-/

namespace GeneralModel

/--
The message server a named actor runs for a named message, when the actor, its class and the server all
exist.

This is a composition of two lookups `Relico/DTR/GeneralSyntax.lean` already provides — `classOfActor?`
then `messageServer?` — named once here because the `take` rule and G2b's correspondence relation both
need it. Spelling the composition out at each use would be a second definition of one convention, free
to drift from the other; the repository has already paid for that mistake twice.
-/
def messageServerFor?
    (model : DTR.GeneralModel)
    (receiver : ActorName)
    (messageName : MsgName) :
    Option DTR.GeneralMessageServer :=
  match model.classOfActor? receiver with

  | none =>
      none

  | some reactiveClass =>
      reactiveClass.messageServer? messageName

end GeneralModel

/--
Bind a message server's declared parameters to the payload of the message being taken.

The paper writes the server's environment as `e_x ∪ v⃗`. `Relico/DTR/GeneralEvaluation.lean`'s
`evaluate` resolves `.stateVar` and `.parameterVar` in **one** store, so that union is an update of the
state valuation rather than a second environment, and stage E's `.parameterShadowsStateVariable`
well-formedness clause is what makes it sound.

Surplus parameters and surplus payload values are both dropped rather than rejected. Rejecting would put
a partiality in the middle of the step relation for a case well-formedness already excludes, and the
`take` rule would then need a hypothesis about a `none` that cannot arise. The agreement is proved
instead, by `evaluateArguments_length` below together with the arity clause.
-/
def bindParameters :
    List DTR.GeneralTypedParameter →
    DTR.GeneralPayload →
    DTR.GeneralValuation →
    DTR.GeneralValuation

  | [], _, valuation =>
      valuation

  | _ :: _, [], valuation =>
      valuation

  | parameter :: parameters, value :: values, valuation =>
      bindParameters
        parameters
        values
        (Store.update valuation parameter.name value)

/--
A server declaring no parameters binds nothing.
-/
@[simp]
theorem bindParameters_nil
    (payload : DTR.GeneralPayload)
    (valuation : DTR.GeneralValuation) :
    bindParameters
        []
        payload
        valuation =
      valuation := by
  rfl

/--
The payload `evaluateArguments` produces has exactly as many values as the argument list it evaluated.

`Relico/DTR/GeneralEvaluation.lean`'s `evaluateArguments` docstring records this statement as owed by
"the stage that writes the step relation, where it is first used". That stage is this one and the `send`
rule is the use: without it, a send whose argument count matches the receiver's declared parameter count
could still produce a payload of a different length, and `bindParameters` would then silently drop a
parameter at `take` time — the surplus-dropping decision above is only safe because of this theorem.

Proved by induction on the argument list, following
`Relico/Correctness/GeneralEvaluation.lean`'s `compileGeneralExpr_preserves_evaluateArguments` in the
`cons` case: `simp only [evaluateArguments]` exposes the two-way `match`, and then a plain `cases` on each
scrutinee **reduces** that match in the branch. The payload quantifier is left inside the statement rather
than taken as a parameter so that the implication is still part of the goal when those `cases` run — a
`match` sitting in an already-introduced hypothesis is not reduced by `cases`, and recovering it would need
the scrutinee equations that `cases h : e` makes unusable for rewriting.

The `nil` case needs one step the precedent does not, and the reason is worth stating because it is
invisible in the goal display. After `rw [← hPayload]` the goal prints as `[].length = [].length`, which
looks closed by reflexivity and is not: the left `[]` is a `GeneralPayload` and the right one is a
`List GeneralExpr`, so the two sides are equal only after `List.length` reduces on both. `rw`'s trailing
`rfl` runs at reducible transparency and does not perform that reduction, so the closing `simp` is doing
real work. Two syntactically identical-looking empty lists at different element types is a shape that will
recur wherever a payload length is compared to an argument-list length.

The equation `hTail` is named, and that is the one legitimate use of the `cases h : e` form here: it is
not used to rewrite anything, only to feed the induction hypothesis.
-/
theorem evaluateArguments_length
    (valuation : DTR.GeneralValuation)
    (arguments : List DTR.GeneralExpr) :
    ∀ (payload : DTR.GeneralPayload),
      DTR.GeneralExpr.evaluateArguments valuation arguments = some payload →
        payload.length = arguments.length := by

  induction arguments with

  | nil =>
      intro payload hEvaluate
      rw [DTR.GeneralExpr.evaluateArguments_nil] at hEvaluate
      injection hEvaluate with hPayload
      rw [← hPayload]
      simp

  | cons argument rest inductionHypothesis =>
      simp only [DTR.GeneralExpr.evaluateArguments]
      cases DTR.GeneralExpr.evaluate valuation argument with

      | none =>
          intro payload hEvaluate
          simp at hEvaluate

      | some value =>
          cases hTail :
              DTR.GeneralExpr.evaluateArguments
                valuation
                rest with

          | none =>
              intro payload hEvaluate
              simp at hEvaluate

          | some values =>
              intro payload hEvaluate
              injection hEvaluate with hPayload
              rw [← hPayload]
              simp only [List.length_cons]
              rw [inductionHypothesis values hTail]
/--
The actor a send statement names, from the point of view of its sender.

`.selfTarget` is the sender itself; `.knownRebec` resolves through the model's derived topology, which is
`Relico/Common/ActorTopology.lean`'s `resolve` applied to `model.topology`. Resolution can fail — a
known-rebec name with no binding — and the `send` rule is premised on it succeeding rather than defaulting
to the sender, because a silent self-send would be a message delivered to the wrong actor.
-/
def sendTargetActor?
    (model : DTR.GeneralModel)
    (sender : ActorName) :
    DTR.GeneralSendTarget →
    Option ActorName

  | .selfTarget =>
      some sender

  | .knownRebec knownRebec =>
      ActorTopology.resolve
        model.topology
        sender
        knownRebec

/--
The source step relation for the general family.

**Index order.** `State → Label → State`, because `Relico/Common/WeakTransition.lean` declares
`abbrev LabeledTransition (State) (Label) := State → Label → State → Prop` and G2c must *instantiate*
`Common.TauSteps` and `Common.WeakStep` at this relation rather than restate either. Recorded as **F70**.

**Five rules.** Table I's are `ASSIGN`, `SEND`, `CONDITIONAL-T`, `CONDITIONAL-F`, `TAKE` and
`TIME PROGRESS`; the two conditionals are absent because `DTR.GeneralStmt` has no conditional, so what
stage G proves is the conditional-free sub-fragment (§7, and G6 owes the declaration). `assign`, `trace` and
`send` carry `.tau`; `take` carries `.consume`; `timeProgress` carries `.timeAdvance`. A `trace` step is
internal instrumentation: it consumes its statement without changing any modeled state, and generated
`printf` output remains outside this formal relation.

**Records are written field by field, never with `{ config with … }`.** `Relico/DTR/Semantics.lean`'s
`Step` — the corpus's only other source step relation — writes every field of every state explicitly, and
a grep found no `{ x with … }` anywhere in `Relico/`. Both structures involved have two fields, so the
explicit form costs little and keeps the rules readable as states rather than as diffs.
-/
inductive GeneralStep
    (model : DTR.GeneralModel) :
    GeneralRuntimeConfiguration →
    DTR.GeneralLabel →
    GeneralRuntimeConfiguration →
    Prop

  /--
  `ASSIGN`. Evaluate the right-hand side in the actor's own valuation and update it in place, dropping
  the statement from the continuation.

  Premised on evaluation succeeding. An expression that fails to evaluate — an unbound variable — has no
  rule, so the actor is stuck rather than silently assigning a default. Stage E's well-formedness makes
  that unreachable for accepted models; making it a *rule* would prove a different language correct.
  -/
  | assign
      {config : GeneralRuntimeConfiguration}
      {actorName : ActorName}
      {actor : GeneralActorRuntime}
      {target : VarName}
      {expression : DTR.GeneralExpr}
      {remaining : DTR.GeneralBody}
      {value : DTR.GeneralValue}
      (hActor :
        Store.lookup config.actors actorName = some actor)
      (hBody :
        actor.activeBody =
          DTR.GeneralStmt.assign target expression :: remaining)
      (hEvaluate :
        DTR.GeneralExpr.evaluate actor.state.valuation expression = some value) :
      GeneralStep
        model
        config
        DTR.GeneralLabel.tau
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
                      Store.update
                        actor.state.valuation
                        target
                        value
                    bag := actor.state.bag
                  }
                activeBody := remaining
              }
        }

  /-- Internal instrumentation. Consume the trace statement without changing modeled state. -/
  | trace
      {config : GeneralRuntimeConfiguration}
      {actorName : ActorName}
      {actor : GeneralActorRuntime}
      {tag : String}
      {remaining : DTR.GeneralBody}
      (hActor :
        Store.lookup config.actors actorName = some actor)
      (hBody :
        actor.activeBody =
          DTR.GeneralStmt.trace tag :: remaining) :
      GeneralStep
        model
        config
        DTR.GeneralLabel.tau
        {
          now := config.now
          actors :=
            Store.update
              config.actors
              actorName
              {
                state := actor.state
                activeBody := remaining
              }
        }

  /--
  `SEND`. Evaluate the argument list, resolve the target, and append the message to the *receiver's* bag
  with an arrival of `now + delay`.

  **Appended, not prepended** — the same choice `Relico/DTR/Semantics.lean`'s `selfSend` makes with
  `pendingMessages ++ [ … ]`, so the two source families agree. Note what this does *not* claim:
  `GeneralMessageBag`'s own docstring (`Relico/DTR/GeneralState.lean:97`) says it is a multi-set and that
  "nothing in the semantics reads the order", and that claim survives this module — `take` below reaches any
  position by decomposition, so append versus prepend changes no reachable behaviour. Appending is a
  house-style agreement, not a semantic commitment, and had `take` been written to pop the head instead it
  would have quietly falsified a docstring two layers down.

  **`hReceiver` looks the receiver up in the store that already carries the sender's update, and that is
  deliberate.** When an actor sends to itself the two updates touch one record, and looking the receiver up
  in the *original* store would produce a record still carrying the consumed statement in its continuation;
  the second update would then write it back and the send would replay forever. Reading the updated store
  makes the self-send case compose correctly, and self-sends are exactly where F56 found a message being
  silently lost once already.

  The send is τ. A message becoming *available* is not observable in Table I; only its `TAKE` is.
  -/
  | send
      {config : GeneralRuntimeConfiguration}
      {senderName receiverName : ActorName}
      {sender receiver : GeneralActorRuntime}
      {sendTarget : DTR.GeneralSendTarget}
      {messageName : MsgName}
      {arguments : List DTR.GeneralExpr}
      {delay : Delay}
      {remaining : DTR.GeneralBody}
      {payload : DTR.GeneralPayload}
      (hSender :
        Store.lookup config.actors senderName = some sender)
      (hBody :
        sender.activeBody =
          DTR.GeneralStmt.send sendTarget messageName arguments delay :: remaining)
      (hArguments :
        DTR.GeneralExpr.evaluateArguments
            sender.state.valuation
            arguments =
          some payload)
      (hTarget :
        sendTargetActor? model senderName sendTarget = some receiverName)
      (hReceiver :
        Store.lookup
            (Store.update
              config.actors
              senderName
              {
                state := sender.state
                activeBody := remaining
              })
            receiverName =
          some receiver) :
      GeneralStep
        model
        config
        DTR.GeneralLabel.tau
        {
          now := config.now
          actors :=
            Store.update
              (Store.update
                config.actors
                senderName
                {
                  state := sender.state
                  activeBody := remaining
                })
              receiverName
              {
                state :=
                  {
                    valuation := receiver.state.valuation
                    bag :=
                      receiver.state.bag ++
                        [{
                          sender := senderName
                          messageName := messageName
                          payload := payload
                          arrival :=
                            LogicalTime.after
                              config.now
                              delay
                        }]
                  }
                activeBody := receiver.activeBody
              }
        }

  /--
  `TAKE`. The selected actor removes a due message from its bag, binds the server's parameters into its
  valuation, and installs the server body as its continuation.

  **The message is taken by decomposition, not from the head of the bag.** `hDue` splits the bag as
  `earlier ++ message :: later`, so the rule can reach any position. Taking the head would have been a
  silent defect: `earliestDueArrival` (`Relico/DTR/GeneralState.lean:142`) scans the **whole** bag for the
  minimum arrival among messages due at `now`, and `readyActorsOf` puts that minimum into the selected
  record's `logicalTime`. A bag whose head is a *future* message but whose tail holds a due one makes the
  actor ready while its head is not takeable, so a head-only rule would be stuck exactly where the state
  layer says the actor may run. `hArrival` ties the taken message to the selection: its arrival must be the
  arrival G1 selected on.

  **What is left nondeterministic, on purpose.** When two messages in one bag share that earliest arrival,
  `hDue` admits either. The paper supplies no tie rule (F27), and §7's settled position is that stage G
  proves determinism *relative to the guard* and proves nothing about tie behaviour rather than quietly
  picking declaration order and calling it correct. A weak bisimulation tolerates this — both sides may
  branch — but G2b must relate the branches, so this is flagged rather than hidden.

  **Premised on the actor being idle.** Table I's `TAKE` requires the continuation to be `ε`. This is what
  makes `R`'s third component do work in G2b: without it an actor could accept a second message mid-body
  and the two sides' continuations would diverge with nothing to notice.

  **The cohort is read through `erase`.** `selectedActor` takes the continuation-free
  `DTR.GeneralConfiguration` because G1 was built before continuations existed, and
  `GeneralRuntimeConfiguration.erase` is exactly that projection. Reuse rather than workaround: a second
  cohort computation would be a second definition of one convention, free to drift from the one G1 proved
  five theorems about.

  This rule is **observable**, carrying `.consume` with the receiver and the message taken.
  -/
  | take
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
        Store.lookup config.actors actorName = some actor)
      (hIdle :
        actor.idle = true)
      (hDue :
        actor.state.bag = earlier ++ message :: later)
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
        (DTR.GeneralLabel.consume actorName message)
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
        }

  /--
  `TIME PROGRESS`. Advance `now` to the next message arrival, leaving every actor untouched.

  **Observable, carrying `.timeAdvance`.** Three premises, and the third is **F74's repair**.

  Strictness and quiescence alone — the two premises this rule shipped with — let the clock jump to an
  *arbitrary* later time. Quiescence is decided by `readyActors`, which reaches `DTR.earliestDueArrival`,
  and that function only ever inspects messages with `arrival ≤ now`. So a bag holding one message
  arriving at 5 with `now = 3` is quiescent, and the rule admitted an advance to 100 — straight over the
  arrival, with the message still sitting in the bag afterwards.

  That made Lemma 1 false and broke Definition 1's **forward** condition, because
  `LF.GeneralStep.timeAdvance` can only reach the earliest pending event's tag and so offers no
  counterpart to the jump. The paper never allowed it: Lemma 1's time case advances "to the minimum
  message arrival time `ar_min`", and Theorem 1's says "time progresses to the next message arrival
  `ar_min`". `DTR.GeneralConfiguration.nextArrival` is that `ar_min`, up to the one restriction the paper
  puts on the comprehension and this development drops — Table I minimises over actors whose continuation
  is `ϵ`, which P17 records as vacuous there and which is not vacuous here, because this rule lets the
  clock advance mid-body. `GeneralState.lean`'s section header argues that case; `hSelected` pins `future`
  to the answer.

  Note the direction. It would also close the gap to weaken the *target* until it too could jump, and the
  docstring this repair replaces argued that way round. That is backwards: a bisimulation between two
  relations that both over-approximate proves nothing about the translator, and the target rule is the one
  matching a real LF scheduler. The permissive side was the source, so the source is what tightens.

  `hForward` is kept even though it is now implied — `earliestFutureArrival` filters on
  `now < message.arrival`, so `nextArrival` never answers with a time at or before `now`. Keeping it lets
  `GeneralStep.lt_of_timeAdvance` read strictness straight off a premise; deriving it from `hSelected`
  instead would need the store-level soundness lemma that row 7 owes.

  Together the premises make the rule **refuse** rather than quietly under-deliver when nothing is
  pending: `nextArrival` answers `none` on a store with no future message, so the clock cannot move at
  all. That matches the target, whose `timeAdvance` likewise needs an event to advance to. The landed
  witness in `Relico/Tests/GeneralSemantics.lean` had to be rewritten for it — it built a step on an
  *empty* configuration, which this rule no longer admits — and its docstring records the substitution.
  That rewrite is the evidence; nothing here pins the refusal itself, since a negative would have to
  quantify over every `future`.

  P24's split lives on the **LF** side, where a tag has a microstep component. `LogicalTime` has no
  microstep, so this rule is the source's whole time story and stays observable.
  -/
  | timeProgress
      {config : GeneralRuntimeConfiguration}
      {future : LogicalTime}
      (hForward :
        config.now < future)
      (hQuiescent :
        DTR.GeneralConfiguration.readyActors config.erase = [])
      (hSelected :
        DTR.GeneralConfiguration.nextArrival config.erase =
          some future) :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance config.now future)
        {
          now := future
          actors := config.actors
        }


/-!
## Inversion

What a step's **label** already tells you about its endpoints. G2b cases on a source step and builds a
target step from it; these are the endpoint facts it needs on the way, stated once here instead of
re-derived at each of its cases.

This section is deliberately equalities and extractions, **not** a structural characterization.
`Relico/DTR/GlobalMultiStorePayloadOneStep.lean`'s `Step.iff_externalSendFrame_or_dispatch` can state its
inversion as a disjunction of existentials because each of its disjuncts is a separately *named* relation.
`GeneralStep`'s five rules are not named separately, so the same shape here would be a disjunction of five
seven-binder existentials — a second spelling of the constructor list, free to drift from it, which is the
mistake this repository has already paid for twice. `cases` delivers the structure for free. What it does
not deliver is the clock arithmetic, so that is what is proved.

Two conventions are taken from that same file, where both are green. Names in a `cases … with | ctor …`
alternative bind the constructor's **explicit** fields only — its implicit data fields are auto-named even
when the indices do not determine them — and an existential witness is then supplied as `_`
(`⟨_, _, hFrame⟩` there, `⟨_, hSelected, hName, hArrival⟩` here). Unconsumed hypotheses are bound to `_`
rather than named, so that the `unusedVariables` linter has nothing to report and the warning count does
not move.

Names are dotted at the top level rather than wrapped in a `namespace GeneralStep` block, following
`ExternalSendFrameStep.attempt_eq` and `ActorPriorityDispatchStep.dispatch`.
-/

/--
A τ step leaves the clock alone.

All three τ rules rebuild the configuration with `now := config.now`, so this is `rfl` in each case; the content is in
the *absence* of a fourth case. `take` and `timeProgress` are eliminated by index unification — their labels
are `.consume` and `.timeAdvance`, neither of which unifies with `.tau` — so this theorem says that no
internal source step can move logical time. G2b needs exactly that to keep a τ step's target tag at the
same time component.
-/
theorem GeneralStep.now_eq_of_tau
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    (hStep :
      GeneralStep
        model
        config
        DTR.GeneralLabel.tau
        next) :
    next.now = config.now := by

  cases hStep with

  | assign _ _ _ =>
      rfl

  | trace _ _ =>
      rfl

  | send _ _ _ _ _ =>
      rfl

/--
A `TAKE` leaves the clock alone too.

Taking a message is observable but not a passage of time: the actor's bag and continuation change, `now`
does not. Together with `now_eq_of_tau` this leaves `timeProgress` as the *only* rule that moves the clock,
which is what makes the source's time story small enough for G2c to relate to a target whose tags carry a
microstep as well.
-/
theorem GeneralStep.now_eq_of_consume
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume receiver message)
        next) :
    next.now = config.now := by

  cases hStep with

  | take _ _ _ _ _ _ _ =>
      rfl

/--
A consumed message was consumed by the actor G1 selected, at the arrival G1 selected on.

This is the load-bearing inversion of the three. `.consume` carries a receiver and a message but says
nothing about *why* that pair was eligible; G2b has to reproduce the same choice on the target side, and the
only thing that pins it is `selectedActor`. Returning the selection record itself — rather than just the
name — is what lets the arrival be recovered, and the arrival is what distinguishes a due message from one
merely sitting in the bag.

The witness is `_`: the record is an implicit field of `take`, so it is auto-named and unreachable, exactly
as `frame` and `result` are in `Step.iff_externalSendFrame_or_dispatch`.
-/
theorem GeneralStep.selected_of_consume
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume receiver message)
        next) :
    ∃ selected,
      DTR.GeneralActorSelection.selectedActor
          model
          config.erase =
        some selected ∧
      selected.actorName = receiver ∧
      message.arrival = selected.logicalTime := by

  cases hStep with

  | take hSelected hName _ _ _ hArrival _ =>
      exact ⟨_, hSelected, hName, hArrival⟩

/--
A consumed message was consumed by an actor that existed and had run its previous body to the end.

The `idle` half is the premise that makes `R`'s continuation component do work in G2b: a source actor
accepts a message only from `ε`, so the target reactor it is related to is never mid-reaction when its
counterpart dispatches.
-/
theorem GeneralStep.idle_of_consume
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume receiver message)
        next) :
    ∃ actor,
      Store.lookup config.actors receiver = some actor ∧
      actor.idle = true := by

  cases hStep with

  | take _ _ hActor hIdle _ _ _ =>
      exact ⟨_, hActor, hIdle⟩

/--
A consumed message was in the bag beforehand, somewhere.

Stated as a decomposition rather than as a membership because that is the form `take` is premised on, and
because the two remainders are what the successor bag is built from. Anything wanting mere membership can
get it from this; going the other way would need the position back.

Note what this does **not** say: nothing here fixes *which* position, and that is the deliberate
nondeterminism recorded on `take`. A caller that needs a unique position needs a tie rule, and the paper
supplies none (F27).
-/
theorem GeneralStep.bag_of_consume
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume receiver message)
        next) :
    ∃ actor earlier later,
      Store.lookup config.actors receiver = some actor ∧
      actor.state.bag = earlier ++ message :: later := by

  cases hStep with

  | take _ _ hActor _ hDue _ _ =>
      exact ⟨_, _, _, hActor, hDue⟩

/--
A consumed message had a message server to run.

G2b's target step is a reaction firing, and the reaction it fires is compiled from this server. Without
this the correspondence would have to re-perform the two lookups `messageServerFor?` composes and argue
that they agree with the ones the rule used — the drift this file's helper exists to prevent.
-/
theorem GeneralStep.server_of_consume
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {receiver : ActorName}
    {message : DTR.GeneralMessage}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.consume receiver message)
        next) :
    ∃ server,
      DTR.GeneralModel.messageServerFor?
          model
          receiver
          message.messageName =
        some server := by

  cases hStep with

  | take _ _ _ _ _ _ hServer =>
      exact ⟨_, hServer⟩

/--
A time advance reports the clock it left as its first label component.

Without this the label would be an unchecked annotation: a rule could emit `.timeAdvance 0 5` from a
configuration at 3 and nothing would notice. G2d's finite-trace agreement compares projected label *lists*,
so a label that does not determine the clock it came from would make two disagreeing runs trace-equal.
-/
theorem GeneralStep.before_eq_of_timeAdvance
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance before after)
        next) :
    before = config.now := by

  cases hStep with

  | timeProgress _ _ _ =>
      rfl

/--
A time advance arrives at the clock it reports as its second label component.
-/
theorem GeneralStep.now_eq_of_timeAdvance
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance before after)
        next) :
    next.now = after := by

  cases hStep with

  | timeProgress _ _ _ =>
      rfl

/--
A time advance touches no actor.

The clock moves and the store is carried across unchanged, so every bag, valuation and continuation
survives. G2b's correspondence relation is a conjunction over the actor store, and this is what lets its
time-advance case reuse the incoming instance of that conjunction instead of rebuilding it.
-/
theorem GeneralStep.actors_eq_of_timeAdvance
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance before after)
        next) :
    next.actors = config.actors := by

  cases hStep with

  | timeProgress _ _ _ =>
      rfl

/--
A time advance goes strictly forward.

Recovered from the rule's own premise rather than from the endpoints, because the endpoints alone would
give it only after `before_eq_of_timeAdvance` and `now_eq_of_timeAdvance` had both been applied. Note the
statement is at `LogicalTime`, so **F72** applies to every consumer: a `<` between two `LogicalTime`s is
invisible to `omega`, and a caller combining this with another bound must reach for an explicit `Nat`
lemma. The proof itself needs neither, since the premise is the conclusion.
-/
theorem GeneralStep.lt_of_timeAdvance
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance before after)
        next) :
    before < after := by

  cases hStep with

  | timeProgress hForward _ _ =>
      exact hForward

/--
Time advances only from a configuration where nothing is ready.

This is the maximal-progress half of `TIME PROGRESS` and the reason the source is not free to idle past
due work. G2c consumes it in the direction that matters: a target run that fires a reaction at the current
tag cannot be matched by a source run that skipped it, because the source could not have advanced.
-/
theorem GeneralStep.quiescent_of_timeAdvance
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance before after)
        next) :
    DTR.GeneralConfiguration.readyActors config.erase = [] := by

  cases hStep with

  | timeProgress _ hQuiescent _ =>
      exact hQuiescent

/--
A time advance lands exactly on the next message arrival.

**F74's payoff, and the theorem that makes the repaired premise usable.** The mirror of
`LF.GeneralStep.selected_of_timeAdvance`, which ties the target's advance to its queue; this ties the
source's to its bags. G2b's time case matches one source advance against one target advance, and with
both selection theorems in hand the two chosen times are each pinned to a minimum rather than one being
pinned and the other merely bounded — which is what Lemma 1 needs and what it could not have had while
`future` was arbitrary.

Row 7 still owes the store-level bridge from `nextArrival` to a named message: `earliestFutureArrival`
carries soundness, completeness and minimality per bag, but `earliestFutureArrivalOf` has no lemmas yet,
because their useful shape is decided by the bag-to-queue component of R rather than guessable here.
-/
theorem GeneralStep.selected_of_timeAdvance
    {model : DTR.GeneralModel}
    {config next : GeneralRuntimeConfiguration}
    {before after : LogicalTime}
    (hStep :
      GeneralStep
        model
        config
        (DTR.GeneralLabel.timeAdvance before after)
        next) :
    DTR.GeneralConfiguration.nextArrival config.erase =
      some after := by

  cases hStep with

  | timeProgress _ _ hSelected =>
      exact hSelected

end DTR
end Relico
