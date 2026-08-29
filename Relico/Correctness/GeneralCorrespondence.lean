import Relico.DTR.GeneralRuntime
import Relico.LF.GeneralSemantics
import Relico.DTR.GeneralInitialization
import Relico.LF.GeneralInitialization
import Relico.Correctness.GeneralEvaluation

set_option autoImplicit false

namespace Relico
namespace Correctness

/-!
# The correspondence relation of the general family

Obligation G2b, first half: the relation the paper calls `R`, together with the two facts about it that
can be proved before any step case is attempted — that it survives a retag which keeps logical time, and
that it holds at an initial state. Lemma 1, the time equivalence, is the second half and lives in
`Relico/Correctness/GeneralTimeEquivalence.lean`; the transfer conditions of Definition 1 are G2c.

The module lives under `Correctness/` because it is the first general-family declaration that mentions
both languages at once, which is the boundary `Relico/Correctness/GeneralEvaluation.lean` established
one obligation earlier and which `docs/STAGE_G_FINDINGS.md` F66 part 3 records as the corpus convention.

## The paper's relation, and the four ways ours differs from it

The paper relates a DTR state to an LF state by three per-actor conjuncts — `e_x ≡ η_r` on valuations,
`b_x ≡ q_r` on the message bag against the reactor's event queue, and `π_x ≡ µ_r` on the continuation —
plus the logical-time agreement Lemma 1 states separately. `GeneralStateCorrespondence` below keeps all
four and adds one field the paper has no need of. Each difference is forced by a measurement, so each is
recorded here rather than left for a reader to reconstruct.

**Quantification is over membership, not over lookup.** `Relico/Common/Store.lean`'s own header says the
first binding for a key is the observable one, while `DTR.GeneralConfiguration.nextArrival` minimises
over *every* binding in *every* bag, shadowed ones included. A relation stated through `Store.lookup`
would therefore say nothing about a shadowed actor, whose message could still decide when the source
clock advances — and Lemma 1 would be false for exactly the reason F74 made it false, one obligation
earlier. Membership is the stronger statement, it is what `DTR.nextArrival_sound` hands back, and a
caller holding only a lookup can convert with `Store.mem_of_lookup`. No `Nodup` hypothesis is needed
anywhere as a result, which is the second reason to prefer it: a duplicate actor name is legal in the
source AST and the well-formedness layer does not forbid it.

**Nothing here constrains the microstep.** `docs/STAGE_G_DESIGN.md` §15 item 3 predicted that a τ step
must not change any state `R` constrains; F75 part 1 measures that this is false for five of the six
τ-emitting constructors, all of which change a valuation, a bag, a queue or a continuation. The one τ
step with **no counterpart on the other side** is `LF.GeneralStep.microstepAdvance`, which is P24's
zero-delay send, and it changes only the microstep. So the checkable content of that prediction is that
`R` must be blind to `LF.Tag.microstep`, and `generalCorrespondence_microstepAdvance` below is the proof
that it is: the target may take that step at will and stay related.

**The bag/queue conjunct is per-actor on one side and global on the other.** DTR gives each actor its own
`bag`; `LF.GeneralRuntimeState` carries **one** `pending` queue whose events name their `target`. The
paper's LF state instead maps each reactor to a triple `(η_r, q_r, µ_r)`, so its `q_r` is already
per-reactor and the mismatch is ours, not a defect of the paper — F75 part 3. `GeneralPendingAgrees`
therefore takes the actor's name and selects the global queue by it, and
`GeneralStateCorrespondence.pendingTargeted` is the extra field: it says no event targets an actor the
source does not have. Without it the two directions of the per-actor agreement could both hold while the
queue carried events for a reactor that corresponds to nothing.

**The queue agreement is on time and target, deliberately not a bijection.** Multiplicity — that a bag
holding two identical messages meets a queue holding two matching events — is G2c's business, because it
is the transfer conditions that consume it, and stating it here would mean proving it here with no
consumer. What is stated is the two directions separately, so neither side may hold a message the other
cannot account for at the same logical time.

The multi-store family's `PendingCorresponds` is not reusable for this. It pins the target action name as
a function of the source message name, and general action names are per **send site**
(`Translation.generalActionNameAtSite`, the F56 repair), while `DTR.GeneralMessage` records no site — its
four fields are `sender`, `messageName`, `payload` and `arrival`. The site is not recoverable from a
message, so an agreement that mentioned the action name would be unprovable rather than merely stronger.
Logical time is recoverable, and that is what the definition uses.
-/

/--
One actor's messages, against the events of the global queue that target it.

Two directions, and each is weaker than a bijection on purpose — see the module note. The forward
direction says every message in the bag has an event at the same logical time aimed at this actor; the
backward direction says every event aimed at this actor has a message at the same logical time.

`name` is a parameter rather than being read off the events because the source side has no target field
to read: an actor's bag is identified by *where it is stored*, and the correspondence is what connects
that position to the `target` field the target side does carry.
-/
def GeneralPendingAgrees
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    (pending : LF.GeneralEventQueue) :
    Prop :=
  (∀ message : DTR.GeneralMessage,
      message ∈ bag →
        ∃ event : LF.GeneralPendingEvent,
          event ∈ pending ∧
            event.target = name ∧
              event.tag.time = message.arrival) ∧
    (∀ event : LF.GeneralPendingEvent,
        event ∈ pending →
          event.target = name →
            ∃ message : DTR.GeneralMessage,
              message ∈ bag ∧
                message.arrival = event.tag.time)

/--
An empty bag agrees with an empty queue.

Stated for the same reason `generalValuationAgrees_empty` is stated one module earlier: it makes the
definition demonstrably **satisfiable**, so the results below are not theorems about an empty hypothesis.
`docs/STAGE_G_FINDINGS.md` F66 part 5 is a finding about a conjunct of the paper's own relation being
trivially true, and a module that took an unsatisfiable hypothesis would repeat that defect while
building green.

Note that it is not enough to empty the bag: with a non-empty queue the backward direction would demand a
message for every event that targets this actor. That asymmetry is the point of stating both directions.
-/
theorem generalPendingAgrees_empty
    (name : ActorName) :
    GeneralPendingAgrees
      name
      []
      [] := by

  constructor

  · intro message hMessage

    cases hMessage

  · intro event hEvent

    cases hEvent

/-!
### Reading the two directions

`GeneralPendingAgrees` is a `Prop`-valued `def`, not a structure, so a caller cannot write `hAgrees.left`.
Dot notation resolves in the namespace of the *head symbol of the hypothesis' type*, which here is
`Relico.Correctness.GeneralPendingAgrees`, and that namespace has no `left`; the conjunction only appears
after the definition is unfolded. The two theorems below are the accessors, so that every consumer opens the
definition the same way rather than each one reaching for a tactic that happens to work.

The `unfold … at` step is the idiom `DTR.nextArrival_sound` uses for exactly this: a definition handed over
inside a hypothesis, opened once so the delegated lemma applies.
-/

/--
Every source message has a target event at its instant.

The forward direction — the one Lemma 1 uses when the source is waiting and the target must be shown to
have something pending to advance to.
-/
theorem generalPendingAgrees_event_of_message
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    (pending : LF.GeneralEventQueue)
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        pending)
    (message : DTR.GeneralMessage)
    (hMessage :
      message ∈ bag) :
    ∃ event : LF.GeneralPendingEvent,
      event ∈ pending ∧
        event.target = name ∧
          event.tag.time = message.arrival := by

  unfold GeneralPendingAgrees at hAgrees

  exact
    hAgrees.left
      message
      hMessage

/--
Every target event aimed at this actor has a source message at its instant.

The backward direction — the one Lemma 1 uses when the target selects an event and the source must be shown
to have a matching arrival, so that the instant the target moves to is one the source can also reach. The
`target` premise is what makes this per-actor: the queue is global, and an event aimed elsewhere says
nothing about this bag.
-/
theorem generalPendingAgrees_message_of_event
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    (pending : LF.GeneralEventQueue)
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        pending)
    (event : LF.GeneralPendingEvent)
    (hEvent :
      event ∈ pending)
    (hTarget :
      event.target = name) :
    ∃ message : DTR.GeneralMessage,
      message ∈ bag ∧
        message.arrival = event.tag.time := by

  unfold GeneralPendingAgrees at hAgrees

  exact
    hAgrees.right
      event
      hEvent
      hTarget

/--
The target continuation is a compilation of the source continuation.

The paper's `π_x ≡ µ_r`. It is an existential over the compiler's three auxiliary inputs rather than an
equation against a named target body, because a source continuation alone does not determine them: the
output-port environment belongs to the sending class, the body context belongs to the message server, and
the index is the statement's address inside it. None of the three is recoverable from a
`DTR.GeneralBody`.

**This is a documented weakening, not a finished statement.** As written, the relation permits a target
continuation compiled under some *other* class's port environment. Tightening it means pinning the
environment to the one the program being executed actually built, which in turn means giving `R` the two
programs as parameters — the paper's `R` is likewise indexed by a fixed pair of systems. Nothing in this
module needs the tighter form: the two theorems below are about an empty continuation and about a step
that changes no continuation at all. G2c is where a statement step must be transferred, and G2c is where
the environment first has a name to be pinned to, so that is where the parameter belongs if it is needed.
Recording the slack here is the alternative to discovering it there.

`Except String LF.GeneralBody` is the compiler's return type, so `.ok` is spelled out as `Except.ok` to
keep the definition readable without the expected type in view.
-/
def GeneralContinuationCompiles
    (source : DTR.GeneralBody)
    (target : LF.GeneralBody) :
    Prop :=
  ∃ env : Translation.GeneralOutputPortEnv,
    ∃ context : Translation.GeneralBodyContext,
      ∃ index : Nat,
        Translation.compileGeneralBody
            env
            context
            index
            source =
          Except.ok target

/--
The empty continuation compiles to the empty continuation.

The satisfiability witness, and the case both theorems below actually use: every actor is idle initially,
and `Translation.compileGeneralBody_nil` is an `@[simp]` `rfl` lemma, so the three auxiliary inputs may be
anything at all. The empty port environment and `default` context are chosen because they are the two
values that need no construction.
-/
theorem generalContinuationCompiles_nil :
    GeneralContinuationCompiles
      []
      [] :=
  ⟨[],
   default,
   0,
   Translation.compileGeneralBody_nil
     []
     default
     0⟩

/--
Consuming a trace head preserves the compilation relation for the remaining continuations.

The compiler emits the trace statement literally, so inversion of a successful body compilation exposes
the same trace head and advances the statement index by one. This is the continuation fact used by any
future correspondence transfer case for the internal instrumentation rule.
-/
theorem generalContinuationCompiles_trace_tail
    {tag : String}
    {sourceRemaining : DTR.GeneralBody}
    {targetRemaining : LF.GeneralBody}
    (hCompiles :
      GeneralContinuationCompiles
        (.trace tag :: sourceRemaining)
        (.trace tag :: targetRemaining)) :
    GeneralContinuationCompiles
      sourceRemaining
      targetRemaining := by

  rcases hCompiles with
    ⟨env, context, index, hCompiled⟩

  obtain
    ⟨compiledStatement, compiledRemaining, hStatement, hRemaining, hEqual⟩ :=
      Translation.compileGeneralBody_cons_ok_inversion
        hCompiled

  rw [Translation.compileGeneralStmt_trace] at hStatement
  injection hStatement with hStatement
  subst compiledStatement

  injection hEqual with hRemainingTarget
  subst targetRemaining

  exact
    ⟨env,
     context,
     index + 1,
     hRemaining⟩

/--
One actor against one reactor: the paper's three per-actor conjuncts.

`valuation` **reuses** `GeneralValuationAgrees` from `Relico/Correctness/GeneralEvaluation.lean`, whose own
docstring names this obligation as its consumer. Redefining it here would be the defect this development
keeps finding, and it would silently detach G2a-i's evaluation theorems from the relation they were proved
for.

The queue is passed whole rather than filtered to this actor, and `GeneralPendingAgrees` does the selecting
by `name`. Filtering first would need a `List.filter` and would then owe lemmas relating membership in the
filtered queue to membership in the real one, to no benefit: the relation is the only consumer.
-/
structure GeneralActorCorresponds
    (name : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (reactor : LF.GeneralReactorRuntime)
    (pending : LF.GeneralEventQueue) :
    Prop where

  valuation :
    GeneralValuationAgrees
      actor.state.valuation
      reactor.valuation

  messages :
    GeneralPendingAgrees
      name
      actor.state.bag
      pending

  continuation :
    GeneralContinuationCompiles
      actor.activeBody
      reactor.activeBody

/-- A paired trace head may be removed from an actor correspondence. -/
theorem generalActorCorresponds_trace_tail
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {reactor : LF.GeneralReactorRuntime}
    {pending : LF.GeneralEventQueue}
    {tag : String}
    {sourceRemaining : DTR.GeneralBody}
    {targetRemaining : LF.GeneralBody}
    (hCorresponds :
      GeneralActorCorresponds
        name
        actor
        reactor
        pending)
    (hSource :
      actor.activeBody =
        .trace tag :: sourceRemaining)
    (hTarget :
      reactor.activeBody =
        .trace tag :: targetRemaining) :
    GeneralActorCorresponds
      name
      {
        state := actor.state
        activeBody := sourceRemaining
      }
      {
        valuation := reactor.valuation
        activeBody := targetRemaining
      }
      pending := by

  refine
    {
      valuation := hCorresponds.valuation
      messages := hCorresponds.messages
      continuation := ?_
    }

  apply generalContinuationCompiles_trace_tail
  simpa [hSource, hTarget] using hCorresponds.continuation

/--
The idle case: an actor with an empty bag and no work left corresponds to a reactor with no work left.

Factored out because both directions of `generalCorrespondence_initial` need it and each reaches it
through a differently-spelled actor — one obtained by inverting `DTR.attachEmptyContinuations`, the other
built by hand. Stating it once means the emptiness hypotheses are discharged once.

Only the valuation carries information here, which is exactly F66 part 5's observation about the paper's
own initial case, and the reason the other two conjuncts must still be *stated*: a conjunct that is
trivial initially is not trivial after a step.
-/
theorem generalActorCorresponds_idle
    (name : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (reactor : LF.GeneralReactorRuntime)
    (hValuation :
      GeneralValuationAgrees
        actor.state.valuation
        reactor.valuation)
    (hBag :
      actor.state.bag = [])
    (hSource :
      actor.activeBody = [])
    (hTarget :
      reactor.activeBody = []) :
    GeneralActorCorresponds
      name
      actor
      reactor
      [] := by

  refine
    {
      valuation := hValuation
      messages := ?_
      continuation := ?_
    }

  · rw [hBag]

    exact generalPendingAgrees_empty name

  · rw [
      hSource,
      hTarget
    ]

    exact generalContinuationCompiles_nil

/--
The relation `R` of the paper's Definition 1, on our two runtime states.

Four fields. `logicalTime` is Lemma 1's equation, kept as a *field* rather than proved as a consequence,
because it is a conjunct of the paper's relation and G2c's transfer conditions consume it directly;
`Relico/Correctness/GeneralTimeEquivalence.lean` is where it is put to work against the two arrival
computations. `reactorOfActor` and `actorOfReactor` are the two directions of the per-actor
correspondence, each carrying `GeneralActorCorresponds`. `pendingTargeted` is the field the paper has no
counterpart for, and the module note says why: its LF state gives each reactor its own event queue, while
ours has one global queue whose events name a target that might not exist.

**The microstep is deliberately unconstrained** — see the module note and
`generalCorrespondence_microstepAdvance`. So is the *order* of the two stores, and so are shadowed
bindings beyond the requirement that each one be related: `Store` is an association list, and two stores
that relate pointwise need not be equal.
-/
structure GeneralStateCorrespondence
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState) :
    Prop where

  logicalTime :
    state.currentTag.time = config.now

  reactorOfActor :
    ∀ (name : ActorName) (actor : DTR.GeneralActorRuntime),
      (name, actor) ∈ config.actors →
        ∃ reactor : LF.GeneralReactorRuntime,
          (name, reactor) ∈ state.reactors ∧
            GeneralActorCorresponds
              name
              actor
              reactor
              state.pending

  actorOfReactor :
    ∀ (name : ActorName) (reactor : LF.GeneralReactorRuntime),
      (name, reactor) ∈ state.reactors →
        ∃ actor : DTR.GeneralActorRuntime,
          (name, actor) ∈ config.actors ∧
            GeneralActorCorresponds
              name
              actor
              reactor
              state.pending

  pendingTargeted :
    ∀ event : LF.GeneralPendingEvent,
      event ∈ state.pending →
        ∃ actor : DTR.GeneralActorRuntime,
          (event.target, actor) ∈ config.actors

/--
Retagging the target preserves the relation, provided logical time is unchanged.

The whole content of the claim is in what `GeneralStateCorrespondence` does *not* mention: three of its
four fields are about the two stores and the queue, and the fourth reads only `Tag.time`. So a tag may be
replaced by any tag with the same time. Stated separately from its consumer below because it is the
general fact, and because it is the fact that would break first if a later obligation added a microstep
constraint to the relation — a regression there fails here rather than deep inside a step case.
-/
theorem generalCorrespondence_retag
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (tag : LF.Tag)
    (hTime :
      tag.time = state.currentTag.time)
    (hCorrespondence :
      GeneralStateCorrespondence config state) :
    GeneralStateCorrespondence
      config
      {
        currentTag := tag
        reactors := state.reactors
        pending := state.pending
      } := by

  exact
    {
      logicalTime :=
        hTime.trans
          hCorrespondence.logicalTime
      reactorOfActor :=
        hCorrespondence.reactorOfActor
      actorOfReactor :=
        hCorrespondence.actorOfReactor
      pendingTargeted :=
        hCorrespondence.pendingTargeted
    }

/--
The one τ step with no source counterpart keeps the relation.

`LF.GeneralStep.microstepAdvance` is P24's zero-delay send: the earliest pending event sits at the current
logical time and a later microstep, so the target moves to it while the source cannot move at all. The
paper's Theorem 1 has no case for this, which is what P24 records; what makes the omission harmless is
precisely this theorem, because a τ step that lands in a related state is absorbed by the *weak*
transition relation the architecture is built on (`docs/STAGE_G_FINDINGS.md`, and
`Relico/Common/WeakTransition.lean` for the generic machinery).

This is also the checkable residue of `docs/STAGE_G_DESIGN.md` §15 item 3, whose stated form — that a τ
step changes nothing `R` constrains — is false for the other five τ-emitting constructors. F75 part 1
records that measurement.

All three premises of the constructor are taken as hypotheses and all three are used: `hSelected` and
`hMicrostep` to build the step, `hTime` to retag. The existential is over the *reached* state rather than
being an equation, because that is the shape G2c's forward transfer condition consumes.
-/
theorem generalCorrespondence_microstepAdvance
    (program : LF.GeneralProgram)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (event : LF.GeneralPendingEvent)
    (hSelected :
      LF.GeneralRuntimeState.earliestPendingEvent? state =
        some event)
    (hTime :
      event.tag.time = state.currentTag.time)
    (hMicrostep :
      state.currentTag.microstep < event.tag.microstep)
    (hCorrespondence :
      GeneralStateCorrespondence config state) :
    ∃ next : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          next ∧
        GeneralStateCorrespondence config next := by

  refine
    ⟨{
       currentTag := event.tag
       reactors := state.reactors
       pending := state.pending
     },
     ?_,
     ?_⟩

  · exact
      LF.GeneralStep.microstepAdvance
        hSelected
        hTime
        hMicrostep

  · exact
      generalCorrespondence_retag
        config
        state
        event.tag
        hTime
        hCorrespondence

/--
The relation holds at the start of a run — **the scoped form**, for callers holding two arbitrary
states.

Renamed from `generalCorrespondence_initial` when row 11's initializers landed, because the
unconditional statement took that name: this variant quantifies over an arbitrary source configuration
and an arbitrary target reactor store, hypothesising the three things an initializer establishes by
construction — every source bag empty, and the two stores covering each other with agreeing valuations
and idle bodies.

The hypotheses are exactly what a caller relating two states it did not build must check, which is why
the theorem survives its unconditional sibling: nothing downstream should re-derive the initial states
just to apply the initial case. `docs/STAGE_G_DESIGN.md` §7 item 1 records the scoped form's history,
and **F75** part 2 the reason both exist.

The source continuations need no hypothesis — `ofConfiguration` sets them all to `[]` by construction,
and `DTR.mem_attachEmptyContinuations` is how that fact is recovered from membership rather than from a
lookup. The pending queue is the literal `[]` for the same reason.
-/
theorem generalCorrespondence_initial_scoped
    (config : DTR.GeneralConfiguration)
    (reactors : Store ActorName LF.GeneralReactorRuntime)
    (hBags :
      ∀ (name : ActorName) (state : DTR.GeneralActorState),
        (name, state) ∈ config.actors →
          state.bag = [])
    (hReactors :
      ∀ (name : ActorName) (state : DTR.GeneralActorState),
        (name, state) ∈ config.actors →
          ∃ reactor : LF.GeneralReactorRuntime,
            (name, reactor) ∈ reactors ∧
              GeneralValuationAgrees
                  state.valuation
                  reactor.valuation ∧
                reactor.activeBody = [])
    (hActors :
      ∀ (name : ActorName) (reactor : LF.GeneralReactorRuntime),
        (name, reactor) ∈ reactors →
          ∃ state : DTR.GeneralActorState,
            (name, state) ∈ config.actors ∧
              GeneralValuationAgrees
                  state.valuation
                  reactor.valuation ∧
                reactor.activeBody = []) :
    GeneralStateCorrespondence
      (DTR.GeneralRuntimeConfiguration.ofConfiguration config)
      {
        currentTag :=
          {
            time := config.now
            microstep := 0
          }
        reactors := reactors
        pending := []
      } := by

  refine
    {
      logicalTime := ?_
      reactorOfActor := ?_
      actorOfReactor := ?_
      pendingTargeted := ?_
    }

  · rfl

  · intro name actor hMember

    have hAttached :
        (name, actor) ∈
          DTR.attachEmptyContinuations
            config.actors :=
      hMember

    obtain ⟨hState, hBody⟩ :=
      DTR.mem_attachEmptyContinuations
        config.actors
        name
        actor
        hAttached

    obtain
        ⟨reactor,
         hReactorMember,
         hValuation,
         hReactorBody⟩ :=
      hReactors
        name
        actor.state
        hState

    exact
      ⟨reactor,
       hReactorMember,
       generalActorCorresponds_idle
         name
         actor
         reactor
         hValuation
         (hBags
           name
           actor.state
           hState)
         hBody
         hReactorBody⟩

  · intro name reactor hMember

    obtain
        ⟨state,
         hStateMember,
         hValuation,
         hReactorBody⟩ :=
      hActors
        name
        reactor
        hMember

    refine
      ⟨{
         state := state
         activeBody := []
       },
       ?_,
       ?_⟩

    · exact
        DTR.mem_attachEmptyContinuations_of_mem
          config.actors
          name
          state
          hStateMember

    · exact
        generalActorCorresponds_idle
          name
          {
            state := state
            activeBody := []
          }
          reactor
          hValuation
          (hBags
            name
            state
            hStateMember)
          rfl
          hReactorBody

  · intro event hEvent

    simp at hEvent

/-!
## Constructor entry: the initial states the paper's "holds initially" line is about

Row 11's acquired obligation (**F75** part 2). `generalCorrespondence_initial` below is the
unconditional statement §7 item 1 specified and G2b could not state, over the two initializers
`DTR.GeneralModel.initialState` and `LF.GeneralProgram.initialState`. Its scoped predecessor is kept,
renamed `generalCorrespondence_initial_scoped`, because its three hypotheses are exactly what a caller
holding two arbitrary states must check, and F75's argument that the unconditional form follows "by
instantiation rather than re-proof" turned out to be **false in one respect worth recording**: the
scoped theorem relates idle actors with empty continuations, while the initializers install constructor
bodies as the active bodies. **F85** carries the discrepancy; the constructor-entry case needed its own
actor correspondence, `generalActorCorresponds_constructorEntry` below, rather than an instance of the
idle one.
-/

/--
Binding the constructor's parameters to the instance's arguments, on both sides, keeps two agreeing
valuations agreeing.

The source initializer's `DTR.bindParameters` and the target initializer's
`LF.bindReactionParameters` are the same recursion on two different declaration walks, and this is the
lemma that says so: the compiled name list is `parameters.map (·.name)` — which
`Translation.compileGeneralReactiveClass_startupParameterNames` proves is the startup reaction's
parameter list — and the compiled values are the pointwise image of the source's, which
`Translation.compileGeneralActorInstance_arguments` proves is the instance's compiled argument list.

The lockstep induction is the one both bind functions' equations dictate. A surplus on either side is
dropped by *both* — their own definitions do it, not this lemma — so the recursion needs no length
hypothesis at all.
-/
theorem generalValuationAgrees_bind :
    ∀ (parameters : List DTR.GeneralTypedParameter)
      (values : List DTR.GeneralValue)
      (source : DTR.GeneralValuation)
      (target : LF.GeneralValuation),
      GeneralValuationAgrees source target →
        GeneralValuationAgrees
          (DTR.bindParameters
              parameters
              values
              source)
          (LF.bindReactionParameters
              (parameters.map
                (fun parameter =>
                  parameter.name))
              (values.map
                Translation.compileGeneralValue)
              target) := by

  intro parameters
  induction parameters with

  | nil =>
      intro values source target hAgrees

      exact hAgrees

  | cons parameter remaining inductionHypothesis =>
      intro values source target hAgrees

      cases values with

      | nil =>
          exact hAgrees

      | cons head tail =>
          exact
            inductionHypothesis
              tail
              (Store.update
                  source
                  parameter.name
                  head)
              (Store.update
                  target
                  parameter.name
                  (Translation.compileGeneralValue
                    head))
              (generalValuationAgrees_update
                source
                target
                parameter.name
                head
                hAgrees)

/-!
### Private lookup helpers

Four small facts about the repository's recursive find functions, none of which the syntax modules
state: a found element carries the queried name, a lookup that answers can be turned into membership,
and — the one place the well-formedness layers' uniqueness clauses enter the initial correspondence —
a *member* of a list with duplicate-free names is the element its own name finds. Each is proved by
the same induction the find functions themselves are defined by.
-/

private theorem findActor?_name_of_eq_some :
    ∀ (instances : List DTR.GeneralActorInstance)
      (actorName : ActorName)
      (actor : DTR.GeneralActorInstance),
      DTR.findActor? instances actorName = some actor →
        actor.name = actorName := by

  intro instances
  induction instances with

  | nil =>
      intro actorName actor hFound

      simp [
        DTR.findActor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro actorName actor hFound

      by_cases hHead :
          head.name = actorName

      · rw [
          DTR.findActor?,
          if_pos hHead
        ] at hFound

        injection hFound with hFound

        subst hFound

        exact hHead

      · rw [
          DTR.findActor?,
          if_neg hHead
        ] at hFound

        exact
          inductionHypothesis
            actorName
            actor
            hFound

private theorem findActor?_of_mem_of_nodup :
    ∀ (instances : List DTR.GeneralActorInstance)
      (actor : DTR.GeneralActorInstance),
      actor ∈ instances →
        (instances.map
          (fun instanceDecl =>
            instanceDecl.name)).Nodup →
          DTR.findActor?
              instances
              actor.name =
            some actor := by

  intro instances
  induction instances with

  | nil =>
      intro actor hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro actor hMember hNodup

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          simp [
            DTR.findActor?
          ]

      | inr hTail =>
          have hHeadName :
              head.name ≠ actor.name := by
            intro hEqual

            have hMapped :
                head.name ∈
                  remaining.map
                    (fun instanceDecl =>
                      instanceDecl.name) := by
              rw [hEqual]

              exact
                List.mem_map_of_mem
                  hTail

            exact
              (List.nodup_cons.mp hNodup).1
                hMapped

          rw [
            DTR.findActor?,
            if_neg hHeadName
          ]

          exact
            inductionHypothesis
              actor
              hTail
              (List.nodup_cons.mp hNodup).2

private theorem findInstance?_of_mem_of_nodup :
    ∀ (instances : List LF.GeneralReactorInstance)
      (reactorInstance : LF.GeneralReactorInstance),
      reactorInstance ∈ instances →
        (instances.map
          (fun instanceDecl =>
            instanceDecl.name)).Nodup →
          LF.findInstance?
              instances
              reactorInstance.name =
            some reactorInstance := by

  intro instances
  induction instances with

  | nil =>
      intro reactorInstance hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro reactorInstance hMember hNodup

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          simp [
            LF.findInstance?
          ]

      | inr hTail =>
          have hHeadName :
              head.name ≠ reactorInstance.name := by
            intro hEqual

            have hMapped :
                head.name ∈
                  remaining.map
                    (fun instanceDecl =>
                      instanceDecl.name) := by
              rw [hEqual]

              exact
                List.mem_map_of_mem
                  hTail

            exact
              (List.nodup_cons.mp hNodup).1
                hMapped

          rw [
            LF.findInstance?,
            if_neg hHeadName
          ]

          exact
            inductionHypothesis
              reactorInstance
              hTail
              (List.nodup_cons.mp hNodup).2

private theorem findReactor?_of_mem_of_nodup :
    ∀ (reactors : List LF.GeneralReactor)
      (reactor : LF.GeneralReactor),
      reactor ∈ reactors →
        (reactors.map
          (fun candidate =>
            candidate.name)).Nodup →
          LF.findReactor?
              reactors
              reactor.name =
            some reactor := by

  intro reactors
  induction reactors with

  | nil =>
      intro reactor hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro reactor hMember hNodup

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          simp [
            LF.findReactor?
          ]

      | inr hTail =>
          have hHeadName :
              head.name ≠ reactor.name := by
            intro hEqual

            have hMapped :
                head.name ∈
                  remaining.map
                    (fun candidate =>
                      candidate.name) := by
              rw [hEqual]

              exact
                List.mem_map_of_mem
                  hTail

            exact
              (List.nodup_cons.mp hNodup).1
                hMapped

          rw [
            LF.findReactor?,
            if_neg hHeadName
          ]

          exact
            inductionHypothesis
              reactor
              hTail
              (List.nodup_cons.mp hNodup).2

private theorem findClass?_of_mem_of_nodup :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (reactiveClass : DTR.GeneralReactiveClass),
      reactiveClass ∈ classes →
        (classes.map
          (fun candidate =>
            candidate.name)).Nodup →
          DTR.findClass?
              classes
              reactiveClass.name =
            some reactiveClass := by

  intro classes
  induction classes with

  | nil =>
      intro reactiveClass hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro reactiveClass hMember hNodup

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          simp [
            DTR.findClass?
          ]

      | inr hTail =>
          have hHeadName :
              head.name ≠ reactiveClass.name := by
            intro hEqual

            have hMapped :
                head.name ∈
                  remaining.map
                    (fun candidate =>
                      candidate.name) := by
              rw [hEqual]

              exact
                List.mem_map_of_mem
                  hTail

            exact
              (List.nodup_cons.mp hNodup).1
                hMapped

          rw [
            DTR.findClass?,
            if_neg hHeadName
          ]

          exact
            inductionHypothesis
              reactiveClass
              hTail
              (List.nodup_cons.mp hNodup).2

private theorem mem_of_findReactor?_eq_some :
    ∀ (reactors : List LF.GeneralReactor)
      (reactorName : ReactorName)
      (reactor : LF.GeneralReactor),
      LF.findReactor? reactors reactorName = some reactor →
        reactor ∈ reactors := by

  intro reactors
  induction reactors with

  | nil =>
      intro reactorName reactor hFound

      simp [
        LF.findReactor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro reactorName reactor hFound

      by_cases hHead :
          head.name = reactorName

      · rw [
          LF.findReactor?,
          if_pos hHead
        ] at hFound

        injection hFound with hFound

        subst hFound

        exact
          List.mem_cons.mpr
            (Or.inl rfl)

      · rw [
          LF.findReactor?,
          if_neg hHead
        ] at hFound

        exact
          List.mem_cons.mpr
            (Or.inr
              (inductionHypothesis
                reactorName
                reactor
                hFound))

private theorem findReactor?_name_of_eq_some :
    ∀ (reactors : List LF.GeneralReactor)
      (reactorName : ReactorName)
      (reactor : LF.GeneralReactor),
      LF.findReactor? reactors reactorName = some reactor →
        reactor.name = reactorName := by

  intro reactors
  induction reactors with

  | nil =>
      intro reactorName reactor hFound

      simp [
        LF.findReactor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro reactorName reactor hFound

      by_cases hHead :
          head.name = reactorName

      · rw [
          LF.findReactor?,
          if_pos hHead
        ] at hFound

        injection hFound with hFound

        subst hFound

        exact hHead

      · rw [
          LF.findReactor?,
          if_neg hHead
        ] at hFound

        exact
          inductionHypothesis
            reactorName
            reactor
            hFound

/-!
### What a successful compilation already guarantees

Three local copies of `LF.GeneralProgram.wellFormed`'s conjunct extractors — private in
`Relico/LF/GeneralWellFormed.lean`, and duplicated here rather than de-privatised for the reason that
module records: a ten-clause predicate must not become ten independent obligations. The house proof
shape, `revert` then case-analysis on the clause's own name, survives appended conjuncts.
-/

private theorem instancesResolve_of_wellFormed
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed = true) :
    program.instancesResolve = true := by
  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.instancesResolve <;> simp

private theorem instanceNamesUnique_of_wellFormed
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed = true) :
    program.instanceNamesUnique = true := by
  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.instanceNamesUnique <;> simp

private theorem reactorNamesUnique_of_wellFormed
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed = true) :
    program.reactorNamesUnique = true := by
  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.reactorNamesUnique <;> simp

/--
A successfully compiled program instantiates no actor name twice.

The first of the three facts the initial correspondence needs and the model itself does not provide:
`DTR.GeneralModel.wellFormed` does constrain instance names through its topology clause, but the
theorem below takes none of that — compilation already refuses a program whose instance names collide,
through `instanceNamesUnique`, and pulling the fact off the compiled side is one proof where assuming
the model's well-formedness would be a second hypothesis saying the same thing.
-/
private theorem modelInstanceNames_nodup_of_compiled
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program) :
    (model.instances.map
      (fun instanceDecl =>
        instanceDecl.name)).Nodup := by
  have hProgramNames :
      (program.instances.map
        (fun instanceDecl =>
          instanceDecl.name)).Nodup :=
    of_decide_eq_true
      (instanceNamesUnique_of_wellFormed
        (Translation.compileGeneralModel_wellFormed
          hCompiled))

  rw [
    Translation.compileGeneralModel_instances
      hCompiled,
    List.map_map
  ] at hProgramNames

  have hNameFunction :
      (fun instanceDecl =>
          instanceDecl.name) ∘
        Translation.compileGeneralActorInstance =
        (fun instanceDecl =>
          instanceDecl.name) := by
    funext instanceDecl

    exact
      Translation.compileGeneralActorInstance_name
        instanceDecl

  rw [hNameFunction] at hProgramNames

  exact hProgramNames

/--
A successfully compiled program's instance names are duplicate-free, on the target's own list.
-/
private theorem programInstanceNames_nodup_of_compiled
    {program : LF.GeneralProgram}
    (hWellFormed :
      program.wellFormed = true) :
    (program.instances.map
      (fun instanceDecl =>
        instanceDecl.name)).Nodup :=
  of_decide_eq_true
    (instanceNamesUnique_of_wellFormed
      hWellFormed)

/--
A successfully compiled program declares no class name twice.

Pulled back through `reactorNamesUnique` and `Translation.reactorNameFor_injective`: reactor names are
the class names wrapped, so a duplicate class name would be a duplicate reactor name, which the guard
refuses. The map-map rearrangement is the whole proof.
-/
private theorem modelClassNames_nodup_of_compiled
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program) :
    (model.classes.map
      (fun reactiveClass =>
        reactiveClass.name)).Nodup := by
  have hReactorNames :
      (program.reactors.map
        (fun reactor =>
          reactor.name)).Nodup :=
    of_decide_eq_true
      (reactorNamesUnique_of_wellFormed
        (Translation.compileGeneralModel_wellFormed
          hCompiled))

  rw [
    Translation.compileGeneralModel_reactorNames
      hCompiled
  ] at hReactorNames

  have hRewritten :
      ((model.classes.map
          (fun reactiveClass =>
            reactiveClass.name)).map
        Translation.reactorNameFor).Nodup := by
    rw [List.map_map]

    exact hReactorNames

  exact
    Translation.nodup_of_nodup_map_injective
      Translation.reactorNameFor
      _
      hRewritten
      Translation.reactorNameFor_injective

/--
Everything the initial correspondence needs to know about one instance of a successfully compiled
model: its class resolves, that class compiled to a reactor of the program, and the reactor's startup
body, state variables and parameter names are that class's compilations.

This is the bridge between the two initializers. The source initializer resolves
`model.classOfActor?` and the target initializer resolves `program.reactorOfInstance?`, and nothing
upstream says the two resolutions agree — the model's instance may name a class the program's reactors
say nothing about. Compilation is what makes them agree, and this lemma is where that agreement becomes
usable: one bundle per instance, consumed once in each direction of the theorem below.

The last conjunct is stated through `reactor?` under the **instance's own class name**, because that is
the lookup `LF.GeneralProgram.initialState_lookup` needs, and it is what
`LF.GeneralReactorInstance.reactorName` holds after `Translation.compileGeneralActorInstance`.
-/
private theorem initialResolution
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program) :
    ∀ (instanceDecl : DTR.GeneralActorInstance),
      instanceDecl ∈ model.instances →
      ∃ (reactiveClass : DTR.GeneralReactiveClass)
         (routes : List Translation.GeneralRoute)
         (env : Translation.GeneralOutputPortEnv)
         (compiledBody : LF.GeneralBody)
         (reactor : LF.GeneralReactor),
        model.classOfActor? instanceDecl.name =
          some reactiveClass ∧
        Translation.compileGeneralReactiveClass
            model.classes
            routes
            reactiveClass =
          .ok reactor ∧
        reactor ∈ program.reactors ∧
        Translation.compileGeneralBody
            env
            { bodyKey := .constructor,
              selfSends :=
                Translation.selfSendsOfClass
                  reactiveClass }
            0
            reactiveClass.constructor.body =
          .ok compiledBody ∧
        reactor.startupReaction.body =
          compiledBody ∧
        reactor.stateVariables =
          reactiveClass.stateVariables.map
            Translation.compileGeneralStateVariableDecl ∧
        reactor.startupReaction.parameters =
          reactiveClass.constructor.parameters.map
            (fun parameter =>
              parameter.name) ∧
        program.reactor?
            (Translation.reactorNameFor
              instanceDecl.className) =
          some reactor := by

  intro instanceDecl hInstanceMember

  have hWellFormed :
      program.wellFormed = true :=
    Translation.compileGeneralModel_wellFormed
      hCompiled

  have hCompiledInstanceMember :
      (Translation.compileGeneralActorInstance
          instanceDecl) ∈
        program.instances := by
    rw [
      Translation.compileGeneralModel_instances
        hCompiled
    ]

    exact
      List.mem_map_of_mem
        hInstanceMember

  have hReactorLookup :
      ∃ reactor : LF.GeneralReactor,
        program.reactor?
            (Translation.reactorNameFor
              instanceDecl.className) =
          some reactor := by
    have hResolve :=
      (List.all_eq_true.mp
        (instancesResolve_of_wellFormed
          hWellFormed))
        _
        hCompiledInstanceMember

    rw [
      Translation.compileGeneralActorInstance_reactorName
    ] at hResolve

    cases hFound :
        program.reactor?
          (Translation.reactorNameFor
            instanceDecl.className) with

    | none =>
        rw [hFound] at hResolve

        simp at hResolve

    | some reactor =>
        exact
          ⟨reactor, rfl⟩

  obtain ⟨reactor, hReactorLookup⟩ :=
    hReactorLookup

  have hReactorMember :
      reactor ∈ program.reactors :=
    mem_of_findReactor?_eq_some
      program.reactors
      (Translation.reactorNameFor
        instanceDecl.className)
      reactor
      hReactorLookup

  obtain
      ⟨routes,
       _hRoutes,
       walk⟩ :=
    Translation.compileGeneralModel_startupBody
      hCompiled

  obtain
      ⟨reactiveClass,
       env,
       compiledBody,
       hClassMember,
       hClassCompiled,
       _hEnv,
       hBody,
       hStartupBody,
       hStateVariables,
       _hParameters⟩ :=
    walk reactor hReactorMember

  have hStartupParameters :
      reactor.startupReaction.parameters =
        reactiveClass.constructor.parameters.map
          (fun parameter =>
            parameter.name) :=
    Translation.compileGeneralReactiveClass_startupParameterNames
      hClassCompiled

  have hClassName :
      reactiveClass.name = instanceDecl.className := by
    apply
      Translation.reactorNameFor_injective

    rw [
      ← Translation.compileGeneralReactiveClass_name
        hClassCompiled,
      findReactor?_name_of_eq_some
        program.reactors
        (Translation.reactorNameFor
          instanceDecl.className)
        reactor
        hReactorLookup
    ]

  refine
    ⟨
      reactiveClass,
      routes,
      env,
      compiledBody,
      reactor,
      ?_,
      hClassCompiled,
      hReactorMember,
      hBody,
      hStartupBody,
      hStateVariables,
      hStartupParameters,
      hReactorLookup
    ⟩

  have hActorFound :
      DTR.findActor? model.instances instanceDecl.name =
        some instanceDecl :=
    findActor?_of_mem_of_nodup
      model.instances
      instanceDecl
      hInstanceMember
      (modelInstanceNames_nodup_of_compiled
        hCompiled)

  have hClassFound :
      DTR.findClass? model.classes instanceDecl.className =
        some reactiveClass := by
    have hByOwnName :
        DTR.findClass? model.classes reactiveClass.name =
          some reactiveClass :=
      findClass?_of_mem_of_nodup
        model.classes
        reactiveClass
        hClassMember
        (modelClassNames_nodup_of_compiled
          hCompiled)

    rw [hClassName] at hByOwnName

    exact hByOwnName

  simp only [
    DTR.GeneralModel.classOfActor?,
    DTR.GeneralModel.actor?,
    DTR.GeneralModel.class?,
    hActorFound,
    hClassFound
  ]

/--
One actor at constructor entry corresponds to one reactor at startup-entry, given the compilation facts
that connect the two.

The constructor-entry counterpart of `generalActorCorresponds_idle`, and — **F85** — the reason the
unconditional initial theorem is not an instance of the scoped one: both initializers install bodies
(the constructor's on the source side, the compiled startup reaction's on the target side), so neither
side is idle, and the idle lemma's two `activeBody = []` premises are unprovable here. What replaces
them is the continuation conjunct's real content: the target body is a successful `compileGeneralBody`
of the source body, witnessed by the environment and self-send list the reactor itself was compiled
against — which is exactly `GeneralContinuationCompiles`' existential.

The parameter correspondence is in the two bind hypotheses: the startup reaction's parameter names are
the class's (`hStartupParameters`), and the compiled instance's arguments are the source's
(`hArguments`), so `generalValuationAgrees_bind` applies to the two initial valuations once their
default halves are related by `generalValuationAgrees_defaults`.
-/
theorem generalActorCorresponds_constructorEntry
    (name : ActorName)
    (reactiveClass : DTR.GeneralReactiveClass)
    (sourceInstance : DTR.GeneralActorInstance)
    (env : Translation.GeneralOutputPortEnv)
    (compiledBody : LF.GeneralBody)
    (reactor : LF.GeneralReactor)
    (compiledInstance : LF.GeneralReactorInstance)
    (hBody :
      Translation.compileGeneralBody
          env
          { bodyKey := .constructor,
            selfSends :=
              Translation.selfSendsOfClass
                reactiveClass }
          0
          reactiveClass.constructor.body =
        .ok compiledBody)
    (hStartupBody :
      reactor.startupReaction.body =
        compiledBody)
    (hStateVariables :
      reactor.stateVariables =
        reactiveClass.stateVariables.map
          Translation.compileGeneralStateVariableDecl)
    (hStartupParameters :
      reactor.startupReaction.parameters =
        reactiveClass.constructor.parameters.map
          (fun parameter =>
            parameter.name))
    (hArguments :
      compiledInstance.arguments =
        sourceInstance.arguments.map
          Translation.compileGeneralValue) :
    GeneralActorCorresponds
      name
      (DTR.GeneralModel.initialActorRuntime
          reactiveClass
          sourceInstance)
      (LF.GeneralProgram.initialReactorRuntime
          reactor
          compiledInstance)
      [] := by

  refine
    {
      valuation := ?_
      messages := ?_
      continuation := ?_
    }

  · simp only [
      DTR.GeneralModel.initialActorRuntime,
      DTR.GeneralModel.initialValuation,
      LF.GeneralProgram.initialReactorRuntime
    ]

    rw [
      hStartupParameters,
      hArguments,
      hStateVariables
    ]

    exact
      generalValuationAgrees_bind
        reactiveClass.constructor.parameters
        sourceInstance.arguments
        _
        _
        (generalValuationAgrees_defaults
          reactiveClass.stateVariables)

  · rw [
      DTR.GeneralModel.initialActorRuntime_bag
    ]

    exact
      generalPendingAgrees_empty
        name

  · simp only [
      DTR.GeneralModel.initialActorRuntime,
      LF.GeneralProgram.initialReactorRuntime
    ]

    rw [
      hStartupBody
    ]

    exact
      ⟨
        env,
        {
          bodyKey := .constructor
          selfSends :=
            Translation.selfSendsOfClass
              reactiveClass
        },
        0,
        hBody
      ⟩

/--
The relation `R` holds at the initial states of a model and its compiled program. Unconditional.

The paper's *"holds initially"* line, stated as specified. The only hypothesis is that the program is
the model's successful compilation, which is the standing shape of every translation-side theorem here
and says nothing about correspondence — everything an initializer would establish is established, by
the two initializers this theorem quantifies over.

No model well-formedness is assumed, and the omission is a theorem rather than an oversight: the guard
already refuses programs with duplicate instance names (`instanceNamesUnique`) or duplicate reactor
names (`reactorNamesUnique`), and reactor names are class names wrapped injectively, so a successfully
compiled model has duplicate-free instance names and duplicate-free class names whether or not
`DTR.GeneralModel.wellFormed` was ever consulted. The three derivations live above, and each direction
of the proof consumes them through `initialResolution`.

**F75 part 2 is discharged here, and part of its argument was wrong**: the prediction that the
unconditional statement would follow *"by instantiation rather than re-proof"* of the scoped form does
not survive contact with the initializers the prediction was waiting for. The scoped theorem relates
idle actors — empty continuations on both sides — while the initializers are at **constructor entry**,
with bodies installed on both sides (`DTR.GeneralStep.take` cannot install a constructor body, and
`LF.GeneralEventKind` has no `startup` arm, so nothing else ever will). **F85** records the gap; the
constructor-entry case is `generalActorCorresponds_constructorEntry`, and the scoped theorem survives
under its own name for callers relating two states they did not build.
-/
theorem generalCorrespondence_initial
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program) :
    GeneralStateCorrespondence
      (DTR.GeneralModel.initialState model)
      (LF.GeneralProgram.initialState program) := by

  have hWellFormed :
      program.wellFormed = true :=
    Translation.compileGeneralModel_wellFormed
      hCompiled

  have hInstancesEq :
      program.instances =
        model.instances.map
          Translation.compileGeneralActorInstance :=
    Translation.compileGeneralModel_instances
      hCompiled

  refine
    {
      logicalTime := ?_
      reactorOfActor := ?_
      actorOfReactor := ?_
      pendingTargeted := ?_
    }

  · rfl

  · intro name actorRuntime hMember

    unfold DTR.GeneralModel.initialState at hMember

    obtain
        ⟨instanceDecl,
         hInstanceMember,
         hPair⟩ :=
      List.mem_map.mp hMember

    obtain ⟨hName, hRuntime⟩ :=
      Prod.mk.inj hPair

    obtain
        ⟨reactiveClass,
         _routes,
         env,
         compiledBody,
         reactor,
         hClassOfActor,
         _hClassCompiled,
         _hReactorMember,
         hBody,
         hStartupBody,
         hStateVariables,
         hStartupParameters,
         hReactorLookup⟩ :=
      initialResolution
        hCompiled
        instanceDecl
        hInstanceMember

    rw [hClassOfActor] at hRuntime

    dsimp only at hRuntime

    subst hRuntime

    have hCompiledInstanceMember :
        (Translation.compileGeneralActorInstance
            instanceDecl) ∈
          program.instances := by
      rw [hInstancesEq]

      exact
        List.mem_map_of_mem
          hInstanceMember

    have hInstanceFound :
        LF.findInstance?
            program.instances
            (Translation.compileGeneralActorInstance
              instanceDecl).name =
          some
            (Translation.compileGeneralActorInstance
              instanceDecl) :=
      findInstance?_of_mem_of_nodup
        program.instances
        _
        hCompiledInstanceMember
        (programInstanceNames_nodup_of_compiled
          hWellFormed)

    have hReactorFound :
        program.reactor?
            (Translation.compileGeneralActorInstance
              instanceDecl).reactorName =
          some reactor := by
      rw [
        Translation.compileGeneralActorInstance_reactorName,
        hReactorLookup
      ]

    have hLookup :
        Store.lookup
            (LF.GeneralProgram.initialState
              program).reactors
            (Translation.compileGeneralActorInstance
              instanceDecl).name =
        some
          (LF.GeneralProgram.initialReactorRuntime
              reactor
              (Translation.compileGeneralActorInstance
                instanceDecl)) :=
      LF.GeneralProgram.initialState_lookup
        program
        _
        reactor
        hInstanceFound
        hReactorFound

    rw [
      Translation.compileGeneralActorInstance_name
        instanceDecl,
      hName
    ] at hLookup

    refine
      ⟨
        LF.GeneralProgram.initialReactorRuntime
          reactor
          (Translation.compileGeneralActorInstance
            instanceDecl),
        Store.mem_of_lookup
          _ _ _ hLookup,
        ?_
      ⟩

    exact
      generalActorCorresponds_constructorEntry
        name
        reactiveClass
        instanceDecl
        env
        compiledBody
        reactor
        _
        hBody
        hStartupBody
        hStateVariables
        hStartupParameters
        (Translation.compileGeneralActorInstance_arguments
          instanceDecl)

  · intro name reactorRuntime hMember

    unfold LF.GeneralProgram.initialState at hMember

    obtain
        ⟨compiledInstance,
         hCompiledInstanceMember,
         hPair⟩ :=
      List.mem_map.mp hMember

    obtain ⟨hName, hRuntime⟩ :=
      Prod.mk.inj hPair

    rw [hInstancesEq] at hCompiledInstanceMember

    obtain
        ⟨instanceDecl,
         hInstanceMember,
         hInstanceEq⟩ :=
      List.mem_map.mp hCompiledInstanceMember

    obtain
        ⟨reactiveClass,
         _routes,
         env,
         compiledBody,
         reactor,
         hClassOfActor,
         _hClassCompiled,
         _hReactorMember,
         hBody,
         hStartupBody,
         hStateVariables,
         hStartupParameters,
         hReactorLookup⟩ :=
      initialResolution
        hCompiled
        instanceDecl
        hInstanceMember

    have hInstanceFound :
        program.instance?
            (Translation.compileGeneralActorInstance
              instanceDecl).name =
          some
            (Translation.compileGeneralActorInstance
              instanceDecl) := by
      have hMembership :
          (Translation.compileGeneralActorInstance
              instanceDecl) ∈
            program.instances := by
        rw [hInstancesEq]

        exact
          List.mem_map_of_mem
            hInstanceMember

      exact
        findInstance?_of_mem_of_nodup
          program.instances
          _
          hMembership
          (programInstanceNames_nodup_of_compiled
            hWellFormed)

    have hReactorOfInstance :
        program.reactorOfInstance? compiledInstance.name =
          some reactor := by
      rw [← hInstanceEq]

      simp only [
        LF.GeneralProgram.reactorOfInstance?,
        hInstanceFound,
        Translation.compileGeneralActorInstance_reactorName,
        hReactorLookup
      ]

    rw [hReactorOfInstance] at hRuntime

    dsimp only at hRuntime

    subst hRuntime

    have hActorFound :
        model.actor? instanceDecl.name =
          some instanceDecl :=
      findActor?_of_mem_of_nodup
        model.instances
        instanceDecl
        hInstanceMember
        (modelInstanceNames_nodup_of_compiled
          hCompiled)

    have hClassFound :
        model.class? instanceDecl.className =
          some reactiveClass := by
      have hResolution :=
        hClassOfActor

      simp only [
        DTR.GeneralModel.classOfActor?,
        hActorFound
      ] at hResolution

      exact hResolution

    have hLookup :
        Store.lookup
            (DTR.GeneralModel.initialState
              model).actors
            instanceDecl.name =
        some
          (DTR.GeneralModel.initialActorRuntime
              reactiveClass
              instanceDecl) :=
      DTR.GeneralModel.initialState_lookup
        model
        instanceDecl
        reactiveClass
        hActorFound
        hClassFound

    have hSourceName :
        instanceDecl.name = name := by
      rw [
        ← Translation.compileGeneralActorInstance_name
          instanceDecl,
        hInstanceEq
      ]

      exact hName

    rw [
      hSourceName
    ] at hLookup

    refine
      ⟨
        DTR.GeneralModel.initialActorRuntime
          reactiveClass
          instanceDecl,
        Store.mem_of_lookup
          _ _ _ hLookup,
        ?_
      ⟩

    exact
      generalActorCorresponds_constructorEntry
        name
        reactiveClass
        instanceDecl
        env
        compiledBody
        reactor
        compiledInstance
        hBody
        hStartupBody
        hStateVariables
        hStartupParameters
        (by
          rw [← hInstanceEq]

          exact
            Translation.compileGeneralActorInstance_arguments
              instanceDecl)

  · intro event hEvent

    simp at hEvent

/-!
## Reaction order is not observable at the run level

The closing theorem of `#106` item 1, and the one place in the general family where stage F's two
ordering theorems are confronted with the semantics that is supposed to consume them. F80 asks for
"the refutation stated as a theorem", in the shape `#60` gave §10.2's refuted `setPort` obligation:
not a weakened Lemma 2, but the fact that makes Lemma 2's run-level content empty.

The two halves were built in `Relico/LF/GeneralSemantics.lean` and `Relico/Translation/GeneralBasic.lean`
respectively — `reactionFor?` is permutation-invariant when a reactor's triggers are distinct, and the
translator always emits distinct triggers. This is the first place they meet, which is why it lives here
and not in either of those modules: the composition mentions the translator and the target semantics at
once, and `Correctness/` is the boundary for that.
-/

/--
`reactionFor?` cannot see the order of a translated reactor's message reactions.

If the reactor sitting at `target` in `left` is one `Translation.compileGeneralReactiveClass` produced
from `reactiveClass`, and the reactor at `target` in `right` holds the same message reactions in any
order, then the two programs resolve every event kind to the same reaction. Since `reactionFor?` is
the only route from a program to the reaction a step fires, no permutation of the emitted reaction list
changes which reaction fires — which is exactly what F80 says stage F's level-1 and level-2 sorts do
*not* change at run level.

Only `hPerm` and the distinctness of `leftReactor`'s triggers are needed; `right` is not required to be
a translation of anything. That asymmetry is deliberate: the theorem is meant to be applied with the
translator's output on one side and an arbitrary reordering on the other, which is the situation F80's
Fig. 2a witness describes.

`LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers` composes
`LF.UniquelyTriggered.of_nodup_triggers` internally, so the trigger `Nodup` is supplied directly and
`UniquelyTriggered` is never mentioned here.

**The three distinctness hypotheses are guard-relative, and nothing public discharges them yet**
(measured 2026-08-26, recorded as F81). `Translation.inputPortNames_nodup_of_wellFormed` is the
projection that turns a decided `LF.GeneralReactor.declaredNames` `Nodup` into the first hypothesis, and
it is `private`; for the action names and the message-server names there is no such projection anywhere
in the repository, only the conjunct of `DTR.GeneralModel.namesUniqueAndValid` that would supply the
third. So the hypotheses are passed at the source model's own lists, in the same spelling
`Translation.generalRouteEndpoints_nodup` and
`Translation.compileGeneralReactiveClass_reactionTriggers_nodup` already use. Discharging them belongs to
the commit that first has a consumer, not to this one.

**What this does not reach.** F80's sentence continues "and hence `LF.GeneralStep`". That step is item 3's
weak-step lifting, not this theorem: nothing below concerns the step relation, and reading a step-level
consequence into it would be the F75 defect — crediting a statement with the deliverable of a later one.
-/
theorem generalReactionFor?_perm_of_compiled
    {classes : List DTR.GeneralReactiveClass}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {leftReactor rightReactor : LF.GeneralReactor}
    {left right : LF.GeneralProgram}
    {target : ActorName}
    {kind : LF.GeneralEventKind}
    (hCompiled :
      Translation.compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok leftReactor)
    (hInputPortNames :
      ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup)
    (hLeft :
      left.reactorOfInstance? target =
        some leftReactor)
    (hRight :
      right.reactorOfInstance? target =
        some rightReactor)
    (hPerm :
      List.Perm
        leftReactor.messageReactions
        rightReactor.messageReactions) :
    left.reactionFor? target kind =
      right.reactionFor? target kind :=
  LF.GeneralProgram.reactionFor?_perm_of_nodup_triggers
    hLeft
    hRight
    hPerm
    (Translation.compileGeneralReactiveClass_reactionTriggers_nodup
      hCompiled
      hInputPortNames
      hActionNames
      hServerNames)

/--
The same fact at **every** instance and every event kind, which is the shape a step-level consumer needs.

`generalReactionFor?_perm_of_compiled` above is stated at one `target` and one `kind`, and those two
restrictions are not alike. The `kind` half is not a restriction at all: no hypothesis of that theorem
mentions `kind`, so quantifying over it is `fun kind => …` and costs nothing. The `target` half is real,
because `hLeft` and `hRight` pin the one instance whose reactor is permuted and **nothing constrains
either program anywhere else**.

Hence `hElsewhere`, and hence **F82**. A `GeneralStep` derivation may resolve reactions at any instance
the runtime reaches, so a statement about one permuted reactor cannot become a statement about the step
relation without saying what the two programs do at the other instances. What holds of the situation this
theorem exists for — one reactor's reaction list reordered, the rest of the program untouched — is that
they agree there, so that is stated as a hypothesis. It is *not* built into a program-rebuilding function,
for the reason `LF.GeneralProgram.reactionFor?_perm` records: no stage has needed one, and inventing one
here would put a definition in the tree with no caller.

The proof splits on whether the instance asked about is the permuted one. Off it, the resolutions agree
because `reactionFor?` matches on `reactorOfInstance?` and on nothing else, so rewriting the lookup is the
whole argument — the same move `reactionFor?_perm` makes at both of its own `simp` calls.
-/
theorem generalReactionFor?_perm_of_compiled_pointwise
    {classes : List DTR.GeneralReactiveClass}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {leftReactor rightReactor : LF.GeneralReactor}
    {left right : LF.GeneralProgram}
    {target : ActorName}
    (hCompiled :
      Translation.compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok leftReactor)
    (hInputPortNames :
      ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup)
    (hLeft :
      left.reactorOfInstance? target =
        some leftReactor)
    (hRight :
      right.reactorOfInstance? target =
        some rightReactor)
    (hPerm :
      List.Perm
        leftReactor.messageReactions
        rightReactor.messageReactions)
    (hElsewhere :
      ∀ (other : ActorName),
        other ≠ target →
        left.reactorOfInstance? other =
          right.reactorOfInstance? other) :
    ∀ (instanceName : ActorName)
      (kind : LF.GeneralEventKind),
      left.reactionFor? instanceName kind =
        right.reactionFor? instanceName kind := by

  intro instanceName kind

  by_cases hSame : instanceName = target

  · subst hSame

    exact
      generalReactionFor?_perm_of_compiled
        hCompiled
        hInputPortNames
        hActionNames
        hServerNames
        hLeft
        hRight
        hPerm

  · have hLookup :
        left.reactorOfInstance? instanceName =
          right.reactorOfInstance? instanceName :=
      hElsewhere
        instanceName
        hSame

    simp
      [LF.GeneralProgram.reactionFor?,
       hLookup]

/-!
## Exact resolution of the compiled send routes

The composition half of the message-name ↔ event-kind bridge (task `#129`, decision 0042), and
prerequisite infrastructure only: nothing here states or prepares a `.consume` transfer
condition, which F86 keeps waiting on the multiplicity and quotient-placement decisions.

The bridge's two halves landed on either side of this file. The translator half —
`Translation.compileGeneralReactiveClass_actionRoute_mem` and
`Translation.compileGeneralReactiveClass_portRoute_mem` — proves each send route's compiled
reaction is a member of the compiled reactor's list and pins its trigger. The target half —
`LF.findReactionForKind?_eq_some_of_mem` and
`LF.GeneralProgram.reactionFor?_eq_findReactionForKind?_of_reactorOfInstance?` — turns
membership-plus-match into a whole-program lookup answer, under `LF.UniquelyTriggered`. What
neither half could supply is the middle fact: that the translator's own output satisfies
`UniquelyTriggered`, which no well-formedness clause gives, for the reason `LF.UniquelyTriggered`
records (measured as Test 11 of `Relico/Tests/GeneralSemantics.lean`). The first theorem below is
that middle fact, composed from `Translation.compileGeneralReactiveClass_reactionTriggers_nodup`
and `LF.UniquelyTriggered.of_nodup_triggers` — the meeting this file exists for. The two after it
resolve each send route exactly, in the shape `Correctness.GeneralConsumeMatch` deliberately left
external: the eventual transfer conditions take the resolved reaction as a premise, and these
theorems are how a caller discharges one.
-/

/--
A compiled reactor's reaction list is uniquely triggered, at every event kind at once.

The C7 prerequisite the routing bridge named and could not carry: the target half's lemmas
condition on `LF.UniquelyTriggered`, well-formedness cannot supply it, and the translator half
could not even state it. `Translation.compileGeneralReactiveClass_reactionTriggers_nodup` proved
the output's trigger list carries no duplicates — in `Nodup` form, because
`Relico.Translation.GeneralBasic` cannot reach `Relico.LF.GeneralSemantics` — and
`LF.UniquelyTriggered.of_nodup_triggers` was designed as the bridge from exactly that shape. This
theorem is the two composed; `kind` is an explicit binder so a consumer at one pinned kind
applies it directly.

The three distinctness hypotheses are the same three `generalReactionFor?_perm_of_compiled`
passes at the source model's own lists, and they stay hypotheses for the reason that theorem
records (F81): two are `LF.GeneralReactor.declaredNames` `Nodup` clauses in disguise, the third a
conjunct of `DTR.GeneralModel.namesUniqueAndValid`, and no public projection discharges them —
the one that exists for the first is `private` by a rule this repository keeps. Guard-relative is
the house form and the strongest available; no well-formedness clause is added here.

Startup reactions need nothing from this theorem: `LF.GeneralReactor` carries them in the
separate `startupReaction` field, while the compiled `messageReactions`' trigger list is pinned
to the action and port families `Translation.generalReactionTriggersOf` enumerates — and
independently, `LF.GeneralTrigger.not_matchesKind_startup` records that a `.startup` trigger
matches no event kind. Either fact alone keeps startup reactions out of every conclusion in
this section.
-/
theorem generalUniquelyTriggered_of_compiled
    {classes : List DTR.GeneralReactiveClass}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      Translation.compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hInputPortNames :
      ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup)
    (kind : LF.GeneralEventKind) :
    LF.UniquelyTriggered
      reactor.messageReactions
      kind :=
  LF.UniquelyTriggered.of_nodup_triggers
    (Translation.compileGeneralReactiveClass_reactionTriggers_nodup
      hCompiled
      hInputPortNames
      hActionNames
      hServerNames)
    kind

/--
The action send route resolves exactly: the whole-program lookup returns the self-send site's
compiled reaction — `reactionFor? = some …`, the conclusion the `#129` bridge was commissioned
for.

Three composed facts, each already proved:
`Translation.compileGeneralReactiveClass_actionRoute_mem` pins the member reaction and the
body's provenance; `LF.GeneralTrigger.matchesKind` decides the match on `.logicalAction` by
`decide` on name equality, and the event kind below is the member's own trigger name, so the
match holds definitionally; and `generalUniquelyTriggered_of_compiled` plus the two target-half
lemmas turn member-and-match into the lookup answer through the `reactorOfInstance?` seam.

Every conjunct except the resolution equation is the membership theorem's own, restated here so
that one application yields resolution and body provenance together — the two existentials share
one `compiledBody`, which is the point of the packaging: identifying a resolution theorem's body
with the membership theorem's body would otherwise re-run the uniqueness argument, because the
lookup's answer is only pinned to the member once `UniquelyTriggered` has spoken.

What this does **not** reach: the `.consume` transfer conditions (F86 — they wait on the
multiplicity and quotient-placement decisions), and any claim about *which pending event* a step
selects. That is the scheduler's question; this theorem answers what an event kind resolves to
once asked, which is all the eventual conditions were promised as a premise.
-/
theorem generalReactionFor?_eq_some_of_actionRoute
    {classes : List DTR.GeneralReactiveClass}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {program : LF.GeneralProgram}
    {target : ActorName}
    (hCompiled :
      Translation.compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hInputPortNames :
      ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup)
    (hReactor :
      program.reactorOfInstance? target =
        some reactor)
    (server : DTR.GeneralMessageServer)
    (hServer :
      server ∈ reactiveClass.messageServers)
    (selfSend : Translation.GeneralSelfSend)
    (hSelfSend :
      selfSend ∈
        Translation.generalSelfSendSitesOf
          server.name
          (Translation.selfSendsOfClass
            reactiveClass)) :
    ∃ compiledBody : LF.GeneralBody,
      program.reactionFor? target
          (.logicalAction
            (Translation.generalActionNameAtSite
              (Translation.selfSendsOfClass
                reactiveClass)
              selfSend.site
              server.name)) =
        some
          (
            {
              name :=
                Translation.messageReactionNameFor
                  server.name

              trigger :=
                .logicalAction
                  (Translation.generalActionNameAtSite
                    (Translation.selfSendsOfClass
                      reactiveClass)
                    selfSend.site
                    server.name)

              parameters :=
                server.parameters.map
                  (fun parameter =>
                    parameter.name)

              body :=
                compiledBody

              priority :=
                none
            } :
              LF.GeneralReaction
          ) ∧
      ∃ env : Translation.GeneralOutputPortEnv,
        Translation.outputPortEnvOf
            classes
            reactiveClass =
          .ok env ∧
        Translation.compileGeneralBody
            env
            { bodyKey := .messageServer server.name,
              selfSends :=
                Translation.selfSendsOfClass
                  reactiveClass }
            0
            server.body =
          .ok compiledBody := by
  obtain ⟨compiledBody, hMember, env, hEnv, hBody⟩ :=
    Translation.compileGeneralReactiveClass_actionRoute_mem
      hCompiled
      server
      hServer
      selfSend
      hSelfSend

  refine ⟨compiledBody, ?_, env, hEnv, hBody⟩

  have hUnique :
      LF.UniquelyTriggered
        reactor.messageReactions
        (.logicalAction
          (Translation.generalActionNameAtSite
            (Translation.selfSendsOfClass
              reactiveClass)
            selfSend.site
            server.name)) :=
    generalUniquelyTriggered_of_compiled
      hCompiled
      hInputPortNames
      hActionNames
      hServerNames
      (.logicalAction
        (Translation.generalActionNameAtSite
          (Translation.selfSendsOfClass
            reactiveClass)
          selfSend.site
          server.name))

  rw [
    LF.GeneralProgram.reactionFor?_eq_findReactionForKind?_of_reactorOfInstance?
      hReactor
  ]

  exact
    LF.findReactionForKind?_eq_some_of_mem
      (.logicalAction
        (Translation.generalActionNameAtSite
          (Translation.selfSendsOfClass
            reactiveClass)
          selfSend.site
          server.name))
      reactor.messageReactions
      hUnique
      _
      hMember
      (by
        simp [LF.GeneralTrigger.matchesKind])

/--
The port send route resolves exactly: the whole-program lookup returns the route's compiled
reaction — the second half of the `#129` bridge's conclusion.

The same three-part composition as `generalReactionFor?_eq_some_of_actionRoute`, with the port
route's own member fact: `Translation.compileGeneralReactiveClass_portRoute_mem` pins the member
reaction to trigger `.inputPort (Translation.generalInputPortOfRoute route)` — the input port
the connection emitted, the same name `Translation.compileGeneralStmt_send_knownRebec_ok`'s
output-port entry feeds — and the match is decided on `.inputPort` by `decide` on name equality,
so member-and-kind agree definitionally here too.

The two route theorems are stated separately rather than unified because their member facts are:
the action route's membership is stated per self-send site and the port route's per route, and
folding them into one theorem would need a trigger hypothesis neither consumer holds. Their
proofs differ only in the member fact and the kind constructor.
-/
theorem generalReactionFor?_eq_some_of_portRoute
    {classes : List DTR.GeneralReactiveClass}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {program : LF.GeneralProgram}
    {target : ActorName}
    (hCompiled :
      Translation.compileGeneralReactiveClass
          classes
          routes
          reactiveClass =
        .ok reactor)
    (hInputPortNames :
      ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
        (fun port =>
          port.name.value)).Nodup)
    (hActionNames :
      ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
        (fun name =>
          name.value)).Nodup)
    (hServerNames :
      (reactiveClass.messageServers.map
        (fun server =>
          server.name)).Nodup)
    (hReactor :
      program.reactorOfInstance? target =
        some reactor)
    (server : DTR.GeneralMessageServer)
    (hServer :
      server ∈ reactiveClass.messageServers)
    (route : Translation.GeneralRoute)
    (hRoute :
      route ∈
        Translation.generalRoutesIntoMessageServer
          reactiveClass.name
          server.name
          routes) :
    ∃ compiledBody : LF.GeneralBody,
      program.reactionFor? target
          (.inputPort
            (Translation.generalInputPortOfRoute
              route)) =
        some
          (
            {
              name :=
                Translation.portReactionNameFor
                  (Translation.generalInputPortOfRoute
                    route)

              trigger :=
                .inputPort
                  (Translation.generalInputPortOfRoute
                    route)

              parameters :=
                server.parameters.map
                  (fun parameter =>
                    parameter.name)

              body :=
                compiledBody

              priority :=
                none
            } :
              LF.GeneralReaction
          ) ∧
      ∃ env : Translation.GeneralOutputPortEnv,
        Translation.outputPortEnvOf
            classes
            reactiveClass =
          .ok env ∧
        Translation.compileGeneralBody
            env
            { bodyKey := .messageServer server.name,
              selfSends :=
                Translation.selfSendsOfClass
                  reactiveClass }
            0
            server.body =
          .ok compiledBody := by
  obtain ⟨compiledBody, hMember, env, hEnv, hBody⟩ :=
    Translation.compileGeneralReactiveClass_portRoute_mem
      hCompiled
      server
      hServer
      route
      hRoute

  refine ⟨compiledBody, ?_, env, hEnv, hBody⟩

  have hUnique :
      LF.UniquelyTriggered
        reactor.messageReactions
        (.inputPort
          (Translation.generalInputPortOfRoute
            route)) :=
    generalUniquelyTriggered_of_compiled
      hCompiled
      hInputPortNames
      hActionNames
      hServerNames
      (.inputPort
        (Translation.generalInputPortOfRoute
          route))

  rw [
    LF.GeneralProgram.reactionFor?_eq_findReactionForKind?_of_reactorOfInstance?
      hReactor
  ]

  exact
    LF.findReactionForKind?_eq_some_of_mem
      (.inputPort
        (Translation.generalInputPortOfRoute
          route))
      reactor.messageReactions
      hUnique
      _
      hMember
      (by
        simp [LF.GeneralTrigger.matchesKind])

end Correctness
end Relico
