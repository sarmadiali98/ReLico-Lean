import Relico.DTR.GeneralRuntime
import Relico.LF.GeneralSemantics
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
The relation holds at the start of a run.

**Scoped, with named hypotheses, and that is a finding rather than a choice.** `docs/STAGE_G_DESIGN.md` §7
specifies this theorem as *unconditional*, which would require an initial-state constructor on each side to
quantify over. There is none: the source has
`DTR.GeneralRuntimeConfiguration.ofConfiguration`, which builds a runtime configuration from a
configuration that is itself given, and the target side has no `ofProgram` at all — the general family's
initialization modules do not exist, and §13's twelve rows create none. F75 part 2 records this, and the
unconditional statement is owed at G5, where the LF initial state must be built anyway to produce a
runnable witness.

So the theorem takes the target store as a parameter and three hypotheses that say what "initial" means:
every source bag is empty, and the two stores relate pointwise with every reactor idle. The source
continuations need no hypothesis — `ofConfiguration` sets them all to `[]` by construction, and
`DTR.mem_attachEmptyContinuations` is how that fact is recovered from membership rather than from a lookup.

The pending queue is the literal `[]` rather than a parameter, because an initial LF state has nothing
scheduled: `pendingTargeted` and both directions of `GeneralPendingAgrees` would otherwise need
hypotheses of their own, and they would be hypotheses about a state the design has no way to build yet.
-/
theorem generalCorrespondence_initial
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

end Correctness
end Relico
