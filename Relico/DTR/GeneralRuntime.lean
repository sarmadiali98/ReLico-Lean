import Relico.DTR.GeneralState

set_option autoImplicit false

namespace Relico
namespace DTR

/-!
# Source runtime state and observable labels for the general family

Obligation G2a-ii, source side. This module holds two things and deliberately not a third: the
runtime **state** a source configuration needs in order to execute one statement at a time, and the
**label** type an observable step carries. The step relation itself is G2a-iii, in
`Relico/DTR/GeneralSemantics.lean`.

## Why the split is state-here, rules-there

It is the corpus convention, not a new one. `Relico/DTR/DetailedMultiStorePayloadRuntime.lean` holds
exactly a state type and a label type — `DetailedMultiStorePayloadState` and
`DetailedMultiStorePayloadLabel`, two declarations and nothing else — while
`Relico/DTR/DetailedMultiStorePayloadSemantics.lean` holds the single inductive
`DetailedMultiStorePayloadStep`. Following it means the G2a-ii/G2a-iii boundary in
`docs/STAGE_G_DESIGN.md` §13 lands on a seam the repository already uses.

## The label type is `GeneralLabel`, not `GeneralDtrAction`

`docs/STAGE_G_DESIGN.md` §7 **first specified** `GeneralDtrAction` and `GeneralLfAction`; it now records
this respelling instead, and `docs/STAGE_G_FINDINGS.md` F66 part 7 — the finding that chose the original
names — records that the names it proposed are not the ones that landed. Its *reason* is kept
here in full — an LTS label and an LF logical-action declaration must not share an identifier, and
`ϕ : Act_1 → Act_2` needs two types rather than one — and both types are still declared separately, one
per language. Only the spelling changed, for three measured reasons:

* The repository declares **thirty-nine** `…Label` inductives for observable transition labels —
  thirty-seven of them predating this obligation, which contributes the other two — and **zero**
  `…Action` inductives. `Label` is the house word for this concept.
* `GeneralLfAction` does not actually remove the collision the design objected to. It would live in
  `namespace LF`, one word away from `LF.GeneralAction`, the syntactic logical-action *structure*
  declared in `Relico/LF/GeneralSyntax.lean` — cited by name, because a line number into a 936-line
  file is the stale cite F68 warns about. Naming the label `LF.GeneralLabel` removes it.
* The `Dtr`/`Lf` infix is redundant inside `namespace DTR` and `namespace LF`, and it breaks the
  symmetry G2a-i established one obligation earlier: `DTR.GeneralValuation` and `LF.GeneralValuation`
  are one name in two namespaces, qualified at the `Correctness` boundary.

This is a naming decision, not a divergence from the paper: the paper's `Act` sets are unchanged, and
nothing about Theorem 1 reads an identifier. Recorded here rather than in `docs/decisions/`, whose
entries are semantic paper-drift approvals of a different weight class.

## The continuation is added by composition, not by a new field on `GeneralActorState`

`GeneralActorState` already carries the valuation and the bag, and it is read by built code —
`Relico/DTR/GeneralActorSelection.lean` and stage F's ordering theorems among it. Adding an
`activeBody` field there would edit a structure those modules elaborate against and would change its
derived instances. `GeneralActorRuntime` therefore *contains* a `GeneralActorState` and adds the
continuation beside it, so the existing type keeps exactly one definition and no caller changes.

The same reasoning is why `GeneralActorState` itself records no class: its own docstring says
duplicating static information into the state "would create a second place for the two to disagree".
A second store keyed by `ActorName`, holding continuations alongside `GeneralConfiguration.actors`,
would be that defect — an actor could appear in one and not the other. One store of a richer value
type cannot.

## Why `erase` exists

G1's `selectedActor` is a function of `GeneralConfiguration`, and stage F's ordering results are stated
against the same type. The step relation must be able to ask "which actor does the source dispatch
next?" without those results being restated over a new configuration type. `erase` forgets the
continuations and hands back precisely the `GeneralConfiguration` the existing development already
reasons about, so G2a-iii calls `selectedActor config.erase` and inherits stage F rather than
duplicating it.
-/

/--
One actor's runtime state: its `GeneralActorState`, plus the statements it has left to run.

`activeBody` is the continuation of the level the actor is executing *now*. An actor with nothing left
to run at any level is the idle actor — the one eligible to accept a dispatch — and one part-way
through a body is not. There is no separate "executing" flag, because a flag and a list can disagree
about whether work remains and the list alone cannot.

**`frames` is the stack of enclosing continuations, innermost first, and it is not defaultable.** Stage
H's step-into semantics needs somewhere to remember *"what to run after this branch finishes"*, and a
`List DTR.GeneralBody` read as a stack is that place: entering the then-branch of
`ifThenElse c t e :: remaining` pushes `remaining` and makes `t` the active body, and an active body
that runs out pops the stack instead of ending the message server.

The field is deliberately declared **without** a default, unlike `activeBody`, and that is a decision
about failure modes rather than about style. Every existing rule of `DTR.GeneralStep` rewrites an
actor as a full record literal; with a default, each of those literals would silently write
`frames := []` and *discard* the pending stack, which is a lost-continuation bug of exactly the shape
F56 found for a lost message, and no test in this repository would fail. Without a default, the
compiler names every construction site and each one has to say what happens to the stack.

Splicing the branch into the active body instead — `activeBody := t ++ remaining`, no new field —
was rejected and must not be reintroduced: the spliced statements would then sit at top-level
positions of a flat list, while the routing table addresses them at `levelPath ++ [i, 0, …]`, so the
ports and actions of a branch would be resolved at addresses that do not exist. Keeping one level per
frame is what keeps `Translation.SendSite` meaningful under nesting, which is the whole content of
`docs/decisions/0046-send-site-identity-under-nested-control-flow.md`.

The class is not recorded here for the same reason `GeneralActorState` does not record it.
-/
structure GeneralActorRuntime where
  state :
    DTR.GeneralActorState

  activeBody :
    DTR.GeneralBody := []

  frames :
    List DTR.GeneralBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
A global runtime configuration: one logical time, and one runtime state per actor.

Actor order is the model's instance order, exactly as in `GeneralConfiguration`, and for the same
reason: it is the order the frontend emits and the order the measured target semantics uses to decide
which reaction runs first at one tag.
-/
structure GeneralRuntimeConfiguration where
  now :
    LogicalTime

  actors :
    Store ActorName DTR.GeneralActorRuntime

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralActorRuntime

/--
Whether this actor has no statements left to run, at any level.

The eligibility test for accepting a dispatch. Stated as a `Bool` because the step relation guards on
it and both fields are `List`s, whose emptiness is already decidable.

**Both conjuncts are load-bearing as of stage H.** An actor whose active body has run out but whose
frame stack still holds an enclosing continuation is *not* finished: it owes the statements after the
branch it stepped into. Testing `activeBody` alone would let `TAKE` install a second message-server
body on top of a half-executed one, which is precisely the divergence Table I's *"continuation is ε"*
premise exists to prevent, and the third component of `R` would then relate two states whose
continuations disagree with nothing to notice.

For every model of the currently accepted fragment `frames` is `[]`, so the second conjunct is `true`
wherever the pre-stage-H development goes and no existing behaviour moved.
-/
def idle
    (actor : GeneralActorRuntime) :
    Bool :=
  actor.activeBody.isEmpty &&
    actor.frames.isEmpty

@[simp]
theorem idle_of_nil
    (state : DTR.GeneralActorState) :
    idle { state := state, activeBody := [], frames := [] } = true := by
  rfl

@[simp]
theorem idle_of_cons
    (state : DTR.GeneralActorState)
    (statement : DTR.GeneralStmt)
    (remaining : DTR.GeneralBody)
    (frames : List DTR.GeneralBody) :
    idle
        {
          state := state
          activeBody := statement :: remaining
          frames := frames
        } =
      false := by
  rfl

/--
An actor with a pending frame is not idle, whatever its active body.

The other half of the guard, stated separately because the two reasons an actor is busy are
independent: `idle_of_cons` covers *"this level has statements left"* and this covers *"an enclosing
level does"*. A proof that only knew the first would accept an actor that has just run the last
statement of a branch as ready for a new message.
-/
@[simp]
theorem idle_of_frames_cons
    (state : DTR.GeneralActorState)
    (activeBody : DTR.GeneralBody)
    (frame : DTR.GeneralBody)
    (frames : List DTR.GeneralBody) :
    idle
        {
          state := state
          activeBody := activeBody
          frames := frame :: frames
        } =
      false := by
  simp [
    idle
  ]

end GeneralActorRuntime

/--
Forget the continuations of a store of actor runtimes.

Pointwise, and order-preserving: `Store` is an ordered association list whose first binding for a key
is the observable one, so a mapping that keeps the key and the position keeps the observable content.

Written as an explicit recursion rather than as `List.map`, following
`Translation.compileGlobalMultiStorePayloadActors`, which is the built precedent for a componentwise
store image. The reason is not style: an explicit recursion generates equation lemmas that
`simp [eraseContinuations, Store.lookup]` can drive directly, which is exactly how that precedent's
lookup lemma is proved. A `List.map` body would force every proof through `List.map_cons` first.
-/
def eraseContinuations :
    Store ActorName DTR.GeneralActorRuntime →
    Store ActorName DTR.GeneralActorState

  | [] =>
      []

  | (name, actor) :: remaining =>
      (name, actor.state) ::
        eraseContinuations remaining

/--
Attach an empty continuation to every actor of a store.

The inverse direction, used to build the initial runtime configuration from a configuration the
existing development already constructs.

"Empty" means empty at every level as of stage H: an empty active body **and** an empty frame stack.
The name is left alone because that is still exactly what it does, and because it appears in committed
proofs.
-/
def attachEmptyContinuations :
    Store ActorName DTR.GeneralActorState →
    Store ActorName DTR.GeneralActorRuntime

  | [] =>
      []

  | (name, state) :: remaining =>
      (name,
        {
          state := state
          activeBody := []
          frames := []
        }) ::
        attachEmptyContinuations remaining

@[simp]
theorem eraseContinuations_nil :
    eraseContinuations [] = [] := by
  rfl

/--
Erasure commutes with lookup.

The load-bearing lemma of the projection: anything the existing development proves by looking an actor
up in a `GeneralConfiguration` transfers to the runtime configuration, because the two lookups differ
only by the continuation this function drops.

Proved by the same induction as `Translation.lookup_compileGlobalMultiStorePayloadActors`, the built
lemma of the same shape for the multi-store family — `rcases` the head binding, split on whether its
key is the one being looked up, and let `simp` discharge each branch from the two definitions' equation
lemmas plus, in the negative branch, the inductive hypothesis.
-/
theorem eraseContinuations_lookup
    (actors : Store ActorName DTR.GeneralActorRuntime)
    (name : ActorName) :
    Store.lookup
        (eraseContinuations actors)
        name =
      Option.map
        GeneralActorRuntime.state
        (Store.lookup actors name) := by

  induction actors with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨candidate, actor⟩

      by_cases hCandidate :
          candidate = name

      · subst candidate

        simp [
          eraseContinuations,
          Store.lookup
        ]

      · simp [
          eraseContinuations,
          Store.lookup,
          hCandidate,
          inductionHypothesis
        ]

/--
Attaching empty continuations and then erasing them is the identity.

The round trip that makes `ofConfiguration` below a genuine embedding rather than a lossy encoding.
-/
theorem eraseContinuations_attachEmptyContinuations
    (actors : Store ActorName DTR.GeneralActorState) :
    eraseContinuations
        (attachEmptyContinuations actors) =
      actors := by

  induction actors with

  | nil =>
      rfl

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨name, state⟩

      simp [
        eraseContinuations,
        attachEmptyContinuations,
        inductionHypothesis
      ]

/-!
### Attachment through membership

`eraseContinuations_lookup` is the projection's lookup lemma, and it is the right shape for anything
that observes an actor by name. The two lemmas below are the *membership* shape, and G2b needs them
instead.

The reason is that `Store` is an ordered association list whose header records that only the first
binding for a key is observable, while `DTR.GeneralConfiguration.nextArrival` minimises over **every**
binding — including a shadowed one. A correspondence relation stated over `Store.lookup` would
therefore say nothing about a shadowed actor, and its message could still decide when the source clock
moves; the target, whose reactors are also keyed by name, would have no event to match it with, and
Lemma 1 would be false for the same reason **F74** made it false. Quantifying over membership closes
that, and `Store.mem_of_lookup` converts a lookup into the membership fact when a caller has one.
-/

/--
Every binding of an attached store is an attached binding, continuation and all.

The inversion direction: what a member of `attachEmptyContinuations actors` tells you about `actors`.

Stage H added the third conjunct. The function sets both continuation fields, so an inversion that
reported only the active body would leave a caller unable to see the frame stack it had just been
handed, and every consumer of this lemma feeds a pairing whose idleness now reads both.
-/
theorem mem_attachEmptyContinuations
    (actors : Store ActorName DTR.GeneralActorState)
    (name : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (hMember :
      (name, actor) ∈
        attachEmptyContinuations actors) :
    (name, actor.state) ∈ actors ∧
      actor.activeBody = [] ∧
      actor.frames = [] := by

  induction actors with

  | nil =>
      simp [
        attachEmptyContinuations
      ] at hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headState⟩

      simp only [
        attachEmptyContinuations,
        List.mem_cons
      ] at hMember

      rcases hMember with
        hEqual |
          hRemaining

      · simp only [
          Prod.mk.injEq
        ] at hEqual

        rcases hEqual with
          ⟨hName, hActor⟩

        subst hName

        subst hActor

        exact
          ⟨List.mem_cons.mpr (Or.inl rfl),
           rfl,
           rfl⟩

      · rcases
            inductionHypothesis
              hRemaining
          with
            ⟨hState, hBody, hFrames⟩

        exact
          ⟨List.mem_cons.mpr (Or.inr hState),
           hBody,
           hFrames⟩

/--
Every binding of the underlying store is a binding of the attached one.

The forward direction, and the one an initial-state correspondence needs: the source configuration is
given, the runtime configuration is built from it, and the relation has to be shown for every actor of
the built store.
-/
theorem mem_attachEmptyContinuations_of_mem
    (actors : Store ActorName DTR.GeneralActorState)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (hMember :
      (name, state) ∈ actors) :
    (name,
      ({
        state := state
        activeBody := []
        frames := []
      } : DTR.GeneralActorRuntime)) ∈
      attachEmptyContinuations actors := by

  induction actors with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headState⟩

      simp only [
        List.mem_cons
      ] at hMember

      simp only [
        attachEmptyContinuations,
        List.mem_cons
      ]

      rcases hMember with
        hEqual |
          hRemaining

      · simp only [
          Prod.mk.injEq
        ] at hEqual

        rcases hEqual with
          ⟨hName, hState⟩

        subst hName

        subst hState

        exact Or.inl rfl

      · exact
          Or.inr
            (inductionHypothesis
              hRemaining)

/-!
### Erasure through membership

The same two directions for the projection. `eraseContinuations_lookup` above is the lookup shape and stays
where it is: it is what a caller who observes an actor *by name* needs. G2b needs the membership shape for
the reason the note above gives, and needs it in both directions because the correspondence relation and
the results it composes live on opposite sides of the projection.

Concretely: `GeneralStateCorrespondence` quantifies over the bindings of a `GeneralRuntimeConfiguration`,
while `DTR.nextArrival_sound`, `DTR.nextArrival_complete`, `DTR.nextArrival_minimal` and
`DTR.arrival_future_of_readyActors_nil` all quantify over the bindings of the `GeneralConfiguration` that
`erase` produces. Lemma 1 crosses that boundary twice per direction — once to find the reactor matching an
actor the arrival minimum produced, once to hand a message the relation produced back to the minimum — so
both lemmas are spent, not just one.
-/

/--
Every binding of an erased store comes from a binding of the original, continuation and all.

The inversion direction. The continuation is not recovered as a value — it is existentially quantified,
because erasure genuinely forgets it — but the *actor* is, which is all a caller needs: the relation is
stated about the runtime actor, and this produces one whose state is the given one.
-/
theorem mem_eraseContinuations
    (actors : Store ActorName DTR.GeneralActorRuntime)
    (name : ActorName)
    (state : DTR.GeneralActorState)
    (hMember :
      (name, state) ∈
        eraseContinuations actors) :
    ∃ actor : DTR.GeneralActorRuntime,
      (name, actor) ∈ actors ∧
        actor.state = state := by

  induction actors with

  | nil =>
      simp [
        eraseContinuations
      ] at hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headActor⟩

      simp only [
        eraseContinuations,
        List.mem_cons
      ] at hMember

      rcases hMember with
        hEqual |
          hRemaining

      · simp only [
          Prod.mk.injEq
        ] at hEqual

        rcases hEqual with
          ⟨hName, hState⟩

        subst hName

        exact
          ⟨headActor,
           List.mem_cons.mpr (Or.inl rfl),
           hState.symm⟩

      · rcases
            inductionHypothesis
              hRemaining
          with
            ⟨actor, hActorMember, hActorState⟩

        exact
          ⟨actor,
           List.mem_cons.mpr (Or.inr hActorMember),
           hActorState⟩

/--
Every binding of a store of runtimes has its state bound in the erasure.

The forward direction: the relation hands over a runtime actor and a result about the erased configuration
has to be applied to it.
-/
theorem mem_eraseContinuations_of_mem
    (actors : Store ActorName DTR.GeneralActorRuntime)
    (name : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (hMember :
      (name, actor) ∈ actors) :
    (name, actor.state) ∈
      eraseContinuations actors := by

  induction actors with

  | nil =>
      cases hMember

  | cons head remaining inductionHypothesis =>
      rcases head with
        ⟨headName, headActor⟩

      simp only [
        List.mem_cons
      ] at hMember

      simp only [
        eraseContinuations,
        List.mem_cons
      ]

      rcases hMember with
        hEqual |
          hRemaining

      · simp only [
          Prod.mk.injEq
        ] at hEqual

        rcases hEqual with
          ⟨hName, hActor⟩

        subst hName

        subst hActor

        exact Or.inl rfl

      · exact
          Or.inr
            (inductionHypothesis
              hRemaining)

namespace GeneralRuntimeConfiguration

/--
Forget every continuation, recovering the configuration type the rest of the development reasons about.
-/
def erase
    (config : GeneralRuntimeConfiguration) :
    DTR.GeneralConfiguration :=
  {
    now := config.now
    actors := eraseContinuations config.actors
  }

@[simp]
theorem erase_now
    (config : GeneralRuntimeConfiguration) :
    (erase config).now = config.now := by
  rfl

@[simp]
theorem erase_actors
    (config : GeneralRuntimeConfiguration) :
    (erase config).actors = eraseContinuations config.actors := by
  rfl

/--
Build a runtime configuration from a configuration, with every actor idle.

The continuation-free lift of a configuration, and deliberately **not** the initial state of a run:
with every continuation empty and every bag as given, no rule of `DTR.GeneralStep` can ever begin a
constructor, so a lifted configuration is dead unless its bags already carry messages. The initial
state of a run is `DTR.GeneralModel.initialState` in `Relico/DTR/GeneralInitialization.lean`, which
installs constructor bodies; G2b's scoped `generalCorrespondence_initial_scoped` starts from this
function, and the unconditional `generalCorrespondence_initial` starts from that one.
-/
def ofConfiguration
    (config : DTR.GeneralConfiguration) :
    GeneralRuntimeConfiguration :=
  {
    now := config.now
    actors := attachEmptyContinuations config.actors
  }

@[simp]
theorem ofConfiguration_now
    (config : DTR.GeneralConfiguration) :
    (ofConfiguration config).now = config.now := by
  rfl

/--
`ofConfiguration` followed by `erase` is the identity.

Stated because the two functions are what let stage G reuse G1 and stage F unchanged: if this failed,
`erase` would be losing something other than continuations and every result inherited through it would
be inherited unsoundly.
-/
theorem erase_ofConfiguration
    (config : DTR.GeneralConfiguration) :
    erase (ofConfiguration config) = config := by

  rcases config with
    ⟨now, actors⟩

  simp [
    erase,
    ofConfiguration,
    eraseContinuations_attachEmptyContinuations
  ]

end GeneralRuntimeConfiguration

/--
Observable labels of one source step.

Three constructors, mirroring `DetailedMultiStorePayloadLabel`, and the τ/observable division is the
one P24 measured:

* `tau` — a statement step. In this fragment that is `assign` and `send`; the paper's τ set also lists
  CONDITIONAL-T and CONDITIONAL-F, which the general fragment excludes, so no constructor is owed for
  them and `Relico/DTR/GeneralSyntax.lean`'s flat `GeneralBody` is what keeps that exclusion a build
  error rather than a silent default branch.
* `timeAdvance` — logical time moving forward. Observable, and the label the target must match.
* `consume` — a message leaving an actor's bag and its server body beginning. Observable, and it
  carries the whole message rather than the message name, because the correspondence relation has to
  line a source consumption up against a target reaction firing by sender and payload, not by name
  alone. `Relico/DTR/GeneralState.lean` records that a name alone does not determine the sender and
  receiver pair.

Which *rule* emits which label is G2a-iii's business; this type only fixes what a label can be.
-/
inductive GeneralLabel where

  | tau :
      GeneralLabel

  | timeAdvance
      (before after :
        LogicalTime) :
      GeneralLabel

  | consume
      (receiver :
        ActorName)
      (message :
        DTR.GeneralMessage) :
      GeneralLabel

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralLabel

/--
Whether this label is internal.

`Prop`-valued, and returning `True` or `False` by pattern match, because that is the type
`Relico/Common/WeakTransition.lean` requires: `Common.TauSteps` and `Common.WeakStep` both take
`isTau : Label → Prop`. A `Bool` version would need a coercion at every use and would then be a second
spelling of one convention. `Relico/Tests/WeakTransitionFoundation.lean`'s `exampleIsTau` is the built
shape this follows, down to the `True`/`False` bodies.

Note that no `Decidable` instance is owed: `Common.WeakStep.of_step` reaches for `classical` before it
splits on `isTau`, so the generic development already handles an undecidable τ predicate.

Kept with the label type rather than with the step relation, because being internal is a property of a
label while emitting one is a property of a rule.
-/
def isTau :
    GeneralLabel →
    Prop

  | tau =>
      True

  | timeAdvance _ _ =>
      False

  | consume _ _ =>
      False

@[simp]
theorem isTau_tau :
    isTau tau :=
  True.intro

@[simp]
theorem not_isTau_timeAdvance
    (before after : LogicalTime) :
    ¬ isTau (timeAdvance before after) := by
  simp [isTau]

@[simp]
theorem not_isTau_consume
    (receiver : ActorName)
    (message : DTR.GeneralMessage) :
    ¬ isTau (consume receiver message) := by
  simp [isTau]

/--
Project a label onto the observable alphabet.

An internal label is dropped; an observable one is retained unchanged. The observable alphabet is the
label type itself, following `exampleProject` in `Relico/Tests/WeakTransitionFoundation.lean`, because
nothing in this fragment observes less than a whole visible label.

This is the second half of what `Relico/Common/WeakTransition.lean` needs and the piece G2d's finite-trace
agreement consumes: `Common.observableProjection` is `List.filterMap project`, with three `@[simp]`
lemmas already proved, so a trace statement over this function costs no new induction.
-/
def project :
    GeneralLabel →
    Option GeneralLabel

  | tau =>
      none

  | timeAdvance before after =>
      some (timeAdvance before after)

  | consume receiver message =>
      some (consume receiver message)

@[simp]
theorem project_tau :
    project tau = none := by
  rfl

@[simp]
theorem project_timeAdvance
    (before after : LogicalTime) :
    project (timeAdvance before after) =
      some (timeAdvance before after) := by
  rfl

@[simp]
theorem project_consume
    (receiver : ActorName)
    (message : DTR.GeneralMessage) :
    project (consume receiver message) =
      some (consume receiver message) := by
  rfl

end GeneralLabel

end DTR
end Relico
