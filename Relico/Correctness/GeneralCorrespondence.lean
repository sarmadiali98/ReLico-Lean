import Relico.DTR.GeneralRuntime
import Relico.DTR.GeneralWellFormed
import Relico.LF.GeneralSemantics
import Relico.LF.GeneralAlphaEquivalence
import Relico.DTR.GeneralInitialization
import Relico.LF.GeneralInitialization
import Relico.Correctness.GeneralEvaluation
import Relico.Correctness.GeneralConnectionSourceUniqueness

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

**The queue agreement is multiplicity-aware, as a pairing of matched occurrences.** The
relation's first form (down to this module's own note of 2026-08-26) was two directional
existentials on time and target — deliberately weaker than a bijection, because the transfer
conditions that consume multiplicity did not exist yet, and F86 records that the prediction
was right in both directions: the consume case did need multiplicity and could not have it
without changing the relation. The measured counterexample is a bag holding two identical
messages against a queue holding one matching event — the old relation held, both removals
were possible, and either one destroyed it. `GeneralPendingAgrees` below is the approved
repair (β-(i), decision of 2026-08-29): an existential pairing of `DTR.GeneralMessage ×
LF.GeneralPendingEvent` in which every pair satisfies `GeneralConsumeMatch`, the bag is a
permutation of the message projection, and this actor's events — the whole queue filtered by
`target` — are a permutation of the event projection. Permutation carries occurrence
multiplicity, so legal duplicates stay legal, and consuming one matched pair removes exactly
one occurrence from each side. The two old directional facts follow (the accessors below), so
every consumer of the weaker relation survives; the pairing itself is what the two `.consume`
transfer conditions will consume, and they remain unwritten (F86's scheduler question is not
answered here — this change fixes the *representation* of multiplicity, nothing else).

The multi-store family's `PendingCorresponds` is not reusable for this. It pins the target action name as
a function of the source message name, and general action names are per **send site**
(`Translation.generalActionNameAtSite`, the F56 repair), while `DTR.GeneralMessage` records no site — its
four fields are `sender`, `messageName`, `payload` and `arrival`. The site is not recoverable from a
message, so an agreement that mentioned the action name would be unprovable rather than merely stronger.
Logical time is recoverable, and that is what the pairing relates through `GeneralConsumeMatch`.
-/

/--
A source message and a target event match, for the purposes of a `.consume` transfer.

The label correspondence `#129` needs, stated as data rather than as a function because no total
one exists (F78: `consume` carries different payload types on the two sides). A match fixes the
event's target to the receiving actor's name, its logical time to the message's arrival, and its
payload to the pointwise compilation of the message's payload.

`name` is a parameter rather than read off the message for the same reason
`GeneralPendingAgrees` takes it as a parameter: a message records its sender and its message name,
never its receiver, so the receiver is the store position the correspondence already tracks.

The event **kind** is deliberately not constrained here. Constraining it would mean relating a
`DTR.MsgName` to an `LF.GeneralEventKind`, which is a property of the *compiled program* (which
reaction of which reactor the translation emitted for this message server), not of the runtime
states; the transfer conditions take the resolved reaction as a premise instead, which is
strictly more honest — it lets the caller hold the compiled program's answer rather than
re-deriving a naming convention the runtime never consults.

**Moved here from `Relico/Correctness/GeneralWeakBisimulation.lean` when β-(i) landed its
consumer:** the pairing relation below is stated through this definition, and the import graph
runs the other way (`GeneralWeakBisimulation` imports `GeneralTimeEquivalence`, which imports
this file), so the definition had to move to the module both sides can see. The content is
unchanged by the move — the statement is the same three conjuncts, and it was a `def` with no
proof to carry.
-/
def GeneralConsumeMatch
    (name : ActorName)
    (message : DTR.GeneralMessage)
    (event : LF.GeneralPendingEvent) :
    Prop :=
  event.target = name ∧
    event.tag.time = message.arrival ∧
      event.payload =
        message.payload.map
          Translation.compileGeneralValue

/--
One actor's messages, against the events of the global queue that target it.

An existential pairing of matched occurrences: every pair satisfies `GeneralConsumeMatch`, the
bag is a permutation of the message projection, and the events targeting this actor are a
permutation of the event projection. Permutation carries occurrence multiplicity — two
identical messages are two pairs, and demand two events — so the shape the F86 counterexample
broke (two messages, one event) is refused outright.

The queue side is the whole queue filtered by target, not any pre-selected sublist, so an event
the pairing forgets is a permutation failure rather than a silent omission. The filter decides
on `decide (event.target = name)`, the same `DecidableEq`-only discipline `LF.matchesKind` and
`LF.findReactor?` record: `ActorName` derives `DecidableEq` and `BEq` independently with no
lawfulness bridge between them, and one notion of equality must decide the correspondence's
own filter.

`name` is a parameter rather than being read off the events because the source side has no target field
to read: an actor's bag is identified by *where it is stored*, and the correspondence is what connects
that position to the `target` field the target side does carry.
-/
def GeneralPendingAgrees
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    (pending : LF.GeneralEventQueue) :
    Prop :=
  ∃ pairs : List (DTR.GeneralMessage × LF.GeneralPendingEvent),
    (∀ pair ∈ pairs, GeneralConsumeMatch name pair.1 pair.2) ∧
      List.Perm bag (pairs.map Prod.fst) ∧
      List.Perm
        (pending.filter (fun event => decide (event.target = name)))
        (pairs.map Prod.snd)

/--
An empty bag agrees with an empty queue.

Stated for the same reason `generalValuationAgrees_empty` is stated one module earlier: it makes the
definition demonstrably **satisfiable**, so the results below are not theorems about an empty hypothesis.
`docs/STAGE_G_FINDINGS.md` F66 part 5 is a finding about a conjunct of the paper's own relation being
trivially true, and a module that took an unsatisfiable hypothesis would repeat that defect while
building green.

Under the pairing relation the witness is the empty pair list: both projections are `[]`, and the
empty queue filtered by target is `[]` however the filter decides. What the pairing adds over the
old existential form is exactly what this case shows off — the relation talks about *occurrences*,
and zero occurrences is the smallest satisfiable state.
-/
theorem generalPendingAgrees_empty
    (name : ActorName) :
    GeneralPendingAgrees
      name
      []
      [] := by

  refine ⟨[], ?_, ?_, ?_⟩

  · intro pair hPair

    cases hPair

  · exact List.Perm.nil

  · simp

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
have something pending to advance to. A corollary of the pairing relation: the message is a member of the
bag, hence of the message projection (`List.Perm.mem_iff` against the projection permutation), hence some
pair carries it, and that pair's `GeneralConsumeMatch` is the whole existential.
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

  obtain ⟨pairs, hPairs, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  obtain ⟨pair, hPairMember, hPairFst⟩ :=
    List.mem_map.mp
      (hBagPerm.mem_iff.mp hMessage)

  obtain ⟨hTarget, hArrival, _⟩ :=
    hPairs
      pair
      hPairMember

  have hEventMember :
      pair.2 ∈ pending :=
    (List.mem_filter.mp
      (hQueuePerm.mem_iff.mpr
        (List.mem_map.mpr
          ⟨pair, hPairMember, rfl⟩))).left

  refine ⟨pair.2, hEventMember, hTarget, ?_⟩

  rw [← hPairFst]

  exact hArrival

/--
Every target event aimed at this actor has a source message at its instant.

The backward direction — the one Lemma 1 uses when the target selects an event and the source must be shown
to have a matching arrival, so that the instant the target moves to is one the source can also reach. The
`target` premise is what makes this per-actor: the queue is global, and an event aimed elsewhere says
nothing about this bag. A corollary of the pairing relation, symmetric to the forward one: the event is a
member of the filtered queue, hence of the event projection, hence some pair carries it, and that pair's
`GeneralConsumeMatch` supplies the message.
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

  obtain ⟨pairs, hPairs, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  have hEventFiltered :
      event ∈
        pending.filter
          (fun e => decide (e.target = name)) :=
    List.mem_filter.mpr
      ⟨hEvent,
       by
         show
           decide (event.target = name) =
             true

         rw [hTarget]

         exact decide_eq_true rfl⟩

  obtain ⟨pair, hPairMember, hPairSnd⟩ :=
    List.mem_map.mp
      (hQueuePerm.mem_iff.mp hEventFiltered)

  obtain ⟨_, hArrival, _⟩ :=
    hPairs
      pair
      hPairMember

  have hMessageMember :
      pair.1 ∈ bag :=
    hBagPerm.mem_iff.mpr
      (List.mem_map.mpr
        ⟨pair, hPairMember, rfl⟩)

  refine ⟨pair.1, hMessageMember, ?_⟩

  rw [← hPairSnd]

  exact hArrival.symm

/-!
### Consuming one matched occurrence

The β-(i) relation exists for one consumer: the `.consume` transfer conditions, which remove one
message from the bag and one event from the queue and must know the remainders still agree. The
theorem below is that fact, and nothing more beside it. It does not choose which message the
source scheduler takes or which event the target scheduler fires — those are the two sides of
F86's still-open scheduling question — and it does not discharge the commutation theorem's
`first ∉ earlier` boundary, which is about execution order between fires, not about the
invariant's survival under a removal that has already happened.

The proof's interesting case exists because `GeneralConsumeMatch` pins target, time and compiled
payload but cannot pin *which occurrence* carries them: the pair holding the message and the pair
holding the event may be two different occurrences of the pairing. When they are, removing both
and splicing the far sides together — `(message, e₁)` alongside `(m₂, event)` leaves `(m₂, e₁)` —
is licensed by pure transitivity of the three conjuncts (all four values share target, time and
compiled payload), and it is multiplicity-honest: two occurrences out, one in, exactly matching
the two removals that shrank each side by one. Duplicates need no special treatment anywhere in
the argument, which is the point of representing occurrences as a list rather than a set.

The generic half — removing one occurrence of the same value from each side of a permutation
leaves a permutation — is isolated as `perm_remove_middle` below. It is composed from core's
`List.perm_middle`, `List.perm_append_comm` and `List.Perm.cons_inv`; Mathlib's
`List.Perm.remove` does not exist in this core-only development, and core's `List.Perm.erase` is
deliberately not used because `List.erase` runs on `BEq`, and this repository's types derive
`BEq` and `DecidableEq` independently with no lawfulness bridge between them — the same hazard
`LF.matchesKind`'s `decide`-only discipline records.
-/

/--
Moving one occurrence from the middle of a list to its end is a permutation.

Stated with the occurrence as a cons between explicit splits because that is the shape every
consumer of this section produces: a removal exposes `earlier ++ a :: later`, and the repair
below needs the removed value re-attached to the far end instead. Composed from core's
`List.perm_middle` (middle to front) and `List.perm_append_comm` (front to end) rather than
proved by induction.
-/
private theorem perm_middle_append
    {α : Type}
    {a : α}
    {x y : List α} :
    List.Perm
      (x ++ a :: y)
      ((x ++ y) ++ [a]) :=
  List.perm_middle.trans
    (List.perm_append_comm
      (l₁ := [a])
      (l₂ := x ++ y))

/--
Removing one occurrence of the same value from each side of a permutation leaves a permutation
of the remainders.

This is the occurrence-removal congruence the `.consume` transfer conditions need, in split
form: both sides present the occurrence as `splits ++ a :: splits`, the value `a` is the *same*
on both sides, and the conclusion drops it from each. It is the fact Mathlib packages as
`List.Perm.remove`; here it is derived from `perm_middle_append` by moving both occurrences to
the ends — `List.Perm.cons_inv` then cancels the common heads — which needs no induction over
the permutation's derivation and no `BEq` lawfulness.
-/
private theorem perm_remove_middle
    {α : Type}
    {a : α}
    {x y x' y' : List α}
    (h :
      List.Perm
        (x ++ a :: y)
        (x' ++ a :: y')) :
    List.Perm
      (x ++ y)
      (x' ++ y') := by
  have hLeft :
      List.Perm
        (x ++ a :: y)
        ((x ++ y) ++ [a]) :=
    perm_middle_append

  have hRight :
      List.Perm
        (x' ++ a :: y')
        ((x' ++ y') ++ [a]) :=
    perm_middle_append

  have hEnd :
      List.Perm
        ((x ++ y) ++ [a])
        ((x' ++ y') ++ [a]) :=
    hLeft.symm.trans
      (h.trans hRight)

  have hHeadLeft :
      List.Perm
        ((x ++ y) ++ [a])
        (a :: (x ++ y)) :=
    List.perm_append_comm
      (l₁ := x ++ y)
      (l₂ := [a])

  have hHeadRight :
      List.Perm
        ((x' ++ y') ++ [a])
        (a :: (x' ++ y')) :=
    List.perm_append_comm
      (l₁ := x' ++ y')
      (l₂ := [a])

  exact
    List.Perm.cons_inv
      (hHeadLeft.symm.trans
        (hEnd.trans hHeadRight))

/--
Consuming one matched occurrence on each side preserves the agreement.

The premise shape is exactly what the two `.consume` rules hand over: the source `take` splits
the bag as `earlier ++ message :: later`, the target `fire` splits the queue as
`earlier' ++ event :: later'`, and `GeneralConsumeMatch` is the pairing's own notion of the two
occurrences being the same event. The conclusion is the β-(i) agreement of the remainders —
`earlier ++ later` against `earlier' ++ later'`.

The witness construction is where multiplicity lives. The pairing's list loses one
*occurrence* — not all occurrences of a value — and when the message's pair and the event's
pair are different occurrences, the proof removes both and appends their spliced remainder
`(pair2.fst, pair1.snd)`, whose match is three transitivities of the hypotheses' conjuncts.
Nothing forbids `message` or `event` occurring several times; each removal takes exactly one,
because `List.Perm` counts occurrences, and the queue-side filter passes only the events that
target this actor — the removed event's target being pinned by `hMatch` is what lets the filter
computation expose that one occurrence while every other event's fate under the filter is
untouched by the removal.

What this theorem deliberately does **not** do: it does not relate the source's choice of
`message` to the target's choice of `event` beyond `hMatch`, does not schedule, and does not
order — the F86 questions stay open, and the commutation theorem's duplicate boundary
(`first ∉ earlier`) is untouched, being about firing order rather than invariant preservation.
-/
theorem generalPendingAgrees_removeOne
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    (pending : LF.GeneralEventQueue)
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        pending)
    (message : DTR.GeneralMessage)
    (event : LF.GeneralPendingEvent)
    (hMatch :
      GeneralConsumeMatch
        name
        message
        event)
    (earlier later : DTR.GeneralMessageBag)
    (hBagSplit :
      bag =
        earlier ++ message :: later)
    (earlier' later' : LF.GeneralEventQueue)
    (hQueueSplit :
      pending =
        earlier' ++ event :: later') :
    GeneralPendingAgrees
      name
      (earlier ++ later)
      (earlier' ++ later') := by
  obtain ⟨pairs, hPairsMatch, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  obtain ⟨hMatchTarget, hMatchArrival, hMatchPayload⟩ :=
    hMatch

  have hEventPasses :
      decide (event.target = name) = true := by
    rw [hMatchTarget]

    exact decide_eq_true rfl

  have hFilterCons :
      (event :: later').filter
          (fun e => decide (e.target = name)) =
        event ::
          later'.filter
            (fun e => decide (e.target = name)) :=
    List.filter_cons_of_pos
      (p := (fun e => decide (e.target = name)))
      (a := event)
      hEventPasses

  have hMessageMem :
      message ∈ bag := by
    rw [hBagSplit]

    exact
      List.mem_append.mpr
        (Or.inr List.mem_cons_self)

  have hEventFiltered :
      event ∈
        pending.filter
          (fun e => decide (e.target = name)) := by
    rw [hQueueSplit, List.filter_append, hFilterCons]

    exact
      List.mem_append.mpr
        (Or.inr List.mem_cons_self)

  obtain ⟨pair1, hPair1Mem, hPair1Fst⟩ :=
    List.mem_map.mp
      (hBagPerm.mem_iff.mp hMessageMem)

  obtain ⟨pair2, hPair2Mem, hPair2Snd⟩ :=
    List.mem_map.mp
      (hQueuePerm.mem_iff.mp hEventFiltered)

  obtain ⟨h1Target, h1Arrival, h1Payload⟩ :=
    hPairsMatch
      pair1
      hPair1Mem

  obtain ⟨h2Target, h2Arrival, h2Payload⟩ :=
    hPairsMatch
      pair2
      hPair2Mem

  rw [hBagSplit] at hBagPerm

  rw [hQueueSplit, List.filter_append, hFilterCons] at hQueuePerm

  by_cases hDirect : pair1.snd = event

  · obtain ⟨before1, after1, hSplit1⟩ :=
      List.append_of_mem hPair1Mem

    refine ⟨before1 ++ after1, ?_, ?_, ?_⟩

    · intro pair hPairMem

      rcases
        List.mem_append.mp hPairMem with
        hIn | hIn
      · exact
          hPairsMatch pair
            (by
              rw [hSplit1]

              exact
                List.mem_append.mpr
                  (Or.inl hIn))
      · exact
          hPairsMatch pair
            (by
              rw [hSplit1]

              exact
                List.mem_append.mpr
                  (Or.inr
                    (List.mem_cons.mpr
                      (Or.inr hIn))))

    · rw [List.map_append]

      rw [hSplit1, List.map_append, List.map_cons, hPair1Fst] at hBagPerm

      exact perm_remove_middle hBagPerm

    · rw [List.filter_append, List.map_append]

      rw [hSplit1, List.map_append, List.map_cons, hDirect] at hQueuePerm

      exact perm_remove_middle hQueuePerm

  · obtain ⟨before1, after1, hSplit1⟩ :=
      List.append_of_mem hPair1Mem

    have hPair2Rest :
        pair2 ∈ before1 ++ after1 := by
      have hPair2In :
          pair2 ∈ before1 ++ pair1 :: after1 := by
        rw [← hSplit1]

        exact hPair2Mem

      rcases
        List.mem_append.mp hPair2In with
        hIn | hIn
      · exact
          List.mem_append.mpr
            (Or.inl hIn)
      · rcases
          List.mem_cons.mp hIn with
          hEq | hIn
        · exact
            absurd
              (by
                rw [← hEq]

                exact hPair2Snd)
              hDirect
        · exact
            List.mem_append.mpr
              (Or.inr hIn)

    obtain ⟨middle, tail2, hSplit2⟩ :=
      List.append_of_mem hPair2Rest

    refine
      ⟨(middle ++ tail2) ++ [(pair2.fst, pair1.snd)],
        ?_, ?_, ?_⟩

    · intro pair hPairMem

      rcases
        List.mem_append.mp hPairMem with
        hIn | hIn
      · have hPairInRest :
            pair ∈ before1 ++ after1 := by
          rw [hSplit2]

          rcases
            List.mem_append.mp hIn with
            hIn' | hIn'
          · exact
              List.mem_append.mpr
                (Or.inl hIn')
          · exact
              List.mem_append.mpr
                (Or.inr
                  (List.mem_cons.mpr
                    (Or.inr hIn')))

        exact
          hPairsMatch pair
            (by
              rw [hSplit1]

              rcases
                List.mem_append.mp hPairInRest with
                hIn' | hIn'
              · exact
                  List.mem_append.mpr
                    (Or.inl hIn')
              · exact
                  List.mem_append.mpr
                    (Or.inr
                      (List.mem_cons.mpr
                        (Or.inr hIn'))))
      · obtain rfl :=
          List.mem_singleton.mp hIn

        refine ⟨h1Target, ?_, ?_⟩

        · rw [h1Arrival, hPair1Fst, ← hMatchArrival, ← h2Arrival, hPair2Snd]

        · rw [h1Payload, hPair1Fst, ← hMatchPayload, ← h2Payload, hPair2Snd]

    · rw [List.map_append, List.map_append, List.map_singleton]

      have hBagExposed :
          List.Perm
            (earlier ++ message :: later)
            (List.map Prod.fst before1 ++ message :: List.map Prod.fst after1) := by
        rw [hSplit1, List.map_append, List.map_cons, hPair1Fst] at hBagPerm

        exact hBagPerm

      have hBagRest :
          List.map Prod.fst before1 ++ List.map Prod.fst after1 =
        List.map Prod.fst middle ++ pair2.fst :: List.map Prod.fst tail2 := by
        rw [← List.map_append, hSplit2, List.map_append, List.map_cons]

      have hBagRot :
          List.Perm
            (List.map Prod.fst middle ++ pair2.fst :: List.map Prod.fst tail2)
            ((List.map Prod.fst middle ++ List.map Prod.fst tail2) ++ [pair2.fst]) :=
        perm_middle_append

      have hBagStep :=
        perm_remove_middle hBagExposed

      rw [hBagRest] at hBagStep

      exact hBagStep.trans hBagRot

    · rw [List.filter_append, List.map_append, List.map_append, List.map_singleton,
        List.append_assoc]

      have hQueueExposed :
          pairs.map Prod.snd =
        List.map Prod.snd before1 ++ pair1.snd :: List.map Prod.snd after1 := by
        rw [hSplit1, List.map_append, List.map_cons]

      rw [hQueueExposed] at hQueuePerm

      have hQueueFront :
          List.Perm
            (List.map Prod.snd before1 ++ pair1.snd :: List.map Prod.snd after1)
            (pair1.snd :: (List.map Prod.snd before1 ++ List.map Prod.snd after1)) :=
        List.perm_middle

      have hQueueMid :=
        hQueuePerm.trans hQueueFront

      have hQueueRest :
          List.map Prod.snd before1 ++ List.map Prod.snd after1 =
        List.map Prod.snd middle ++ event :: List.map Prod.snd tail2 := by
        rw [← List.map_append, hSplit2, List.map_append, List.map_cons, hPair2Snd]

      rw [hQueueRest] at hQueueMid

      have hQueueEnd :
          List.Perm
            (pair1.snd :: (List.map Prod.snd middle ++ event :: List.map Prod.snd tail2))
            ((List.map Prod.snd middle ++ event :: List.map Prod.snd tail2) ++ [pair1.snd]) :=
        List.perm_append_comm
          (l₁ := [pair1.snd])
          (l₂ := List.map Prod.snd middle ++ event :: List.map Prod.snd tail2)

      have hQueueMid2 :=
        hQueueMid.trans hQueueEnd

      have hQueueShuffle :
          (List.map Prod.snd middle ++ event :: List.map Prod.snd tail2) ++ [pair1.snd] =
        List.map Prod.snd middle ++ (event :: (List.map Prod.snd tail2 ++ [pair1.snd])) := by
        rw [List.append_assoc, List.cons_append]

      rw [hQueueShuffle] at hQueueMid2

      exact perm_remove_middle hQueueMid2

/-!
### Transporting the agreement across queue equivalences

Two small closure facts the `.consume` transfer conditions need: the pairing is invariant under a
permutation of the pending queue, and under dropping an event the filter never selected. The first is
what lets a transfer condition move the pairing from the correspondence's own queue to an
α-representative's (F86's light quotient permutes queues and nothing else); the second is what lets
every *other* actor's pairing survive one actor's event being consumed — the removed event fails the
other actors' target filters, so their filtered projections never see it go.
-/

/--
The agreement is invariant under permutation of the pending queue.

The bag conjunct and the pair conjunct mention only the pairing itself; the queue conjunct filters the
queue, and `List.Perm.filter` carries the permutation through the filter. No occurrence bookkeeping is
needed — the permutation already carries it — which is the β-(i) design paying off twice over: the same
clause that made multiplicity provable makes queue-permutation transport free.
-/
theorem generalPendingAgrees_of_queue_perm
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    {pending pending' : LF.GeneralEventQueue}
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        pending)
    (hPerm :
      List.Perm
        pending
        pending') :
    GeneralPendingAgrees
      name
      bag
      pending' := by
  obtain ⟨pairs, hPairsMatch, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  exact
    ⟨pairs,
     hPairsMatch,
     hBagPerm,
     (List.Perm.filter
        (fun event =>
          decide (event.target = name))
        hPerm).symm.trans
       hQueuePerm⟩

/--
Dropping an event that targets another actor leaves this actor's agreement intact.

The queue conjunct filters by target, so an event aimed elsewhere is invisible to it: filtering
`earlier ++ event :: later` and filtering `earlier ++ later` produce the same list, and the same pairing
witnesses both. This is the half of one consume that belongs to everyone else — the consumed occurrence
is removed from the global queue, but only the consuming actor's projection ever contained it.
-/
theorem generalPendingAgrees_of_queue_drop
    (name : ActorName)
    (bag : DTR.GeneralMessageBag)
    (event : LF.GeneralPendingEvent)
    (earlier later : LF.GeneralEventQueue)
    (hAgrees :
      GeneralPendingAgrees
        name
        bag
        (earlier ++ event :: later))
    (hElsewhere :
      event.target ≠ name) :
    GeneralPendingAgrees
      name
      bag
      (earlier ++ later) := by
  obtain ⟨pairs, hPairsMatch, hBagPerm, hQueuePerm⟩ :=
    hAgrees

  refine
    ⟨pairs,
     hPairsMatch,
     hBagPerm,
     ?_⟩

  have hFilter :
      (earlier ++ event :: later).filter
          (fun e =>
            decide (e.target = name)) =
        (earlier ++ later).filter
          (fun e =>
            decide (e.target = name)) := by
    rw [
      List.filter_append,
      List.filter_append,
      List.filter_cons_of_neg
        (p := fun e =>
          decide (e.target = name))
        (a := event)
        (by
          simp [hElsewhere])
    ]

  rw [hFilter] at hQueuePerm

  exact hQueuePerm

/--
The target continuation is a compilation of the source continuation, **under a named environment**.

The paper's `π_x ≡ μ_r`. The output-port environment is a *parameter*, not an existential: it belongs
to the sending class, and which class a runtime reactor belongs to is a fact the correspondence must
carry if a routed send is ever to be transferred. The body context and the statement index stay
existential, because both vary along one execution — the context differs between a constructor body
and a message-server body, and the index advances at every consumed statement — so pinning either
would oblige every τ rule to re-derive it for no consumer's benefit.

**This replaces a documented weakening.** An earlier revision quantified the environment
existentially, and its docstring recorded the consequence: the relation permitted a target
continuation compiled under some *other* class's port environment. That slack blocked
`Correctness.generalRoutedSend_forward`, whose entry (recovered from a compiled `.setPort` head)
belonged to an unknown environment while `Translation.generalConnectionFrom?_siteFaithful` needs the
one the routing table was built from. The old docstring named the repair site correctly — "G2c is
where the environment first has a name to be pinned to" — and this is that repair.

**The site conjunct carries two field equations, and the second was added after the first proved
insufficient.** An earlier revision concluded only `entry.knownRebec = rebec`, and its own docstring
argued that the rebec was the field deciding where a message goes. That is true and was not enough:
`LF.GeneralStmt.setPort` carries no delay, because on the LF side a send's `after` is a property of the
connection the value travels along rather than of the statement. So the generated program's *only*
record of a routed statement's delay is the entry it resolved to, and a transfer proof that cannot tie
the entry's delay to the statement's cannot show the emitted event lands at the tag the source names.
The three routing lemmas
(`Translation.externalSendsFromIndex_delay_of_drop`, `Translation.generalOutputPortEntryFor_delay`,
`Translation.generalRouteFor_delay`) close statement to send to entry to route, but the first of them
needs the class's declared body and the running statement's position in it — and `activeBody` is a
*suffix* of a declared body whose `bodyKey` and `index` are existential here. Composing them at the
transfer site is therefore impossible, not merely awkward, which is the same obstruction the rebec half
hit. Both fields are resolved the same way: at the one construction site, where the declared body *is*
in hand.

`Except String LF.GeneralBody` is the compiler's return type, so `.ok` is spelled out as `Except.ok`
to keep the definition readable without the expected type in view.
-/
def GeneralContinuationCompiles
    (env : Translation.GeneralOutputPortEnv)
    (source : DTR.GeneralBody)
    (target : LF.GeneralBody) :
    Prop :=
  ∃ context : Translation.GeneralBodyContext,
    ∃ index : Nat,
      Translation.compileGeneralBody
            env
            context
            index
            source =
          Except.ok target ∧
        ∀ (path : List Nat)
          (rebec : KnownRebecName)
          (message : MsgName)
          (delay : Delay),
          Translation.GeneralSendAtPath
            source
            path
            rebec
            message
            delay →
          ∀ entry : Translation.GeneralOutputPortEntry,
            Translation.generalEntryAtSite?
                env
                {
                  body :=
                    context.bodyKey

                  index :=
                    context.levelPath ++
                      Translation.shiftHeadPath
                        index
                        path
                } =
              some entry →
            entry.knownRebec = rebec ∧
              entry.delay = delay

/--
The empty continuation compiles to the empty continuation.

The satisfiability witness, and the case both theorems below actually use: every actor is idle initially,
and `Translation.compileGeneralBody_nil` is an `@[simp]` `rfl` lemma, so the three auxiliary inputs may be
anything at all. The empty port environment and `default` context are chosen because they are the two
values that need no construction.
-/
theorem generalContinuationCompiles_nil
    (env : Translation.GeneralOutputPortEnv) :
    GeneralContinuationCompiles
      env
      []
      [] :=
  ⟨default,
   0,
   Translation.compileGeneralBody_nil
     env
     default
     0,
   by
     intro _ _ _ _ hPath

     exact
       absurd
         hPath
         (fun hDerivation =>
           Translation.generalSendAtPath_nil
             hDerivation)⟩

/--
Consuming a trace head preserves the compilation relation for the remaining continuations.

The compiler emits the trace statement literally, so inversion of a successful body compilation exposes
the same trace head and advances the statement index by one. This is the continuation fact used by any
future correspondence transfer case for the internal instrumentation rule.
-/
theorem generalContinuationCompiles_trace_tail
    {env : Translation.GeneralOutputPortEnv}
    {tag : String}
    {sourceRemaining : DTR.GeneralBody}
    {targetRemaining : LF.GeneralBody}
    (hCompiles :
      GeneralContinuationCompiles
        env
        (.trace tag :: sourceRemaining)
        (.trace tag :: targetRemaining)) :
    GeneralContinuationCompiles
      env
      sourceRemaining
      targetRemaining := by

  rcases hCompiles with
    ⟨context, index, hCompiled, hSites⟩

  obtain
    ⟨compiledStatement, compiledRemaining, hStatement, hRemaining, hEqual⟩ :=
      Translation.compileGeneralBody_cons_ok_inversion
        hCompiled

  rw [Translation.compileGeneralStmt_trace] at hStatement
  injection hStatement with hStatement
  subst compiledStatement

  injection hEqual with hRemainingTarget
  subst targetRemaining

  refine
    ⟨context,
     index + 1,
     hRemaining,
     ?_⟩

  -- Reindex: a send at path `p` of the tail is a send at `Translation.bumpHeadPath p` of the body, and
  -- `Translation.shiftHeadPath (index + 1) p = Translation.shiftHeadPath index (Translation.bumpHeadPath p)`, so the incoming
  -- obligation answers directly. Stage H replaced the flat `k`/`k + 1` pair by these two, and the
  -- singleton-path case is the old arithmetic unchanged.
  intro path rebec message delay hPath entry hEntry

  refine
    hSites
      (Translation.bumpHeadPath
        path)
      rebec
      message
      delay
      (Translation.generalSendAtPath_cons
        hPath)
      entry
      ?_

  rw [
    ← Translation.shiftHeadPath_bumpHeadPath
  ]

  exact hEntry

/--
The two frame stacks compile, level for level.

Stage H's fourth conjunct of the actor pairing, and the reason it is a definition of its own rather
than an inline `List.Forall₂`: the pointwise relation is `GeneralContinuationCompiles`, this
development depends on no library function whose name has churned across Lean releases, and an
explicit recursion generates the equation lemmas the two idleness transfers rewrite with.

Equal length is part of the statement, by construction: mismatched lengths fall into the `False` arm.
That is what makes *"the source has nothing pending at any level"* and *"the target has nothing
pending at any level"* the same claim, which is what `Correctness.generalReactorIdle_of_actorIdle` and
`Correctness.generalActorIdle_of_reactorIdle` need in opposite directions. Before this conjunct
existed the two `idle` predicates had a conjunct each that the relation said nothing about, and the
transfers stopped being provable in exactly one direction each; the compiler found both.

For every state reachable in the currently accepted fragment both stacks are `[]`, so this conjunct is
`True` wherever the pre-stage-H development goes.
-/
def GeneralFramesCompile
    (env : Translation.GeneralOutputPortEnv) :
    List DTR.GeneralBody →
    List LF.GeneralBody →
    Prop

  | [], [] =>
      True

  | sourceFrame :: sourceRest, targetFrame :: targetRest =>
      GeneralContinuationCompiles
          env
          sourceFrame
          targetFrame ∧
        GeneralFramesCompile
          env
          sourceRest
          targetRest

  | _, _ =>
      False

/--
An empty source stack forces an empty target stack.

The forward half of the idleness transfer, read off the relation's own shape: a non-empty target stack
against an empty source one is the `False` arm.
-/
theorem generalFramesCompile_target_nil
    {env : Translation.GeneralOutputPortEnv}
    {targetFrames : List LF.GeneralBody}
    (hFrames :
      GeneralFramesCompile
        env
        []
        targetFrames) :
    targetFrames = [] := by

  cases targetFrames with

  | nil =>
      rfl

  | cons targetFrame targetRest =>
      exact
        absurd
          hFrames
          (by
            simp [
              GeneralFramesCompile
            ])

/--
An empty target stack forces an empty source stack.

The backward half, and the mirror of the lemma above.
-/
theorem generalFramesCompile_source_nil
    {env : Translation.GeneralOutputPortEnv}
    {sourceFrames : List DTR.GeneralBody}
    (hFrames :
      GeneralFramesCompile
        env
        sourceFrames
        []) :
    sourceFrames = [] := by

  cases sourceFrames with

  | nil =>
      rfl

  | cons sourceFrame sourceRest =>
      exact
        absurd
          hFrames
          (by
            simp [
              GeneralFramesCompile
            ])

/--
A non-empty source stack forces a non-empty target stack, level by level.

The cons inversion, and what `Correctness.generalResume_forward` runs on: stage H's `resume` promotes
the head frame to the active body, so the transfer needs the target's head frame, the fact that the
source's compiles to it, and the relation on the two tails. All three are the `cons`/`cons` arm of the
relation read backwards; a target `nil` against a source `cons` is the `False` arm.

Stated as an existential over the target's shape rather than as a pair of projections, because the
caller does not have the target stack decomposed — the runtime hands it a `reactor.frames` and this
lemma is what splits it.
-/
theorem generalFramesCompile_cons_source
    {env : Translation.GeneralOutputPortEnv}
    {sourceFrame : DTR.GeneralBody}
    {sourceRest : List DTR.GeneralBody}
    {targetFrames : List LF.GeneralBody}
    (hFrames :
      GeneralFramesCompile
        env
        (sourceFrame :: sourceRest)
        targetFrames) :
    ∃ (targetFrame : LF.GeneralBody)
      (targetRest : List LF.GeneralBody),
      targetFrames =
          targetFrame :: targetRest ∧
        GeneralContinuationCompiles
          env
          sourceFrame
          targetFrame ∧
        GeneralFramesCompile
          env
          sourceRest
          targetRest := by

  cases targetFrames with

  | nil =>
      exact
        absurd
          hFrames
          (by
            simp [
              GeneralFramesCompile
            ])

  | cons targetFrame targetRest =>

      obtain ⟨hHead, hTail⟩ :=
        hFrames

      exact
        ⟨targetFrame,
         targetRest,
         rfl,
         hHead,
         hTail⟩

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
    (env : Translation.GeneralOutputPortEnv)
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
      env
      actor.activeBody
      reactor.activeBody

  frames :
    GeneralFramesCompile
      env
      actor.frames
      reactor.frames

/-- A paired trace head may be removed from an actor correspondence. -/
theorem generalActorCorresponds_trace_tail
    {env : Translation.GeneralOutputPortEnv}
    {name : ActorName}
    {actor : DTR.GeneralActorRuntime}
    {reactor : LF.GeneralReactorRuntime}
    {pending : LF.GeneralEventQueue}
    {tag : String}
    {sourceRemaining : DTR.GeneralBody}
    {targetRemaining : LF.GeneralBody}
    (hCorresponds :
      GeneralActorCorresponds
        env
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
      env
      name
      {
        state := actor.state
        activeBody := sourceRemaining
        frames := actor.frames
      }
      {
        valuation := reactor.valuation
        activeBody := targetRemaining
        frames := reactor.frames
      }
      pending := by

  refine
    {
      valuation := hCorresponds.valuation
      messages := hCorresponds.messages
      continuation := ?_
      frames := hCorresponds.frames
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

**The two frame-stack premises arrived with stage H and are what make the name accurate.** Idleness is
now emptiness at every level, so an actor with an empty active body and a pending enclosing
continuation is not idle; a version of this lemma without those premises would be claiming the pairing
for states neither `idle` predicate accepts. Both are `rfl` at every call site, because every
initializer starts an actor and a reactor at the top level.
-/
theorem generalActorCorresponds_idle
    (env : Translation.GeneralOutputPortEnv)
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
      reactor.activeBody = [])
    (hSourceFrames :
      actor.frames = [])
    (hTargetFrames :
      reactor.frames = []) :
    GeneralActorCorresponds
      env
      name
      actor
      reactor
      [] := by

  refine
    {
      valuation := hValuation
      messages := ?_
      continuation := ?_
      frames := ?_
    }

  · rw [hBag]

    exact generalPendingAgrees_empty name

  · rw [
      hSource,
      hTarget
    ]

    exact generalContinuationCompiles_nil env

  · rw [
      hSourceFrames,
      hTargetFrames
    ]

    exact
      trivial

/--
The output-port environment of whichever class an actor instance belongs to.

The function that lets `GeneralStateCorrespondence` pin each actor's compiled environment without
carrying a second store beside itself. `DTR.GeneralModel.classOfActor?` resolves the instance and its
class in one step, and `Translation.outputPortEnvOf` is the environment the routing table was built
from — so the two agree by construction rather than by hypothesis.

`none` whenever the class or the environment fails to resolve, which for an accepted model means
never; the relation states the success as an equation rather than assuming it, so a consumer reads
the environment off the field instead of supplying it.
-/
def outputPortEnvOfActorName
    (model : DTR.GeneralModel)
    (name : ActorName) :
    Option Translation.GeneralOutputPortEnv :=
  match
      model.classOfActor?
        name
  with

  | none =>
      none

  | some sendingClass =>
      (Translation.outputPortEnvOf
        model.classes
        sendingClass).toOption

/--
The environment equation, from a resolved class and a resolved environment.

The one-step introduction rule, so that a caller holding the two facts an initializer or a routing
walk already produces never unfolds the helper.
-/
theorem outputPortEnvOfActorName_eq
    {model : DTR.GeneralModel}
    {name : ActorName}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : Translation.GeneralOutputPortEnv}
    (hClass :
      model.classOfActor? name =
        some sendingClass)
    (hEnv :
      Translation.outputPortEnvOf
          model.classes
          sendingClass =
        .ok env) :
    outputPortEnvOfActorName model name =
      some env := by
  unfold outputPortEnvOfActorName
  rw [hClass]
  dsimp only
  rw [hEnv]
  rfl

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
    (model : DTR.GeneralModel)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState) :
    Prop where

  logicalTime :
    state.currentTag.time = config.now

  reactorOfActor :
    ∀ (name : ActorName) (actor : DTR.GeneralActorRuntime),
      (name, actor) ∈ config.actors →
        ∃ (env : Translation.GeneralOutputPortEnv)
          (reactor : LF.GeneralReactorRuntime),
          outputPortEnvOfActorName model name = some env ∧
            (name, reactor) ∈ state.reactors ∧
            GeneralActorCorresponds
              env
              name
              actor
              reactor
              state.pending

  actorOfReactor :
    ∀ (name : ActorName) (reactor : LF.GeneralReactorRuntime),
      (name, reactor) ∈ state.reactors →
        ∃ (env : Translation.GeneralOutputPortEnv)
          (actor : DTR.GeneralActorRuntime),
          outputPortEnvOfActorName model name = some env ∧
            (name, actor) ∈ config.actors ∧
            GeneralActorCorresponds
              env
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
    (model : DTR.GeneralModel)
    (config : DTR.GeneralRuntimeConfiguration)
    (state : LF.GeneralRuntimeState)
    (tag : LF.Tag)
    (hTime :
      tag.time = state.currentTag.time)
    (hCorrespondence :
      GeneralStateCorrespondence model config state) :
    GeneralStateCorrespondence
      model
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

/-!
### Compatibility with α-equivalence

The F86 light-quotient layer (`Relico/LF/GeneralAlphaEquivalence.lean`) lets the eventual `.consume`
transfer conditions step to an α-equivalent representative before firing. These two theorems are why
that is free: the correspondence survives replacement of the whole target state by an α-equivalent one.
Nothing here inspects the generator — the transport runs on the clauses of the state relation and
the four fields of `GeneralStateCorrespondence`, which is the whole point of stating the queue clause as
a closure with proved consequences (`List.Perm` for membership, filter equality for the per-actor
projection) rather than as raw swaps.
-/

/--
One actor's correspondence survives an α-exchange of the pending queue.

Only the `messages` field reads the queue, and `GeneralPendingAgrees` reads it through exactly the
filter whose equality `generalQueueAlphaEquiv.filter_target` preserves — so the same pairing witnesses
both sides. The valuation and continuation fields are queue-blind and pass through untouched.
-/
theorem generalActorCorresponds_of_queueAlphaEquiv
    (env : Translation.GeneralOutputPortEnv)
    (name : ActorName)
    (actor : DTR.GeneralActorRuntime)
    (reactor : LF.GeneralReactorRuntime)
    {pending pending' : LF.GeneralEventQueue}
    (hCorresponds :
      GeneralActorCorresponds
        env
        name
        actor
        reactor
        pending)
    (hEquiv :
      LF.generalQueueAlphaEquiv
        pending
        pending') :
    GeneralActorCorresponds
      env
      name
      actor
      reactor
      pending' := by
  obtain
      ⟨hValuation, ⟨pairs, hPairsMatch, hBagPerm, hQueuePerm⟩, hContinuation, hFrames⟩ :=
    hCorresponds

  have hFilter :
      pending.filter
          (fun event =>
            decide (event.target = name)) =
        pending'.filter
          (fun event =>
            decide (event.target = name)) :=
    LF.generalQueueAlphaEquiv.filter_target
      name
      hEquiv

  refine
    {
      valuation := hValuation

      messages :=
        ⟨pairs,
         hPairsMatch,
         hBagPerm,
         by
           rw [← hFilter]

           exact hQueuePerm⟩

      continuation := hContinuation
      frames := hFrames
    }

/--
The correspondence is invariant under α-equivalence of the target state.

This is the lemma the light-quotient transfer conditions consume whenever a step begins at (or lands
in) a representative rather than the state the correspondence was stated at. Each field transports
along the clause of `generalStateAlphaEquiv` that reads the same state component: `logicalTime` along
tag equality, the two store fields along the membership half of the store component (the lookup half
is for `GeneralStep`'s reading, not this relation's — `Store.mem_of_lookup`'s docstring records the
shadowed-binding discipline the correspondence's own fields follow), and `pendingTargeted` along the
`List.Perm` that every queue α-equivalence carries.
-/
theorem generalStateCorrespondence_of_generalStateAlphaEquiv
    {model : DTR.GeneralModel}
    {config : DTR.GeneralRuntimeConfiguration}
    {state state' : LF.GeneralRuntimeState}
    (hCorresponds :
      GeneralStateCorrespondence
        model
        config
        state)
    (hAlpha :
      LF.generalStateAlphaEquiv
        state
        state') :
    GeneralStateCorrespondence
      model
      config
      state' := by
  obtain ⟨hTag, hStore, _, hQueue⟩ :=
    hAlpha

  refine
    {
      logicalTime := by
        rw [← hTag]

        exact
          hCorresponds.logicalTime

      reactorOfActor := by
        intro name actor hActor

        obtain
            ⟨env, reactor, hEnv, hMember, hCorrespondsActor⟩ :=
          hCorresponds.reactorOfActor
            name
            actor
            hActor

        exact
          ⟨env,
           reactor,
           hEnv,
           (hStore name reactor).mp hMember,
           generalActorCorresponds_of_queueAlphaEquiv
             env
             name
             actor
             reactor
             hCorrespondsActor
             hQueue⟩

      actorOfReactor := by
        intro name reactor hMember

        obtain
            ⟨env, actor, hEnv, hActor, hCorrespondsActor⟩ :=
          hCorresponds.actorOfReactor
            name
            reactor
            ((hStore name reactor).mpr hMember)

        exact
          ⟨env,
           actor,
           hEnv,
           hActor,
           generalActorCorresponds_of_queueAlphaEquiv
             env
             name
             actor
             reactor
             hCorrespondsActor
             hQueue⟩

      pendingTargeted := by
        intro event hEvent

        exact
          hCorresponds.pendingTargeted
            event
            ((LF.generalQueueAlphaEquiv.perm
                hQueue).mem_iff.mpr
              hEvent)
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
    (model : DTR.GeneralModel)
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
      GeneralStateCorrespondence model config state) :
    ∃ next : LF.GeneralRuntimeState,
      LF.GeneralStep
          program
          state
          LF.GeneralLabel.tau
          next ∧
        GeneralStateCorrespondence model config next := by

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
        model
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
    (model : DTR.GeneralModel)
    (config : DTR.GeneralConfiguration)
    (reactors : Store ActorName LF.GeneralReactorRuntime)
    (hEnvs :
      ∀ (name : ActorName) (state : DTR.GeneralActorState),
        (name, state) ∈ config.actors →
          ∃ env : Translation.GeneralOutputPortEnv,
            outputPortEnvOfActorName model name = some env)
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
                reactor.activeBody = [] ∧
                  reactor.frames = [])
    (hActors :
      ∀ (name : ActorName) (reactor : LF.GeneralReactorRuntime),
        (name, reactor) ∈ reactors →
          ∃ state : DTR.GeneralActorState,
            (name, state) ∈ config.actors ∧
              GeneralValuationAgrees
                  state.valuation
                  reactor.valuation ∧
                reactor.activeBody = [] ∧
                  reactor.frames = []) :
    GeneralStateCorrespondence
      model
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

    obtain ⟨hState, hBody, hFrames⟩ :=
      DTR.mem_attachEmptyContinuations
        config.actors
        name
        actor
        hAttached

    obtain
        ⟨reactor,
         hReactorMember,
         hValuation,
         hReactorBody,
         hReactorFrames⟩ :=
      hReactors
        name
        actor.state
        hState

    obtain ⟨env, hEnv⟩ :=
      hEnvs
        name
        actor.state
        hState

    exact
      ⟨env,
       reactor,
       hEnv,
       hReactorMember,
       generalActorCorresponds_idle
         env
         name
         actor
         reactor
         hValuation
         (hBags
           name
           actor.state
           hState)
         hBody
         hReactorBody
         hFrames
         hReactorFrames⟩

  · intro name reactor hMember

    obtain
        ⟨state,
         hStateMember,
         hValuation,
         hReactorBody,
         hReactorFrames⟩ :=
      hActors
        name
        reactor
        hMember

    obtain ⟨env, hEnv⟩ :=
      hEnvs
        name
        state
        hStateMember

    refine
      ⟨env,
       {
         state := state
         activeBody := []
         frames := []
       },
       hEnv,
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
          env
          name
          {
            state := state
            activeBody := []
            frames := []
          }
          reactor
          hValuation
          (hBags
            name
            state
            hStateMember)
          rfl
          hReactorBody
          rfl
          hReactorFrames

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
        Translation.outputPortEnvOf
            model.classes
            reactiveClass =
          .ok env ∧
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
       hEnv,
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
      hEnv,
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
The environment equation at a declared instance, from its class and that class's environment.

The form a statement-transfer proof can actually reach. `outputPortEnvOfActorName_eq` above takes
`model.classOfActor?` at the actor's *name*, but a caller holding a routed send holds the instance
itself plus `model.class?` at its class name — and `classOfActor?` is `actor?` followed by `class?`,
so the bridge is instance-name resolution, which needs the model's instance names to be
duplicate-free.

Instance-name `Nodup` is the same accepted-program fact `DTR.generalStoreKeyUnique_initial` and
`Translation.routesOf_sourceEndpoints_nodup` consume, spelled as a `Nodup` over instance names rather
than as a whole `wellFormed` premise. It is not optional: `findActor?` returns the first match, so a
model with two instances of one name would resolve the name to the wrong instance's class.
-/
theorem outputPortEnvOfActorName_eq_of_mem_instances
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : Translation.GeneralOutputPortEnv}
    (hActor :
      actor ∈ model.instances)
    (hNames :
      (List.map
        (fun candidate =>
          candidate.name)
        model.instances).Nodup)
    (hClass :
      model.class? actor.className =
        some sendingClass)
    (hEnv :
      Translation.outputPortEnvOf
          model.classes
          sendingClass =
        .ok env) :
    outputPortEnvOfActorName model actor.name =
      some env := by

  refine
    outputPortEnvOfActorName_eq
      ?_
      hEnv

  unfold DTR.GeneralModel.classOfActor?

  rw [
    show
        model.actor? actor.name =
          some actor from
      findActor?_of_mem_of_nodup
        model.instances
        actor
        hActor
        hNames
  ]

  exact hClass


/--
One actor at constructor entry corresponds to one reactor at startup-entry, given the compilation facts
that connect the two.

The constructor-entry counterpart of `generalActorCorresponds_idle`, and — **F85** — the reason the
unconditional initial theorem is not an instance of the scoped one: both initializers install bodies
(the constructor's on the source side, the compiled startup reaction's on the target side), so neither
side is idle, and the idle lemma's two `activeBody = []` premises are unprovable here. What replaces
them is the continuation conjunct's real content: the target body is a successful `compileGeneralBody`
of the source body, witnessed by the environment and self-send list the reactor itself was compiled
against — which is now `GeneralContinuationCompiles`' `env` parameter together with its two
remaining existentials.

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
    (classes : List DTR.GeneralReactiveClass)
    (hEnv :
      Translation.outputPortEnvOf
          classes
          reactiveClass =
        .ok env)
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
      env
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
      frames := ?_
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

    refine
      ⟨
        {
          bodyKey := .constructor
          selfSends :=
            Translation.selfSendsOfClass
              reactiveClass
        },
        0,
        hBody,
        ?_
      ⟩

    -- The one place the drop-position invariant is CONSTRUCTED rather than reindexed. The startup
    -- body is the class's whole constructor body at index 0, so a site the compiler resolved is a
    -- site of that body's own walk, and the committed routing lemmas identify its rebec *and its
    -- delay* with the statement's. Both halves are discharged here and nowhere else, because this is
    -- the only place the class's declared body is in hand.
    intro path rebec message delay hPath entry hEntry

    -- Stage H: the obligation is over a path, and it is discharged **positively** for every
    -- path, branch or not. `Translation.externalSendsFromIndex_knownRebec_of_path` says the walk's
    -- send at that address carries that path's rebec and delay; the entry the runtime resolved is
    -- that send's, because `exists_send_of_mem_outputPortEnv` produced it from this very
    -- environment. No refutation and no well-formedness premise: an earlier draft asked the caller
    -- for "the constructor body has no conditional", which `generalCorrespondence_initial` cannot
    -- supply — `compileGeneralModel` never checks `DTR.GeneralModel.wellFormed` — and which this
    -- theorem does not need.
    obtain ⟨send, hSendMember, hSendRebec, hSendSite, hSendDelay⟩ :=
      Translation.exists_send_of_mem_outputPortEnv
        hEnv
        (Translation.generalEntryAtSite?_mem
          env
          _
          entry
          hEntry)

    have hSiteEq :
        send.site =
          {
            body :=
              Translation.GeneralBodyKey.constructor

            index :=
              Translation.shiftHeadPath
                0
                path
          } := by
      rw [
        ← hSendSite
      ]

      exact
        Translation.generalEntryAtSite?_site
          env
          _
          entry
          hEntry

    have hBodyMember :
        send ∈
          Translation.externalSendsFromIndex
            .constructor
            []
            0
            reactiveClass.constructor.body :=
      Translation.mem_externalSendsOfBody_constructor_of_mem_externalSendsOfClass
        hSendMember
        (by
          rw [hSiteEq])

    have hSendIndex :
        send.site.index =
          [] ++
            Translation.shiftHeadPath
              0
              path := by
      rw [hSiteEq]

      simp

    obtain ⟨hRebec, hDelay⟩ :=
      Translation.externalSendsFromIndex_knownRebec_of_path
        .constructor
        []
        0
        hPath
        hBodyMember
        hSendIndex

    refine ⟨?_, ?_⟩

    · rw [
        hSendRebec
      ]

      exact hRebec

    · rw [
        hSendDelay
      ]

      exact hDelay

  · -- Both initializers start at the top level, so both stacks are empty and the fourth
    -- conjunct is `True`. It is stated rather than skipped for the reason the other trivial
    -- conjuncts are: what is trivial initially is not trivial after a step.
    simp [
      DTR.GeneralModel.initialActorRuntime,
      LF.GeneralProgram.initialReactorRuntime,
      GeneralFramesCompile
    ]

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
      model
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
         hEnvOfClass,
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
        env,
        LF.GeneralProgram.initialReactorRuntime
          reactor
          (Translation.compileGeneralActorInstance
            instanceDecl),
        outputPortEnvOfActorName_eq
          (by
            rw [← hName]
            exact hClassOfActor)
          hEnvOfClass,
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
        model.classes
        hEnvOfClass
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
         hEnvOfClass,
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
        env,
        DTR.GeneralModel.initialActorRuntime
          reactiveClass
          instanceDecl,
        outputPortEnvOfActorName_eq
          (by
            rw [← hSourceName]
            exact hClassOfActor)
          hEnvOfClass,
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
        model.classes
        hEnvOfClass
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

**The three distinctness hypotheses are guard-relative; their public dischargers landed
2026-08-30, closing the gap F81 measured.** At this theorem's landing (measured 2026-08-26,
recorded as F81) nothing public concluded any of the three: the projection turning a decided
`LF.GeneralReactor.declaredNames` `Nodup` into the first hypothesis was `private`, and for the
action names and the message-server names there was no such projection anywhere in the
repository, only the conjunct of `DTR.GeneralModel.namesUniqueAndValid` that would supply the
third. The consumer F81 waited for — the resolution theorems at this file's end — has since
arrived, and with it the dischargers:
`Translation.compileGeneralReactiveClass_inputPortNames_nodup` and
`Translation.compileGeneralReactiveClass_actionNames_nodup` (per class, from the compiled
reactor's own well-formedness) and `DTR.GeneralModel.messageServerNames_nodup_of_wellFormed`,
composed at model level by `generalTriggerDistinctness_of_wellFormed` below. The hypotheses
keep their guard-relative spelling here — the theorem changes nothing about itself, and a
caller that holds the guard applies the discharger rather than this theorem assuming it.

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
passes at the source model's own lists. They stayed hypotheses from this theorem's landing
until 2026-08-30 because nothing public concluded them (F81): two are `LF.GeneralReactor.declaredNames`
`Nodup` clauses in disguise, the third a conjunct of `DTR.GeneralModel.namesUniqueAndValid`,
and the one projection that existed was `private` by a rule this repository keeps. The
dischargers have since landed — the two per-class `Translation` theorems and the model-level
`generalTriggerDistinctness_of_wellFormed` below — and the spelling is unchanged here:
guard-relative remains the house form, no well-formedness clause was added, and a consumer
holding the guard applies the discharger rather than this theorem assuming it.

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

/--
The three F81 distinctness premises hold of every reactor of an accepted translation — the
model-level composition F81 waited for.

F81 measured that the routing/resolution theorems hypothesize three `Nodup` facts at the source
model's own lists and that nothing public concluded any of them; the resolution theorems at
this section's head became the consumers, and the per-class dischargers have landed beside
their sources — `Translation.compileGeneralReactiveClass_inputPortNames_nodup` and
`Translation.compileGeneralReactiveClass_actionNames_nodup` from the compiled reactor's own
well-formedness, `DTR.GeneralModel.messageServerNames_nodup_of_wellFormed` from the model's.
This theorem composes the three with the program-level plumbing between them: the guard's
acceptance is the compiled program's well-formedness
(`Translation.guardGeneralProgram_wellFormed`), whose `reactorsWellFormed` clause gives each
reactor its own well-formedness, and `Translation.compileGeneralModel_startupBody` names the
class and routes behind any reactor of a successful translation. What a future `.consume`
consumer holds — a well-formed model, its compiled program, the guard's acceptance, and a
reactor of that program — is exactly the premise set, and the conclusion is the three premises
in the spelling the resolution theorems take.

Two scope notes. The model well-formedness premise needs the model's own well-formedness
module, which is why this file imports `Relico.DTR.GeneralWellFormed` — the one new import
edge of the discharge, with no cycle, since that module imports only `DTR.GeneralSyntax`. And
the theorem deliberately stops at the three premises: composing them further, into
`generalUniquelyTriggered_of_compiled` or a resolution theorem, is the eventual consumer's one
line, not a second packaging with no caller.

This changes nothing about the frozen questions: no scheduler, selection, or ordering
semantics is involved, and neither `.consume` transfer condition is any closer to being
stated — F86's placement decision still gates those.
-/
theorem generalTriggerDistinctness_of_wellFormed
    {model : DTR.GeneralModel}
    {program accepted : LF.GeneralProgram}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hGuard :
      Translation.guardGeneralProgram program =
        .ok accepted)
    {reactor : LF.GeneralReactor}
    (hReactor :
      reactor ∈ program.reactors) :
    ∃ (reactiveClass : DTR.GeneralReactiveClass)
      (routes : List Translation.GeneralRoute),
      reactiveClass ∈ model.classes ∧
        Translation.routesOf model =
          .ok routes ∧
          Translation.compileGeneralReactiveClass
              model.classes
              routes
              reactiveClass =
            .ok reactor ∧
          ((Translation.generalInputPortsOf
              reactiveClass.name
              routes).map
            (fun port =>
              port.name.value)).Nodup ∧
          ((Translation.generalActionNamesOf
              (Translation.selfSendsOfClass
                reactiveClass)
              reactiveClass.messageServers).map
            (fun name =>
              name.value)).Nodup ∧
          (reactiveClass.messageServers.map
            (fun server =>
              server.name)).Nodup := by
  have hProgramWellFormed :
      program.wellFormed =
        true :=
    Translation.guardGeneralProgram_wellFormed
      hGuard

  have hReactorsWellFormed :
      program.reactorsWellFormed =
        true := by
    revert hProgramWellFormed
    unfold LF.GeneralProgram.wellFormed
    cases program.reactorsWellFormed <;>
      simp

  have hReactorWellFormed :
      reactor.wellFormed =
        true :=
    List.all_eq_true.mp
      hReactorsWellFormed
      reactor
      hReactor

  obtain ⟨routes, hRoutes, hForEach⟩ :=
    Translation.compileGeneralModel_startupBody
      hCompiled

  obtain
      ⟨reactiveClass, _, _, hClass, hClassCompiled, -⟩ :=
    hForEach
      reactor
      hReactor

  refine
    ⟨reactiveClass,
      routes,
      hClass,
      hRoutes,
      hClassCompiled,
      ?_,
      ?_,
      ?_⟩

  · exact
      Translation.compileGeneralReactiveClass_inputPortNames_nodup
        hClassCompiled
        hReactorWellFormed

  · exact
      Translation.compileGeneralReactiveClass_actionNames_nodup
        hClassCompiled
        hReactorWellFormed

  · exact
      DTR.GeneralModel.messageServerNames_nodup_of_wellFormed
        hModelWellFormed
        hClass

end Correctness
end Relico
