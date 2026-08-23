import Relico.DTR.GeneralSyntax

/-!
# Stage F: the general priority sort

`docs/STAGE_F_DESIGN.md` §4.3. Stage F needs a stable priority sort at **two** element types —
`DTR.GeneralActorInstance` for level 1 (§III-D, ordering a message server's port reactions by the
sending actor's priority) and `DTR.GeneralMessageServer` for level 2 (ordering the per-server groups
by message-server priority). This module is that sort, once, generic in the element type and
parameterized on a priority projection, with the two instantiations at the end.

**Why generic rather than a third and fourth monomorphic copy.** The repository already has two
monomorphic copies of this algorithm, `Relico/DTR/MessageServerPriority.lean` and
`Relico/DTR/MultiStorePayloadPriority.lean`. Following that precedent here would put stage F's two
levels in two separate files, and §1.1 of the design argues that the two levels compose — that they
order disjoint pairs of reactions and therefore cannot disagree — **on the assumption that both use the
same convention for an absent priority**. Two copies could drift on exactly that point, and the drift
would be invisible: both would still compile and both would still be total preorders. Sharing one
definition makes the shared convention a type-checked fact instead of a comment.

**The convention is inherited, not chosen here.** `Relico/DTR/GeneralSyntax.lean:335-337` already
fixed it: *"An absent priority is a priority class in its own right and is ordered after every explicit
one."* That discharges the paper's P5 (priorities may be absent) and the tie half of P4 at the AST
level, so this module implements the convention rather than deciding it.

**Stability, and why it is not the obvious mechanism.** `insert` places the incoming element *before*
the first element of equal-or-lower priority, and the test is reflexive, so an equal-priority element
stops the scan. Taken alone that would put a later element ahead of an earlier one. Stability comes
from `normalize` traversing the source list **right to left**, so the element earlier in source is
inserted later and lands ahead of the equal-priority elements already placed. Both halves are load
bearing; a test made strict "for clarity" would silently reverse ties, and reversed ties would
contradict decision `0041`, which resolves equal LF microsteps by deferring to declaration order.
-/

namespace Relico
namespace DTR
namespace GeneralPriority

/-!
## The order on priority metadata

Stated on `Option Nat` rather than on the elements, so that the four order facts below are proved once
about priorities and inherited by both instantiations. This is the one structural departure from
`MessageServerPriority.lean`, which states the order directly on its element type and therefore cannot
share these facts with anything.
-/

/--
Priority `left` precedes or ties priority `right`.

Explicit priorities compare numerically, every explicit priority precedes an absent one, and two
absences tie. The relation is a total preorder, not a total order: ties are possible, and
`normalize` resolves them by source declaration order rather than arbitrarily.
-/
def PriorityPrecedesOrEqual
    (left right : Option Nat) :
    Prop :=
  match left, right with

  | some leftPriority,
    some rightPriority =>
      leftPriority ≤
        rightPriority

  | some _,
    none =>
      True

  | none,
    some _ =>
      False

  | none,
    none =>
      True

instance instDecidablePriorityPrecedesOrEqual
    (left right : Option Nat) :
    Decidable
      (PriorityPrecedesOrEqual
        left
        right) := by

  unfold PriorityPrecedesOrEqual

  cases left <;>
    cases right <;>
    infer_instance

theorem priorityPrecedesOrEqual_refl
    (priority : Option Nat) :
    PriorityPrecedesOrEqual
      priority
      priority := by

  cases priority <;>
    simp [
      PriorityPrecedesOrEqual
    ]

/--
Every explicit priority precedes an absent one. This is the AST's convention, restated as a theorem so
that a change to `PriorityPrecedesOrEqual` that broke it would fail here rather than silently reorder
generated reactions.
-/
theorem priority_explicit_precedes_unannotated
    (priority : Nat) :
    PriorityPrecedesOrEqual
      (some priority)
      none := by

  simp [
    PriorityPrecedesOrEqual
  ]

theorem priority_unannotated_not_precedes_explicit
    (priority : Nat) :
    ¬ PriorityPrecedesOrEqual
        none
        (some priority) := by

  simp [
    PriorityPrecedesOrEqual
  ]

theorem priority_lower_numeric_precedes
    {left right : Nat}
    (hOrder :
      left ≤ right) :
    PriorityPrecedesOrEqual
      (some left)
      (some right) := by

  simpa [
    PriorityPrecedesOrEqual
  ] using
    hOrder

/-!
### The order is a total preorder

`docs/STAGE_F_DESIGN.md` §6 rests on this, and so does the guard-relative shape of the ordering
theorems: without a distinctness hypothesis the order is a total preorder in which ties are possible,
and with one it is a strict total order. Both halves are proved here rather than asserted, because §6
declines to add a `wellFormed` clause on the strength of the second half and that argument should not
depend on an unproved claim.
-/

theorem priorityPrecedesOrEqual_trans
    {left middle right : Option Nat}
    (hLeft :
      PriorityPrecedesOrEqual
        left
        middle)
    (hRight :
      PriorityPrecedesOrEqual
        middle
        right) :
    PriorityPrecedesOrEqual
      left
      right := by

  cases left <;>
    cases middle <;>
    cases right <;>
    simp_all [
      PriorityPrecedesOrEqual
    ] <;>
    omega

theorem priorityPrecedesOrEqual_total
    (left right : Option Nat) :
    PriorityPrecedesOrEqual
        left
        right ∨
      PriorityPrecedesOrEqual
        right
        left := by

  cases left <;>
    cases right <;>
    simp [
      PriorityPrecedesOrEqual
    ] <;>
    omega

/--
Two priorities that precede each other are equal. Together with totality this is what turns the
preorder into a strict total order once priorities are known distinct, which is the step
`docs/STAGE_F_DESIGN.md` §6 needs and the step that makes `PrioritiesDistinct` the right hypothesis.
-/
theorem priorityPrecedesOrEqual_antisymm
    {left right : Option Nat}
    (hLeft :
      PriorityPrecedesOrEqual
        left
        right)
    (hRight :
      PriorityPrecedesOrEqual
        right
        left) :
    left = right := by

  cases left <;>
    cases right <;>
    simp_all [
      PriorityPrecedesOrEqual
    ] <;>
    omega

/-!
## The sort

From here the shape follows `Relico/DTR/MessageServerPriority.lean` declaration for declaration, with a
priority projection threaded through. The proof scripts are deliberately the blueprint's, because those
are known green and divergence here buys nothing.
-/

/--
Element `left` precedes or ties element `right` under the projection `priorityOf`.
-/
def PrecedesOrEqual
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (left right : α) :
    Prop :=
  PriorityPrecedesOrEqual
    (priorityOf left)
    (priorityOf right)

instance instDecidablePrecedesOrEqual
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (left right : α) :
    Decidable
      (PrecedesOrEqual
        priorityOf
        left
        right) := by

  unfold PrecedesOrEqual

  infer_instance

theorem precedesOrEqual_refl
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (element : α) :
    PrecedesOrEqual
      priorityOf
      element
      element :=
  priorityPrecedesOrEqual_refl
    (priorityOf element)

/--
Insert one element into an already priority-normalized list.

Insertion occurs before the first element of equal or lower priority. Because `normalize` processes the
original list from right to left, this preserves source declaration order among equal-priority
elements. Both halves matter; see this module's header.
-/
def insert
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (element : α) :
    List α →
    List α

  | [] =>
      [element]

  | current :: remaining =>
      if
        PrecedesOrEqual
          priorityOf
          element
          current
      then
        element ::
          current ::
          remaining
      else
        current ::
          insert
            priorityOf
            element
            remaining

/--
Stable priority normalization of a declaration list.

The input list remains the source declaration order. This function produces the emitted order.
-/
def normalize
    {α : Type}
    (priorityOf :
      α → Option Nat) :
    List α →
    List α

  | [] =>
      []

  | element :: remaining =>
      insert
        priorityOf
        element
        (normalize
          priorityOf
          remaining)

@[simp]
theorem mem_insert_iff
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (candidate element : α)
    (elements : List α) :
    candidate ∈
        insert
          priorityOf
          element
          elements ↔
      candidate = element ∨
        candidate ∈ elements := by

  induction elements with

  | nil =>
      simp [
        insert
      ]

  | cons current remaining inductionHypothesis =>
      by_cases hOrder :
          PrecedesOrEqual
            priorityOf
            element
            current

      · simp [
          insert,
          hOrder
        ]

      · simp [
          insert,
          hOrder,
          inductionHypothesis,
          or_left_comm
        ]

@[simp]
theorem length_insert
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (element : α)
    (elements : List α) :
    (insert
      priorityOf
      element
      elements).length =
      elements.length + 1 := by

  induction elements with

  | nil =>
      simp [
        insert
      ]

  | cons current remaining inductionHypothesis =>
      by_cases hOrder :
          PrecedesOrEqual
            priorityOf
            element
            current

      · simp [
          insert,
          hOrder
        ]

      · simp [
          insert,
          hOrder,
          inductionHypothesis
        ]

@[simp]
theorem normalize_nil
    {α : Type}
    (priorityOf :
      α → Option Nat) :
    normalize
        priorityOf
        ([] : List α) =
      [] := by

  rfl

@[simp]
theorem normalize_singleton
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (element : α) :
    normalize
        priorityOf
        [element] =
      [element] := by

  rfl

@[simp]
theorem mem_normalize_iff
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (candidate : α)
    (elements : List α) :
    candidate ∈
        normalize
          priorityOf
          elements ↔
      candidate ∈ elements := by

  induction elements with

  | nil =>
      simp [
        normalize
      ]

  | cons element remaining inductionHypothesis =>
      simp [
        normalize,
        mem_insert_iff,
        inductionHypothesis
      ]

@[simp]
theorem length_normalize
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (elements : List α) :
    (normalize
      priorityOf
      elements).length =
      elements.length := by

  induction elements with

  | nil =>
      simp [
        normalize
      ]

  | cons element remaining inductionHypothesis =>
      simp [
        normalize,
        length_insert,
        inductionHypothesis
      ]

/--
Insertion permutes the list it is given onto the front of the original list.
-/
theorem insert_perm
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (element : α)
    (elements : List α) :
    List.Perm
      (insert
        priorityOf
        element
        elements)
      (element :: elements) := by

  induction elements with

  | nil =>
      simp [
        insert
      ]

  | cons current remaining inductionHypothesis =>
      by_cases hOrder :
          PrecedesOrEqual
            priorityOf
            element
            current

      · simp [
          insert,
          hOrder
        ]

      · simpa [
          insert,
          hOrder
        ] using
          (List.Perm.cons
              current
              inductionHypothesis).trans
            (List.Perm.swap
              element
              current
              remaining)

/--
Priority normalization is a permutation of the source declaration list.

This is the lemma `docs/STAGE_F_DESIGN.md` §7.3 leans on: because the sort only permutes, every
property of the route or reaction *set* rather than its order transfers through it, which is what keeps
#47's site totality, #58's endpoint uniqueness and #60's setPort `Nodup` from needing re-proof.
-/
theorem normalize_perm
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (elements : List α) :
    List.Perm
      (normalize
        priorityOf
        elements)
      elements := by

  induction elements with

  | nil =>
      exact
        List.Perm.nil

  | cons element remaining inductionHypothesis =>
      exact
        (insert_perm
            priorityOf
            element
            (normalize
              priorityOf
              remaining)).trans
          (List.Perm.cons
            element
            inductionHypothesis)

/--
Stable priority normalization preserves uniqueness after mapping each element through an arbitrary
projection.
-/
theorem map_normalize_nodup
    {α β : Type}
    (priorityOf :
      α → Option Nat)
    (function :
      α → β)
    {elements : List α}
    (hNodup :
      (elements.map
        function).Nodup) :
    ((normalize
      priorityOf
      elements).map
        function).Nodup :=
  ((normalize_perm
    priorityOf
    elements).map
      function).nodup_iff.mpr
    hNodup

/--
Two elements that precede each other carry the same priority.

This is the form `docs/STAGE_F_DESIGN.md` §6's guard-relative theorems consume: combined with a
distinctness hypothesis it rules out ties, which is exactly the step that upgrades the total preorder
to a strict total order.
-/
theorem precedesOrEqual_antisymm_priority
    {α : Type}
    {priorityOf :
      α → Option Nat}
    {left right : α}
    (hLeft :
      PrecedesOrEqual
        priorityOf
        left
        right)
    (hRight :
      PrecedesOrEqual
        priorityOf
        right
        left) :
    priorityOf left =
      priorityOf right :=
  priorityPrecedesOrEqual_antisymm
    hLeft
    hRight

/--
The distinctness guard survives the sort.

`docs/STAGE_F_DESIGN.md` §6 states the strict ordering theorems with `PrioritiesDistinct` as a
hypothesis about the **source** model, while the list actually emitted is the sorted one. This lemma is
the bridge, and without it the guard would have to be assumed twice. It is stated on the raw `Nodup` so
that this module keeps `Relico.DTR.GeneralSyntax` as its only import, mirroring
`MessageServerPriority.lean`; `Relico/Correctness/GeneralPriorityOrder.lean` connects it to the named
predicates in `Relico/DTR/GeneralWellFormed.lean`.
-/
theorem priorities_nodup_normalize
    {α : Type}
    (priorityOf :
      α → Option Nat)
    {elements : List α}
    (hNodup :
      (elements.map
        priorityOf).Nodup) :
    ((normalize
      priorityOf
      elements).map
        priorityOf).Nodup :=
  map_normalize_nodup
    priorityOf
    priorityOf
    hNodup

/-!
## Sortedness — the step no priority sort in this repository had proved

Everything above this point is a *structural* fact about `normalize`: it permutes, and it therefore
preserves membership, length and uniqueness. None of it says the output is in priority order.

That gap is not local to this module. Measured across all 144 files of `Relico/`, there is no
occurrence of `List.Sorted`, `List.Pairwise` or `Chain'` anywhere, and the two pre-existing sorts
(`Relico/DTR/MessageServerPriority.lean`, `Relico/DTR/MultiStorePayloadPriority.lean`) prove exactly
the structural list — `mem`, `length`, `perm`, `nodup` — and nothing about output order.
`Relico/Correctness/PriorityOrder.lean` does not close it either, and cannot: its headline iff is
stated against `DTR.PriorityServerNamePrecedesOrEqual`, which
`Relico/DTR/MultiStorePriorityScheduling.lean:64` *defines* as a name scan over
`MessageServerPriority.normalize`'s **own output**. So that theorem proves emitted reaction order
equals normalized declaration order — order preservation through compilation, which is real and is the
harder half — but it is silent on whether normalized order is priority order. When that was measured on
2026-08-23 the only thing pinning any sort's behaviour anywhere in this repository was one `rfl`
regression at a single four-element input, `Relico/Tests/MessageServerPriority.lean:104`. This commit is
what changes that: `Relico/Tests/GeneralPriority.lean` lands beside it, pinning both instantiations
below, and the sentence is dated rather than deleted because the measurement is what motivated the
lemmas that follow.

`docs/STAGE_F_DESIGN.md` §6 requires two statements at each level: an **unconditional** one, that
emitted order equals sorted order, and a **guard-relative** one, that emitted order *realizes priority
strictly* under a distinctness hypothesis. The second cannot be stated at all without the lemmas below,
so they are stage F's foundation rather than an optional extra.

`Sorted` is defined here rather than reused from core deliberately. This development has zero
dependencies, and an unfamiliar core lemma name is avoidable risk when the whole proof needs only
`priorityPrecedesOrEqual_trans` and `priorityPrecedesOrEqual_total`, both already proved above.
-/

/--
Every element precedes or ties every element that follows it.

Stated by recursion on the list rather than as a pairwise predicate over indices, because the two
consumers below both destructure an `earlier ++ later` split and that is the shape this form supports
directly.
-/
def Sorted
    {α : Type}
    (priorityOf :
      α → Option Nat) :
    List α →
    Prop

  | [] =>
      True

  | element :: remaining =>
      (∀ later,
        later ∈ remaining →
        PrecedesOrEqual
          priorityOf
          element
          later) ∧
      Sorted
        priorityOf
        remaining

/--
Insertion into a sorted list yields a sorted list.

This is the load-bearing step, and it is where totality earns its place: in the branch where the
incoming element does **not** precede the head, sortedness of the result needs the head to precede the
incoming element, which is exactly `priorityPrecedesOrEqual_total` applied to the negated test.
-/
theorem insert_sorted
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (element : α)
    (elements : List α) :
    Sorted
        priorityOf
        elements →
      Sorted
        priorityOf
        (insert
          priorityOf
          element
          elements) := by

  induction elements with

  | nil =>
      intro _

      simp [
        insert,
        Sorted
      ]

  | cons current remaining inductionHypothesis =>
      intro hSorted

      have hHead :
          ∀ later,
            later ∈ remaining →
            PrecedesOrEqual
              priorityOf
              current
              later :=
        hSorted.left

      have hTail :
          Sorted
            priorityOf
            remaining :=
        hSorted.right

      by_cases hOrder :
          PrecedesOrEqual
            priorityOf
            element
            current

      · have hInsert :
            insert
                priorityOf
                element
                (current :: remaining) =
              element ::
                current ::
                remaining := by

          simp [
            insert,
            hOrder
          ]

        rw [hInsert]

        refine
          ⟨?_,
            hSorted⟩

        intro later hLater

        rcases
          List.mem_cons.mp
            hLater with
          hEqual | hMember

        · subst hEqual

          exact hOrder

        · exact
            priorityPrecedesOrEqual_trans
              hOrder
              (hHead
                later
                hMember)

      · have hInsert :
            insert
                priorityOf
                element
                (current :: remaining) =
              current ::
                insert
                  priorityOf
                  element
                  remaining := by

          simp [
            insert,
            hOrder
          ]

        rw [hInsert]

        have hCurrentPrecedes :
            PrecedesOrEqual
              priorityOf
              current
              element := by

          rcases
            priorityPrecedesOrEqual_total
              (priorityOf element)
              (priorityOf current) with
            hLeft | hRight

          · exact
              absurd
                hLeft
                hOrder

          · exact hRight

        refine
          ⟨?_,
            inductionHypothesis
              hTail⟩

        intro later hLater

        rcases
          (mem_insert_iff
            priorityOf
            later
            element
            remaining).mp
            hLater with
          hEqual | hMember

        · subst hEqual

          exact hCurrentPrecedes

        · exact
            hHead
              later
              hMember

/--
Stable priority normalization produces a sorted list.

With `insert_sorted` in hand this is a one-line induction, and it is the theorem that makes the phrase
"the sort sorts" mean something in this development for the first time.
-/
theorem normalize_sorted
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (elements : List α) :
    Sorted
      priorityOf
      (normalize
        priorityOf
        elements) := by

  induction elements with

  | nil =>
      trivial

  | cons element remaining inductionHypothesis =>
      exact
        insert_sorted
          priorityOf
          element
          (normalize
            priorityOf
            remaining)
          inductionHypothesis

/-!
### From sortedness to the append split

`docs/STAGE_F_DESIGN.md` §9.2 states stage F's ordering results as append splits rather than as name
orders, for the reason given there: the blueprint's key — a message-server name identifying one
reaction — does not exist in the general family, where one instance contributes a whole block of port
reactions. So the two lemmas below are the ones the translation theorems actually consume, and both are
phrased over `earlier ++ later` to meet `assembleGeneralPortReactions_instanceDeclarationOrder` in the
shape it already has.
-/

/--
In a sorted list split as `earlier ++ later`, every element of `earlier` precedes or ties every element
of `later`.
-/
theorem sorted_append_precedes
    {α : Type}
    (priorityOf :
      α → Option Nat)
    (earlier later : List α) :
    Sorted
        priorityOf
        (earlier ++ later) →
      ∀ earlierElement,
        earlierElement ∈ earlier →
        ∀ laterElement,
          laterElement ∈ later →
          PrecedesOrEqual
            priorityOf
            earlierElement
            laterElement := by

  induction earlier with

  | nil =>
      intro _ earlierElement hEarlier

      simp at hEarlier

  | cons current remaining inductionHypothesis =>
      intro hSorted earlierElement hEarlier laterElement hLater

      have hHead :
          ∀ element,
            element ∈ remaining ++ later →
            PrecedesOrEqual
              priorityOf
              current
              element :=
        hSorted.left

      have hTail :
          Sorted
            priorityOf
            (remaining ++ later) :=
        hSorted.right

      rcases
        List.mem_cons.mp
          hEarlier with
        hEqual | hMember

      · subst hEqual

        exact
          hHead
            laterElement
            (by
              simp [
                hLater
              ])

      · exact
          inductionHypothesis
            hTail
            earlierElement
            hMember
            laterElement
            hLater

/--
Across an `append` whose concatenation is duplicate free, an element drawn from the left is distinct
from an element drawn from the right.

Proved from first principles rather than assembled from a `nodup_append` characterisation, so that the
only core facts relied on are `List.cons_append`, `List.nodup_cons` and `List.mem_cons`. The guard
relative ordering theorem needs exactly this and nothing stronger.
-/
theorem nodup_append_ne
    {β : Type}
    (earlier later : List β) :
    (earlier ++ later).Nodup →
      ∀ earlierElement,
        earlierElement ∈ earlier →
        ∀ laterElement,
          laterElement ∈ later →
          earlierElement ≠ laterElement := by

  induction earlier with

  | nil =>
      intro _ earlierElement hEarlier

      simp at hEarlier

  | cons current remaining inductionHypothesis =>
      intro hNodup earlierElement hEarlier laterElement hLater

      simp only [
        List.cons_append,
        List.nodup_cons
      ] at hNodup

      obtain ⟨hNotMember, hRest⟩ := hNodup

      rcases
        List.mem_cons.mp
          hEarlier with
        hEqual | hMember

      · subst hEqual

        intro hSame

        exact
          hNotMember
            (by
              simp [
                hSame,
                hLater
              ])

      · exact
          inductionHypothesis
            hRest
            earlierElement
            hMember
            laterElement
            hLater

/--
The unconditional ordering result: however the normalized list is split, the left part precedes or ties
the right part.

No guard. True of every model the pipeline accepts, which is what `docs/STAGE_F_DESIGN.md` §6 means by
the unconditional half of each level.
-/
theorem normalize_append_precedes
    {α : Type}
    (priorityOf :
      α → Option Nat)
    {elements earlier later : List α}
    (hSplit :
      normalize
          priorityOf
          elements =
        earlier ++ later) :
    ∀ earlierElement,
      earlierElement ∈ earlier →
      ∀ laterElement,
        laterElement ∈ later →
        PrecedesOrEqual
          priorityOf
          earlierElement
          laterElement := by

  have hSorted :
      Sorted
        priorityOf
        (earlier ++ later) := by

    rw [← hSplit]

    exact
      normalize_sorted
        priorityOf
        elements

  exact
    sorted_append_precedes
      priorityOf
      earlier
      later
      hSorted

/--
The guard-relative ordering result: with source priorities distinct, the precedence across the split is
strict, in the sense that the two priorities cannot coincide.

`docs/STAGE_F_DESIGN.md` §6 settles that distinctness is a **hypothesis** and not a `wellFormed`
clause, because `PrioritiesDistinct` is `(map priority).Nodup` over `List (Option Nat)` and so forbids
two *absent* priorities, which would reject `expressions.rebeca` and `control-flow.rebeca` outright.
This is the statement that decision buys: strictness where it is asked for, and the unconditional form
above everywhere else.

Stated on the raw `Nodup` of the mapped source list so that this module keeps
`Relico.DTR.GeneralSyntax` as its only import; `Relico/Correctness/GeneralPriorityOrder.lean` connects
it to the named predicates in `Relico/DTR/GeneralWellFormed.lean`.
-/
theorem normalize_append_strict
    {α : Type}
    (priorityOf :
      α → Option Nat)
    {elements earlier later : List α}
    (hSplit :
      normalize
          priorityOf
          elements =
        earlier ++ later)
    (hNodup :
      (elements.map
        priorityOf).Nodup) :
    ∀ earlierElement,
      earlierElement ∈ earlier →
      ∀ laterElement,
        laterElement ∈ later →
        PrecedesOrEqual
            priorityOf
            earlierElement
            laterElement ∧
          priorityOf earlierElement ≠
            priorityOf laterElement := by

  have hNodupSplit :
      (earlier.map priorityOf ++
        later.map priorityOf).Nodup := by

    have hNodupNormalized :
        ((normalize
          priorityOf
          elements).map
            priorityOf).Nodup :=
      priorities_nodup_normalize
        priorityOf
        hNodup

    rw [
      hSplit,
      List.map_append
    ] at hNodupNormalized

    exact hNodupNormalized

  intro earlierElement hEarlier laterElement hLater

  refine
    ⟨normalize_append_precedes
      priorityOf
      hSplit
      earlierElement
      hEarlier
      laterElement
      hLater,
      ?_⟩

  have hEarlierMapped :
      priorityOf earlierElement ∈
        earlier.map priorityOf := by

    simp only [
      List.mem_map
    ]

    exact
      ⟨earlierElement,
        hEarlier,
        rfl⟩

  have hLaterMapped :
      priorityOf laterElement ∈
        later.map priorityOf := by

    simp only [
      List.mem_map
    ]

    exact
      ⟨laterElement,
        hLater,
        rfl⟩

  exact
    nodup_append_ne
      (earlier.map priorityOf)
      (later.map priorityOf)
      hNodupSplit
      (priorityOf earlierElement)
      hEarlierMapped
      (priorityOf laterElement)
      hLaterMapped

end GeneralPriority

/-!
## Level 2: message servers, ordered by message-server priority

`docs/STAGE_F_DESIGN.md` §9. Orders the per-server groups of one reactive class. The walk site this
replaces is `reactiveClass.messageServers` at `Relico/Translation/GeneralBasic.lean:1927`.
-/

namespace GeneralMessageServerPriority

/--
The priority projection for message servers, named so that both instantiations read the same way at
their use sites.
-/
def priorityOf
    (messageServer :
      DTR.GeneralMessageServer) :
    Option Nat :=
  messageServer.priority

/--
Stable message-server priority normalization.
-/
def normalize
    (messageServers :
      List DTR.GeneralMessageServer) :
    List DTR.GeneralMessageServer :=
  GeneralPriority.normalize
    priorityOf
    messageServers

theorem normalize_perm
    (messageServers :
      List DTR.GeneralMessageServer) :
    List.Perm
      (normalize
        messageServers)
      messageServers :=
  GeneralPriority.normalize_perm
    priorityOf
    messageServers

@[simp]
theorem mem_normalize_iff
    (candidate :
      DTR.GeneralMessageServer)
    (messageServers :
      List DTR.GeneralMessageServer) :
    candidate ∈
        normalize
          messageServers ↔
      candidate ∈ messageServers :=
  GeneralPriority.mem_normalize_iff
    priorityOf
    candidate
    messageServers

@[simp]
theorem length_normalize
    (messageServers :
      List DTR.GeneralMessageServer) :
    (normalize
      messageServers).length =
      messageServers.length :=
  GeneralPriority.length_normalize
    priorityOf
    messageServers

/--
Message-server priority normalization produces a sorted server list.

Level 2's append-split consumers are the two theorems below, and they arrived with task #87 as this
docstring previously said they would. Sortedness is still stated separately from them, so that both
instantiations expose the same guarantee and neither level can drift into relying on an unproved sort.
-/
theorem normalize_sorted
    (messageServers :
      List DTR.GeneralMessageServer) :
    GeneralPriority.Sorted
      priorityOf
      (normalize
        messageServers) :=
  GeneralPriority.normalize_sorted
    priorityOf
    messageServers

/--
The unconditional level-2 ordering result, in the append-split shape
`compileGeneralMessageServerReactions_append` already consumes.

Ties are possible and are resolved by source declaration order, which is `normalize`'s stability and
what decision `0041` requires. At this element type a tie is the ordinary case rather than the corner
one: an unannotated message server is permitted, so any class with two unannotated servers ties them,
and `docs/STAGE_F_DESIGN.md` §6 records that this is exactly why the guard below cannot be a
`wellFormed` clause.
-/
theorem normalize_append_precedes
    {messageServers earlier later :
      List DTR.GeneralMessageServer}
    (hSplit :
      normalize
          messageServers =
        earlier ++ later) :
    ∀ earlierServer,
      earlierServer ∈ earlier →
      ∀ laterServer,
        laterServer ∈ later →
        GeneralPriority.PrecedesOrEqual
          priorityOf
          earlierServer
          laterServer :=
  GeneralPriority.normalize_append_precedes
    priorityOf
    hSplit

/--
The guard-relative level-2 ordering result, with message-server priorities distinct.

The `Nodup` premise is the unfolded form of `GeneralMessageServers.PrioritiesDistinct`, and that
predicate is **per class** where level 1's is model-wide: `GeneralModel.MessageServerPrioritiesDistinct`
quantifies over `model.classes`, because two classes may both annotate a server `1` without conflict.
So the bridge in `Relico/Correctness/GeneralPriorityOrder.lean` has to apply class membership before it
can apply this theorem, which is the one step level 1's bridge does not need and the only structural
difference between the two instantiations.
-/
theorem normalize_append_strict
    {messageServers earlier later :
      List DTR.GeneralMessageServer}
    (hSplit :
      normalize
          messageServers =
        earlier ++ later)
    (hNodup :
      (messageServers.map
        priorityOf).Nodup) :
    ∀ earlierServer,
      earlierServer ∈ earlier →
      ∀ laterServer,
        laterServer ∈ later →
        GeneralPriority.PrecedesOrEqual
            priorityOf
            earlierServer
            laterServer ∧
          priorityOf earlierServer ≠
            priorityOf laterServer :=
  GeneralPriority.normalize_append_strict
    priorityOf
    hSplit
    hNodup

end GeneralMessageServerPriority

/-!
## Level 1: actor instances, ordered by actor priority

`docs/STAGE_F_DESIGN.md` §4.1 and §7.2. Orders one message server's port reactions by the sending
actor's priority, by ordering the instance list the routes are derived from.

This is the **first consumer of `DTR.GeneralActorInstance.priority` in the translation**. Before stage F
the field was read in exactly one place in the repository, `Relico/DTR/GeneralWellFormed.lean:490`,
inside a predicate that nothing enforced.
-/

namespace GeneralActorPriority

/--
The priority projection for actor instances. The binder is `actor` rather than `instance`, which is a
Lean keyword, matching the spelling `Relico/DTR/GeneralWellFormed.lean:490` already uses.
-/
def priorityOf
    (actor :
      DTR.GeneralActorInstance) :
    Option Nat :=
  actor.priority

/--
Stable actor priority normalization.
-/
def normalize
    (instances :
      List DTR.GeneralActorInstance) :
    List DTR.GeneralActorInstance :=
  GeneralPriority.normalize
    priorityOf
    instances

theorem normalize_perm
    (instances :
      List DTR.GeneralActorInstance) :
    List.Perm
      (normalize
        instances)
      instances :=
  GeneralPriority.normalize_perm
    priorityOf
    instances

@[simp]
theorem mem_normalize_iff
    (candidate :
      DTR.GeneralActorInstance)
    (instances :
      List DTR.GeneralActorInstance) :
    candidate ∈
        normalize
          instances ↔
      candidate ∈ instances :=
  GeneralPriority.mem_normalize_iff
    priorityOf
    candidate
    instances

@[simp]
theorem length_normalize
    (instances :
      List DTR.GeneralActorInstance) :
    (normalize
      instances).length =
      instances.length :=
  GeneralPriority.length_normalize
    priorityOf
    instances

/--
Instance names survive the sort, which is what lets every name-based route and port theorem transfer
by permutation rather than re-proof.
-/
theorem names_perm
    (instances :
      List DTR.GeneralActorInstance) :
    List.Perm
      ((normalize
        instances).map
          (fun actor =>
            actor.name))
      (instances.map
        (fun actor =>
          actor.name)) :=
  (normalize_perm
    instances).map
      (fun actor =>
        actor.name)

/--
Actor priority normalization produces a sorted instance list.
-/
theorem normalize_sorted
    (instances :
      List DTR.GeneralActorInstance) :
    GeneralPriority.Sorted
      priorityOf
      (normalize
        instances) :=
  GeneralPriority.normalize_sorted
    priorityOf
    instances

/--
The unconditional level-1 ordering result, in the append-split shape
`assembleGeneralPortReactions_instanceDeclarationOrder` already consumes.
-/
theorem normalize_append_precedes
    {instances earlier later :
      List DTR.GeneralActorInstance}
    (hSplit :
      normalize
          instances =
        earlier ++ later) :
    ∀ earlierInstance,
      earlierInstance ∈ earlier →
      ∀ laterInstance,
        laterInstance ∈ later →
        GeneralPriority.PrecedesOrEqual
          priorityOf
          earlierInstance
          laterInstance :=
  GeneralPriority.normalize_append_precedes
    priorityOf
    hSplit

/--
The guard-relative level-1 ordering result, with actor priorities distinct.

The `Nodup` premise is the unfolded form of `GeneralActorInstances.PrioritiesDistinct`;
`Relico/Correctness/GeneralPriorityOrder.lean` supplies the named predicate.
-/
theorem normalize_append_strict
    {instances earlier later :
      List DTR.GeneralActorInstance}
    (hSplit :
      normalize
          instances =
        earlier ++ later)
    (hNodup :
      (instances.map
        priorityOf).Nodup) :
    ∀ earlierInstance,
      earlierInstance ∈ earlier →
      ∀ laterInstance,
        laterInstance ∈ later →
        GeneralPriority.PrecedesOrEqual
            priorityOf
            earlierInstance
            laterInstance ∧
          priorityOf earlierInstance ≠
            priorityOf laterInstance :=
  GeneralPriority.normalize_append_strict
    priorityOf
    hSplit
    hNodup

end GeneralActorPriority

end DTR
end Relico
