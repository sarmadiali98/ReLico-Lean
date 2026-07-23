import Relico.Basic

set_option autoImplicit false

universe u

namespace Relico
namespace Occurrence

/--
`RemovesOne selected before after` means that `after` is obtained by
removing one concrete occurrence of `selected` from `before`.

Unlike set membership, this relation preserves duplicate occurrences.
-/
inductive RemovesOne
    {α : Type u}
    (selected : α) :
    List α →
    List α →
    Prop where

  | head
      (remaining : List α) :
      RemovesOne
        selected
        (selected :: remaining)
        remaining

  | tail
      (headValue : α)
      {before after : List α}
      (hRemove :
        RemovesOne
          selected
          before
          after) :
      RemovesOne
        selected
        (headValue :: before)
        (headValue :: after)

/--
The selected occurrence was present in the original list.
-/
theorem RemovesOne.selected_mem
    {α : Type u}
    {selected : α}
    {before after : List α}
    (hRemove :
      RemovesOne selected before after) :
    selected ∈ before := by
  induction hRemove with

  | head remaining =>
      simp

  | tail headValue hRemove inductionHypothesis =>
      simp [inductionHypothesis]

end Occurrence
end Relico
