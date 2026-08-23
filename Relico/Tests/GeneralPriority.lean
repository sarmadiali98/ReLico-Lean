import Relico.DTR.GeneralPriority

set_option autoImplicit false

/-!
# Value-level pins for the general priority sorts

`docs/STAGE_F_DESIGN.md` §10. This is the first test module for the general family: `Relico/Tests/`
held 172 files and none of them mentioned a general-family declaration, so before this file nothing
pinned `GeneralActorPriority.normalize` or `GeneralMessageServerPriority.normalize` at any input.

## Why a regression is still needed once sortedness is proved

`Relico/DTR/GeneralPriority.lean` proves `normalize_sorted`, so it is fair to ask what a fixture adds.
Two things, both of which sortedness is structurally unable to see.

First, **`Sorted` cannot see tie order.** `Sorted` is stated against `PrecedesOrEqual`, which is
reflexive on equal priorities, so for two elements of equal priority *both* orders are sorted. A
`normalize` that reversed ties would satisfy `normalize_sorted` and `normalize_perm` together and still
contradict decision `0041`, which requires ties to fall back on source declaration order. Only a value
pin catches that, which is why `general_actor_priority_tie_stability` swaps the two tied inputs.

Second, **`Sorted` cannot see the direction of the unannotated convention.** Sortedness is proved
relative to `PriorityPrecedesOrEqual`; if that relation placed absent priorities *first*, the sort would
place them first, and `normalize_sorted` would prove the result sorted just the same. The convention
itself is pinned by `priority_explicit_precedes_unannotated` at the relation level and by the expected
list below at the value level.

So the two obligations are complementary: `normalize_sorted` pins the *algorithm* against the relation,
and this module pins the *relation's conventions and the tie-breaking* against concrete output. The
restricted family has only the second kind — `Relico/Tests/MessageServerPriority.lean:104` was, when
measured, the only pin on any priority sort's behaviour anywhere in the repository.
-/

namespace Relico
namespace Tests

/-!
## Actor-instance fixtures

Four instances of one class differing only in name and priority, so that the expected output below is
readable as an ordering claim rather than as a claim about anything else. `bindings` and `arguments` are
empty because neither participates in the sort; `priority` is omitted on the unannotated fixtures so
that the structure default is exercised rather than restated.
-/

def generalPriorityClassName :
    ClassName :=
  ⟨"GeneralPrioritySubject"⟩

def generalActorHigh :
    DTR.GeneralActorInstance where

  name :=
    ⟨"generalActorHigh"⟩

  className :=
    generalPriorityClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    some 1

def generalActorHighTie :
    DTR.GeneralActorInstance where

  name :=
    ⟨"generalActorHighTie"⟩

  className :=
    generalPriorityClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    some 1

def generalActorLow :
    DTR.GeneralActorInstance where

  name :=
    ⟨"generalActorLow"⟩

  className :=
    generalPriorityClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    some 4

def generalActorNone :
    DTR.GeneralActorInstance where

  name :=
    ⟨"generalActorNone"⟩

  className :=
    generalPriorityClassName

  bindings :=
    []

  arguments :=
    []

def generalActorNoneSecond :
    DTR.GeneralActorInstance where

  name :=
    ⟨"generalActorNoneSecond"⟩

  className :=
    generalPriorityClassName

  bindings :=
    []

  arguments :=
    []

/-!
## The relation, at the fixture level

Both facts are already theorems about `Option Nat`. Restating them on instances checks the one step
those theorems do not take: that `GeneralActorPriority.priorityOf` is the projection the sort is
actually keyed on. A rename of the `priority` field that missed the projection would fail here.
-/

/--
Smaller numeric priorities precede larger numeric priorities.
-/
theorem general_actor_lower_numeric_precedes :
    DTR.GeneralPriority.PrecedesOrEqual
      DTR.GeneralActorPriority.priorityOf
      generalActorHigh
      generalActorLow := by

  show
    DTR.GeneralPriority.PriorityPrecedesOrEqual
      (some 1)
      (some 4)

  exact
    DTR.GeneralPriority.priority_lower_numeric_precedes
      (by decide)

/--
Explicitly prioritized instances precede unannotated instances.
-/
theorem general_actor_explicit_precedes_unannotated :
    DTR.GeneralPriority.PrecedesOrEqual
      DTR.GeneralActorPriority.priorityOf
      generalActorLow
      generalActorNone := by

  show
    DTR.GeneralPriority.PriorityPrecedesOrEqual
      (some 4)
      none

  exact
    DTR.GeneralPriority.priority_explicit_precedes_unannotated
      4

/-!
## Normalization, at concrete inputs
-/

/--
Actor normalization follows numeric priority, places unannotated instances last, and preserves
declaration order for equal numeric priorities.

The input is deliberately in none of those orders: `generalActorLow` leads, the unannotated instance sits
second, and the two tied instances trail.
-/
theorem general_actor_priority_normalization_regression :
    DTR.GeneralActorPriority.normalize [
      generalActorLow,
      generalActorNone,
      generalActorHigh,
      generalActorHighTie
    ] = [
      generalActorHigh,
      generalActorHighTie,
      generalActorLow,
      generalActorNone
    ] := by
  rfl

/--
Ties fall back on source declaration order, in whichever order they were declared.

This is the pin `normalize_sorted` cannot supply: `PrecedesOrEqual` is reflexive on equal priorities, so
both orders of a tie are `Sorted`, and only a value pin distinguishes them. Swapping the two tied
instances swaps the output, which is decision `0041`.
-/
theorem general_actor_priority_tie_stability :
    DTR.GeneralActorPriority.normalize [
      generalActorHighTie,
      generalActorHigh
    ] = [
      generalActorHighTie,
      generalActorHigh
    ] := by
  rfl

/--
A model in which no instance carries a priority is left exactly as declared.

This is `P23`'s property at the value level: the corpus contains models with no priority annotation
anywhere, and stage F must not reorder them.
-/
theorem general_actor_unannotated_order_regression :
    DTR.GeneralActorPriority.normalize [
      generalActorNone,
      generalActorNoneSecond
    ] = [
      generalActorNone,
      generalActorNoneSecond
    ] := by
  rfl

/--
Normalization preserves declaration count.
-/
theorem general_actor_priority_normalization_preserves_length :
    (DTR.GeneralActorPriority.normalize [
      generalActorLow,
      generalActorNone,
      generalActorHigh,
      generalActorHighTie
    ]).length =
      4 := by
  rfl

/-!
## Message-server fixtures

Level 2's sort is the same development at a different element type, and it is pinned here rather than
with task #87 so that neither level can land with an unpinned sort. `parameters` and `body` are empty for
the same reason `bindings` and `arguments` were.
-/

def generalServerHigh :
    DTR.GeneralMessageServer where

  name :=
    ⟨"generalServerHigh"⟩

  parameters :=
    []

  body :=
    []

  priority :=
    some 1

def generalServerHighTie :
    DTR.GeneralMessageServer where

  name :=
    ⟨"generalServerHighTie"⟩

  parameters :=
    []

  body :=
    []

  priority :=
    some 1

def generalServerLow :
    DTR.GeneralMessageServer where

  name :=
    ⟨"generalServerLow"⟩

  parameters :=
    []

  body :=
    []

  priority :=
    some 4

def generalServerNone :
    DTR.GeneralMessageServer where

  name :=
    ⟨"generalServerNone"⟩

  parameters :=
    []

  body :=
    []

def generalServerNoneSecond :
    DTR.GeneralMessageServer where

  name :=
    ⟨"generalServerNoneSecond"⟩

  parameters :=
    []

  body :=
    []

/--
Message-server normalization obeys the same three conventions as the actor sort.

Stated separately rather than derived from the actor regression because the two instantiate
`GeneralPriority.normalize` at different projections, and a mistake in either projection would leave the
other green.
-/
theorem general_server_priority_normalization_regression :
    DTR.GeneralMessageServerPriority.normalize [
      generalServerLow,
      generalServerNone,
      generalServerHigh,
      generalServerHighTie
    ] = [
      generalServerHigh,
      generalServerHighTie,
      generalServerLow,
      generalServerNone
    ] := by
  rfl

/--
Message-server ties fall back on declaration order.
-/
theorem general_server_priority_tie_stability :
    DTR.GeneralMessageServerPriority.normalize [
      generalServerHighTie,
      generalServerHigh
    ] = [
      generalServerHighTie,
      generalServerHigh
    ] := by
  rfl

/--
A class in which no message server carries a priority is left exactly as declared.
-/
theorem general_server_unannotated_order_regression :
    DTR.GeneralMessageServerPriority.normalize [
      generalServerNone,
      generalServerNoneSecond
    ] = [
      generalServerNone,
      generalServerNoneSecond
    ] := by
  rfl

end Tests
end Relico
