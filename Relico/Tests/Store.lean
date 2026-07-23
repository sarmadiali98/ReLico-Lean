import Relico.Common.Store

set_option autoImplicit false

namespace Relico
namespace Tests

def sampleStore :
    Store String Int := [
  ("x", 0),
  ("y", 1)
]

theorem sample_lookup_x :
    Store.lookup
        sampleStore
        "x" =
      some 0 := by
  rfl

theorem sample_lookup_y :
    Store.lookup
        sampleStore
        "y" =
      some 1 := by
  rfl

theorem sample_lookup_missing :
    Store.lookup
        sampleStore
        "z" =
      none := by
  rfl

theorem update_existing_binding :
    Store.lookup
        (Store.update
          sampleStore
          "x"
          5)
        "x" =
      some 5 := by
  exact
    Store.lookup_update_eq
      sampleStore
      "x"
      5

theorem update_preserves_distinct_binding :
    Store.lookup
        (Store.update
          sampleStore
          "x"
          5)
        "y" =
      some 1 := by
  rfl

theorem update_inserts_missing_binding :
    Store.lookup
        (Store.update
          sampleStore
          "z"
          9)
        "z" =
      some 9 := by
  exact
    Store.lookup_update_eq
      sampleStore
      "z"
      9

theorem second_update_wins :
    Store.update
        (Store.update
          sampleStore
          "x"
          5)
        "x"
        7 =
      Store.update
        sampleStore
        "x"
        7 := by
  exact
    Store.update_same
      sampleStore
      "x"
      5
      7

end Tests
end Relico
