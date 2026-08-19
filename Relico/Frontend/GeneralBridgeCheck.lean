import Relico.Frontend.GeneralDecoder

set_option autoImplicit false

namespace Relico
namespace Frontend

/-!
# The `general-v1` bridge check

Reads a `general-v1` document from disk and reports what the frontend made of
it. This module deliberately stops after decoding: there is no general
translation yet (stage D), so there is nothing to render into LF and nothing to
print about a reactor.

Kept INSIDE the build closure: `Relico.lean` imports it, so `lake build`
type-checks it. That is possible only because the `main` lives separately, in
`frontend/lean-bridge/GeneralBridgeMain.lean` — a module carrying an inline
`def main` cannot be imported, which is exactly why the three older bridge
checks (`BridgeCheck`, `StoreBridgeCheck`, `MultiStoreBridgeCheck`) are all
absent from `Relico.lean`. This module follows the newest sibling,
`MultiStorePayloadBridgeCheck`, which made the same split and is imported at
`Relico.lean:545`.

`frontend/check-general-lean.sh` therefore runs
`lake env lean --run frontend/lean-bridge/GeneralBridgeMain.lean` after an
explicit `lake build`, and `Relico/Tests/` may import this module without
dragging in an entry point.

The summary is deterministic — no set iteration, no hashing, no timestamps — so
a test may compare it byte for byte, and it names counts that a silent
elaboration bug would change.
-/

/--
Instance priority, which is `Option Nat` because a general model may leave it
unset.

Shown because priority is the one field the elaborator carries through and
`wellFormed` deliberately says nothing about: distinctness is a hypothesis of the
theorems that need deterministic selection, not a condition on decodability. If
priorities were being dropped in transit, no well-formedness check would notice
and this line is the only place it would show.

Matches `MultiStoreBridgeCheck.renderPriority`, including rendering absence as
`none` rather than as an empty string.
-/
private def renderGeneralPriority :
    Option Nat →
    String

  | some priority =>
      toString priority

  | none =>
      "none"

/--
One line per reactive class: its name and the size of each of its four member
lists.
-/
private def renderGeneralClass
    (reactiveClass : DTR.GeneralReactiveClass) :
    String :=
  "  class " ++
    reactiveClass.name.value ++
    ": knownRebecs=" ++
    toString reactiveClass.knownRebecs.length ++
    " stateVariables=" ++
    toString reactiveClass.stateVariables.length ++
    " messageServers=" ++
    toString reactiveClass.messageServers.length ++
    " constructorStatements=" ++
    toString reactiveClass.constructor.body.length

/--
One line per instance.

The binder is `actor`, not `instance`: `instance` is a Lean keyword and cannot be
a binder name.
-/
private def renderGeneralInstance
    (actor : DTR.GeneralActorInstance) :
    String :=
  "  instance " ++
    actor.name.value ++
    " : " ++
    actor.className.value ++
    " arguments=" ++
    toString actor.arguments.length ++
    " bindings=" ++
    toString actor.bindings.length ++
    " priority=" ++
    renderGeneralPriority actor.priority

/--
Decode a `general-v1` document and report what the frontend made of it.

Exit codes follow the sibling bridge checks: `0` on success, `1` on a decode
failure, and `2` from the `main` wrapper on bad usage.

The diagnostic is printed by `render` with nothing prepended. The siblings
prefix their errors (`"payload frontend decode failed: "`) because their error is
a bare `String` that describes nothing about itself; a `GeneralDiagnostic`
already renders its family, its rule, the offending detail, the context and the
line, so a prefix here would only say `general` twice.

Classes and instances are joined into a single `println` so that neither an empty
class list nor an empty instance list can contribute a stray blank line to output
a test may be comparing byte for byte.
-/
def runGeneralBridgeCheck
    (jsonPath : String) :
    IO UInt32 := do

  let text ←
    IO.FS.readFile jsonPath

  match decodeGeneralModelText text with

  | .error diagnostic =>
      IO.eprintln
        diagnostic.render

      pure 1

  | .ok model =>
      IO.println
        "GENERAL_FRONTEND_OK"

      IO.println
        s!"classes={model.classes.length} instances={model.instances.length}"

      IO.println
        (String.intercalate
          "\n"
          (model.classes.map renderGeneralClass ++
            model.instances.map renderGeneralInstance))

      pure 0

end Frontend
end Relico
