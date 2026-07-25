import Relico.LF.MultiStoreSyntax
import Relico.LF.StoreInitialization

set_option autoImplicit false

namespace Relico
namespace LF
namespace MultiStoreProgram

/--
The generated-LF runtime state at startup-reaction entry for a
multi-reaction finite-store program.

Execution begins at the initial LF tag with the declaration-derived
store, no pending logical actions, and the startup-reaction body active.
-/
def initialState
    (program : LF.MultiStoreProgram) :
    LF.StoreState where

  currentTag :=
    LF.initialTag

  stateStore :=
    LF.initialStore
      program.reactor.stateVariables

  pendingActions :=
    []

  activeBody :=
    program.reactor.startupReaction.body

@[simp]
theorem initialState_currentTag
    (program : LF.MultiStoreProgram) :
    (initialState program).currentTag =
      LF.initialTag := by
  rfl

@[simp]
theorem initialState_stateStore
    (program : LF.MultiStoreProgram) :
    (initialState program).stateStore =
      LF.initialStore
        program.reactor.stateVariables := by
  rfl

@[simp]
theorem initialState_pendingActions
    (program : LF.MultiStoreProgram) :
    (initialState program).pendingActions =
      [] := by
  rfl

@[simp]
theorem initialState_activeBody
    (program : LF.MultiStoreProgram) :
    (initialState program).activeBody =
      program.reactor.startupReaction.body := by
  rfl

end MultiStoreProgram
end LF
end Relico
