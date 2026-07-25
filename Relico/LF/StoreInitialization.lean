import Relico.Common.StateStore
import Relico.LF.Initialization
import Relico.LF.StoreState
import Relico.LF.StoreSyntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
Construct the initial generated-LF finite store from reactor-state
declarations.

Declaration order is retained exactly.
-/
def initialStore
    (declarations : List LF.StateVariableDecl) :
    StateStore :=
  declarations.map
    (fun declaration =>
      (declaration.name,
       declaration.initialValue))

namespace StoreProgram

/--
The finite-store generated-LF runtime state at startup-reaction entry.

The reactor starts at the initial LF tag with no pending logical
actions. Its active body is the startup-reaction body.
-/
def initialState
    (program : LF.StoreProgram) :
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
    (program : LF.StoreProgram) :
    (initialState program).currentTag =
      LF.initialTag := by
  rfl

@[simp]
theorem initialState_stateStore
    (program : LF.StoreProgram) :
    (initialState program).stateStore =
      LF.initialStore
        program.reactor.stateVariables := by
  rfl

@[simp]
theorem initialState_pendingActions
    (program : LF.StoreProgram) :
    (initialState program).pendingActions =
      [] := by
  rfl

@[simp]
theorem initialState_activeBody
    (program : LF.StoreProgram) :
    (initialState program).activeBody =
      program.reactor.startupReaction.body := by
  rfl

end StoreProgram
end LF
end Relico
