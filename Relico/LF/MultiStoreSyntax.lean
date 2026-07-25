import Relico.LF.StoreSyntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
A generated LF reactor with finite state and ordered finite lists of
logical actions and message reactions.

The action and reaction lists have corresponding positions.
-/
structure MultiStoreReactor where
  name :
    ReactorName

  stateVariables :
    List LF.StateVariableDecl

  logicalActions :
    List ActionName

  startupReaction :
    LF.Reaction

  messageReactions :
    List LF.Reaction

deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete generated LF program with one finite-state reactor and
multiple message reactions.
-/
structure MultiStoreProgram where
  reactor :
    LF.MultiStoreReactor

  reactorInstance :
    LF.ReactorInstance

deriving Repr, DecidableEq, BEq, Inhabited

namespace StoreProgram

/--
Embed the existing verified one-reaction finite-store program into the
multi-reaction program.
-/
def toMultiStoreProgram
    (program : LF.StoreProgram) :
    LF.MultiStoreProgram where

  reactor := {
    name :=
      program.reactor.name

    stateVariables :=
      program.reactor.stateVariables

    logicalActions := [
      program.reactor.logicalAction
    ]

    startupReaction :=
      program.reactor.startupReaction

    messageReactions := [
      program.reactor.messageReaction
    ]
  }

  reactorInstance :=
    program.reactorInstance

@[simp]
theorem toMultiStoreProgram_logicalActions
    (program : LF.StoreProgram) :
    (toMultiStoreProgram
      program).reactor.logicalActions = [
        program.reactor.logicalAction
      ] := by
  rfl

@[simp]
theorem toMultiStoreProgram_messageReactions
    (program : LF.StoreProgram) :
    (toMultiStoreProgram
      program).reactor.messageReactions = [
        program.reactor.messageReaction
      ] := by
  rfl

end StoreProgram
end LF
end Relico
