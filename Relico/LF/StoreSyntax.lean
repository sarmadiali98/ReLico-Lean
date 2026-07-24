import Relico.LF.Syntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
One generated LF reactor-state declaration together with its initial
integer value.
-/
structure StateVariableDecl where
  name :
    VarName

  initialValue :
    Int

deriving Repr, DecidableEq, BEq, Inhabited

/--
The reactor-state names declared by a list of generated declarations.
-/
def stateVariableNames
    (declarations : List LF.StateVariableDecl) :
    List VarName :=
  declarations.map
    (fun declaration =>
      declaration.name)

/--
A generated LF reactor containing an arbitrary finite list of state
declarations.
-/
structure StoreReactor where
  name :
    ReactorName

  stateVariables :
    List LF.StateVariableDecl

  logicalAction :
    ActionName

  startupReaction :
    LF.Reaction

  messageReaction :
    LF.Reaction

deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete generated LF program using finite reactor-state
declarations.
-/
structure StoreProgram where
  reactor :
    LF.StoreReactor

  reactorInstance :
    LF.ReactorInstance

deriving Repr, DecidableEq, BEq, Inhabited

namespace Program

/--
Embed a generated legacy singleton-state program into the generalized
store-program representation.
-/
def toStoreProgram
    (program : LF.Program)
    (initialValue : Int) :
    LF.StoreProgram where

  reactor := {
    name :=
      program.reactor.name

    stateVariables := [
      {
        name :=
          program.reactor.stateVar

        initialValue :=
          initialValue
      }
    ]

    logicalAction :=
      program.reactor.logicalAction

    startupReaction :=
      program.reactor.startupReaction

    messageReaction :=
      program.reactor.messageReaction
  }

  reactorInstance :=
    program.reactorInstance

end Program
end LF
end Relico
