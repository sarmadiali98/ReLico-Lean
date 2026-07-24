import Relico.DTR.Syntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
One declared DTR state variable together with its initial integer
value.
-/
structure StateVariableDecl where
  name :
    VarName

  initialValue :
    Int

deriving Repr, DecidableEq, BEq, Inhabited

/--
The state-variable names declared by a list of DTR declarations.
-/
def stateVariableNames
    (declarations : List DTR.StateVariableDecl) :
    List VarName :=
  declarations.map
    (fun declaration =>
      declaration.name)

/--
A DTR reactive class with an arbitrary finite list of state-variable
declarations.

The statement and expression languages are unchanged. Their variable
references are validated against `stateVariables`.
-/
structure StoreReactiveClass where
  name :
    ClassName

  stateVariables :
    List DTR.StateVariableDecl

  constructor :
    DTR.Constructor

  messageServer :
    DTR.MessageServer

deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete DTR model using finite state-variable declarations.
-/
structure StoreModel where
  reactiveClass :
    DTR.StoreReactiveClass

  actor :
    DTR.ActorInstance

deriving Repr, DecidableEq, BEq, Inhabited

namespace Model

/--
Embed a legacy singleton-state model into the generalized store model.

The legacy AST does not contain an initial value, so it is supplied
explicitly.
-/
def toStoreModel
    (model : DTR.Model)
    (initialValue : Int) :
    DTR.StoreModel where

  reactiveClass := {
    name :=
      model.reactiveClass.name

    stateVariables := [
      {
        name :=
          model.reactiveClass.stateVar

        initialValue :=
          initialValue
      }
    ]

    constructor :=
      model.reactiveClass.constructor

    messageServer :=
      model.reactiveClass.messageServer
  }

  actor :=
    model.actor

end Model
end DTR
end Relico
