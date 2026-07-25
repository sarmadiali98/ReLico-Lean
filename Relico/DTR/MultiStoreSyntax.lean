import Relico.DTR.StoreSyntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
The message-server names declared by an ordered server list.
-/
def messageServerNames
    (messageServers : List DTR.MessageServer) :
    List MsgName :=
  messageServers.map
    (fun messageServer =>
      messageServer.name)

/--
A DTR reactive class with finite state and an ordered finite list of
message servers.

The declaration order will later encode message-server priority where
the supported source model requires an explicit same-time order.
-/
structure MultiStoreReactiveClass where
  name :
    ClassName

  stateVariables :
    List DTR.StateVariableDecl

  constructor :
    DTR.Constructor

  messageServers :
    List DTR.MessageServer

deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete one-actor DTR model with finite state and multiple message
servers.

Actor multiplicity remains a later generalization.
-/
structure MultiStoreModel where
  reactiveClass :
    DTR.MultiStoreReactiveClass

  actor :
    DTR.ActorInstance

deriving Repr, DecidableEq, BEq, Inhabited

namespace StoreModel

/--
Embed the existing verified one-server finite-store model into the
multi-server model.
-/
def toMultiStoreModel
    (model : DTR.StoreModel) :
    DTR.MultiStoreModel where

  reactiveClass := {
    name :=
      model.reactiveClass.name

    stateVariables :=
      model.reactiveClass.stateVariables

    constructor :=
      model.reactiveClass.constructor

    messageServers := [
      model.reactiveClass.messageServer
    ]
  }

  actor :=
    model.actor

@[simp]
theorem toMultiStoreModel_messageServers
    (model : DTR.StoreModel) :
    (toMultiStoreModel
      model).reactiveClass.messageServers = [
        model.reactiveClass.messageServer
      ] := by
  rfl

end StoreModel
end DTR
end Relico
