import Relico.Common.Name

set_option autoImplicit false

namespace Relico
namespace Translation

def reactorNameFor
    (className : ClassName) :
    ReactorName :=
  ⟨className.value⟩

def actionNameFor
    (messageName : MsgName) :
    ActionName :=
  ⟨messageName.value ++ "_action"⟩

def startupReactionName :
    ReactionName :=
  ⟨"startup"⟩

def messageReactionNameFor
    (messageName : MsgName) :
    ReactionName :=
  ⟨messageName.value ++ "_reaction"⟩

end Translation
end Relico
