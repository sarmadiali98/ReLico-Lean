import Relico.LF.CppPrinter
import Relico.LF.StoreSyntax

set_option autoImplicit false

namespace Relico
namespace LF
namespace CppPrinter

def renderStateVariableDecl
    (declaration : LF.StateVariableDecl) :
    String :=
  "  state " ++
    declaration.name.value ++
    ": int = " ++
    toString declaration.initialValue

def renderStateVariableDecls
    (declarations : List LF.StateVariableDecl) :
    String :=
  String.intercalate
    "\n"
    (declarations.map
      renderStateVariableDecl)

def renderStoreReactor
    (reactor : LF.StoreReactor) :
    String :=
  "reactor " ++
    reactor.name.value ++
    " {\n" ++
    renderStateVariableDecls
      reactor.stateVariables ++
    "\n" ++
    "  logical action " ++
    reactor.logicalAction.value ++
    ": void\n\n" ++
    renderReaction
      reactor.startupReaction ++
    "\n\n" ++
    renderReaction
      reactor.messageReaction ++
    "\n}"

def renderStoreProgram
    (program : LF.StoreProgram) :
    String :=
  targetHeader ++
    "\n\n" ++
    renderStoreReactor
      program.reactor ++
    "\n\n" ++
    renderMain
      program.reactorInstance ++
    "\n"

end CppPrinter
end LF
end Relico
