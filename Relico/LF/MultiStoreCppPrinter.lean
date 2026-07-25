import Relico.LF.StoreCppPrinter
import Relico.LF.MultiStoreSyntax

set_option autoImplicit false

namespace Relico
namespace LF
namespace CppPrinter

/--
Render one logical-action declaration.
-/
def renderLogicalActionDecl
    (action : ActionName) :
    String :=
  "  logical action " ++
    action.value ++
    ": void\n"

/--
Render logical-action declarations in their existing list order.

For translated programs, this is the normalized source priority order.
-/
def renderLogicalActionDecls :
    List ActionName →
    String

  | [] =>
      ""

  | action :: remaining =>
      renderLogicalActionDecl
          action ++
        renderLogicalActionDecls
          remaining

/--
Render message reactions in their existing list order.

A blank line separates adjacent reactions. No additional blank line is
placed after the final reaction, preserving exact compatibility with
the existing singleton finite-store printer.
-/
def renderMessageReactions :
    List LF.Reaction →
    String

  | [] =>
      ""

  | [reaction] =>
      renderReaction
        reaction

  | reaction :: remaining =>
      renderReaction
          reaction ++
        "\n\n" ++
        renderMessageReactions
          remaining

/--
Render a finite-state reactor with multiple logical actions and message
reactions.

List order is semantic: generated logical actions and reactions are
already normalized by the executable Lean translator.
-/
def renderMultiStoreReactor
    (reactor : LF.MultiStoreReactor) :
    String :=
  "reactor " ++
    reactor.name.value ++
    " {\n" ++
    renderStateVariableDecls
      reactor.stateVariables ++
    "\n" ++
    renderLogicalActionDecls
      reactor.logicalActions ++
    "\n" ++
    renderReaction
      reactor.startupReaction ++
    "\n\n" ++
    renderMessageReactions
      reactor.messageReactions ++
    "\n}\n"

/--
Render a complete multiple-message-server LF/C++ program.
-/
def renderMultiStoreProgram
    (program : LF.MultiStoreProgram) :
    String :=
  targetHeader ++
    "\n\n" ++
    renderMultiStoreReactor
      program.reactor ++
    "\n" ++
    renderMain
      program.reactorInstance ++
    "\n"

/--
The multi-server printer is an exact conservative extension of the
existing finite-store printer.
-/
theorem renderMultiStoreProgram_toMultiStoreProgram
    (program : LF.StoreProgram) :
    renderMultiStoreProgram
        (LF.StoreProgram.toMultiStoreProgram
          program) =
      renderStoreProgram
        program := by

  cases program with

  | mk reactor reactorInstance =>
      cases reactor with

      | mk
          name
          stateVariables
          logicalAction
          startupReaction
          messageReaction =>

          have newlineLogicalActionPrefix
              (suffix : String) :
              "\n" ++
                  ("  logical action " ++
                    suffix) =
                "\n  logical action " ++
                  suffix := by

            rw [
              ← String.append_assoc
            ]

            rfl

          simp [
            LF.StoreProgram.toMultiStoreProgram,
            renderMultiStoreProgram,
            renderMultiStoreReactor,
            renderLogicalActionDecls,
            renderLogicalActionDecl,
            renderMessageReactions,
            renderStoreProgram,
            renderStoreReactor,
            newlineLogicalActionPrefix,
            String.append_assoc
          ]

end CppPrinter
end LF
end Relico
