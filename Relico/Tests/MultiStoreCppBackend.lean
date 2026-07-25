import Relico.Translation.MultiStoreCppBackend
import Relico.Tests.MessageServerPriority
import Relico.Tests.MultiStoreModelTranslation
import Relico.Tests.StoreCppBackend

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The generalized printer preserves the previous finite-store output
exactly when the program contains one logical action and one message
reaction.
-/
theorem existing_store_cpp_printer_embeds_exactly :
    LF.CppPrinter.renderMultiStoreProgram
        (LF.StoreProgram.toMultiStoreProgram
          (Translation.translateStoreCore
            expectedDecodedStoreModel)) =
      LF.CppPrinter.renderStoreProgram
        (Translation.translateStoreCore
          expectedDecodedStoreModel) := by

  exact
    LF.CppPrinter.renderMultiStoreProgram_toMultiStoreProgram
      (Translation.translateStoreCore
        expectedDecodedStoreModel)

/--
Concrete logical-action declarations retain the normalized
high-priority-first order produced by the executable translator.
-/
theorem priority_cpp_action_declaration_order :
    LF.CppPrinter.renderLogicalActionDecls
        (Translation.compileLogicalActions
          priorityTranslationServers) =
      LF.CppPrinter.renderLogicalActionDecl
          (Translation.actionNameFor
            priorityHighName) ++
        LF.CppPrinter.renderLogicalActionDecl
          (Translation.actionNameFor
            priorityHighTieName) ++
        LF.CppPrinter.renderLogicalActionDecl
          (Translation.actionNameFor
            priorityLowName) ++
        LF.CppPrinter.renderLogicalActionDecl
          (Translation.actionNameFor
            priorityNoneName) := by
  rfl

/--
Concrete message-reaction source retains the same normalized order.
-/
theorem priority_cpp_reaction_declaration_order :
    LF.CppPrinter.renderMessageReactions
        (Translation.compileMessageReactions
          priorityTranslationServers) =
      LF.CppPrinter.renderReaction
          (Translation.compileMessageReaction
            priorityHighServer) ++
        "\n\n" ++
        LF.CppPrinter.renderReaction
          (Translation.compileMessageReaction
            priorityHighTieServer) ++
        "\n\n" ++
        LF.CppPrinter.renderReaction
          (Translation.compileMessageReaction
            priorityLowServer) ++
        "\n\n" ++
        LF.CppPrinter.renderReaction
          (Translation.compileMessageReaction
            priorityNoneServer) := by
  rfl

/--
The public C++ backend renders the precise multi-server LF AST returned
by the executable Lean translation.
-/
theorem twoMessageModel_renders_from_executable_translation :
    Translation.translateMultiStoreToCppSource
        twoMessageModel =
      .ok
        (LF.CppPrinter.renderMultiStoreProgram
          (Translation.translateMultiStoreCore
            twoMessageModel)) := by
  rfl

end Tests
end Relico
