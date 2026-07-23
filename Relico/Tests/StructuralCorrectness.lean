import Relico.Correctness.Structural
import Relico.Tests.Translation

set_option autoImplicit false

namespace Relico
namespace Tests

theorem validModel_generatedProgram_wellFormed :
    LF.Program.WellFormed expectedProgram := by
  exact
    Correctness.translate_wellFormed
      validModel_wellFormed
      validModel_translates_to_expectedProgram

end Tests
end Relico
