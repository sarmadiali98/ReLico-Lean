import Relico.Correctness.MachineInitialization
import Relico.Correctness.Structural
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Any program returned successfully by the executable translator is the
program produced by `translateCore`.

This lemma connects correctness results about the compiler core to the
public executable translation entry point.
-/
theorem translatedProgram_eq_translateCore
    {model : DTR.Model}
    {program : LF.Program}
    (hTranslate :
      Translation.translate model =
        Except.ok program) :
    program =
      Translation.translateCore model := by
  simpa [Translation.translate] using
    hTranslate.symm

/--
Structural correctness for the program returned by the executable
translator.
-/
theorem executableTranslation_wellFormed
    {model : DTR.Model}
    {program : LF.Program}
    (hModel :
      DTR.Model.WellFormed model)
    (hTranslate :
      Translation.translate model =
        Except.ok program) :
    LF.Program.WellFormed program := by

  have hProgram :
      program =
        Translation.translateCore model :=
    translatedProgram_eq_translateCore
      hTranslate

  subst program

  exact
    translateCore_wellFormed
      hModel

/--
Conditional finite forward correctness for the program returned by the
executable translator.

The compatibility evidence retains the explicit scheduler condition
required for every source dispatch step.
-/
theorem executableTranslation_initialMachineSteps_forward
    {model : DTR.Model}
    {program : LF.Program}
    {initialValue : Int}
    {sourceLabels : List DTR.MachineLabel}
    {sourceStateAfter : DTR.State}
    (hTranslate :
      Translation.translate model =
        Except.ok program)
    (hCompatible :
      ForwardMachineExecutionCompatible
        model
        (DTR.initialState
          model
          initialValue)
        sourceLabels
        sourceStateAfter
        (LF.initialState
          program
          initialValue)) :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          model
          (DTR.initialState
            model
            initialValue)
          sourceLabels
          sourceStateAfter ∧
      LF.MachineSteps
          program
          (LF.initialState
            program
            initialValue)
          targetLabels
          targetStateAfter ∧
      MachineTraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  have hProgram :
      program =
        Translation.translateCore model :=
    translatedProgram_eq_translateCore
      hTranslate

  subst program

  exact
    initialMachineSteps_forward_of_compatible
      hCompatible

/--
Unconditional finite backward correctness for the program returned by
the executable translator.

For a well-formed source model, every finite execution of the returned
generated-LF program from startup entry has a corresponding finite DTR
execution from constructor entry.
-/
theorem executableTranslation_initialMachineSteps_backward
    {model : DTR.Model}
    {program : LF.Program}
    {initialValue : Int}
    {targetLabels : List LF.MachineLabel}
    {targetStateAfter : LF.State}
    (hTranslate :
      Translation.translate model =
        Except.ok program)
    (hTargetSteps :
      LF.MachineSteps
        program
        (LF.initialState
          program
          initialValue)
        targetLabels
        targetStateAfter)
    (hModel :
      DTR.Model.WellFormed model) :
    ∃ sourceLabels sourceStateAfter,
      DTR.MachineSteps
          model
          (DTR.initialState
            model
            initialValue)
          sourceLabels
          sourceStateAfter ∧
      MachineTraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter ∧
      DTR.State.WellFormed
          model
          sourceStateAfter := by

  have hProgram :
      program =
        Translation.translateCore model :=
    translatedProgram_eq_translateCore
      hTranslate

  subst program

  exact
    initialMachineSteps_backward
      hTargetSteps
      hModel

end Correctness
end Relico
