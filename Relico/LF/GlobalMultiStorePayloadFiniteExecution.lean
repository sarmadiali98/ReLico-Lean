import Relico.LF.GlobalMultiStorePayloadOneStep

set_option autoImplicit false

namespace Relico

namespace LF
namespace GlobalMultiStorePayloadFiniteExecution

/--
A finite reflexive sequence of published target one-step transitions.
-/
inductive Steps
    (targetProgram :
      LF.GlobalMultiStorePayloadProgram) :
    LF.GlobalMultiStorePayloadState →
    LF.GlobalMultiStorePayloadState →
    Prop where

  | refl
      (state :
        LF.GlobalMultiStorePayloadState) :
      Steps
        targetProgram
        state
        state

  | cons
      {before middle after :
        LF.GlobalMultiStorePayloadState}
      (head :
        LF.GlobalMultiStorePayloadOneStep.Step
          targetProgram
          before
          middle)
      (tail :
        Steps
          targetProgram
          middle
          after) :
      Steps
        targetProgram
        before
        after

end GlobalMultiStorePayloadFiniteExecution
end LF

end Relico
