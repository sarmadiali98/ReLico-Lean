import Relico.DTR.StoreSemantics
import Relico.DTR.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A finite execution of the store-based DTR statement semantics.

The label list records the transition labels in execution order.
-/
inductive StoreTrace
    (declaredVariables : List VarName)
    (messageServer : MsgName) :
    DTR.StoreState →
    List DTR.Label →
    DTR.StoreState →
    Prop where

  | refl
      (state : DTR.StoreState) :

      StoreTrace
        declaredVariables
        messageServer
        state
        []
        state

  | step
      {before middle after : DTR.StoreState}
      {label : DTR.Label}
      {remainingLabels : List DTR.Label}
      (hStep :
        DTR.StoreStep
          declaredVariables
          messageServer
          before
          label
          middle)
      (hTrace :
        StoreTrace
          declaredVariables
          messageServer
          middle
          remainingLabels
          after) :

      StoreTrace
        declaredVariables
        messageServer
        before
        (label :: remainingLabels)
        after

namespace StoreStep

/--
A DTR store statement step preserves structural well-formedness of the
remaining active body.

Every statement step removes exactly the current head statement.
-/
theorem preserves_body_storeWellFormed
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStep :
      DTR.StoreStep
        declaredVariables
        messageServer
        before
        label
        after)
    (hBefore :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        before.activeBody) :
    DTR.Body.StoreWellFormed
      declaredVariables
      messageServer
      after.activeBody := by

  cases hStep with

  | assign
      currentTime
      stateStore
      pendingMessages
      target
      expression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      exact
        ((DTR.Body.storeWellFormed_cons
          declaredVariables
          messageServer
          (DTR.Stmt.assign
            target
            expression)
          remaining).mp
          hBefore).2

  | selfSend
      currentTime
      stateStore
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      exact
        ((DTR.Body.storeWellFormed_cons
          declaredVariables
          messageServer
          (DTR.Stmt.selfSend
            targetMessage
            delay)
          remaining).mp
          hBefore).2

end StoreStep
end DTR
end Relico
