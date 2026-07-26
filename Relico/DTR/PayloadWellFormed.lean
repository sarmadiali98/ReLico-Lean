import Relico.DTR.PayloadSyntax

set_option autoImplicit false

namespace Relico
namespace DTR

namespace PayloadStmt

/--
A payload self-send is well formed when it targets the message server
declared for the current payload fragment.
-/
def WellFormed
    (declaredMessageServer : MsgName) :
    DTR.PayloadStmt →
    Prop

  | .selfSendInt
      targetMessage
      _payloadExpression
      _delay =>

      targetMessage =
        declaredMessageServer

@[simp]
theorem wellFormed_selfSendInt
    (declaredMessageServer targetMessage : MsgName)
    (payloadExpression : DTR.Expr)
    (delay : Delay) :
    WellFormed
        declaredMessageServer
        (.selfSendInt
          targetMessage
          payloadExpression
          delay) ↔
      targetMessage =
        declaredMessageServer := by
  rfl

end PayloadStmt

namespace PayloadBody

/--
Every statement in an additive payload body must target the declared
payload message server.
-/
def WellFormed
    (declaredMessageServer : MsgName)
    (body : DTR.PayloadBody) :
    Prop :=
  ∀ statement ∈ body,
    DTR.PayloadStmt.WellFormed
      declaredMessageServer
      statement

@[simp]
theorem wellFormed_nil
    (declaredMessageServer : MsgName) :
    WellFormed
      declaredMessageServer
      [] := by

  intro statement membership
  cases membership

theorem wellFormed_cons
    (declaredMessageServer : MsgName)
    (statement : DTR.PayloadStmt)
    (remaining : DTR.PayloadBody) :
    WellFormed
        declaredMessageServer
        (statement :: remaining) ↔
      DTR.PayloadStmt.WellFormed
          declaredMessageServer
          statement ∧
        WellFormed
          declaredMessageServer
          remaining := by

  constructor

  · intro hWellFormed

    constructor

    · exact
        hWellFormed
          statement
          (by simp)

    · intro nextStatement hMember

      exact
        hWellFormed
          nextStatement
          (by
            simp [
              hMember
            ])

  · intro hParts
    intro nextStatement hMember

    simp only [
      List.mem_cons
    ] at hMember

    rcases hMember with
      hHead | hTail

    · subst nextStatement
      exact hParts.1

    · exact
        hParts.2
          nextStatement
          hTail

end PayloadBody
end DTR
end Relico
