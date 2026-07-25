import Relico.DTR.MultiStoreSyntax
import Relico.DTR.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

namespace Stmt

/--
Structural validity of a DTR statement for finite state and multiple
declared message servers.

Assignments must use declared state variables. Self-sends may target
any declared message server.
-/
def MultiStoreWellFormed
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName) :
    DTR.Stmt →
    Prop

  | .assign target expression =>
      target ∈ declaredVariables ∧
      DTR.Expr.StoreWellFormed
        declaredVariables
        expression

  | .selfSend targetMessage _ =>
      targetMessage ∈
        declaredMessageServers

@[simp]
theorem multiStoreWellFormed_assign
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName)
    (target : VarName)
    (expression : DTR.Expr) :
    MultiStoreWellFormed
        declaredVariables
        declaredMessageServers
        (.assign target expression) ↔
      target ∈ declaredVariables ∧
      DTR.Expr.StoreWellFormed
        declaredVariables
        expression := by
  rfl

@[simp]
theorem multiStoreWellFormed_selfSend
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName)
    (targetMessage : MsgName)
    (delay : Delay) :
    MultiStoreWellFormed
        declaredVariables
        declaredMessageServers
        (.selfSend targetMessage delay) ↔
      targetMessage ∈
        declaredMessageServers := by
  rfl

/--
The multi-server predicate specializes exactly to the existing
finite-store predicate for a singleton server list.
-/
theorem multiStoreWellFormed_singleton_iff
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName)
    (statement : DTR.Stmt) :
    MultiStoreWellFormed
        declaredVariables
        [declaredMessageServer]
        statement ↔
      DTR.Stmt.StoreWellFormed
        declaredVariables
        declaredMessageServer
        statement := by

  cases statement <;>
    simp [
      MultiStoreWellFormed,
      DTR.Stmt.StoreWellFormed
    ]

end Stmt

namespace Body

/--
Every statement in a source body must be valid for the complete state
declaration list and complete message-server declaration list.
-/
def MultiStoreWellFormed
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName)
    (body : DTR.Body) :
    Prop :=
  ∀ statement,
    statement ∈ body →
    DTR.Stmt.MultiStoreWellFormed
      declaredVariables
      declaredMessageServers
      statement

@[simp]
theorem multiStoreWellFormed_nil
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName) :
    MultiStoreWellFormed
      declaredVariables
      declaredMessageServers
      [] := by

  intro statement hMember
  cases hMember

@[simp]
theorem multiStoreWellFormed_cons
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName)
    (statement : DTR.Stmt)
    (remaining : DTR.Body) :
    MultiStoreWellFormed
        declaredVariables
        declaredMessageServers
        (statement :: remaining) ↔
      DTR.Stmt.MultiStoreWellFormed
          declaredVariables
          declaredMessageServers
          statement ∧
        MultiStoreWellFormed
          declaredVariables
          declaredMessageServers
          remaining := by

  constructor

  · intro hBody

    constructor

    · exact
        hBody
          statement
          (by simp)

    · intro nextStatement hMember

      exact
        hBody
          nextStatement
          (by simp [hMember])

  · intro hParts

    rcases hParts with
      ⟨hHead, hTail⟩

    intro nextStatement hMember

    simp only [List.mem_cons] at hMember

    rcases hMember with
      rfl | hRemaining

    · exact hHead

    · exact
        hTail
          nextStatement
          hRemaining

/--
The multi-server body predicate specializes exactly to the existing
finite-store predicate for a singleton server list.
-/
theorem multiStoreWellFormed_singleton_iff
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName)
    (body : DTR.Body) :
    MultiStoreWellFormed
        declaredVariables
        [declaredMessageServer]
        body ↔
      DTR.Body.StoreWellFormed
        declaredVariables
        declaredMessageServer
        body := by

  constructor

  · intro hBody statement hMember

    exact
      (DTR.Stmt.multiStoreWellFormed_singleton_iff
        declaredVariables
        declaredMessageServer
        statement).mp
        (hBody statement hMember)

  · intro hBody statement hMember

    exact
      (DTR.Stmt.multiStoreWellFormed_singleton_iff
        declaredVariables
        declaredMessageServer
        statement).mpr
        (hBody statement hMember)

end Body
end DTR
end Relico
