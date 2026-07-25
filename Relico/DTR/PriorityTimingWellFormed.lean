import Relico.DTR.MultiStoreModelWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

namespace Stmt

/--
Timing restriction used by the priority-preserving multi-server
translation theorem.

Assignments impose no timing condition. Every self-send must use a
strictly positive delay.

This restriction is specific to the priority-sensitive fragment. The
general DTR semantics continues to support zero-delay self-sends.
-/
def PriorityTimingWellFormed :
    DTR.Stmt →
    Prop

  | .assign _ _ =>
      True

  | .selfSend _ delay =>
      0 < delay.value

@[simp]
theorem priorityTimingWellFormed_assign
    (target : VarName)
    (expression : DTR.Expr) :
    PriorityTimingWellFormed
      (.assign target expression) := by
  exact True.intro

@[simp]
theorem priorityTimingWellFormed_selfSend
    (target : MsgName)
    (delay : Delay) :
    PriorityTimingWellFormed
        (.selfSend target delay) ↔
      0 < delay.value := by
  rfl

end Stmt

namespace Body

/--
Every self-send in a body has a strictly positive delay.
-/
def PriorityTimingWellFormed :
    DTR.Body →
    Prop

  | [] =>
      True

  | statement :: remaining =>
      DTR.Stmt.PriorityTimingWellFormed
          statement ∧
        PriorityTimingWellFormed
          remaining

@[simp]
theorem priorityTimingWellFormed_nil :
    PriorityTimingWellFormed
      [] := by
  exact True.intro

@[simp]
theorem priorityTimingWellFormed_cons
    (statement : DTR.Stmt)
    (remaining : DTR.Body) :
    PriorityTimingWellFormed
        (statement :: remaining) ↔
      DTR.Stmt.PriorityTimingWellFormed
          statement ∧
        PriorityTimingWellFormed
          remaining := by
  rfl

theorem priorityTimingWellFormed_append
    (left right : DTR.Body) :
    PriorityTimingWellFormed
        (left ++ right) ↔
      PriorityTimingWellFormed left ∧
        PriorityTimingWellFormed right := by

  induction left with

  | nil =>
      simp [
        PriorityTimingWellFormed
      ]

  | cons statement remaining inductionHypothesis =>
      change
        DTR.Stmt.PriorityTimingWellFormed
              statement ∧
            PriorityTimingWellFormed
              (remaining ++ right) ↔
          (DTR.Stmt.PriorityTimingWellFormed
                statement ∧
              PriorityTimingWellFormed
                remaining) ∧
            PriorityTimingWellFormed
              right

      rw [
        inductionHypothesis
      ]

      constructor

      · intro hParts

        exact
          ⟨⟨hParts.1,
             hParts.2.1⟩,
           hParts.2.2⟩

      · intro hParts

        exact
          ⟨hParts.1.1,
           hParts.1.2,
           hParts.2⟩

end Body

namespace MultiStoreModel

/--
Model-level timing assumption for priority-preserving execution
correspondence.

The constructor and every declared message-server body must use only
strictly positive self-send delays.

This is intentionally separate from ordinary structural
well-formedness so models without priority-sensitive claims retain the
existing zero-delay semantics.
-/
structure PriorityTimingWellFormed
    (model : DTR.MultiStoreModel) :
    Prop where

  constructorBody :
    DTR.Body.PriorityTimingWellFormed
      model.reactiveClass.constructor.body

  messageServerBodies :
    ∀ messageServer,
      messageServer ∈
          model.reactiveClass.messageServers →
      DTR.Body.PriorityTimingWellFormed
        messageServer.body

end MultiStoreModel
end DTR
end Relico
