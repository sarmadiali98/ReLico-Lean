import Relico.DTR.WellFormed

set_option autoImplicit false

namespace Relico
namespace Tests

def controllerClassName : ClassName :=
  ⟨"Controller"⟩

def controllerActorName : ActorName :=
  ⟨"controller"⟩

def stateVariableName : VarName :=
  ⟨"x"⟩

def tickMessageName : MsgName :=
  ⟨"tick"⟩

def validConstructor : DTR.Constructor where
  body := [
    .assign stateVariableName (.intLiteral 0),
    .selfSend tickMessageName { value := 1 }
  ]

def validMessageServer : DTR.MessageServer where
  name := tickMessageName
  body := [
    .assign stateVariableName (.stateVar stateVariableName),
    .selfSend tickMessageName { value := 1 }
  ]

def validReactiveClass : DTR.ReactiveClass where
  name := controllerClassName
  stateVar := stateVariableName
  constructor := validConstructor
  messageServer := validMessageServer

def validActor : DTR.ActorInstance where
  name := controllerActorName
  className := controllerClassName

def validModel : DTR.Model where
  reactiveClass := validReactiveClass
  actor := validActor

theorem validModel_wellFormed :
    DTR.Model.WellFormed validModel := by
  refine {
    classNameValid := ?_
    actorNameValid := ?_
    stateVarNameValid := ?_
    messageServerNameValid := ?_
    actorClassMatches := ?_
    constructorBodyWellFormed := ?_
    messageServerBodyWellFormed := ?_
  }
  · simp [
      validModel,
      validReactiveClass,
      controllerClassName,
      ClassName.isValid
    ]
  · simp [
      validModel,
      validActor,
      controllerActorName,
      ActorName.isValid
    ]
  · simp [
      validModel,
      validReactiveClass,
      stateVariableName,
      VarName.isValid
    ]
  · simp [
      validModel,
      validReactiveClass,
      validMessageServer,
      tickMessageName,
      MsgName.isValid
    ]
  · rfl
  · simp [
      validModel,
      validReactiveClass,
      validConstructor,
      validMessageServer,
      tickMessageName,
      stateVariableName,
      DTR.Body.WellFormed,
      DTR.Stmt.WellFormed,
      DTR.Expr.WellFormed
    ]
  · simp [
      validModel,
      validReactiveClass,
      validMessageServer,
      DTR.Body.WellFormed,
      DTR.Stmt.WellFormed,
      DTR.Expr.WellFormed
    ]

def emptyClassNameModel : DTR.Model :=
  {
    validModel with
    reactiveClass := {
      validReactiveClass with
      name := ⟨""⟩
    }
  }

theorem emptyClassNameModel_not_wellFormed :
    ¬ DTR.Model.WellFormed emptyClassNameModel := by
  intro h
  exact h.classNameValid rfl

def otherClassName : ClassName :=
  ⟨"OtherController"⟩

def wrongActorClassModel : DTR.Model :=
  {
    validModel with
    actor := {
      validActor with
      className := otherClassName
    }
  }

theorem wrongActorClassModel_not_wellFormed :
    ¬ DTR.Model.WellFormed wrongActorClassModel := by
  intro h
  have hDifferent :
      otherClassName ≠ controllerClassName := by
    decide
  apply hDifferent
  simpa [
    wrongActorClassModel,
    validModel,
    validActor,
    validReactiveClass
  ] using h.actorClassMatches

def otherMessageName : MsgName :=
  ⟨"otherMessage"⟩

def invalidSelfSendConstructor : DTR.Constructor where
  body := [
    .selfSend otherMessageName { value := 0 }
  ]

def invalidSelfSendModel : DTR.Model :=
  {
    validModel with
    reactiveClass := {
      validReactiveClass with
      constructor := invalidSelfSendConstructor
    }
  }

theorem invalidSelfSendModel_not_wellFormed :
    ¬ DTR.Model.WellFormed invalidSelfSendModel := by
  intro h

  have hStatement :=
    h.constructorBodyWellFormed
      (.selfSend otherMessageName { value := 0 })
      (by
        simp [
          invalidSelfSendModel,
          invalidSelfSendConstructor,
          validReactiveClass,
          validModel
        ])

  have hNamesEqual :
      otherMessageName = tickMessageName := by
    simpa [
      invalidSelfSendModel,
      validModel,
      validReactiveClass,
      validMessageServer,
      DTR.Stmt.WellFormed
    ] using hStatement

  have hDifferent :
      otherMessageName ≠ tickMessageName := by
    decide

  exact hDifferent hNamesEqual

end Tests
end Relico
