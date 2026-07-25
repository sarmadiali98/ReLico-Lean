import Relico.DTR.MultiStoreModelWellFormed
import Relico.LF.MultiStoreModelWellFormed
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

private theorem nodup_map_of_injective
    {α β : Type}
    (function : α → β)
    (hInjective :
      Function.Injective
        function)
    {values : List α}
    (hValues :
      values.Nodup) :
    (values.map
      function).Nodup := by

  induction values with

  | nil =>
      simp

  | cons value remaining inductionHypothesis =>
      cases hValues with

      | cons hHead hTail =>
          constructor

          · intro mappedValue hMappedMember hEqual

            rcases
                List.mem_map.mp
                  hMappedMember
              with
                ⟨sourceValue,
                 hSourceMember,
                 hMappedValue⟩

            apply
              hHead
                sourceValue
                hSourceMember

            apply hInjective

            exact
              hEqual.trans
                hMappedValue.symm

          · exact
              inductionHypothesis
                hTail

private theorem compileMessageReactionNames
    (messageServers : List DTR.MessageServer) :
    LF.reactionNames
        (Translation.compileMessageReactions
          messageServers) =
      (DTR.messageServerNames
        messageServers).map
          Translation.messageReactionNameFor := by

  simp [
    LF.reactionNames,
    Translation.compileMessageReactions,
    Translation.compileMessageReaction,
    DTR.messageServerNames,
    List.map_map
  ]

theorem compileExpr_multiStoreWellFormed
    {declaredVariables : List VarName}
    {expression : DTR.Expr}
    (hExpression :
      DTR.Expr.StoreWellFormed
        declaredVariables
        expression) :
    LF.Expr.StoreWellFormed
      declaredVariables
      (Translation.compileExpr
        expression) := by

  cases expression with

  | intLiteral value =>
      trivial

  | stateVar referencedVariable =>
      exact hExpression

theorem compileStmt_multiStoreWellFormed
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {statement : DTR.Stmt}
    (hStatement :
      DTR.Stmt.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        statement) :
    LF.Stmt.MultiStoreWellFormed
      declaredVariables
      (Translation.compileLogicalActions
        messageServers)
      (Translation.compileStmt
        statement) := by

  cases statement with

  | assign target expression =>
      rcases hStatement with
        ⟨hTarget, hExpression⟩

      exact
        ⟨hTarget,
         compileExpr_multiStoreWellFormed
           hExpression⟩

  | selfSend targetMessage delay =>
      change
        Translation.actionNameFor
            targetMessage ∈
          Translation.compileLogicalActions
            messageServers

      have hMapped :
          Translation.actionNameFor
              targetMessage ∈
            (DTR.messageServerNames
              messageServers).map
                Translation.actionNameFor :=
        List.mem_map_of_mem
          hStatement

      simpa only [
        Translation.compileLogicalActions_names
      ] using
        hMapped

theorem compileBody_multiStoreWellFormed
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {body : DTR.Body}
    (hBody :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        body) :
    LF.Body.MultiStoreWellFormed
      declaredVariables
      (Translation.compileLogicalActions
        messageServers)
      (Translation.compileBody
        body) := by

  intro compiledStatement hCompiledStatement

  simp only [
    Translation.compileBody,
    List.mem_map
  ] at hCompiledStatement

  rcases hCompiledStatement with
    ⟨sourceStatement,
     hSourceStatement,
     rfl⟩

  exact
    compileStmt_multiStoreWellFormed
      (hBody
        sourceStatement
        hSourceStatement)

/--
Compilation preserves structural validity of a finite-state,
multiple-message-server reactor.
-/
theorem compileMultiStoreReactor_wellFormed
    {reactiveClass : DTR.MultiStoreReactiveClass}
    (hClassName :
      ClassName.isValid
        reactiveClass.name)
    (hStateVariableNames :
      ∀ declaration,
        declaration ∈
          reactiveClass.stateVariables →
        VarName.isValid
          declaration.name)
    (hStateVariableNamesUnique :
      (DTR.stateVariableNames
        reactiveClass.stateVariables).Nodup)
    (hMessageServersNonempty :
      reactiveClass.messageServers ≠
        [])
    (_hMessageServerNames :
      ∀ messageServer,
        messageServer ∈
          reactiveClass.messageServers →
        MsgName.isValid
          messageServer.name)
    (hMessageServerNamesUnique :
      (DTR.messageServerNames
        reactiveClass.messageServers).Nodup)
    (hConstructorBody :
      DTR.Body.MultiStoreWellFormed
        (DTR.stateVariableNames
          reactiveClass.stateVariables)
        (DTR.messageServerNames
          reactiveClass.messageServers)
        reactiveClass.constructor.body)
    (hMessageBodies :
      ∀ messageServer,
        messageServer ∈
          reactiveClass.messageServers →
        DTR.Body.MultiStoreWellFormed
          (DTR.stateVariableNames
            reactiveClass.stateVariables)
          (DTR.messageServerNames
            reactiveClass.messageServers)
          messageServer.body) :
    LF.MultiStoreReactor.WellFormed
      (Translation.compileMultiStoreReactor
        reactiveClass) := by

  refine {
    reactorNameValid := ?_
    stateVariableNamesValid := ?_
    stateVariableNamesUnique := ?_
    logicalActionsNonempty := ?_
    logicalActionNamesValid := ?_
    logicalActionNamesUnique := ?_
    startupReactionNameValid := ?_
    startupTriggerCorrect := ?_
    startupBodyWellFormed := ?_
    messageReactionNamesValid := ?_
    messageReactionNamesUnique := ?_
    messageReactionTriggersCorrect := ?_
    messageReactionBodiesWellFormed := ?_
  }

  · simpa [
      Translation.compileMultiStoreReactor,
      Translation.reactorNameFor,
      ReactorName.isValid,
      ClassName.isValid
    ] using
      hClassName

  · intro targetDeclaration hTargetDeclaration

    change
      targetDeclaration ∈
        Translation.compileStateVariableDecls
          reactiveClass.stateVariables
      at hTargetDeclaration

    simp only [
      Translation.compileStateVariableDecls,
      List.mem_map
    ] at hTargetDeclaration

    rcases hTargetDeclaration with
      ⟨sourceDeclaration,
       hSourceDeclaration,
       rfl⟩

    simpa [
      Translation.compileStateVariableDecl
    ] using
      hStateVariableNames
        sourceDeclaration
        hSourceDeclaration

  · simpa [
      Translation.compileMultiStoreReactor
    ] using
      hStateVariableNamesUnique

  · simpa [
      Translation.compileMultiStoreReactor,
      Translation.compileLogicalActions
    ] using
      hMessageServersNonempty

  · intro logicalAction hLogicalAction

    change
      logicalAction ∈
        Translation.compileLogicalActions
          reactiveClass.messageServers
      at hLogicalAction

    simp only [
      Translation.compileLogicalActions,
      List.mem_map
    ] at hLogicalAction

    rcases hLogicalAction with
      ⟨messageServer,
       hMessageServer,
       rfl⟩

    simp [
      Translation.actionNameFor,
      ActionName.isValid
    ]

  · change
      (Translation.compileLogicalActions
        reactiveClass.messageServers).Nodup

    simpa only [
      Translation.compileLogicalActions_names
    ] using
      nodup_map_of_injective
        Translation.actionNameFor
        Translation.actionNameFor_injective
        hMessageServerNamesUnique

  · simp [
      Translation.compileMultiStoreReactor,
      Translation.compileMultiStoreStartupReaction,
      Translation.startupReactionName,
      ReactionName.isValid
    ]

  · rfl

  · simpa [
      Translation.compileMultiStoreReactor,
      Translation.compileMultiStoreStartupReaction
    ] using
      compileBody_multiStoreWellFormed
        hConstructorBody

  · intro reaction hReaction

    change
      reaction ∈
        Translation.compileMessageReactions
          reactiveClass.messageServers
      at hReaction

    simp only [
      Translation.compileMessageReactions,
      List.mem_map
    ] at hReaction

    rcases hReaction with
      ⟨messageServer,
       hMessageServer,
       rfl⟩

    simp [
      Translation.compileMessageReaction,
      Translation.messageReactionNameFor,
      ReactionName.isValid
    ]

  · change
      (LF.reactionNames
        (Translation.compileMessageReactions
          reactiveClass.messageServers)).Nodup

    rw [
      compileMessageReactionNames
    ]

    exact
      nodup_map_of_injective
        Translation.messageReactionNameFor
        Translation.messageReactionNameFor_injective
        hMessageServerNamesUnique

  · simp [
      LF.reactionTriggers,
      Translation.compileMultiStoreReactor,
      Translation.compileMessageReactions,
      Translation.compileLogicalActions,
      Translation.compileMessageReaction,
      List.map_map
    ]

  · intro reaction hReaction

    change
      reaction ∈
        Translation.compileMessageReactions
          reactiveClass.messageServers
      at hReaction

    simp only [
      Translation.compileMessageReactions,
      List.mem_map
    ] at hReaction

    rcases hReaction with
      ⟨messageServer,
       hMessageServer,
       rfl⟩

    simpa [
      Translation.compileMultiStoreReactor,
      Translation.compileMessageReaction
    ] using
      compileBody_multiStoreWellFormed
        (hMessageBodies
          messageServer
          hMessageServer)

/--
The executable multi-server compiler core preserves complete program
structural validity.
-/
theorem translateMultiStoreCore_wellFormed
    {model : DTR.MultiStoreModel}
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model) :
    LF.MultiStoreProgram.WellFormed
      (Translation.translateMultiStoreCore
        model) := by

  refine {
    reactorWellFormed := ?_
    instanceNameValid := ?_
    instanceReactorMatches := ?_
  }

  · exact
      compileMultiStoreReactor_wellFormed
        hModel.classNameValid
        hModel.stateVariableNamesValid
        hModel.stateVariableNamesUnique
        hModel.messageServersNonempty
        hModel.messageServerNamesValid
        hModel.messageServerNamesUnique
        hModel.constructorBodyWellFormed
        hModel.messageServerBodiesWellFormed

  · simpa [
      Translation.translateMultiStoreCore,
      Translation.compileReactorInstance
    ] using
      hModel.actorNameValid

  · simpa [
      Translation.translateMultiStoreCore,
      Translation.compileMultiStoreReactor,
      Translation.compileReactorInstance
    ] using
      congrArg
        Translation.reactorNameFor
        hModel.actorClassMatches

/--
Structural correctness of the public executable multi-server
translator.
-/
theorem translateMultiStore_wellFormed
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hTranslate :
      Translation.translateMultiStore model =
        .ok program) :
    LF.MultiStoreProgram.WellFormed
      program := by

  simp [
    Translation.translateMultiStore
  ] at hTranslate

  subst program

  exact
    translateMultiStoreCore_wellFormed
      hModel

end Correctness
end Relico
