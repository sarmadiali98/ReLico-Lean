import Relico.DTR.MessageServerPriority
import Relico.DTR.MultiStoreSyntax
import Relico.LF.MultiStoreSyntax
import Relico.Translation.StoreBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
The stable source-server order used for LF logical actions and message
reactions.

The source AST retains its original declaration list. Only the
generated order is normalized.
-/
def priorityOrderedMessageServers
    (messageServers :
      List DTR.MessageServer) :
    List DTR.MessageServer :=
  DTR.MessageServerPriority.normalize
    messageServers

@[simp]
theorem priorityOrderedMessageServers_mem_iff
    (messageServer : DTR.MessageServer)
    (messageServers :
      List DTR.MessageServer) :
    messageServer ∈
        priorityOrderedMessageServers
          messageServers ↔
      messageServer ∈
        messageServers := by

  exact
    DTR.MessageServerPriority.mem_normalize_iff
      messageServer
      messageServers

@[simp]
theorem priorityOrderedMessageServers_length
    (messageServers :
      List DTR.MessageServer) :
    (priorityOrderedMessageServers
      messageServers).length =
      messageServers.length := by

  exact
    DTR.MessageServerPriority.length_normalize
      messageServers

/--
Generate one LF logical-action name for each source message server in
stable local-priority order.
-/
def compileLogicalActions
    (messageServers :
      List DTR.MessageServer) :
    List ActionName :=
  (priorityOrderedMessageServers
    messageServers).map
      (fun messageServer =>
        actionNameFor
          messageServer.name)

/--
Generate one LF reaction for each source message server in the same
stable local-priority order as the logical actions.
-/
def compileMessageReactions
    (messageServers :
      List DTR.MessageServer) :
    List LF.Reaction :=
  (priorityOrderedMessageServers
    messageServers).map
      compileMessageReaction

@[simp]
theorem compileLogicalActions_names
    (messageServers :
      List DTR.MessageServer) :
    compileLogicalActions
        messageServers =
      (DTR.messageServerNames
        (priorityOrderedMessageServers
          messageServers)).map
            actionNameFor := by

  simp [
    compileLogicalActions,
    DTR.messageServerNames,
    List.map_map
  ]

@[simp]
theorem compileLogicalActions_length
    (messageServers :
      List DTR.MessageServer) :
    (compileLogicalActions
      messageServers).length =
      messageServers.length := by

  simp [
    compileLogicalActions
  ]

theorem compileLogicalActions_ne_nil
    {messageServers :
      List DTR.MessageServer}
    (hMessageServers :
      messageServers ≠
        []) :
    compileLogicalActions
        messageServers ≠
      [] := by

  intro hEmpty

  cases messageServers with

  | nil =>
      exact
        hMessageServers
          rfl

  | cons messageServer remaining =>
      have hLength :
          (compileLogicalActions
            (messageServer ::
              remaining)).length =
            (messageServer ::
              remaining).length :=

        compileLogicalActions_length
          (messageServer ::
            remaining)

      rw [
        hEmpty
      ] at hLength

      simp at hLength

/--
Recover the original source declaration associated with a generated
logical-action occurrence.
-/
theorem mem_compileLogicalActions
    {logicalAction : ActionName}
    {messageServers :
      List DTR.MessageServer}
    (hMember :
      logicalAction ∈
        compileLogicalActions
          messageServers) :
    ∃ messageServer,
      messageServer ∈
          messageServers ∧
        actionNameFor
            messageServer.name =
          logicalAction := by

  simp only [
    compileLogicalActions,
    List.mem_map
  ] at hMember

  rcases hMember with
    ⟨messageServer,
     hOrderedMember,
     hAction⟩

  exact
    ⟨messageServer,
     (priorityOrderedMessageServers_mem_iff
        messageServer
        messageServers).mp
          hOrderedMember,
     hAction⟩

/--
Generated logical-action membership is equivalent to membership of the
corresponding source message-server name.
-/
theorem actionName_mem_compileLogicalActions_iff
    (messageName : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    actionNameFor
          messageName ∈
        compileLogicalActions
          messageServers ↔
      messageName ∈
        DTR.messageServerNames
          messageServers := by

  constructor

  · intro hMember

    rcases
        mem_compileLogicalActions
          hMember
      with
        ⟨messageServer,
         hServerMember,
         hAction⟩

    have hName :
        messageServer.name =
          messageName :=

      actionNameFor_injective
        hAction

    apply
      List.mem_map.mpr

    exact
      ⟨messageServer,
       hServerMember,
       hName⟩

  · intro hMember

    rcases
        List.mem_map.mp
          hMember
      with
        ⟨messageServer,
         hServerMember,
         hName⟩

    apply
      List.mem_map.mpr

    exact
      ⟨messageServer,
       (priorityOrderedMessageServers_mem_iff
          messageServer
          messageServers).mpr
            hServerMember,
       congrArg
         actionNameFor
         hName⟩

@[simp]
theorem compileMessageReactions_length
    (messageServers :
      List DTR.MessageServer) :
    (compileMessageReactions
      messageServers).length =
      messageServers.length := by

  simp [
    compileMessageReactions
  ]

/--
Every declared source server has its compiled reaction in the
priority-ordered target list.
-/
theorem compileMessageReaction_mem
    {messageServer : DTR.MessageServer}
    {messageServers :
      List DTR.MessageServer}
    (hMember :
      messageServer ∈
        messageServers) :
    compileMessageReaction
          messageServer ∈
        compileMessageReactions
          messageServers := by

  apply
    List.mem_map.mpr

  exact
    ⟨messageServer,
     (priorityOrderedMessageServers_mem_iff
        messageServer
        messageServers).mpr
          hMember,
     rfl⟩

/--
Recover the original source declaration associated with a compiled
reaction occurrence.
-/
theorem mem_compileMessageReactions
    {reaction : LF.Reaction}
    {messageServers :
      List DTR.MessageServer}
    (hMember :
      reaction ∈
        compileMessageReactions
          messageServers) :
    ∃ messageServer,
      messageServer ∈
          messageServers ∧
        compileMessageReaction
            messageServer =
          reaction := by

  simp only [
    compileMessageReactions,
    List.mem_map
  ] at hMember

  rcases hMember with
    ⟨messageServer,
     hOrderedMember,
     hReaction⟩

  exact
    ⟨messageServer,
     (priorityOrderedMessageServers_mem_iff
        messageServer
        messageServers).mp
          hOrderedMember,
     hReaction⟩

/--
Compile the constructor into the generated startup reaction.
-/
def compileMultiStoreStartupReaction
    (constructor : DTR.Constructor) :
    LF.Reaction where

  name :=
    startupReactionName

  trigger :=
    .startup

  body :=
    compileBody
      constructor.body

/--
Compile a finite-state, multiple-message-server DTR class into one LF
reactor.

Logical actions and message reactions use the same stable
priority-normalized source list.
-/
def compileMultiStoreReactor
    (reactiveClass :
      DTR.MultiStoreReactiveClass) :
    LF.MultiStoreReactor where

  name :=
    reactorNameFor
      reactiveClass.name

  stateVariables :=
    compileStateVariableDecls
      reactiveClass.stateVariables

  logicalActions :=
    compileLogicalActions
      reactiveClass.messageServers

  startupReaction :=
    compileMultiStoreStartupReaction
      reactiveClass.constructor

  messageReactions :=
    compileMessageReactions
      reactiveClass.messageServers

/--
Executable core translation for the one-actor, multiple-message-server
finite-store model.
-/
def translateMultiStoreCore
    (model : DTR.MultiStoreModel) :
    LF.MultiStoreProgram where

  reactor :=
    compileMultiStoreReactor
      model.reactiveClass

  reactorInstance :=
    compileReactorInstance
      model.actor

/--
Public executable translation entry point for multiple-message-server
finite-store models.
-/
def translateMultiStore
    (model : DTR.MultiStoreModel) :
    Except
      TranslationError
      LF.MultiStoreProgram :=
  .ok
    (translateMultiStoreCore
      model)

@[simp]
theorem translateMultiStore_eq_ok
    (model : DTR.MultiStoreModel) :
    translateMultiStore model =
      .ok
        (translateMultiStoreCore
          model) := by
  rfl

theorem translateMultiStore_succeeds
    (model : DTR.MultiStoreModel) :
    ∃ program,
      translateMultiStore model =
        .ok program := by

  exact
    ⟨translateMultiStoreCore model,
     rfl⟩

/--
The multi-server translator remains an exact conservative extension of
the verified finite-store translator for singleton server lists.
-/
theorem translateMultiStoreCore_singleton
    (model : DTR.StoreModel) :
    translateMultiStoreCore
        (DTR.StoreModel.toMultiStoreModel
          model) =
      LF.StoreProgram.toMultiStoreProgram
        (translateStoreCore
          model) := by
  rfl

end Translation
end Relico
