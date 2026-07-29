import Relico.DTR.MultiStorePayloadPriority
import Relico.LF.MultiStorePayloadSyntax
import Relico.Translation.StoreBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Compile one payload-aware finite-store expression.
-/
def compileMultiStorePayloadExpr :
    DTR.MultiStorePayloadExpr →
    LF.MultiStorePayloadExpr

  | .intLiteral value =>
      .intLiteral value

  | .stateVar variableName =>
      .stateVar variableName

  | .parameterVar parameterName =>
      .parameterVar parameterName

/--
Compile an ordered payload-expression list componentwise.
-/
def compileMultiStorePayloadExprs
    (expressions :
      List DTR.MultiStorePayloadExpr) :
    List LF.MultiStorePayloadExpr :=
  expressions.map
    compileMultiStorePayloadExpr

/--
Compile one payload-aware finite-store statement.
-/
def compileMultiStorePayloadStmt :
    DTR.MultiStorePayloadStmt →
    LF.MultiStorePayloadStmt

  | .assign
      target
      expression =>

      .assign
        target
        (compileMultiStorePayloadExpr
          expression)

  | .selfSend
      messageName
      payloadExpressions
      delay =>

      .schedule
        (actionNameFor
          messageName)
        (compileMultiStorePayloadExprs
          payloadExpressions)
        delay

/--
Compile a complete payload-aware body without reordering statements or
payload components.
-/
def compileMultiStorePayloadBody
    (body :
      DTR.MultiStorePayloadBody) :
    LF.MultiStorePayloadBody :=
  body.map
    compileMultiStorePayloadStmt

/--
Generate the typed logical action associated with one source message
server.
-/
def compileMultiStorePayloadAction
    (messageServer :
      DTR.MultiStorePayloadMessageServer) :
    LF.MultiStorePayloadAction where

  name :=
    actionNameFor
      messageServer.name

  parameters :=
    messageServer.parameters

/--
Compile the source constructor into the generated startup reaction.
-/
def compileMultiStorePayloadStartupReaction
    (constructor :
      DTR.MultiStorePayloadConstructor) :
    LF.MultiStorePayloadReaction where

  name :=
    startupReactionName

  trigger :=
    .startup

  parameters :=
    []

  body :=
    compileMultiStorePayloadBody
      constructor.body

  priority :=
    none

/--
Compile one payload-aware message server into its generated logical-
action reaction. Formal-parameter order and priority metadata are
preserved exactly.
-/
def compileMultiStorePayloadReaction
    (messageServer :
      DTR.MultiStorePayloadMessageServer) :
    LF.MultiStorePayloadReaction where

  name :=
    messageReactionNameFor
      messageServer.name

  trigger :=
    .logicalAction
      (actionNameFor
        messageServer.name)

  parameters :=
    messageServer.parameters

  body :=
    compileMultiStorePayloadBody
      messageServer.body

  priority :=
    messageServer.priority

/--
The source-server order used for generated actions and reactions.
-/
def priorityOrderedMultiStorePayloadMessageServers
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    List DTR.MultiStorePayloadMessageServer :=
  DTR.MultiStorePayloadMessageServerPriority.normalize
    messageServers

/--
Compile the local message-server list into exactly the generated
message-reaction declaration order.

This helper names the reaction list already constructed by
`compileMultiStorePayloadReactor`; it introduces no new ordering policy.
-/
def compileMultiStorePayloadMessageReactions
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    List LF.MultiStorePayloadReaction :=
  (priorityOrderedMultiStorePayloadMessageServers
      messageServers).map
    compileMultiStorePayloadReaction

/--
Compile a one-actor payload-aware class into one generated payload-aware
reactor. Actions and reactions are generated from the same normalized
server list.
-/
def compileMultiStorePayloadReactor
    (reactiveClass :
      DTR.MultiStorePayloadReactiveClass) :
    LF.MultiStorePayloadReactor :=
  let orderedMessageServers :=
    priorityOrderedMultiStorePayloadMessageServers
      reactiveClass.messageServers

  {
    name :=
      reactorNameFor
        reactiveClass.name

    stateVariables :=
      compileStateVariableDecls
        reactiveClass.stateVariables

    logicalActions :=
      orderedMessageServers.map
        compileMultiStorePayloadAction

    startupReaction :=
      compileMultiStorePayloadStartupReaction
        reactiveClass.constructor

    messageReactions :=
      orderedMessageServers.map
        compileMultiStorePayloadReaction
  }

/--
Executable structural core for the local Option-C foundation.

Correctness theorems over this core will require explicit source
well-formedness, including distinct local message-server priorities.
-/
def translateMultiStorePayloadCore
    (model :
      DTR.MultiStorePayloadModel) :
    LF.MultiStorePayloadProgram where

  reactor :=
    compileMultiStorePayloadReactor
      model.reactiveClass

  reactorInstance :=
    compileReactorInstance
      model.actor

@[simp]
theorem compileMultiStorePayloadExprs_nil :
    compileMultiStorePayloadExprs [] =
      [] := by
  rfl

@[simp]
theorem compileMultiStorePayloadExprs_cons
    (expression :
      DTR.MultiStorePayloadExpr)
    (remaining :
      List DTR.MultiStorePayloadExpr) :
    compileMultiStorePayloadExprs
        (expression :: remaining) =
      compileMultiStorePayloadExpr
          expression ::
        compileMultiStorePayloadExprs
          remaining := by
  rfl

@[simp]
theorem compileMultiStorePayloadReaction_parameters
    (messageServer :
      DTR.MultiStorePayloadMessageServer) :
    (compileMultiStorePayloadReaction
      messageServer).parameters =
      messageServer.parameters := by
  rfl

@[simp]
theorem compileMultiStorePayloadReaction_priority
    (messageServer :
      DTR.MultiStorePayloadMessageServer) :
    (compileMultiStorePayloadReaction
      messageServer).priority =
      messageServer.priority := by
  rfl


/--
The priority-ordered source declaration list contains exactly the declarations
of the original message-server list.
-/
theorem priorityOrderedMultiStorePayloadMessageServers_mem_iff
    (candidate :
      DTR.MultiStorePayloadMessageServer)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    candidate ∈
        priorityOrderedMultiStorePayloadMessageServers
          messageServers ↔
      candidate ∈
        messageServers := by

  simpa [
    priorityOrderedMultiStorePayloadMessageServers
  ] using
    DTR.MultiStorePayloadMessageServerPriority.mem_normalize_iff
      candidate
      messageServers

/--
Every declared payload-aware message server generates a reaction occurrence.
-/
theorem compileMultiStorePayloadReaction_mem
    {messageServer :
      DTR.MultiStorePayloadMessageServer}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hMember :
      messageServer ∈
        messageServers) :
    compileMultiStorePayloadReaction
          messageServer ∈
        compileMultiStorePayloadMessageReactions
          messageServers := by

  apply
    List.mem_map.mpr

  exact
    ⟨messageServer,
     (priorityOrderedMultiStorePayloadMessageServers_mem_iff
        messageServer
        messageServers).mpr
          hMember,
     rfl⟩

/--
Every generated payload-aware reaction occurrence originates from a declared
source message server.
-/
theorem mem_compileMultiStorePayloadMessageReactions
    {reaction :
      LF.MultiStorePayloadReaction}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hMember :
      reaction ∈
        compileMultiStorePayloadMessageReactions
          messageServers) :
    ∃ messageServer,
      messageServer ∈
          messageServers ∧
        compileMultiStorePayloadReaction
            messageServer =
          reaction := by

  simp only [
    compileMultiStorePayloadMessageReactions,
    List.mem_map
  ] at hMember

  rcases hMember with
    ⟨messageServer,
     hOrderedMember,
     hReaction⟩

  exact
    ⟨messageServer,
     (priorityOrderedMultiStorePayloadMessageServers_mem_iff
        messageServer
        messageServers).mp
          hOrderedMember,
     hReaction⟩

end Translation
end Relico
