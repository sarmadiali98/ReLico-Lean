import Relico.DTR.MultiStorePriorityScheduling
import Relico.LF.MultiStoreReactionScheduling
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compiling a server list into logical-action reactions preserves the
name-scan order exactly.

No uniqueness premise is required. Both relations scan the same list,
and generated logical-action names are injective in source message
names.
-/
theorem serverNamePrecedesOrEqual_compileMessageReactions
    (left right : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    DTR.ServerNamePrecedesOrEqual
        left
        right
        messageServers ↔
      LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          left)
        (Translation.actionNameFor
          right)
        (messageServers.map
          Translation.compileMessageReaction) := by

  induction messageServers with

  | nil =>
      simp

  | cons current remaining inductionHypothesis =>
      by_cases hLeft :
          current.name =
            left

      · have hActionLeft :
            Translation.actionNameFor
                current.name =
              Translation.actionNameFor
                left :=

          congrArg
            Translation.actionNameFor
            hLeft

        simp [
          Translation.compileMessageReaction,
          hLeft
        ]

      · have hActionLeft :
            Translation.actionNameFor
                current.name ≠
              Translation.actionNameFor
                left := by

          intro hEqual

          exact
            hLeft
              (Translation.actionNameFor_injective
                hEqual)

        by_cases hRight :
            current.name =
              right

        · have hRightNotLeft :
              right ≠
                left := by

            intro hEqual

            exact
              hLeft
                (hRight.trans
                  hEqual)

          have hActionRightNotLeft :
              Translation.actionNameFor
                  right ≠
                Translation.actionNameFor
                  left := by

            intro hEqual

            exact
              hRightNotLeft
                (Translation.actionNameFor_injective
                  hEqual)

          simp [
            Translation.compileMessageReaction,
            hRight,
            hRightNotLeft,
            hActionRightNotLeft
          ]

        · have hActionRight :
              Translation.actionNameFor
                  current.name ≠
                Translation.actionNameFor
                  right := by

            intro hEqual

            exact
              hRight
                (Translation.actionNameFor_injective
                  hEqual)

          simpa [
            Translation.compileMessageReaction,
            hLeft,
            hRight,
            hActionLeft,
            hActionRight
          ] using
            inductionHypothesis

/--
Stable source priority order is exactly the reaction declaration order
produced by the executable multi-server translator.
-/
theorem priorityServerNamePrecedesOrEqual_compileMessageReactions
    (left right : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    DTR.PriorityServerNamePrecedesOrEqual
        left
        right
        messageServers ↔
      LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          left)
        (Translation.actionNameFor
          right)
        (Translation.compileMessageReactions
          messageServers) := by

  simpa [
    DTR.PriorityServerNamePrecedesOrEqual,
    Translation.compileMessageReactions,
    Translation.priorityOrderedMessageServers
  ] using
    serverNamePrecedesOrEqual_compileMessageReactions
      left
      right
      (DTR.MessageServerPriority.normalize
        messageServers)

/--
Forward transport from normalized DTR server order to generated LF
reaction order.
-/
theorem priorityServerOrder_implies_reactionOrder
    {left right : MsgName}
    {messageServers :
      List DTR.MessageServer}
    (hOrder :
      DTR.PriorityServerNamePrecedesOrEqual
        left
        right
        messageServers) :
    LF.ReactionActionPrecedesOrEqual
      (Translation.actionNameFor
        left)
      (Translation.actionNameFor
        right)
      (Translation.compileMessageReactions
        messageServers) :=

  (priorityServerNamePrecedesOrEqual_compileMessageReactions
    left
    right
    messageServers).mp
      hOrder

/--
Backward transport from generated LF reaction order to normalized DTR
server order.
-/
theorem reactionOrder_implies_priorityServerOrder
    {left right : MsgName}
    {messageServers :
      List DTR.MessageServer}
    (hOrder :
      LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          left)
        (Translation.actionNameFor
          right)
        (Translation.compileMessageReactions
          messageServers)) :
    DTR.PriorityServerNamePrecedesOrEqual
      left
      right
      messageServers :=

  (priorityServerNamePrecedesOrEqual_compileMessageReactions
    left
    right
    messageServers).mpr
      hOrder

end Correctness
end Relico
