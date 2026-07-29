import Relico.DTR.MultiStorePayloadDispatch
import Relico.LF.MultiStorePayloadDispatch
import Relico.Translation.MultiStorePayloadBasic

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
theorem multiStorePayloadServerNamePrecedesOrEqual_compileMessageReactions
    (left right :
      MsgName)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    DTR.MultiStorePayloadServerNamePrecedesOrEqual
        left
        right
        messageServers ↔
      LF.MultiStorePayloadReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          left)
        (Translation.actionNameFor
          right)
        (messageServers.map
          Translation.compileMultiStorePayloadReaction) := by

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
          DTR.multiStorePayloadServerNamePrecedesOrEqual_cons,
          LF.multiStorePayloadReactionActionPrecedesOrEqual_cons,
          Translation.compileMultiStorePayloadReaction,
          hLeft,
          hActionLeft
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

        · have hActionRight :
              Translation.actionNameFor
                  current.name =
                Translation.actionNameFor
                  right :=
            congrArg
              Translation.actionNameFor
              hRight

          have hRightNotLeft :
              right ≠
                left := by

            intro hNames

            apply hLeft

            calc
              current.name =
                  right :=
                hRight

              _ =
                  left :=
                hNames

          have hActionRightNotLeft :
              Translation.actionNameFor
                  right ≠
                Translation.actionNameFor
                  left := by

            intro hActions

            exact
              hRightNotLeft
                (Translation.actionNameFor_injective
                  hActions)

          simp [
            DTR.multiStorePayloadServerNamePrecedesOrEqual_cons,
            LF.multiStorePayloadReactionActionPrecedesOrEqual_cons,
            Translation.compileMultiStorePayloadReaction,
            hLeft,
            hRight,
            hActionLeft,
            hActionRight,
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

          simp [
            DTR.multiStorePayloadServerNamePrecedesOrEqual_cons,
            LF.multiStorePayloadReactionActionPrecedesOrEqual_cons,
            Translation.compileMultiStorePayloadReaction,
            hLeft,
            hRight,
            hActionLeft,
            hActionRight,
            inductionHypothesis
          ]

/--
Priority normalization on the source side is exactly the declaration
order used by the generated Option-C message reactions.
-/
theorem multiStorePayloadPriorityServerNamePrecedesOrEqual_compileMessageReactions
    (left right : MsgName)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
        left
        right
        messageServers ↔
      LF.MultiStorePayloadReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          left)
        (Translation.actionNameFor
          right)
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers) := by

  simpa [
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual,
    Translation.compileMultiStorePayloadMessageReactions,
    Translation.priorityOrderedMultiStorePayloadMessageServers
  ] using
    multiStorePayloadServerNamePrecedesOrEqual_compileMessageReactions
      left
      right
      (DTR.MultiStorePayloadMessageServerPriority.normalize
        messageServers)

/--
Forward transport from normalized DTR server order to generated LF
reaction order.
-/
theorem multiStorePayloadPriorityServerOrder_implies_reactionOrder
    {left right : MsgName}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hOrder :
      DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
        left
        right
        messageServers) :
    LF.MultiStorePayloadReactionActionPrecedesOrEqual
      (Translation.actionNameFor
        left)
      (Translation.actionNameFor
        right)
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers) :=

  (multiStorePayloadPriorityServerNamePrecedesOrEqual_compileMessageReactions
    left
    right
    messageServers).mp
      hOrder

/--
Backward transport from generated LF reaction order to normalized DTR
server order.
-/
theorem multiStorePayloadReactionOrder_implies_priorityServerOrder
    {left right : MsgName}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hOrder :
      LF.MultiStorePayloadReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          left)
        (Translation.actionNameFor
          right)
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      left
      right
      messageServers :=

  (multiStorePayloadPriorityServerNamePrecedesOrEqual_compileMessageReactions
    left
    right
    messageServers).mpr
      hOrder

end Correctness
end Relico
