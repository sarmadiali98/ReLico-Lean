import Relico.LF.PriorityTimingInvariant
import Relico.Correctness.MultiStorePayloadDetailedInitialization

set_option autoImplicit false
set_option pp.universes false
set_option pp.all false

namespace Relico

/-
Reference APIs used by the singleton construction.
-/

namespace DTR

/--
Canonical source occurrence for one external invocation of a declared
multi-store payload message server.
-/
def MultiStorePayloadMessageServer.invocationPendingMessage
    (server :
      DTR.MultiStorePayloadMessageServer)
    (payload :
      Payload)
    (delay :
      Delay) :
    DTR.PendingMessage :=
  DTR.PendingMessage.scheduleWithPayload
    0
    server.name
    payload
    delay

/--
Canonical source invocation state.

The persistent store is supplied explicitly. The state contains exactly one
pending message and has no activation-local parameters or active body.
-/
def MultiStorePayloadMessageServer.invocationMultiStorePayloadState
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    DTR.MultiStorePayloadState :=
  {
    currentTime :=
      0

    stateStore :=
      initialStateStore

    parameters :=
      ParameterStore.empty

    pendingMessages :=
      [
        server.invocationPendingMessage
          payload
          delay
      ]

    activeBody :=
      []
  }

/--
Stable detailed source wrapper for the canonical singleton invocation state.
-/
def MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    DTR.DetailedMultiStorePayloadState
      messageServers :=
  .stable
    (server.invocationMultiStorePayloadState
      initialStateStore
      payload
      delay)

end DTR

namespace LF

/--
Canonical generated-LF occurrence corresponding to one source invocation.

Its action name is generated directly from the selected source message-server
name. Payload order and values are unchanged.
-/
def invocationMultiStorePayloadPendingAction
    (server :
      DTR.MultiStorePayloadMessageServer)
    (payload :
      Payload)
    (delay :
      Delay) :
    LF.PendingAction :=
  LF.PendingAction.scheduleWithPayload
    ({ time := 0, microstep := 0 } : LF.Tag)
    (Translation.actionNameFor
      server.name)
    payload
    delay

/--
Canonical generated-LF singleton invocation state.
-/
def invocationLFMultiStorePayloadState
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    LF.MultiStorePayloadState :=
  {
    currentTag :=
      ({ time := 0, microstep := 0 } : LF.Tag)

    stateStore :=
      initialStateStore

    parameters :=
      ParameterStore.empty

    pendingActions :=
      [
        LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay
      ]

    activeBody :=
      []
  }

/--
Stable detailed generated-LF wrapper for the singleton invocation state.
-/
def invocationDetailedLFMultiStorePayloadState
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    LF.DetailedMultiStorePayloadState
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers) :=
  .stable
    (LF.invocationLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay)

end LF


namespace DTR

/--
Canonical source state after dispatching the singleton invocation.
-/
def MultiStorePayloadMessageServer.invocationDispatchedMultiStorePayloadState
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore) :
    DTR.MultiStorePayloadState :=
  {
    currentTime :=
      (server.invocationPendingMessage
        payload
        delay).arrivalTime

    stateStore :=
      initialStateStore

    parameters :=
      boundParameters

    pendingMessages :=
      []

    activeBody :=
      server.body
  }

end DTR

namespace LF

/--
Canonical generated-LF state after dispatching the singleton invocation.
-/
def invocationDispatchedLFMultiStorePayloadState
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore) :
    LF.MultiStorePayloadState :=
  {
    currentTag :=
      (LF.invocationMultiStorePayloadPendingAction
        server
        payload
        delay).tag

    stateStore :=
      initialStateStore

    parameters :=
      boundParameters

    pendingActions :=
      []

    activeBody :=
      (Translation.compileMultiStorePayloadReaction
        server).body
  }

end LF

namespace Correctness

/--
The canonical singleton source message and generated-LF action correspond
exactly, including payload order and values.
-/
theorem multiStorePayloadInvocationPending_correspond
    (server :
      DTR.MultiStorePayloadMessageServer)
    (payload :
      Payload)
    (delay :
      Delay) :
    PendingPayloadCorresponds
      (server.invocationPendingMessage
        payload
        delay)
      (LF.invocationMultiStorePayloadPendingAction
        server
        payload
        delay) := by

  exact
    pendingPayloadCorresponds_scheduleWithPayload
      0
      ({ time := 0, microstep := 0 } : LF.Tag)
      server.name
      payload
      delay
      rfl

/--
The singleton pending-message and pending-action collections correspond.
-/
theorem multiStorePayloadInvocationQueues_correspond
    (server :
      DTR.MultiStorePayloadMessageServer)
    (payload :
      Payload)
    (delay :
      Delay) :
    PayloadQueueCorresponds
      [
        server.invocationPendingMessage
          payload
          delay
      ]
      [
        LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay
      ] := by

  exact
    payloadQueueCorresponds_singleton
      (multiStorePayloadInvocationPending_correspond
        server
        payload
        delay)

/--
The canonical singleton invocation states satisfy the structural payload-aware
state correspondence.

This theorem deliberately stops before selection compatibility and the LF
pending-not-past runtime invariant.
-/
theorem multiStorePayloadInvocationStates_structurally_correspond
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadStateCorresponds
      (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay)
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay) := by

  exact
    {
      currentTime :=
        rfl

      stateStore :=
        rfl

      parameters :=
        rfl

      pendingQueues :=
        multiStorePayloadInvocationQueues_correspond
          server
          payload
          delay

      activeBody :=
        rfl
    }

/--
The singleton states preserve exactly the supplied persistent store.
-/
theorem multiStorePayloadInvocationStores
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay).stateStore =
      initialStateStore ∧
    (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).stateStore =
      initialStateStore := by

  simp [
    DTR.MultiStorePayloadMessageServer.invocationMultiStorePayloadState,
    LF.invocationLFMultiStorePayloadState
  ]

/--
Both invocation states are idle except for their corresponding singleton
pending occurrence.
-/
theorem multiStorePayloadInvocationStates_idle
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay).parameters =
      ParameterStore.empty ∧
    (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay).activeBody =
      [] ∧
    (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).parameters =
      ParameterStore.empty ∧
    (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).activeBody =
      [] := by

  simp [
    DTR.MultiStorePayloadMessageServer.invocationMultiStorePayloadState,
    LF.invocationLFMultiStorePayloadState
  ]


/--
The canonical singleton invocation queues satisfy the complete
permutation-invariant selection-compatibility relation.

The singleton lists are used as their own representatives. Any two aligned
occurrences are necessarily the same head occurrence, so the pairwise
scheduler obligation is discharged by equality of the target microsteps.
-/
theorem multiStorePayloadInvocationSelectionCompatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadSelectionCompatible
      messageServers
      [
        server.invocationPendingMessage
          payload
          delay
      ]
      [
        LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay
      ] := by

  refine
    ⟨ [server.invocationPendingMessage
          payload
          delay],
      [LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay],
      List.Perm.refl _,
      List.Perm.refl _,
      ?_ ⟩

  refine
    {
      selection :=
        {
          queues :=
            (multiStorePayloadInvocationQueues_correspond
              server
              payload
              delay).toQueueCorresponds

          pairwise := ?_
        }

      payloads :=
        multiStorePayloadInvocationQueues_correspond
          server
          payload
          delay
    }

  intro
    sourceLeft
    sourceRight
    targetLeft
    targetRight
    hLeft
    hRight

  cases hLeft with
  | head hLeftPending =>
      cases hRight with
      | head hRightPending =>
          exact
            ⟨ hLeftPending,
              hRightPending,
              Or.inr
                (Or.inl rfl) ⟩

      | tail _hHead hTail =>
          cases hTail

  | tail _hHead hTail =>
      cases hTail

/--
The generated-LF singleton invocation queue contains no action before the
canonical initial tag.

This theorem covers both cases:

* zero delay schedules at the same metric time and a later microstep;
* positive delay schedules at a later metric time.
-/
theorem multiStorePayloadInvocationTarget_pendingNotPast
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    (LF.invocationLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay).PendingNotPast := by

  unfold LF.MultiStorePayloadState.PendingNotPast
  unfold LF.ActionQueue.PendingNotPast

  intro action hAction

  simp only [
    LF.invocationLFMultiStorePayloadState,
    List.mem_singleton
  ] at hAction

  subst action

  simpa [
    LF.invocationLFMultiStorePayloadState,
    LF.invocationMultiStorePayloadPendingAction,
    LF.PendingAction.scheduleWithPayload_tag
  ] using
    LF.Tag.precedesOrEqual_schedule
      ({ time := 0, microstep := 0 } : LF.Tag)
      delay

/--
The singleton invocation states satisfy structural state correspondence and
the full scheduler-selection compatibility relation.
-/
theorem multiStorePayloadInvocationStoreStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadStoreStateCorresponds
      messageServers
      (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay)
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay) := by

  exact
    {
      states :=
        multiStorePayloadInvocationStates_structurally_correspond
          server
          initialStateStore
          payload
          delay

      pendingEvents :=
        multiStorePayloadInvocationSelectionCompatible
          messageServers
          server
          payload
          delay
    }

/--
The canonical singleton invocation states satisfy complete runtime-state
correspondence.

No server-list membership premise is needed at this stage: membership is a
dispatch obligation, not a queue/state-correspondence obligation.
-/
theorem multiStorePayloadInvocationRuntimeStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadRuntimeStateCorresponds
      messageServers
      (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay)
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay) := by

  exact
    {
      states :=
        multiStorePayloadInvocationStoreStates_correspond
          messageServers
          server
          initialStateStore
          payload
          delay

      pendingNotPast :=
        multiStorePayloadInvocationTarget_pendingNotPast
          server
          initialStateStore
          payload
          delay
    }

/--
The stable detailed singleton invocation states correspond.
-/
theorem detailedMultiStorePayloadInvocationStates_correspond
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (server.invocationDetailedMultiStorePayloadState
        messageServers
        initialStateStore
        payload
        delay)
      (LF.invocationDetailedLFMultiStorePayloadState
        messageServers
        server
        initialStateStore
        payload
        delay) := by

  exact
    MultiStorePayloadDetailedRuntimeStateCorresponds.stable
      (multiStorePayloadInvocationRuntimeStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay)

/--
A declared source server's compiled reaction belongs to the generated reaction
list.

Unlike runtime-state correspondence, this fact requires the explicit source
server membership premise.
-/
theorem multiStorePayloadInvocationCompiledReaction_mem
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {server :
      DTR.MultiStorePayloadMessageServer}
    (hMember :
      server ∈ messageServers) :
    Translation.compileMultiStorePayloadReaction
        server ∈
      Translation.compileMultiStorePayloadMessageReactions
        messageServers := by

  exact
    Translation.compileMultiStorePayloadReaction_mem
      hMember

/--
Package the complete canonical singleton runtime-entry boundary.
-/
theorem multiStorePayloadInvocationRuntimeEntry_package
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (server.invocationDetailedMultiStorePayloadState
          messageServers
          initialStateStore
          payload
          delay)
        (LF.invocationDetailedLFMultiStorePayloadState
          messageServers
          server
          initialStateStore
          payload
          delay) ∧
      PendingPayloadCorresponds
        (server.invocationPendingMessage
          payload
          delay)
        (LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay) ∧
      PayloadQueueCorresponds
        [
          server.invocationPendingMessage
            payload
            delay
        ]
        [
          LF.invocationMultiStorePayloadPendingAction
            server
            payload
            delay
        ] ∧
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).PendingNotPast := by

  exact
    ⟨ detailedMultiStorePayloadInvocationStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay,
      multiStorePayloadInvocationPending_correspond
        server
        payload
        delay,
      multiStorePayloadInvocationQueues_correspond
        server
        payload
        delay,
      multiStorePayloadInvocationTarget_pendingNotPast
        server
        initialStateStore
        payload
        delay ⟩

/--
Package runtime entry together with compiled-reaction membership for a
declared source server. This is the boundary required by the later dispatch
construction.
-/
theorem multiStorePayloadDeclaredInvocationEntry_package
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (server.invocationDetailedMultiStorePayloadState
          messageServers
          initialStateStore
          payload
          delay)
        (LF.invocationDetailedLFMultiStorePayloadState
          messageServers
          server
          initialStateStore
          payload
          delay) ∧
      Translation.compileMultiStorePayloadReaction
          server ∈
        Translation.compileMultiStorePayloadMessageReactions
          messageServers := by

  exact
    ⟨ detailedMultiStorePayloadInvocationStates_correspond
        messageServers
        server
        initialStateStore
        payload
        delay,
      multiStorePayloadInvocationCompiledReaction_mem
        hMember ⟩


/--
A server name precedes itself in any concrete declaration list that contains
that server.

The proof follows the declaration scan used by the source scheduler.
-/
theorem multiStorePayloadServerNamePrecedesOrEqual_self_of_mem
    (server :
      DTR.MultiStorePayloadMessageServer)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers) :
    DTR.MultiStorePayloadServerNamePrecedesOrEqual
      server.name
      server.name
      messageServers := by

  induction messageServers with

  | nil =>
      simp at hMember

  | cons current remaining inductionHypothesis =>
      simp only [
        List.mem_cons
      ] at hMember

      rcases hMember with
        hCurrent |
        hRemaining

      · subst current

        simpa [
          DTR.multiStorePayloadServerNamePrecedesOrEqual_cons
        ]

      · by_cases hName :
            current.name =
              server.name

        · simpa [
            DTR.multiStorePayloadServerNamePrecedesOrEqual_cons,
            hName
          ]

        · simpa [
            DTR.multiStorePayloadServerNamePrecedesOrEqual_cons,
            hName
          ] using
            inductionHypothesis
              hRemaining

/--
A declared source server's normalized priority position precedes itself.
-/
theorem multiStorePayloadInvocationPriority_self_of_mem
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {server :
      DTR.MultiStorePayloadMessageServer}
    (hMember :
      server ∈ messageServers) :
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      server.name
      server.name
      messageServers := by

  unfold
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual

  apply
    multiStorePayloadServerNamePrecedesOrEqual_self_of_mem

  exact
    (DTR.MultiStorePayloadMessageServerPriority.mem_normalize_iff
      server
      messageServers).2
        hMember

/--
The sole pending source message is priority eligible.

There is only one candidate. Earliestness is therefore structural, and the
same-name priority obligation follows from declaration membership.
-/
theorem multiStorePayloadInvocationSource_priorityEligible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (payload :
      Payload)
    (delay :
      Delay) :
    DTR.MultiStorePayloadIsPriorityEligible
      messageServers
      (server.invocationPendingMessage
        payload
        delay)
      [
        server.invocationPendingMessage
          payload
          delay
      ] := by

  refine
    ⟨ ?_,
      ?_ ⟩

  · simp [
      DTR.IsEarliest
    ]

  · intro candidate
    intro hCandidate
    intro _hSameTime

    simp only [
      List.mem_singleton
    ] at hCandidate

    subst candidate

    simpa [
      DTR.MultiStorePayloadMessageServer.invocationPendingMessage
    ] using
      multiStorePayloadInvocationPriority_self_of_mem
        hMember

/--
Canonical source dispatch for the singleton invocation.
-/
theorem multiStorePayloadInvocation_sourceDispatch
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    DTR.MultiStorePayloadDispatchStep
      messageServers
      (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay)
      (server.invocationPendingMessage
        payload
        delay)
      server
      (server.invocationDispatchedMultiStorePayloadState
        initialStateStore
        payload
        delay
        boundParameters) := by

  have hTarget :
      (server.invocationPendingMessage
        payload
        delay).name =
      server.name := by
    rfl

  have hBoundPayload :
      ParameterStore.bindPayload
          server.parameters
          (server.invocationPendingMessage
            payload
            delay).payload =
        some boundParameters := by

    simpa [
      DTR.MultiStorePayloadMessageServer.invocationPendingMessage
    ] using
      hBind

  simpa [
    DTR.MultiStorePayloadMessageServer.invocationMultiStorePayloadState,
    DTR.MultiStorePayloadMessageServer.invocationDispatchedMultiStorePayloadState
  ] using
    (DTR.MultiStorePayloadDispatchStep.fire
      (messageServers :=
        messageServers)
      0
      initialStateStore
      ParameterStore.empty
      [
        server.invocationPendingMessage
          payload
          delay
      ]
      []
      (server.invocationPendingMessage
        payload
        delay)
      server
      boundParameters
      hMember
      (Occurrence.RemovesOne.head [])
      (multiStorePayloadInvocationSource_priorityEligible
        server
        hMember
        payload
        delay)
      (Nat.zero_le _)
      hTarget
      hBoundPayload)

/--
Forward runtime correspondence produces a generated-LF dispatch whose selected
action is exactly the canonical singleton invocation action.

The target post-state remains existential at this subcheckpoint. Its exact
identification with the canonical target post-state is the next proof.
-/
theorem multiStorePayloadInvocation_forwardDispatchWitness
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    ∃ targetAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          (LF.invocationLFMultiStorePayloadState
            server
            initialStateStore
            payload
            delay)
          (LF.invocationMultiStorePayloadPendingAction
            server
            payload
            delay)
          (Translation.compileMultiStorePayloadReaction
            server)
          targetAfter ∧
        MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          (server.invocationMultiStorePayloadState
            initialStateStore
            payload
            delay)
          (server.invocationPendingMessage
            payload
            delay)
          server
          (server.invocationDispatchedMultiStorePayloadState
            initialStateStore
            payload
            delay
            boundParameters)
          (LF.invocationLFMultiStorePayloadState
            server
            initialStateStore
            payload
            delay)
          (LF.invocationMultiStorePayloadPendingAction
            server
            payload
            delay)
          (Translation.compileMultiStorePayloadReaction
            server)
          targetAfter := by

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      multiStorePayloadDetailedRuntime_dispatch_forward
        (multiStorePayloadInvocation_sourceDispatch
          server
          hMember
          initialStateStore
          payload
          delay
          boundParameters
          hBind)
        (multiStorePayloadInvocationRuntimeStates_correspond
          messageServers
          server
          initialStateStore
          payload
          delay)

  have hSelectedMember :
      selectedAction ∈
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay).pendingActions :=
    LF.MultiStorePayloadDispatchStep.selected_mem
      hTargetDispatch

  have hSelected :
      selectedAction =
        LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay := by

    simpa [
      LF.invocationLFMultiStorePayloadState
    ] using
      hSelectedMember

  subst selectedAction

  exact
    ⟨ targetAfter,
      hTargetDispatch,
      hWitness ⟩

/--
Package the canonical source dispatch and the corresponding generated-LF
forward dispatch witness.
-/
theorem multiStorePayloadInvocationDispatchEntry_package
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    DTR.MultiStorePayloadDispatchStep
        messageServers
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay)
        (server.invocationPendingMessage
          payload
          delay)
        server
        (server.invocationDispatchedMultiStorePayloadState
          initialStateStore
          payload
          delay
          boundParameters) ∧
      ∃ targetAfter,
        LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            (LF.invocationLFMultiStorePayloadState
              server
              initialStateStore
              payload
              delay)
            (LF.invocationMultiStorePayloadPendingAction
              server
              payload
              delay)
            (Translation.compileMultiStorePayloadReaction
              server)
            targetAfter ∧
          MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
            messageServers
            (server.invocationMultiStorePayloadState
              initialStateStore
              payload
              delay)
            (server.invocationPendingMessage
              payload
              delay)
            server
            (server.invocationDispatchedMultiStorePayloadState
              initialStateStore
              payload
              delay
              boundParameters)
            (LF.invocationLFMultiStorePayloadState
              server
              initialStateStore
              payload
              delay)
            (LF.invocationMultiStorePayloadPendingAction
              server
              payload
              delay)
            (Translation.compileMultiStorePayloadReaction
              server)
            targetAfter := by

  exact
    ⟨ multiStorePayloadInvocation_sourceDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind,
      multiStorePayloadInvocation_forwardDispatchWitness
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind ⟩


/--
A generated-LF dispatch obtained from the canonical singleton entry has the
canonical generated-LF post-dispatch state.

The dispatch constructor fixes the selected tag, persistent store and active
reaction body. Post-dispatch runtime correspondence fixes the bound parameter
store and forces the residual target queue to be empty because the source
residual queue is empty.
-/
theorem multiStorePayloadInvocation_targetAfter_eq
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    {targetAfter :
      LF.MultiStorePayloadState}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay)
        (LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay)
        (Translation.compileMultiStorePayloadReaction
          server)
        targetAfter)
    (hWitness :
      MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay)
        (server.invocationPendingMessage
          payload
          delay)
        server
        (server.invocationDispatchedMultiStorePayloadState
          initialStateStore
          payload
          delay
          boundParameters)
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay)
        (LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay)
        (Translation.compileMultiStorePayloadReaction
          server)
        targetAfter) :
    targetAfter =
      LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters := by

  cases hTargetDispatch with

  | fire
      currentTag
      stateStore
      parameters
      pendingActions
      remainingActions
      selectedAction
      selectedReaction
      targetBoundParameters
      hReactionDeclared
      hRemoved
      hPriorityEligible
      hNotPast
      hTrigger
      hTargetBind =>

      have hParameters :
          targetBoundParameters =
            boundParameters := by

        simpa [
          DTR.MultiStorePayloadMessageServer.invocationDispatchedMultiStorePayloadState
        ] using
          hWitness.afterState.states.states.parameters

      have hResidualQueues :
          PayloadQueueCorresponds
            []
            remainingActions := by

        simpa [
          DTR.MultiStorePayloadMessageServer.invocationDispatchedMultiStorePayloadState
        ] using
          hWitness.afterState.states.states.pendingQueues

      have hRemaining :
          remainingActions =
            [] := by

        cases hResidualQueues
        rfl

      cases hParameters
      cases hRemaining

      rfl

/--
The canonical singleton invocation has an exact generated-LF dispatch to the
canonical target post-dispatch state.
-/
theorem multiStorePayloadInvocation_targetDispatch
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    LF.MultiStorePayloadDispatchStep
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers)
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay)
      (LF.invocationMultiStorePayloadPendingAction
        server
        payload
        delay)
      (Translation.compileMultiStorePayloadReaction
        server)
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters) := by

  obtain
    ⟨targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      multiStorePayloadInvocation_forwardDispatchWitness
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind

  have hTargetAfter :
      targetAfter =
        LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters :=
    multiStorePayloadInvocation_targetAfter_eq
      server
      initialStateStore
      payload
      delay
      boundParameters
      hTargetDispatch
      hWitness

  subst targetAfter

  exact hTargetDispatch

/--
The canonical source and target post-dispatch states satisfy complete runtime
correspondence.
-/
theorem multiStorePayloadInvocationDispatchedStates_correspond
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    MultiStorePayloadRuntimeStateCorresponds
      messageServers
      (server.invocationDispatchedMultiStorePayloadState
        initialStateStore
        payload
        delay
        boundParameters)
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters) := by

  obtain
    ⟨targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      multiStorePayloadInvocation_forwardDispatchWitness
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind

  have hTargetAfter :
      targetAfter =
        LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters :=
    multiStorePayloadInvocation_targetAfter_eq
      server
      initialStateStore
      payload
      delay
      boundParameters
      hTargetDispatch
      hWitness

  subst targetAfter

  exact hWitness.afterState

/--
The canonical source and target dispatches satisfy the exact detailed runtime
dispatch-witness correspondence.
-/
theorem multiStorePayloadInvocationExactDispatchWitness_correspond
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
      messageServers
      (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay)
      (server.invocationPendingMessage
        payload
        delay)
      server
      (server.invocationDispatchedMultiStorePayloadState
        initialStateStore
        payload
        delay
        boundParameters)
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay)
      (LF.invocationMultiStorePayloadPendingAction
        server
        payload
        delay)
      (Translation.compileMultiStorePayloadReaction
        server)
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters) := by

  obtain
    ⟨targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      multiStorePayloadInvocation_forwardDispatchWitness
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind

  have hTargetAfter :
      targetAfter =
        LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters :=
    multiStorePayloadInvocation_targetAfter_eq
      server
      initialStateStore
      payload
      delay
      boundParameters
      hTargetDispatch
      hWitness

  subst targetAfter

  exact hWitness

/--
Package both exact canonical dispatch witnesses and their detailed runtime
correspondence.
-/
theorem multiStorePayloadInvocationExactDispatchEntry_package
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    DTR.MultiStorePayloadDispatchStep
        messageServers
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay)
        (server.invocationPendingMessage
          payload
          delay)
        server
        (server.invocationDispatchedMultiStorePayloadState
          initialStateStore
          payload
          delay
          boundParameters) ∧
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay)
        (LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay)
        (Translation.compileMultiStorePayloadReaction
          server)
        (LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters) ∧
      MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay)
        (server.invocationPendingMessage
          payload
          delay)
        server
        (server.invocationDispatchedMultiStorePayloadState
          initialStateStore
          payload
          delay
          boundParameters)
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay)
        (LF.invocationMultiStorePayloadPendingAction
          server
          payload
          delay)
        (Translation.compileMultiStorePayloadReaction
          server)
        (LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters) := by

  exact
    ⟨ multiStorePayloadInvocation_sourceDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind,
      multiStorePayloadInvocation_targetDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind,
      multiStorePayloadInvocationExactDispatchWitness_correspond
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind ⟩


/--
Canonical source detailed state after the positive-delay metric-time step.
-/
def multiStorePayloadInvocationSourceDispatchReadyState
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    DTR.DetailedMultiStorePayloadState
      messageServers :=
  DTR.DetailedMultiStorePayloadState.dispatchReady
    (server.invocationMultiStorePayloadState
      initialStateStore
      payload
      delay)
    (server.invocationPendingMessage
      payload
      delay)
    server
    (server.invocationDispatchedMultiStorePayloadState
      initialStateStore
      payload
      delay
      boundParameters)
    (multiStorePayloadInvocation_sourceDispatch
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind)

/--
Canonical generated-LF detailed state immediately after a positive-delay
metric-time step.
-/
def multiStorePayloadInvocationTargetAfterTimeState
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    LF.DetailedMultiStorePayloadState
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers) :=
  LF.DetailedMultiStorePayloadState.afterTime
    (LF.invocationLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay)
    (LF.invocationMultiStorePayloadPendingAction
      server
      payload
      delay)
    (Translation.compileMultiStorePayloadReaction
      server)
    (LF.invocationDispatchedLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay
      boundParameters)
    (multiStorePayloadInvocation_targetDispatch
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind)

/--
Canonical generated-LF dispatch-ready detailed state. For zero delay it is
reached by a target-only microstep.
-/
def multiStorePayloadInvocationTargetDispatchReadyState
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    LF.DetailedMultiStorePayloadState
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers) :=
  LF.DetailedMultiStorePayloadState.dispatchReady
    (LF.invocationLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay)
    (LF.invocationMultiStorePayloadPendingAction
      server
      payload
      delay)
    (Translation.compileMultiStorePayloadReaction
      server)
    (LF.invocationDispatchedLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay
      boundParameters)
    (multiStorePayloadInvocation_targetDispatch
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind)

/--
Positive delay strictly advances source metric time.
-/
theorem multiStorePayloadInvocation_sourceTime_lt_of_positive
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hPositive :
      0 < delay.value) :
    (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay).currentTime <
      (server.invocationDispatchedMultiStorePayloadState
        initialStateStore
        payload
        delay
        boundParameters).currentTime := by

  simpa [
    DTR.MultiStorePayloadMessageServer.invocationMultiStorePayloadState,
    DTR.MultiStorePayloadMessageServer.invocationPendingMessage,
    DTR.MultiStorePayloadMessageServer.invocationDispatchedMultiStorePayloadState,
    DTR.PendingMessage.scheduleWithPayload,
    LogicalTime.after
  ] using
    hPositive

/--
Positive delay strictly advances generated-LF metric time.
-/
theorem multiStorePayloadInvocation_targetTime_lt_of_positive
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hPositive :
      0 < delay.value) :
    (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).currentTag.time <
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters).currentTag.time := by

  simpa [
    LF.invocationLFMultiStorePayloadState,
    LF.invocationMultiStorePayloadPendingAction,
    LF.invocationDispatchedLFMultiStorePayloadState,
    LF.PendingAction.scheduleWithPayload,
    LF.Tag.schedule_positive
      ({ time := 0, microstep := 0 } : LF.Tag)
      delay
      hPositive,
    LogicalTime.after
  ] using
    hPositive

/--
Positive-delay generated actions have microstep zero.
-/
theorem multiStorePayloadInvocation_targetMicrostep_zero_of_positive
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hPositive :
      0 < delay.value) :
    (LF.invocationDispatchedLFMultiStorePayloadState
      server
      initialStateStore
      payload
      delay
      boundParameters).currentTag.microstep =
      0 := by

  simpa [
    LF.invocationDispatchedLFMultiStorePayloadState,
    LF.invocationMultiStorePayloadPendingAction,
    LF.PendingAction.scheduleWithPayload
  ] using
    LF.Tag.schedule_positive_microstep_zero
      ({ time := 0, microstep := 0 } : LF.Tag)
      delay
      hPositive

/--
A delay whose value is zero is the canonical zero delay.
-/
theorem delay_eq_zero_of_value_eq_zero
    (delay :
      Delay)
    (hZero :
      delay.value = 0) :
    delay =
      ⟨0⟩ := by

  cases delay with
  | mk value =>
      simp only at hZero
      subst value
      rfl

/--
Zero delay leaves source metric time unchanged.
-/
theorem multiStorePayloadInvocation_sourceTime_eq_of_zero
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hZero :
      delay.value = 0) :
    (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay).currentTime =
      (server.invocationDispatchedMultiStorePayloadState
        initialStateStore
        payload
        delay
        boundParameters).currentTime := by

  have hDelay :
      delay =
        ⟨0⟩ :=
    delay_eq_zero_of_value_eq_zero
      delay
      hZero

  subst delay

  simp [
    DTR.MultiStorePayloadMessageServer.invocationMultiStorePayloadState,
    DTR.MultiStorePayloadMessageServer.invocationPendingMessage,
    DTR.MultiStorePayloadMessageServer.invocationDispatchedMultiStorePayloadState,
    DTR.PendingMessage.scheduleWithPayload,
    LogicalTime.after
  ]

/--
Zero delay leaves generated-LF metric time unchanged.
-/
theorem multiStorePayloadInvocation_targetTime_eq_of_zero
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hZero :
      delay.value = 0) :
    (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).currentTag.time =
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters).currentTag.time := by

  have hDelay :
      delay =
        ⟨0⟩ :=
    delay_eq_zero_of_value_eq_zero
      delay
      hZero

  subst delay

  simp [
    LF.invocationLFMultiStorePayloadState,
    LF.invocationMultiStorePayloadPendingAction,
    LF.invocationDispatchedLFMultiStorePayloadState,
    LF.PendingAction.scheduleWithPayload,
    LF.Tag.schedule_zero
  ]

/--
Zero delay strictly advances the generated-LF microstep.
-/
theorem multiStorePayloadInvocation_targetMicrostep_lt_of_zero
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hZero :
      delay.value = 0) :
    (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay).currentTag.microstep <
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters).currentTag.microstep := by

  have hDelay :
      delay =
        ⟨0⟩ :=
    delay_eq_zero_of_value_eq_zero
      delay
      hZero

  subst delay

  simp [
    LF.invocationLFMultiStorePayloadState,
    LF.invocationMultiStorePayloadPendingAction,
    LF.invocationDispatchedLFMultiStorePayloadState,
    LF.PendingAction.scheduleWithPayload,
    LF.Tag.schedule_zero
  ]

/--
Positive delay produces the canonical source metric-time step.
-/
theorem multiStorePayloadInvocation_sourceTimeAdvance_positive
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hPositive :
      0 < delay.value) :
    DTR.DetailedMultiStorePayloadStep
      messageServers
      (DTR.DetailedMultiStorePayloadState.stable
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay))
      (DTR.DetailedMultiStorePayloadLabel.timeAdvance
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay).currentTime
        (server.invocationDispatchedMultiStorePayloadState
          initialStateStore
          payload
          delay
          boundParameters).currentTime)
      (multiStorePayloadInvocationSourceDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) := by

  simpa [
    multiStorePayloadInvocationSourceDispatchReadyState
  ] using
    DTR.DetailedMultiStorePayloadStep.timeAdvance
      (multiStorePayloadInvocation_sourceDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)
      (multiStorePayloadInvocation_sourceTime_lt_of_positive
        server
        initialStateStore
        payload
        delay
        boundParameters
        hPositive)

/--
Positive delay produces the canonical generated-LF metric-time step.
-/
theorem multiStorePayloadInvocation_targetTimeAdvance_positive
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hPositive :
      0 < delay.value) :
    LF.DetailedMultiStorePayloadStep
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers)
      (LF.DetailedMultiStorePayloadState.stable
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay))
      (LF.DetailedMultiStorePayloadLabel.timeAdvance
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay).currentTag.time
        (LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters).currentTag.time)
      (multiStorePayloadInvocationTargetAfterTimeState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) := by

  simpa [
    multiStorePayloadInvocationTargetAfterTimeState
  ] using
    LF.DetailedMultiStorePayloadStep.timeAdvance
      (multiStorePayloadInvocation_targetDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)
      (multiStorePayloadInvocation_targetTime_lt_of_positive
        server
        initialStateStore
        payload
        delay
        boundParameters
        hPositive)

/--
After the positive-delay metric-time steps, source dispatch readiness
corresponds to the generated-LF after-time phase.
-/
theorem multiStorePayloadInvocationPositivePhase_correspond
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hPositive :
      0 < delay.value) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (multiStorePayloadInvocationSourceDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)
      (multiStorePayloadInvocationTargetAfterTimeState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) := by

  simpa [
    multiStorePayloadInvocationSourceDispatchReadyState,
    multiStorePayloadInvocationTargetAfterTimeState
  ] using
    MultiStorePayloadDetailedRuntimeStateCorresponds.futureAfterTime
      (sourceDispatch :=
        multiStorePayloadInvocation_sourceDispatch
          server
          hMember
          initialStateStore
          payload
          delay
          boundParameters
          hBind)
      (targetDispatch :=
        multiStorePayloadInvocation_targetDispatch
          server
          hMember
          initialStateStore
          payload
          delay
          boundParameters
          hBind)
      (multiStorePayloadInvocation_sourceTime_lt_of_positive
        server
        initialStateStore
        payload
        delay
        boundParameters
        hPositive)
      (multiStorePayloadInvocation_targetTime_lt_of_positive
        server
        initialStateStore
        payload
        delay
        boundParameters
        hPositive)
      (multiStorePayloadInvocationExactDispatchWitness_correspond
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)

/--
Zero delay produces the canonical target-only microstep.
-/
theorem multiStorePayloadInvocation_targetMicrostep_zero
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hZero :
      delay.value = 0) :
    LF.DetailedMultiStorePayloadStep
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers)
      (LF.DetailedMultiStorePayloadState.stable
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay))
      (LF.DetailedMultiStorePayloadLabel.microstepAdvance
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay).currentTag
        (LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters).currentTag)
      (multiStorePayloadInvocationTargetDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) := by

  simpa [
    multiStorePayloadInvocationTargetDispatchReadyState
  ] using
    LF.DetailedMultiStorePayloadStep.microstepSameTime
      (multiStorePayloadInvocation_targetDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)
      (multiStorePayloadInvocation_targetTime_eq_of_zero
        server
        initialStateStore
        payload
        delay
        boundParameters
        hZero)
      (multiStorePayloadInvocation_targetMicrostep_lt_of_zero
        server
        initialStateStore
        payload
        delay
        boundParameters
        hZero)

/--
For zero delay, the source remains in its stable entry state while the
generated LF state advances to dispatch readiness by one target-only
microstep.
-/
theorem multiStorePayloadInvocationZeroPhase_correspond
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hZero :
      delay.value = 0) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (DTR.DetailedMultiStorePayloadState.stable
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay))
      (multiStorePayloadInvocationTargetDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) := by

  simpa [
    multiStorePayloadInvocationTargetDispatchReadyState
  ] using
    MultiStorePayloadDetailedRuntimeStateCorresponds.sameTimeMicrostepAhead
      (multiStorePayloadInvocation_sourceDispatch
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)
      (multiStorePayloadInvocation_sourceTime_eq_of_zero
        server
        initialStateStore
        payload
        delay
        boundParameters
        hZero)
      (multiStorePayloadInvocation_targetTime_eq_of_zero
        server
        initialStateStore
        payload
        delay
        boundParameters
        hZero)
      (multiStorePayloadInvocation_targetMicrostep_lt_of_zero
        server
        initialStateStore
        payload
        delay
        boundParameters
        hZero)
      (multiStorePayloadInvocationExactDispatchWitness_correspond
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)

/--
Complete positive-delay phase-entry package.
-/
def MultiStorePayloadInvocationPositivePhaseEntry
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    Prop :=
  DTR.DetailedMultiStorePayloadStep
      messageServers
      (DTR.DetailedMultiStorePayloadState.stable
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay))
      (DTR.DetailedMultiStorePayloadLabel.timeAdvance
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay).currentTime
        (server.invocationDispatchedMultiStorePayloadState
          initialStateStore
          payload
          delay
          boundParameters).currentTime)
      (multiStorePayloadInvocationSourceDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) ∧
    LF.DetailedMultiStorePayloadStep
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers)
      (LF.DetailedMultiStorePayloadState.stable
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay))
      (LF.DetailedMultiStorePayloadLabel.timeAdvance
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay).currentTag.time
        (LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters).currentTag.time)
      (multiStorePayloadInvocationTargetAfterTimeState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) ∧
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (multiStorePayloadInvocationSourceDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)
      (multiStorePayloadInvocationTargetAfterTimeState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)

/--
Complete zero-delay phase-entry package.
-/
def MultiStorePayloadInvocationZeroPhaseEntry
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    Prop :=
  LF.DetailedMultiStorePayloadStep
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers)
      (LF.DetailedMultiStorePayloadState.stable
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay))
      (LF.DetailedMultiStorePayloadLabel.microstepAdvance
        (LF.invocationLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay).currentTag
        (LF.invocationDispatchedLFMultiStorePayloadState
          server
          initialStateStore
          payload
          delay
          boundParameters).currentTag)
      (multiStorePayloadInvocationTargetDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) ∧
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (DTR.DetailedMultiStorePayloadState.stable
        (server.invocationMultiStorePayloadState
          initialStateStore
          payload
          delay))
      (multiStorePayloadInvocationTargetDispatchReadyState
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind)

/--
Construct the complete positive-delay phase-entry package.
-/
theorem multiStorePayloadInvocation_positivePhaseEntry
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hPositive :
      0 < delay.value) :
    MultiStorePayloadInvocationPositivePhaseEntry
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind := by

  exact
    ⟨ multiStorePayloadInvocation_sourceTimeAdvance_positive
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind
        hPositive,
      multiStorePayloadInvocation_targetTimeAdvance_positive
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind
        hPositive,
      multiStorePayloadInvocationPositivePhase_correspond
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind
        hPositive ⟩

/--
Construct the complete zero-delay phase-entry package.
-/
theorem multiStorePayloadInvocation_zeroPhaseEntry
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hZero :
      delay.value = 0) :
    MultiStorePayloadInvocationZeroPhaseEntry
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind := by

  exact
    ⟨ multiStorePayloadInvocation_targetMicrostep_zero
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind
        hZero,
      multiStorePayloadInvocationZeroPhase_correspond
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind
        hZero ⟩

/--
Every invocation delay enters exactly one supported detailed phase class.

Positive delay produces matching metric-time steps. Zero delay produces one
target-only LF microstep while the source remains stable.
-/
theorem multiStorePayloadInvocationDetailedPhaseEntry
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    (0 < delay.value ∧
      MultiStorePayloadInvocationPositivePhaseEntry
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) ∨
    (delay.value = 0 ∧
      MultiStorePayloadInvocationZeroPhaseEntry
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) := by

  by_cases hZero :
      delay.value = 0

  · exact
      Or.inr
        ⟨ hZero,
          multiStorePayloadInvocation_zeroPhaseEntry
            server
            hMember
            initialStateStore
            payload
            delay
            boundParameters
            hBind
            hZero ⟩

  · have hPositive :
        0 < delay.value :=
      Nat.pos_of_ne_zero
        hZero

    exact
      Or.inl
        ⟨ hPositive,
          multiStorePayloadInvocation_positivePhaseEntry
            server
            hMember
            initialStateStore
            payload
            delay
            boundParameters
            hBind
            hPositive ⟩

end Correctness
end Relico
