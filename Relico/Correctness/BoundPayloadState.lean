import Relico.Correctness.PayloadDispatchQueue
import Relico.DTR.BoundPayloadState
import Relico.LF.BoundPayloadState
import Relico.Translation.BoundPayloadBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between parameter-aware source and generated-LF payload
runtime states.

The activation-local parameter environments are equal because
translation preserves formal names and dispatch binds the same ordered
payload on both sides.
-/
structure BoundPayloadStateCorresponds
    (sourceState : DTR.BoundPayloadState)
    (targetState : LF.BoundPayloadState) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateValue :
    targetState.stateValue =
      sourceState.stateValue

  parameters :
    targetState.parameters =
      sourceState.parameters

  pendingEvents :
    PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compileBoundPayloadBody
        sourceState.activeBody

/--
State correspondence also yields the established payload-free queue
correspondence after forgetting payload equality.
-/
theorem BoundPayloadStateCorresponds.pendingEventsOrdinary
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState}
    (hStates :
      BoundPayloadStateCorresponds
        sourceState
        targetState) :
    QueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=

  PayloadQueueCorresponds.toQueueCorresponds
    hStates.pendingEvents

end Correctness
end Relico
