/-
! # Regression pins for the general family's observable alphabet

`Correctness.GeneralObservable.ofSourceLabel` and `..._ofTargetLabel` are executable, so they owe pins.
What these pins protect is the *erasure*: the two functions must agree on a matched consume pair even
though the two labels carry entirely different second components, and they must agree on a time advance
without erasing anything. A change that started observing the payload or the event kind would break tests
3 and 4 immediately, which is the point — the alphabet's whole value is what it refuses to look at.

These are `rfl`/`decide` pins over closed terms, so they cost nothing at build time and fail loudly.
-/
import Relico.Correctness.GeneralObservable

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GeneralObservable

open Relico.Correctness

private def hubName :
    ActorName :=
  { value := "hub" }

private def sensorName :
    ActorName :=
  { value := "sensor" }

private def reportPortName :
    PortName :=
  { value := "hub_report" }

private def otherPortName :
    PortName :=
  { value := "hub_other" }

private def sampleMessage :
    DTR.GeneralMessage :=
  {
    sender := sensorName
    messageName := { value := "report" }
    payload := [DTR.GeneralValue.int 7]
    arrival := 3
  }

private def otherMessage :
    DTR.GeneralMessage :=
  {
    sender := hubName
    messageName := { value := "other" }
    payload := [DTR.GeneralValue.bool true, DTR.GeneralValue.int 0]
    arrival := 99
  }

/- Test 1: an internal source label observes nothing. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        DTR.GeneralLabel.tau =
      none := by
  rfl

/- Test 2: an internal target label observes nothing. P24's microstep-only tag advance is `tau` on this
   side, so this is also the pin that says a microstep is invisible. -/
example :
    Correctness.GeneralObservable.ofTargetLabel
        LF.GeneralLabel.tau =
      none := by
  rfl

/- Test 3: two source consumes of the SAME receiver with different senders, message names, payloads and
   arrivals observe the same thing. This is the payload erasure, pinned. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.consume
          hubName
          sampleMessage) =
      Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.consume
          hubName
          otherMessage) := by
  rfl

/- Test 4: two target consumes of the same reactor with different event kinds observe the same thing.
   This is the kind erasure, pinned — the one F78 requires. -/
example :
    Correctness.GeneralObservable.ofTargetLabel
        (LF.GeneralLabel.consume
          hubName
          (LF.GeneralEventKind.inputPort
            reportPortName)) =
      Correctness.GeneralObservable.ofTargetLabel
        (LF.GeneralLabel.consume
          hubName
          (LF.GeneralEventKind.inputPort
            otherPortName)) := by
  rfl

/- Test 5: a matched consume pair agrees across the two families. This is the obligation the trace
   theorems' transfer premise actually discharges, on a concrete pair. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.consume
          hubName
          sampleMessage) =
      Correctness.GeneralObservable.ofTargetLabel
        (LF.GeneralLabel.consume
          hubName
          (LF.GeneralEventKind.inputPort
            reportPortName)) := by
  rfl

/- Test 6: DIFFERENT receivers are distinguished. The erasure must not collapse everything — receiver
   identity is exactly what survives. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.consume
          hubName
          sampleMessage) ≠
      Correctness.GeneralObservable.ofTargetLabel
        (LF.GeneralLabel.consume
          sensorName
          (LF.GeneralEventKind.inputPort
            reportPortName)) := by
  decide

/- Test 7: a time advance is observed whole, and agrees across the two families. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.timeAdvance 2 5) =
      Correctness.GeneralObservable.ofTargetLabel
        (LF.GeneralLabel.timeAdvance 2 5) := by
  rfl

/- Test 8: time advances with different endpoints are distinguished, so nothing about time is erased. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.timeAdvance 2 5) ≠
      Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.timeAdvance 2 6) := by
  decide

/- Test 9: a consume and a time advance are never confused. -/
example :
    Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.consume
          hubName
          sampleMessage) ≠
      Correctness.GeneralObservable.ofSourceLabel
        (DTR.GeneralLabel.timeAdvance 2 5) := by
  decide

/- Test 10: two whole traces agree through the generic projection, with DIFFERENT numbers of internal
   steps on the two sides. This is the shape the trace theorems conclude, and the reason the result is
   trace *agreement* rather than trace equality: the target's extra τ traffic is invisible. -/
example :
    Common.observableProjection
        Correctness.GeneralObservable.ofSourceLabel
        [
          DTR.GeneralLabel.tau,
          DTR.GeneralLabel.consume
            hubName
            sampleMessage,
          DTR.GeneralLabel.timeAdvance 3 8
        ] =
      Common.observableProjection
        Correctness.GeneralObservable.ofTargetLabel
        [
          LF.GeneralLabel.tau,
          LF.GeneralLabel.tau,
          LF.GeneralLabel.consume
            hubName
            (LF.GeneralEventKind.inputPort
              reportPortName),
          LF.GeneralLabel.tau,
          LF.GeneralLabel.timeAdvance 3 8,
          LF.GeneralLabel.tau
        ] := by
  rfl

/- Test 11: and the agreed trace is the expected one, so test 10 is not two empty lists. -/
example :
    Common.observableProjection
        Correctness.GeneralObservable.ofSourceLabel
        [
          DTR.GeneralLabel.tau,
          DTR.GeneralLabel.consume
            hubName
            sampleMessage,
          DTR.GeneralLabel.timeAdvance 3 8
        ] =
      [
        Correctness.GeneralObservable.consume hubName,
        Correctness.GeneralObservable.timeAdvance 3 8
      ] := by
  rfl

end GeneralObservable
end Tests
end Relico
