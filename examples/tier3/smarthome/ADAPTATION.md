# smarthome — the RQ2 ESP32 case study

The paper's hardware case study: an ESP32 smart-home system of eight
reactive classes — `Heater`, `Light`, `Door`, `TempSensor`,
`LightSensor`, `MotionSensor`, `RoomController`, `CentralController` —
monitoring temperature, light and motion, controlling heater and light,
and coordinating door and alarm policy from a central controller.

Source: `examples.zip:ReLico-main/smarthome/smarthome.rebeca` (359
lines). The adapted source in this directory is 341 lines; the
difference is entirely the removed `env` block and the removed
commented-out scenario variants are retained as comments.

## Original blocker

```
unsupported by the ReLico general parser bridge: environment variable
```

measured against the unmodified archive source.

## The minimal adaptation — three parts, each forced by a measured refusal

1. **`env` folded into literals** (18 declarations, 34 use-site
   substitutions). Each `env int TEMP_LOW = 20;` declaration is removed
   and every code-part use of its name becomes its literal:
   `if (t < TEMP_LOW)` → `if (t < 20)`, `after(NET_DELAY)` → `after(1)`,
   `tempLevel` → `15`, `lightIsDark` → `false`. Comments are untouched.
   Two earlier fold shapes were tried and refused first: same-position
   plain declarations (not valid Rebeca at top level) and per-body
   locals (accepted by Rebeca, but refused at `after(NET_DELAY)` --
   D9, an LF connection delay is static, so the delay must be a
   literal). The literal fold is what the stage K env-normalization
   ruling described, and it is semantically exact: an `env` constant
   *is* its value.
2. **Two self-sends qualified.** `report(9);` and `report(1);` inside
   `CentralController` are unqualified self-sends; the bridge's R14
   statement grammar admits `target.method(...)` sends, so they became
   `self.report(9);` / `self.report(1);`.
3. **Nine marker parameters.** `setOn`, `setOff`, `openDoor`,
   `closeDoor`, `motionDetected`, `activateLightOverride`,
   `deactivateLightOverride`, `fireAlert`, `unwantedPersonAlert` are
   parameterless message servers that are the target of external sends;
   the translator refuses those (the LF port would carry no value
   type), the boundary the stage K corpus wave measured. Each gained
   `int unit` and every send site passes `0`. No server body reads the
   marker.

No other change. Property files (five runtime properties in the paper)
are out of scope for these demonstration runs.

## Results — every pipeline stage green

| stage | result |
|---|---|
| exporter (`run-general-from-zip.sh`) | pass |
| decode (`lean-export --family general --mode decoded-dtr-ast`) | pass |
| translation (`translated-lf-ast`) | pass |
| LF generation (`lf-source`) | pass, 8 reactors |
| `lfc 0.11.0` (C++ target) | pass |
| generated binary under the runtime budget | pass |
| Rebeca model checker (recorded bonus) | `satisfied` |

Run 2026-09-07 at the tree of `examples: record the tier-2 real-corpus
runs (K)`.
