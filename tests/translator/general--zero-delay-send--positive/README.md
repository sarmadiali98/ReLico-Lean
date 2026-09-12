# `general--zero-delay-send--positive`

This positive benchmark belongs to the **general** family. It is a purpose-built capability
fixture for the accepted zero-delay send: the constructor's single `after(0)` self-send
schedules one instantaneous event at logical time 0. The capability was previously the only
accepted General-fragment capability with no executable pipeline evidence; this fixture closes
that gap.

## Capability

The model isolates bounded instantaneous scheduling. The constructor sends `self.ping()
after(0)`, so one event fires at logical time 0 before any positive time passes; the generated
LF program carries `ping_action1.schedule(0ms)` in the startup reaction, which is the
executable shape of the capability. The `ping` message server's re-arming send uses
`after(1)`, so the instantaneous behavior is exactly one event and logical time advances by one
every period thereafter.

## Why the re-arm exists

The mandatory RMC stage requires a `satisfied` deadlock-freedom verdict, and a model that sends
one message and then quiesces reaches an empty-queue state, which RMC reports as a deadlock.
The positive-delay re-arm is the minimum liveness this precondition allows; it is scaffolding
for the checker, not part of the capability claim.

## Distinction from the Minimal boundary

The external corpus screen records Minimal failing at the runtime stage because its `after(0)`
recurrence never advances logical time past the 5 msec wall-clock guard. No instantaneous
recurrence exists here: only the constructor's single `after(0)` send occurs, and every
re-arming send carries `after(1)`. The runtime observation shows the generated binary exiting
cleanly under `--timeout 5 msec --fast`.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

## Evidence

- source: the commented Timed Rebeca model above;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim
  about a particular runtime ordering;
- parser JSON: recorded from a real exporter run and reviewed; `after` is carried as an
  `intLiteral` node without a `line` field, the exporter's documented line-number asymmetry for
  delay literals;
- decoded DTR AST, translated LF AST, LF source, and the formal witness over this benchmark's
  pin module `Relico/Tests/GeneralZeroDelay.lean`, which pins that the compiled startup body
  schedules at delay 0 and the `ping` body at delay 1;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target;
- runtime: the generated binary runs in fast mode to the 5 msec logical-time timeout and exits
  0.

## Keep-alive

This model never terminates on its own; the runtime stage's fast-mode timeout is the bounded-run
policy.
