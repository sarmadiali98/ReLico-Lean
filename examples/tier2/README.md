# Tier 2: real corpus models, unmodified

Every model in the upstream corpus that the current verified fragment
accepts, run through the pipeline exactly as it ships in the archive: no
source edits, no registry entries, no wrappers. 21 models, on
2026-09-07, at the tree of stage K's benchmark completion.

## Method

Each model ran: `run-general-from-zip.sh` (exporter), then
`lean-export --family general` for `decoded-dtr-ast`,
`translated-lf-ast` and `lf-source`, then `lfc 0.11.0` (C++ target),
then the compiled binary under the runtime stage's 5 msec logical-time
budget with a 10 s wall guard. The Rebeca model checker was run as well
and recorded, but it is not a gate for these demonstration runs -- a
model-checking deadlock verdict says the model terminates, which the
paper's own benchmarks include by design.

`RESULTS.tsv` columns: per-stage `pass`/`fail`/`n/a`, the model-checker
verdict, a `final_status` that requires every pipeline stage to pass, and
the precise failure reason where one exists.

## Result: 12 of 21 pass end to end unmodified

Alarm, CheckpointBarrier2, Election, Fibonacci, PingPong, Pipe,
ProcessMsg, Ring, Thermostat, TrainDoor2, TrainDoorFeedback and
WideBarrier24 translate, generate LF, compile and run exactly as
archived.

## The 9 failures are two known causes, nothing new

**Eight fail at translation, all with the same refusal.** A message
server that is the target of an external send and takes no parameters
cannot become an LF port, because the port would carry no value and
whether the target accepts such a port is unmeasured; the translator
refuses rather than guesses. Affected: `AircraftDoor` and `Factorial`
(`KeepAlive.kick`), `SafeSend` and `UnsafeSend` (`Checker.errorIn`),
`Subway` (`Checker.doneIn`), `TrafficLight` (`Checker.sigGIn`),
`TrainDoor` (`Checker.trainEvt`), and `benchmarks/tcsma`
(`User.sendData`). This is the same measured boundary the stage K corpus
wave hit and resolved with additive marker parameters on three of these
very models (`TrafficLight`, `Subway`, and the tcsma-inspired redesign);
the marker parameter is the minimal adaptation if these are to be run.

**One fails at runtime: `Minimal`.** Its recurrence is a zero-delay
self-send, which becomes an LF logical action with no delay, so the
runtime generates unbounded microsteps at logical time 0 and never
advances past its budget; the stage's wall guard fires at 10 s. The stage
K pilot wave measured exactly this and the benchmark source for
`general--one-step-execution--positive` carries the one-word fix,
`after(1)`.

Notably, `benchmarks/tcsma` -- the paper-named TCSMA model -- decodes
successfully; only the parameterless `User.sendData` send blocks its
translation, and the model checker's `queue overflow` verdict on it is
the known uncoupled-producer shape, not a translation defect.
