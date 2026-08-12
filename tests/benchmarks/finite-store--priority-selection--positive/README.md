# finite-store--priority-selection--positive

This positive finite-store benchmark exercises priority selection for two
same-time recurring message servers with distinct message-server priorities.

The source contains `low` with priority 1 and `high` with priority 2. Lower
numeric message-server priority is selected earlier. No actor priority is
required or used by the target candidate.

The benchmark covers 9 accepted target obligations from
`Relico/Tests/DirectLFRuntimeStateCorrespondence.lean`. The formal evidence
scope is runtime-state structural correspondence, pending-not-past,
bag/queue correspondence, and message-server selection compatibility. It does
not introduce a new theorem claim beyond those existing obligations.

`finite-store--dispatch--positive` is used only as the exact nine-stage
package, route, runtime, and toolchain exemplar. Its source semantics are not
inherited. `core--priority-selection--positive` is used only as the
message-server priority-selection source and translation semantics exemplar.

The recurring self-schedules are route liveness scaffolding for bounded
runtime observation. Runtime evidence is bounded observation only and makes
no termination claim. The benchmark does not claim that actor priority is
necessary for the DTR-to-LF correspondence.
