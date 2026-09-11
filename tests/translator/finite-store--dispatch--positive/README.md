# finite-store--dispatch--positive

Positive finite-store dispatch benchmark.

The executable source contains one `Controller` with integer store variable
`x`. The constructor initializes `x` to `0` and schedules
`dispatch(1)`. Each `dispatch(payload)` invocation updates the store with
`x = payload` and schedules the next delayed dispatch.

The source/backend route is:

`source -> rmc -> parser-json -> decoded-dtr-ast -> formal-witness -> translated-lf-ast -> lf-source -> lfc -> runtime`

The parser and Lean export stages use the `multi-store-payload` family.

Formal evidence consists of the 38 accepted canonical obligations in:

- `Relico/Tests/StoreDispatch.lean`
- `Relico/Tests/StoreMachine.lean`
- `Relico/Tests/StoreMachineTrace.lean`

These obligations cover finite-store DTR/LF dispatch, source-state
correspondence, forward compatibility, machine-step compatibility, runtime
well-formedness, and finite traces. They are the formal semantic evidence for
this benchmark; the route exemplar contributes only route, package, executable
source shape, and bounded-runtime artifact shape.

Runtime evidence is a bounded observation of the recurring model. It does not
claim termination.

The obligation registry line-number convention is zero-based.

The paper is the default source of intended semantics. Implemented and
elaborating Lean is authoritative where it differs. This benchmark does not
assert a paper-versus-Lean discrepancy and does not reopen any actor-priority
claim.
