# core--well-formedness--positive

Positive core well-formedness benchmark.

The source is a valid singleton `Controller` model with state variable `x`,
constructor assignment `x = 0`, and a declared delayed recurring
`self.tick()` send. It mirrors the implemented Lean valid-model shape.

Evidence mode: `source-plus-formal-witness`.

Required route:

`source -> rmc -> parser-json -> decoded-dtr-ast -> formal-witness -> translated-lf-ast -> lf-source -> lfc`

The terminal stage is `lfc`. Runtime execution is not required.

Formal evidence consists of the seven accepted current registry obligations in:

- `Relico/Tests/ExpressionCorrectness.lean`
- `Relico/Tests/Inversion.lean`
- `Relico/Tests/StructuralCorrectness.lean`

The obligation registry line-number convention is zero-based.

The paper is the default intended semantics. Implemented and elaborating Lean is
authoritative where it differs. No paper-versus-Lean discrepancy is asserted by
this benchmark.

The route and artifact exemplars are used only where prior executed prototype
evidence established compatibility. Their semantic claims are not inherited.
