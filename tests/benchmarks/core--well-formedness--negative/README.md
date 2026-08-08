# `core--well-formedness--negative`

This negative core benchmark exercises the well-formedness and frontend
rejection evidence boundary over the complete negative benchmark route.

## Source behavior

`Controller()` initializes `phase` to `0` and intentionally schedules
`self.missing()` after one logical time unit even though `missing` is not a
declared message server.

The malformed self-send is the executable source exemplar for the negative
well-formedness boundary. A successful benchmark result therefore means that
the pipeline records the expected boundary or rejection with deterministic
diagnostics; it does not mean that the malformed model executes successfully.

## Formal evidence boundary

Formal evidence remains exactly 34 accepted obligations across two modules:

- 22 obligations from `Relico/Tests/DTRWellFormed.lean`;
- 12 obligations from `Relico/Tests/FrontendDecoder.lean`.

The mapped evidence includes a valid well-formed model, explicit models that
are not well formed, an invalid self-send model, valid frontend decoding, and
frontend rejection cases.

In particular, the formal boundary includes
`invalidSelfSendModel_not_wellFormed`,
`unsupportedStatement_is_rejected`, and
`wrongActorClass_is_rejected`.

The source model is an executable negative exemplar for that evidence
boundary. It does not itself prove all 34 formal obligations.

## Observed rejection boundary

The frozen undefined-self-send source is accepted by the benchmark `source`
stage and rejected by RMC with exit code `1` and the stable diagnostic:

`The method missing() is undefined for the type Controller`

No RMC verdict, parser model, or decoded DTR model is fabricated after that
rejection.

The repository's negative-boundary machinery is extended backward-compatibly:
the existing parser-bridge message-server-parameter boundary keeps its exact
legacy boundary and diagnostics values, while other expected rejection stages
use the generic boundary code `EXPECTED_REJECTION` and preserve the observed
boundary stage, exit codes, and required diagnostic in deterministic evidence.

## Route

The declared route remains:

`source,rmc,parser-json,decoded-dtr-ast,expected-boundary-stage,diagnostics`

For this benchmark, `parser-json` and `decoded-dtr-ast` are expected-absence
evidence stages after the RMC rejection. The terminal stage remains
`diagnostics`. No runtime stage is part of this benchmark.

Generated `actual/` and work products remain ignored.
