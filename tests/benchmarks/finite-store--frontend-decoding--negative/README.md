# finite-store--frontend-decoding--negative

This negative benchmark covers the finite-store frontend-decoding layer.

The canonical formal coverage is the 11 accepted zero-based obligations in
`Relico/Tests/StoreFrontendDecoder.lean`. That module provides a valid raw-store
decode control and two negative decoder cases: an undeclared assignment target
`z` against declared variables `x, y`, and an undeclared state-variable
reference `z` against declared variables `x, y`. Both negative cases establish
the implemented decoder's `nameMismatch` rejection behavior.

The source route has a separate role. Its executable body matches the qualified
`bound-payload--dispatch--negative` route fixture and intentionally reaches the
current ReLico v0 parser-bridge message-server-parameter boundary. It does not
claim direct source-to-StoreDecoder semantic identity.

Required route:

1. `source`
2. `rmc`
3. `parser-json`
4. `decoded-dtr-ast`
5. `expected-boundary-stage`
6. `diagnostics`

`parser-json` is expected to exit with code 1 and emit a diagnostic containing
`message-server parameters`. The `decoded-dtr-ast` stage is implemented as an
`expected-absence` check. It requires both `parser-json/model.json` and
`decoded-dtr-ast/model.txt` to remain absent.

The boundary record is the generic `EXPECTED_REJECTION` form at `parser-json`.
The diagnostics record preserves that same generic rejection. The legacy
bound-payload-specific boundary code is not used by this target.

Runtime evidence is not required for this benchmark.
