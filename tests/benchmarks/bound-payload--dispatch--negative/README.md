# `bound-payload--dispatch--negative`

This negative benchmark exercises a concrete Timed Rebeca message-server
payload.

The source uses a periodic parameterized self-dispatch so RMC's deadlock-freedom
check remains satisfied. It is accepted by RMC and its generated model checker.
The current version-0 ReLico parser bridge deliberately excludes message-server
formal parameters, so parser JSON generation is expected to terminate with:

`unsupported by the ReLico v0 parser bridge: message-server parameters`

No parser JSON or decoded DTR AST is fabricated after that rejection.

The six declared stages are:

1. `source`
2. `rmc`
3. `parser-json`
4. `decoded-dtr-ast`
5. `expected-boundary-stage`
6. `diagnostics`

The final three stages validate absence of post-boundary artifacts and produce
deterministic rejection diagnostics. The benchmark covers the 22 obligations
mapped from `Relico/Tests/DetailedBoundPayloadInvariantMatches.lean`.
