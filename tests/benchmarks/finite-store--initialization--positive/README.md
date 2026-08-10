# finite-store--initialization--positive

This positive benchmark exercises two-state finite-store initialization through
the complete nine-stage source-to-runtime route.

The source declares `x` and `y`, whose declaration-level initial values decode
as zero. The constructor assigns `x = 1` and `y = 2` and schedules `tick`
after one logical-time unit. The `tick` message-server body begins with
`y = x`.

Canonical Lean coverage supplies 18 accepted target obligations across
`Relico/Tests/StoreCppBackend.lean`,
`Relico/Tests/StoreExecutableTranslation.lean`, and
`Relico/Tests/StoreInitialization.lean`.

The source also schedules another `tick` after `y = x`. This recurring
self-send is route-only liveness scaffolding for the RMC deadlock-freedom
stage and bounded LF runtime observation. The mapped formal tick body does
not contain that recurring send, so this benchmark does not claim full
source/formal message-body identity.

The package uses the `multi-store-payload` parser/export family and the
nine-stage package, LFC, and runtime toolchain shape of
`finite-store--dispatch--positive`. That benchmark is a route/toolchain
exemplar only; its source semantics are not inherited.

Runtime evidence is bounded observation only and does not assert termination.
No actor priority is required. The `tick` message server has no priority.
