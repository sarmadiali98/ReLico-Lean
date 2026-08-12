# `finite-store--queue-correspondence--positive`

This positive benchmark exercises finite-store queue correspondence through the
canonical nine-stage source-to-runtime route.

The source preserves the queue-correspondence model used by
`core--queue-correspondence--positive`: the constructor schedules two
indistinguishable `tick()` occurrences at the same logical delay, and each
`tick()` reaction schedules one successor occurrence. The target adds the
finite-store runtime-observation stage while retaining the established
queue-correspondence translation semantics.

## Evidence

- source: duplicate same-server `tick()` sends at the same initial logical
  delay, with recurring successor scheduling;
- RMC: accepted source/model-checking evidence;
- parser JSON and decoded DTR AST: frontend representation through the
  `multiStorePayload` family;
- formal witness: the four accepted `StoreForward` obligations in
  `Relico/Tests/StoreForward.lean`;
- translated LF AST and LF source: queue-correspondence translation evidence
  identical to the implemented core queue-correspondence exemplar;
- `lfc`: successful LF/C++ compilation;
- runtime: bounded runtime observation required by the finite-store registry
  route.

No actor or message-server priority annotation is required or used. Runtime
evidence is bounded observation and is not presented as a termination claim.
