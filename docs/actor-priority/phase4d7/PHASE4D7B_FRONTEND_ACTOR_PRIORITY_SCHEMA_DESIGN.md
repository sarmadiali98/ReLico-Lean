# Phase 4D7B Frontend Actor-Priority Schema and Parser Design

## Result

**FRONTEND_ACTOR_PRIORITY_SCHEMA_AND_PARSER_DESIGN_COMPLETE_IMPLEMENTATION_PENDING**

## Bound current surface

- Message-priority owner:
  `RawMultiStorePayloadMessageServer`
- Existing local message-priority type:
  `Option Nat`
- Payload exporter schema version:
  `3`
- Multi-store exporter schema version:
  `3`
- Proposed next schema version:
  `4`
- Payload exporter `requireOne` calls:
  `4`
- Multi-store exporter `requireOne` calls:
  `4`
- Existing frontend actor-priority occurrences:
  **0**

## Canonical additive representation

~~~lean
structure RawMultiStorePayloadActorInstance where
  name : String
  reactiveClass : String
  priority : Option Nat := none
~~~

Existing constructor arguments and initialization payload must remain attached
to the same actor-instance representation with their existing types.

The top-level payload frontend adds or generalizes:

~~~lean
actors : List RawMultiStorePayloadActorInstance
~~~

The existing message-server field remains unchanged:

~~~lean
RawMultiStorePayloadMessageServer.priority : Option Nat
~~~

Actor priority and local reaction priority are distinct semantic layers.

## Wire-format contract

- Add an `actors` array in main-block declaration order.
- Require `name` and `reactiveClass` for every actor item.
- Permit an optional non-negative integer `priority`.
- Decode missing actor priority as `none`.
- Normalize legacy singleton input to a one-element actor list.
- Do not sort actor entries by actor priority.
- Use schema version `4`.

## Decoder contract

Add `decodeActorPriorityRequest`.

- All actor priorities absent → `none`.
- At least one priority present → `some` containing exactly the explicitly
  prioritized actors.
- Duplicate actor names → rejection.
- Negative wire priority → schema or decoder rejection.
- Partial priority assignment → preserve the partial request.
- Incomplete coverage retains the existing no-filtering behavior.

## Java bridge contract

- Iterate all `MainRebecDefinition` values in declaration order.
- Index all `ReactiveClassDeclaration` values by name.
- Remove singleton cardinality requirements for main actors and reactive
  classes.
- Retain existence and reference-integrity validation.
- Export actor-instance priority separately from
  `LOCAL_PRIORITY_ANNOTATION`.
- Preserve local message-server `@priority`.
- Perform no actor-priority sorting.

## Translation contract

Use the existing pipeline:

`ActorPriorityRequest` → `compileActorPriorityRequest` →
`ActorOrderRequest`

Lower `Nat` is stronger. Equal priorities remain nondeterministic. Absent and
incomplete requests perform no actor-priority filtering. A literal target
actor-priority field is not required; equivalent compiled ordering is
sufficient.

## Change surfaces

1. `Relico/Frontend/MultiStorePayloadSchema.lean` — Add RawMultiStorePayloadActorInstance and a declaration-ordered actors list while leaving message-server priority unchanged.
2. `frontend/schema/multi-store-payload-v1.schema.json` — Add an actors array and optional non-negative per-instance priority, then bump the schema version.
3. `Relico/Frontend/MultiStorePayloadDecoder.lean` — Decode actor instances, validate unique names and reactive-class references, and construct ActorPriorityRequest.
4. `frontend/java-bridge/RebecaMultiStorePayloadJsonExporter.java` — Export every main-block actor and remove singleton main-actor and reactive-class restrictions.
5. `frontend/java-bridge/RebecaMultiStoreJsonExporter.java` — Apply the same multi-actor normalization while preserving local @priority metadata.
6. `Relico/Translation/GlobalMultiStorePayloadActorOrder.lean` — Reuse compileActorPriorityRequest to produce ActorOrderRequest; no literal target priority field is required.
7. `Relico/Tests and frontend/fixtures/multi-store-payload` — Implement the ten-case compatibility and multi-actor validation matrix.

## Regression matrix

1. **legacy-singleton-no-priority** — Legacy singleton payload with no actor priority. Expected: Normalize to one actor, decode the request as none, and preserve current behavior.
2. **multi-actor-no-priority** — Two actor instances with both actor priorities absent. Expected: Preserve declaration order, decode the request as none, and perform no filtering.
3. **multi-actor-reversed-priority** — Two simultaneously ready actors in paired fixtures whose actor priorities are reversed. Expected: The decoded requests differ and the selected-actor trace changes consistently with lower-Nat strength.
4. **equal-actor-priority** — Two simultaneously ready actors with equal actor priorities. Expected: Both actors remain eligible; no deterministic tie-breaking is introduced.
5. **partial-actor-priority** — Only one of multiple actor instances has an explicit actor priority. Expected: Preserve the partial request; incomplete coverage causes no actor-priority filtering.
6. **duplicate-actor-name** — Two actor-instance entries share the same actor name. Expected: Reject the frontend model.
7. **negative-wire-priority** — A serialized actor priority is a negative integer. Expected: Reject through JSON-schema or decoder validation.
8. **local-vs-actor-priority** — Actor priority and message-server @priority are both present with opposing numeric values. Expected: Actor priority controls cross-actor selection; message-server priority controls local reaction selection.
9. **unknown-reactive-class** — An actor instance references an undeclared reactive class. Expected: Reject the unresolved actor-instance class reference.
10. **schema-round-trip** — A multi-actor payload contains mixed optional actor priorities. Expected: Java export, JSON validation, Lean decoding, ActorPriorityRequest construction, and ActorOrderRequest compilation agree.

## Implementation status

Complete:

- schema design;
- parser-normalization design;
- decoder-mapping design;
- Java-exporter generalization design;
- translation mapping;
- ten-case regression matrix.

Pending:

- Lean schema implementation;
- JSON-schema implementation;
- Lean decoder implementation;
- Java exporter implementation;
- multi-actor fixtures and end-to-end validation.

## Validation

- Full `lake build`: **474 jobs passed**
- Source mutation: **none**
- Canonical README mutation: **none**
- Original repository mutation: **none**
- Staging, commit, and push: **none**

## Progress

- Before: **89%**
- After: **90%**
- Remaining: **10%**

## Next phase

**phase4d7c-frontend-actor-priority-schema-and-decoder-implementation**
