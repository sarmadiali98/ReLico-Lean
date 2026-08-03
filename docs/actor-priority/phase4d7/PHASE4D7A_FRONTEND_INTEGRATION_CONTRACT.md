# Phase 4D7A Frontend Actor-Priority Interface Audit

## Result

**FRONTEND_MESSAGE_PRIORITY_BOUND_ACTOR_PRIORITY_FIELD_ABSENT_SINGLE_MAIN_ACTOR_BRIDGE_RESTRICTION_CONFIRMED**

## Bound production surfaces

1. `Relico/Frontend/MultiStorePayloadSchema.lean` — Contains the frontend message-server `priority : Option Nat` field.
2. `Relico/Frontend/MultiStorePayloadDecoder.lean` — Decodes the frontend message-server priority into the source syntax.
3. `frontend/schema/multi-store-payload-v1.schema.json` — Defines serialized message-priority properties but no actor-priority property.
4. `frontend/java-bridge/RebecaMultiStorePayloadJsonExporter.java` — Exports payload frontend data, local priority metadata, and actor/class surfaces.
5. `frontend/java-bridge/RebecaMultiStoreJsonExporter.java` — Exports multi-store frontend data and contains matching parser-bridge constraints.
6. `tests/actor-priority/approach-a-single-main-actor-payload-exclusion/run-approach-a-exclusion.sh` — Mechanically tests the current exact single-main-actor payload profile.
7. `tests/actor-priority/approach-a-single-main-actor-payload-exclusion/manifest.json` — Records the accepted current-profile frontend exclusion boundary.

## Established frontend facts

- The payload frontend schema contains message-server
  `priority : Option Nat`.
- The payload decoder copies that priority into source message-server syntax.
- The serialized payload schema contains message-priority data.
- The Java bridge has local-priority annotation/export logic.
- The Java payload bridge contains main-actor and reactive-class handling
  together with cardinality restrictions.
- The current exact-profile exclusion test records the single-main-actor
  payload boundary.
- No actor-level priority field or serialized actor-priority property exists
  in the bound frontend-facing schema and exporter surfaces.

## Semantic distinction

Message-server priority is local reaction scheduling metadata. Actor priority
orders simultaneously ready actor instances. These are distinct semantic
layers and must not be represented by the same frontend field.

## Required integration contract

1. Add actor-level priority metadata to the frontend actor-instance model.
2. Preserve every actor instance declared by the main block.
3. Generalize the bridge beyond its current one-main-actor and
   one-reactive-class payload profile.
4. Export actor-instance priority separately from local `@priority`.
5. Decode actor priority into `ActorPriorityRequest`.
6. Compile it to the existing `ActorOrderRequest` target interface.
7. Preserve existing absent-priority and priority-inert behavior.
8. Add multi-actor parser, decoder, translation, and end-to-end fixtures.

## Existing completed proof stack

- Actor-selection correspondence: complete
- One-step actor-dispatch correspondence: complete
- Strong finite actor-dispatch correspondence: complete
- Actor-dispatch observable correspondence: complete
- Frontend actor-priority integration: incomplete

## Validation

- Full `lake build`: 474 jobs passed
- Bound evidence rows: 96
- Repository source mutation: none
- Canonical README mutation: none
- Original repository mutation: none
- Staging, commit, and push: none

## Progress

- Before: 88%
- After: 89%
- Remaining: 11%

## Next phase

**phase4d7b-frontend-actor-priority-schema-and-parser-design**
