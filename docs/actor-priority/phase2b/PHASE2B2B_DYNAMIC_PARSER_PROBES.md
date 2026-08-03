# Phase 2B2B Dynamic Parser Probes

## Status

The actual production payload parser/JSON bridge was executed against
external copies of the accepted baseline model.

No tracked source was modified. No RMC behavioral experiment was run.

## Probe construction

Baseline message-server declaration line:
**14**

Baseline main-block line:
**20**

Baseline main actor declaration line:
**21**

Each non-control model differs from the accepted baseline by one inserted
annotation line.

## Results

| Probe | Annotation | Placement | Exit | Classification | JSON equals absence |
|---|---|---|---:|---|---|
| PARSER-ABSENT | none | none | 0 | ACCEPTED_PARSEABLE_JSON | true |
| PARSER-LOCAL-PRIORITY-1 | `@priority(1)` | first-message-server | 0 | ACCEPTED_PARSEABLE_JSON | false |
| PARSER-ACTOR-PRIORITY-1 | `@priority(1)` | first-main-actor | 1 | REJECTED_NO_JSON | false |
| PARSER-ACTOR-PRIORITY-2 | `@priority(2)` | first-main-actor | 1 | REJECTED_NO_JSON | false |
| PARSER-ACTOR-PRIORITY-STRING-2 | `@priority("2")` | first-main-actor | 1 | REJECTED_NO_JSON | false |
| PARSER-ACTOR-PRIORITY-EMPTY-PARENS | `@priority()` | first-main-actor | 1 | REJECTED_NO_JSON | false |
| PARSER-ACTOR-PRIORITY-EMPTY-STRING | `@priority("")` | first-main-actor | 1 | REJECTED_NO_JSON | false |
| PARSER-ACTOR-PRIORITY-BARE | `@priority` | first-main-actor | 1 | REJECTED_NO_JSON | false |

## Control validation

- All parser controls passed.

Local priority value `1` observed in emitted JSON:
**true**

## Nonempty actor-priority classification

**ALL_OFFICIAL_NONEMPTY_ACTOR_PRIORITY_FORMS_REJECTED_WITHOUT_JSON**

This classification is based on the three official forms:

- `@priority(1)`
- `@priority(2)`
- `@priority("2")`

## Explicit-empty candidate classification

**ALL_TESTED_EMPTY_CANDIDATE_FORMS_REJECTED**

The empty candidates were:

- `@priority()`
- `@priority("")`
- bare `@priority`

These are grammar probes. They are not asserted to be official valid
source forms unless accepted by the parser.

## Downstream artifact boundary

No decoded DTR AST, formal witness, translated LF AST, LF source, lfc
artifact, or runtime artifact was produced by any parser invocation.

## Claim B status

Claim B remains **NOT YET PROVED**.

The dynamic parser behavior is now recorded, but final exclusion still
requires Approach A to connect the observed rejection path to:

1. an explicit supported-fragment boundary;
2. production diagnostics;
3. negative benchmark expectations;
4. proof that no translation path bypasses rejection;
5. the current actor-priority boundary theorem.

## Next phase

Phase 2B2C must construct and run official RMC models in which two actors
are simultaneously enabled and changing only actor priority can alter an
observable result.
