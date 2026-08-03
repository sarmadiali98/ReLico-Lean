# Actor-Priority Source Semantics Audit

## Status

Phase 2A static audit completed after correcting an audit-design error.

Published ReLico commit: `57b87cf45eacf9c09af9fa9b45c2ae7d7fc2fc5f`

Official compiler commit: `91dcffcc67fd320fdf27863adbba4d6fab28ac43`

Official model-checker commit: `fb4197f4b3c54c19d569b46c614024fe75bbf4b6`

Actual Java annotation-path classification:
**DIRECT_ACTOR_ANNOTATION_ACCESS_FOUND**

No Approach A or Approach B implementation has started.

## Current Lean theorem domain

The current global source and target ASTs contain actors, topology, and
global execution state, but no actor-priority metadata.

The current source and target one-step relations do not autonomously
select an actor. They compare steps carrying an actor-indexed dispatch
witness.

Therefore actor-priority-aware scheduling is provisionally classified as
**OUTSIDE CURRENT FRAGMENT** for Claim A. This is a domain statement, not
a proof of semantic non-necessity for full Timed Rebeca.

## Existing boundary theorem

The actor-priority boundary represents a request externally as an option,
accepts exactly absence, and rejects every explicit assignment. Its
universal rejection theorem includes an explicit empty assignment.

This is a restriction theorem. It is not yet a parser-enforcement theorem.

## Local priority

Local message-server priority is represented in the bridge schema and is
preserved by reaction compilation.

This evidence does not implement or justify cross-actor priority.

## Actual Java bridge inspection

The initial Phase-2A audit incorrectly required the literal source form
`actor.getAnnotations()` and a particular diagnostic phrase.

The repaired audit records actual Java contexts in:

`phase2/PHASE2_FRONTEND_ANNOTATION_BEHAVIOR.tsv`

The resulting static classification is:

**DIRECT_ACTOR_ANNOTATION_ACCESS_FOUND**

Regardless of this static classification, Claim B remains
**NOT YET PROVED**. Dynamic probes must establish the treatment of:

1. absent actor-priority syntax;
2. a nonempty actor-priority declaration;
3. reversed actor-priority declarations;
4. an explicit empty declaration;
5. local message-server priority without actor priority;
6. whether JSON, decoded AST, or LF output is produced after rejection.

Schema omission alone cannot establish rejection.

## Official source evidence

Immutable snapshots of the official compiler and model checker were
captured at the commits above. Focused hits are retained in the Phase-2
TSV artifacts.

Those search results are navigation evidence. Phase 2B must identify the
exact grammar, object-model field, and scheduling behavior through direct
source interpretation and executable probes.

## Canonical paper

Page-tagged paper hits were captured. The paper was not edited.

Phase 2B must map each relevant statement to its page, theorem scope,
priority level, and required correction or qualification.

## Benchmark registry

Every priority-related benchmark and obligation record was captured.

Each must still be classified as local priority, actor priority,
interaction, ambiguous, or mislabeled.

## Provisional claim matrix

| Claim | Phase-2A classification |
|---|---|
| A | OUTSIDE CURRENT FRAGMENT |
| B | NOT YET PROVED |
| C | NOT YET PROVED |
| D | NOT YET PROVED |
| E | NOT YET PROVED |
| F | NOT YET PROVED |
| G | NOT YET PROVED |

## Claims still prohibited

The current evidence does not justify saying:

- actor priority is unnecessary for full Timed Rebeca;
- the frontend rejects every actor-priority declaration;
- explicit empty declarations are handled correctly;
- local priority implements actor priority;
- current correspondence derives the same actor selection as RMC;
- actor priority cannot change observable behavior;
- the current LF architecture can encode actor priority faithfully;
- every priority benchmark concerns only local priority;
- the canonical paper's unrestricted wording is defensible.

## Next phase

Phase 2B must perform direct Lean theorem elaboration, exact grammar and
object-model interpretation, dynamic parser and JSON-bridge probes, and
official RMC behavior probes before either exclusion or inclusion is
implemented.
