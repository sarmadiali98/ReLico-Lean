# Phase 2B2E Semantic Graph Witness

## Status

The nine runtime executions from the independent witness audit were
reanalyzed as labeled transition systems.

Raw transcript serialization was not used as the semantic equality
criterion.

## Source-delta audit

Base and reversed sources differ only in actor-priority values:
**true**

The first two worker priorities are exactly reversed:
**true**

The absent source equals the base source after removing actor-priority
annotations:
**true**

Base priorities:
`[1, 2, 3]`

Reversed priorities:
`[2, 1, 3]`

## Canonicalization contract

The semantic label of a transition contains:

1. message-server sender;
2. message-server owner;
3. message-server title.

The following are discarded:

- generated state identifiers;
- XML element order;
- file paths;
- timing measurements;
- generated implementation text;
- build transcript text.

The load-bearing observable is the reachable ordered dispatch-trace
language.

## Variant results

| Variant | Semantic graph stable | First worker dispatch | Worker FIRE-order language | Assertion failure reachable |
|---|---|---|---|---|
| base | true | `["workera"]` | `[["workera","workerb"]]` | false |
| reversed | true | `["workerb"]` | `[["workerb","workera"]]` | false |
| absent | true | `["workera"]` | `[["workera","workerb"]]` | true |

## Base-versus-reversed comparison

All runs exited successfully without timeout:
**true**

Base and reversed semantic graphs are stable across three executions:
**true**

Worker FIRE-order languages are nonempty:
**true**

Worker FIRE-order languages are disjoint:
**true**

First worker-dispatch sets differ:
**true**

Canonical transition-prefix languages differ:
**true**

Observer HIT-order languages differ:
**false**

Property verdicts differ:
**false**

## Classification

**SEMANTIC_TRACE_WITNESS_CONFIRMED_ACTOR_PRIORITY_REVERSAL_CHANGES_REACHABLE_DISPATCH_TRACE_LANGUAGE**

Semantic trace witness confirmed:
**true**

## Defensible Claim D statement

For the tested RMC model, reversing only the first two actor priorities changes the canonical reachable actor-dispatch trace language.

This does not establish that every Timed Rebeca model requires actor
priority. It establishes behavioral relevance for the tested model when
only actor priorities are reversed.

It also does not place actor-priority scheduling inside the current ReLico
correspondence theorem. That remains a separate fragment-boundary and
proof-architecture question.

## Provisional claims

Claim A:
**OUTSIDE CURRENT FRAGMENT**

Claim B:
**NOT YET PROVED**

Claim C:
**CONDITIONAL — official RMC accepts actor-priority models**

Claim D:
**YES**

Claims E through G:
**NOT YET PROVED**

## Next phase

**phase2b3-classify-phase2-evidence-before-approach-implementations**
