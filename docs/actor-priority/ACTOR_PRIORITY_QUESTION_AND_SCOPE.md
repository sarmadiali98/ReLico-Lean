# Actor-Priority Question and Scope

## Status

This document is the Phase 1 scope contract for the actor-priority
necessity investigation.

Published baseline commit: `57b87cf45eacf9c09af9fa9b45c2ae7d7fc2fc5f`

Investigation branch: `investigation/actor-priority-necessity-20260802`

No actor-priority implementation or semantic conclusion exists at this
phase. Every claim remains classified as **NOT YET PROVED** until the
required evidence is collected and reviewed.

## Purpose

The investigation must not answer “Are actor priorities necessary?” as
one context-free yes/no question. It must distinguish the following
scopes:

1. Current Lean equivalence and correspondence theorems.
2. The exact fragment encoded by the production ASTs and frontend.
3. The intended Timed Rebeca frontend acceptance surface.
4. Models with multiple simultaneously enabled actors.
5. Existing and planned benchmark obligations.
6. The canonical paper's broader equivalence wording.
7. Faithful encoding in the current Lingua Franca target architecture.

The authoritative row definitions, evidence requirements, and decision
rules are recorded in `ACTOR_PRIORITY_CLAIM_MATRIX.tsv`.

## Working terminology

These terms are provisional navigation definitions. Phase 2 must replace
or refine them using authoritative source semantics and actual
declarations.

### Local or message-server priority

Priority used to choose among handlers, message servers, reactions, or
events within one actor or reactor.

### Actor-level or global priority

Priority used to choose between distinct actors when more than one actor
is simultaneously eligible to execute.

Local priority and actor priority must remain separate in source models,
tests, coverage mappings, theorem assumptions, and conclusions. Evidence
for one is not evidence for the other.

### Explicit absence, explicit empty declaration, and nonempty declaration

The investigation must distinguish:

- no actor-priority syntax or metadata;
- actor-priority syntax that is explicitly present but empty;
- one or more explicit actor-priority assignments.

A frontend that silently erases these distinctions does not mechanically
enforce an actor-priority-free fragment.

## Permitted classifications

Each claim must ultimately receive exactly one classification:

- **YES**: required in the stated scope.
- **NO**: demonstrated unnecessary in the stated scope without assuming
  the disputed feature away.
- **CONDITIONAL**: the answer depends on an explicit fragment,
  architecture, hypothesis, or claim wording.
- **OUTSIDE CURRENT FRAGMENT**: mechanically excluded by the supported
  syntax, schema, AST, validation path, and theorem domain.
- **NOT YET PROVED**: available evidence is insufficient.

“Outside current fragment” is not equivalent to “semantically
unnecessary for Timed Rebeca.”

## Evidence hierarchy

Final classifications must cite concrete, reproducible evidence. Accepted
evidence classes are:

1. Exact Lean declarations and successful elaboration.
2. Parser grammar, parser behavior, JSON schema, and decoder behavior.
3. Authoritative Timed Rebeca or RMC semantics and official tool output.
4. Source models that discriminate actor selection from local priority.
5. RMC verdicts, traces, reachable states, or execution-order evidence.
6. Generated LF, lfc output, and bounded native runtime behavior.
7. Benchmark manifests, expected terminal stages, artifacts, and coverage.
8. Minimal counterexamples and systematically enumerated model families.
9. Page-specific canonical-paper statements.
10. Independent semantic and trust-boundary review.

Search hits, comments, filenames, labels, intuition, or implementation
difficulty are not sufficient by themselves.

## Claim questions

### A — Current Lean theorems

Determine whether actor priority is required by the exact theorem
statements currently present, absent by construction from their quantified
ASTs, or excluded by an explicit hypothesis.

### B — Current supported fragment

Determine whether the production parser-to-Lean path mechanically rejects
every explicit actor-priority request or instead ignores, erases, or cannot
observe it.

### C — Intended frontend language

Determine whether the intended Timed Rebeca frontend accepts
actor-priority syntax and whether the product's claimed source language is
narrower than that acceptance surface.

### D — Simultaneously enabled actors

Determine experimentally whether changing only actor priority changes an
observable source behavior when multiple actors are enabled at the same
logical time.

### E — Benchmark obligations

Separate every local-priority obligation from every actor-level-priority
obligation and identify ambiguous or incorrect mappings.

### F — Canonical-paper wording

Compare the paper's source-language and equivalence wording against the
actual supported fragment and discriminating source semantics.

### G — LF architectural expressiveness

Determine whether the current LF architecture can implement cross-actor
priority directly or whether it requires a coordinator, strengthened
scheduler, additional logical ordering, or another explicit mechanism.

## Approach A acceptance condition

The exclusion approach passes only when all explicit actor-priority
declarations, including explicit empty declarations where semantically
distinct, are observed and rejected before translation; local priority
remains represented; negative benchmarks terminate at the rejection
stage; and correspondence claims state the restriction explicitly.

A Lean predicate alone is insufficient.

## Approach B acceptance condition

The inclusion approach must be tested with discriminating multi-actor
models, official RMC evidence, reversed-priority controls, bounded
systematic search, current-pipeline comparison, an isolated scheduler and
translation prototype, and an explicit proof-obligation audit.

A complete merged proof is not required merely to establish necessity,
but implementation difficulty is not evidence of non-necessity.

## Prohibited premature conclusions

Until Phases 2 through 4 are complete, the investigation must not claim:

- actor priority is unnecessary for Timed Rebeca;
- local priority implements actor priority;
- the current theorem covers actor-priority models;
- parser omission is equivalent to parser rejection;
- an LF reaction priority automatically enforces cross-reactor order;
- a passing non-discriminating example establishes equivalence;
- the paper's broad language is already justified;
- actor priority must be merged merely because an inclusion prototype is
  possible.

## Phase gates

Phase 1 creates only this scope contract, the claim matrix, a reproducible
baseline, and a candidate-evidence inventory.

Phase 2 must audit the canonical paper, Lean semantics, parser and JSON
bridge, official Timed Rebeca/RMC behavior, benchmark registry, and
boundary theorems.

Phases 3 and 4 must then test exclusion and inclusion separately.

No source implementation, staging, commit, push, or remote mutation is
permitted in Phase 1.
