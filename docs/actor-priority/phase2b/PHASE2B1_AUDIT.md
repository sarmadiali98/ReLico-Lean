# Phase 2B1 Actor-Priority Audit

## Status

This phase resolves executable evidence inputs before dynamic parser and
RMC experiments.

Published ReLico commit: `57b87cf45eacf9c09af9fa9b45c2ae7d7fc2fc5f`

Official compiler commit: `91dcffcc67fd320fdf27863adbba4d6fab28ac43`

Official model-checker commit: `fb4197f4b3c54c19d569b46c614024fe75bbf4b6`

## Official syntax evidence

Syntax-resolution status:

**ACTOR_PRIORITY_CANDIDATE_FORMS_IDENTIFIED**

Observed candidate forms:

- `@priority("2")`
- `@priority(1)`
- `@priority(3)`

The complete source contexts are in
`PHASE2B1_OFFICIAL_PRIORITY_SYNTAX.tsv`.

A candidate form is not yet an accepted semantic conclusion. Phase 2B2
must execute the syntax through the official parser and RMC.

## Local versus actor-level evidence

Actor/global candidate rows: **2**

Local message-server rows: **4**

Official `.rebeca` example rows: **3**

These categories are retained separately. Generic uses of “priority” are
not automatically classified as actor-level semantics.

## Official scheduler evidence

Model-checker scheduler and priority contexts were extracted into
`PHASE2B1_OFFICIAL_SCHEDULER_SEMANTICS.tsv`.

The extraction identifies implementation points but does not substitute
for reversed-priority behavioral experiments.

## Current frontend rejection path

The production Java bridge has direct actor-annotation access and a
main-actor annotation context.

Static `assertNoAnnotations` linkage to that path:

**false**

Dynamic rejection is still unproved. Phase 2B2 must capture exit status,
diagnostic text, JSON production, decoded-AST production, and LF
production for every probe case.

## Parser artifact entrypoints

Manifest main classes:

- No manifest main class was found.

Candidate parser/exporter classes and build commands are recorded in
`PHASE2B1_PARSER_ENTRYPOINTS.tsv`.

## Current Lean theorem boundary

Relevant declaration signatures are recorded in
`PHASE2B1_THEOREM_SIGNATURES.tsv`.

The direct elaboration step for the boundary, declared fragment,
correspondence, one-step, finite-execution, schema, decoder, and bridge
modules is run separately by this command.

The current evidence continues to support only this provisional statement:

> Actor-priority scheduling is outside the AST and autonomous step
> selection modeled by the current global correspondence layer.

It does not support saying that actor priority is unnecessary for full
Timed Rebeca.

## Phase 2B2 gate

Phase 2B2 must execute:

1. absent actor priority;
2. local priority only;
3. nonempty actor priority;
4. reversed actor priority;
5. explicit empty actor priority;
6. discriminating RMC base ordering;
7. discriminating RMC reversed ordering;
8. equivalent no-actor-priority control.

No Approach A or Approach B production implementation begins before those
outputs are classified.
