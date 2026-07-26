# Detailed observable multi-store semantics

Status: accepted

Date: 2026-07-26

## Purpose

The executable multi-store DTR and generated-LF semantics use macro dispatch
transitions.

A macro dispatch currently combines:

- scheduler selection;
- logical-time or complete-tag advancement;
- removal of one pending occurrence;
- activation of the selected handler or reaction body.

The paper-level correctness argument distinguishes observable time progression,
observable message consumption or reaction firing, and internal administrative
steps.

This checkpoint introduces a detailed semantic layer without modifying the
existing executable macro semantics.

## DTR labels

The detailed DTR layer contains:

- `tau`;
- `timeAdvance`;
- `consume`.

All executable DTR statement transitions, including assignments and
self-sends, are classified as internal in this layer.

A future DTR macro dispatch refines to:

```text
timeAdvance ; consume

A dispatch at the current logical time refines to:

consume
Generated-LF labels

The detailed generated-LF layer contains:

tau;
timeAdvance;
microstepAdvance;
consume.

Generated reaction-body statement execution is internal.

Metric-time progression is observable. Pure LF microstep progression is
internal. Reaction firing is observable.

A future LF macro dispatch to microstep zero refines to:

timeAdvance ; consume

A future LF macro dispatch to a positive microstep refines to:

timeAdvance ; microstepAdvance ; consume

A same-metric-time dispatch to a later microstep refines to:

microstepAdvance ; consume

A dispatch at the current complete tag refines to:

consume
Intermediate phase states

Detailed phase states are proof-oriented semantic states.

They record the macro-dispatch endpoints, selected occurrence, selected
handler or reaction, and the originating macro-dispatch witness.

This ensures that an intermediate time or microstep phase cannot be created
for an invalid dispatch.

These phase states are not executable compiler runtime states. They form the
semantic refinement layer used to expose the paper-level transition
granularity.

Observable projection

Detailed DTR projection removes tau and retains:

metric-time progression;
message consumption.

Detailed LF projection removes:

tau;
microstepAdvance.

It retains:

metric-time progression;
reaction firing.

DTR message names and generated LF action names remain in separate observable
alphabets at this checkpoint. Their correspondence will be defined through the
translation function in the weak-simulation layer.

Proven refinement results

The checkpoint establishes:

every DTR statement macro step is one detailed internal step;
every LF statement macro step is one detailed internal step;
every DTR macro dispatch has a finite detailed execution;
every LF macro dispatch has a finite detailed execution;
DTR dispatch never moves logical time backward;
LF dispatch preserves complete-tag order;
equal-metric-time LF dispatch never moves to an earlier microstep.
Non-claims

This checkpoint does not prove:

DTR/LF weak simulation;
weak bisimulation;
observable trace equivalence;
unrestricted zero-delay priority preservation;
equal-priority nondeterminism preservation;
actor-level or global priority preservation.

The positive-delay restriction for priority-sensitive execution
correspondence remains unchanged.

Next checkpoint

The next checkpoint will instantiate the generic weak-transition
infrastructure for the detailed DTR and LF relations and prove basic closure
and projection lemmas.
