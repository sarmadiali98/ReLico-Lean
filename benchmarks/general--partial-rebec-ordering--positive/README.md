# `general--partial-rebec-ordering--positive`

A **general**-family positive benchmark: a DTR-fragment redesign of the examples2 model `Paritial_Ordering_Rebec`, which the model checker rejects with a queue overflow.

## Provenance

### 1. Original purpose

Two independent medium-receiver chains are armed together, ordered within a chain and unordered between chains.

### 2. Why the original fails, and what is not the problem

The overflow is caused by the sender rescheduled itself on a timer while its two medium-receiver chains, all with empty terminal bodies, never had to run. This is a real boundedness defect of the original under the model checker's unfair interleavings -- the composition pattern under test is not the defect, and no queue bound fixes it, which is why the originals all declare bound 100 and still overflow.

### 3. Semantic changes made

Each receiver acknowledges to its medium, each medium to the sender, through new back-edges; the sender counts two chain resolutions and re-arms only then. This is the same redesign policy the tcsma-inspired actor-priority benchmark established: couple each producer to the consumption of what it produced, so a starved consumer stops its producer rather than accumulating.

### 4. Preserved behavioural property

Two independent medium-receiver chains are armed together, ordered within a chain and unordered between chains, now with bounded queues and the model checker reporting `satisfied`, and the generated LF compiling and running.

## Stages

8 stages, terminal `runtime`: source, rmc, parser-json, decoded-dtr-ast, translated-lf-ast, lf-source, lfc, runtime. This row owns no Lean obligations, so it carries no formal-witness stage; its evidence is the pipeline artifacts themselves.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free; every recurrence is delayed by one period, so the runtime terminates within its budget.
