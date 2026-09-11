# `general--periodic-sequential-composition--positive`

A **general**-family positive benchmark: a DTR-fragment redesign of the examples2 model `Periodic_Sequential_Composition`, which the model checker rejects with a queue overflow.

## Provenance

### 1. Original purpose

A message traverses a line of four nodes, one hop per period, and the last node holds it periodically.

### 2. Why the original fails, and what is not the problem

The overflow is caused by three nodes armed themselves on independent timers while the line's empty receivers never had to run; the islast flags were also inverted relative to the model's own topology, arming every node except the first. This is a real boundedness defect of the original under the model checker's unfair interleavings -- the composition pattern under test is not the defect, and no queue bound fixes it, which is why the originals all declare bound 100 and still overflow.

### 3. Semantic changes made

Only the non-last nodes relay on receipt, the last node re-arms itself after one period, and the islast flag is assigned to the topologically last node as its name requires. both @priority annotations and the node3 self-loop are kept. This is the same redesign policy the tcsma-inspired actor-priority benchmark established: couple each producer to the consumption of what it produced, so a starved consumer stops its producer rather than accumulating.

### 4. Preserved behavioural property

A message traverses a line of four nodes, one hop per period, and the last node holds it periodically, now with bounded queues and the model checker reporting `satisfied`, and the generated LF compiling and running.

## Stages

8 stages, terminal `runtime`: source, rmc, parser-json, decoded-dtr-ast, translated-lf-ast, lf-source, lfc, runtime. This row owns no Lean obligations, so it carries no formal-witness stage; its evidence is the pipeline artifacts themselves.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free; every recurrence is delayed by one period, so the runtime terminates within its budget.
