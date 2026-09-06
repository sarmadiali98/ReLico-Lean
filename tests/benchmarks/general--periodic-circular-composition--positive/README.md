# `general--periodic-circular-composition--positive`

A **general**-family positive benchmark: a DTR-fragment redesign of the examples2 model `Periodic_Circular_Composition`, which the model checker rejects with a queue overflow.

## Provenance

### 1. Original purpose

A message circulates a ring of four nodes, one hop per period, forever.

### 2. Why the original fails, and what is not the problem

The overflow is caused by all four constructors armed their own token, so four independent timer loops ran and any one node's queue grew under an interleaving that starved it. This is a real boundedness defect of the original under the model checker's unfair interleavings -- the composition pattern under test is not the defect, and no queue bound fixes it, which is why the originals all declare bound 100 and still overflow.

### 3. Semantic changes made

Exactly one token exists: only node 0 arms, and each hop re-arms on receipt rather than on a timer, so every emission is gated by the previous one having been consumed. the four self-timers are gone; per-node emission stays periodic, one period per hop. This is the same redesign policy the tcsma-inspired actor-priority benchmark established: couple each producer to the consumption of what it produced, so a starved consumer stops its producer rather than accumulating.

### 4. Preserved behavioural property

A message circulates a ring of four nodes, one hop per period, forever, now with bounded queues and the model checker reporting `satisfied`, and the generated LF compiling and running.

## Stages

8 stages, terminal `runtime`: source, rmc, parser-json, decoded-dtr-ast, translated-lf-ast, lf-source, lfc, runtime. This row owns no Lean obligations, so it carries no formal-witness stage; its evidence is the pipeline artifacts themselves.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free; every recurrence is delayed by one period, so the runtime terminates within its budget.
