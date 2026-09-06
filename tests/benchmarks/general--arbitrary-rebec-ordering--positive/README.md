# `general--arbitrary-rebec-ordering--positive`

A **general**-family positive benchmark: a DTR-fragment redesign of the examples2 model `Arbitrary_Ordering_Rebec`, which the model checker rejects with a queue overflow.

## Provenance

### 1. Original purpose

One message is fanned out to four receivers armed together, in whatever order the scheduler chooses, and the next round begins only when all four have run.

### 2. Why the original fails, and what is not the problem

The overflow is caused by the sender rescheduled itself on a timer while its four receivers, all with empty bodies, never had to run. This is a real boundedness defect of the original under the model checker's unfair interleavings -- the composition pattern under test is not the defect, and no queue bound fixes it, which is why the originals all declare bound 100 and still overflow.

### 3. Semantic changes made

Each receiver acknowledges with its id through a new back-edge to the sender; the sender counts four acknowledgements and re-arms only then. the receivers gain a `sender` knownrebec and the sender a `resolved` counter, bounded at four. This is the same redesign policy the tcsma-inspired actor-priority benchmark established: couple each producer to the consumption of what it produced, so a starved consumer stops its producer rather than accumulating.

### 4. Preserved behavioural property

One message is fanned out to four receivers armed together, in whatever order the scheduler chooses, and the next round begins only when all four have run, now with bounded queues and the model checker reporting `satisfied`, and the generated LF compiling and running.

## Stages

8 stages, terminal `runtime`: source, rmc, parser-json, decoded-dtr-ast, translated-lf-ast, lf-source, lfc, runtime. This row owns no Lean obligations, so it carries no formal-witness stage; its evidence is the pipeline artifacts themselves.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free; every recurrence is delayed by one period, so the runtime terminates within its budget.
