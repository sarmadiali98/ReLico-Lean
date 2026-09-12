# `general--message-circulation--positive`

A **general**-family positive benchmark: a DTR-fragment redesign of the examples2 model `A_First_Example`, which the model checker rejects with a queue overflow.

## Provenance

### 1. Original purpose

A message circulates between two nodes on a one-period delay, now with the delivery recorded in state.

### 2. Why the original fails, and what is not the problem

The overflow is caused by the sender rescheduled itself on a one-period timer while its peer's empty receiver never had to run, so under an unfair interleaving the peer's queue grew by one message per period at any bound. This is a real boundedness defect of the original under the model checker's unfair interleavings -- the composition pattern under test is not the defect, and no queue bound fixes it, which is why the originals all declare bound 100 and still overflow.

### 3. Semantic changes made

The consumer re-arms the producer: rcvmsg stores the message into a new `seen` state variable and hands `next.sendmsg after(1)`, so one message is in flight at a time; the queue bound drops from 100 to 4. This is the same redesign policy the tcsma-inspired actor-priority benchmark established: couple each producer to the consumption of what it produced, so a starved consumer stops its producer rather than accumulating.

### 4. Preserved behavioural property

A message circulates between two nodes on a one-period delay, now with the delivery recorded in state, now with bounded queues and the model checker reporting `satisfied`, and the generated LF compiling and running.

## Stages

9 stages, terminal `runtime`: source, rmc, rmc-properties, parser-json, decoded-dtr-ast, translated-lf-ast, lf-source, lfc, runtime. Source-level assertions check observed payload bounds and use an expected-`FALSE` counterexample to witness both nodes observing the unit payload.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free; every recurrence is delayed by one period, so the runtime terminates within its budget.
