# YARN deadline FIFO 2AM - adaptation record

Source: `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-2AMs.rebeca`.

## Property boundary

The shared `yarn.property` file is intentionally excluded. The external property language is not
part of the verified executable translation path, so this fixture evaluates translation and runtime
behavior only.

## Approved fragment normalizations

### Three-entry FIFO

The fixed `int[3] fifo_queue` is represented by scalar fields `fifo0`, `fifo1`, and `fifo2`.
`QUEUE_SIZE` is initialized once to 3 and never changed, so every reachable index is 0, 1, or 2.

### Fixed loop expansion

Each dispatch shift is expanded as `fifo0 = fifo1`, `fifo1 = fifo2`, followed by appending the
default deadline to `fifo2`. The queue-aging and expiration shifts are expanded in index order.
This preserves the original behavior where an expiration at an earlier index changes the job aged
at the next index.

### Increment and decrement syntax

Every `++` and `--` operation is written as an ordinary assignment, including queue aging,
`m_queue_misses`, and `doneJobs`. No update is added or removed.

### Finite delay specialization

The queue invariants give dispatched `dline` values in 1-3, while `completion` is always 2. The
miss branch therefore implies `dline == 1`, so `after(dline)` becomes `after(1)`. The completion
branch's `after(completion)` becomes `after(2)`.

### Sender identity

The original `ResourceManager.update` distinguishes `am1` from `am2` through the implicit sender.
The normalized model passes a fixed identity tag through `runJob` and `update`: 1 for `am1` and 2
for `am2`. `update` frees the corresponding application master, preserving the original routing.

### Local boolean initialization

The parser bridge requires local variables to have simple initializers, so
`boolean deadline_miss;` is written as `boolean deadline_miss = false;`. Both branches assign it
before its first read, making the initializer unobservable.

No heartbeat, traffic, protocol action, queue operation, or termination behavior is added. The
two-master topology, sequential dispatch order, periodic `checkQueue() after(1)`, FIFO behavior,
deadline-miss handling, job-completion cycle, and timing order are retained.
