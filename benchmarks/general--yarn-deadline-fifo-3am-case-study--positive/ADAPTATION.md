# YARN deadline FIFO 3AM - adaptation record

Source: `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-3AMs.rebeca`.

## Property boundary

The shared `yarn.property` file is intentionally excluded. The external property language is not
part of the verified executable translation path, so this fixture evaluates translation and runtime
behavior only.

## Approved fragment normalizations

### Four-entry FIFO

The fixed `int[4] fifo_queue` is represented by scalar fields `fifo0` through `fifo3`.
`QUEUE_SIZE` is initialized once to 4 and never changed, so every reachable index is 0-3.

### Fixed loop expansion

Each dispatch shift is expanded in source order, followed by appending the default deadline to
`fifo3`. Queue aging and expiration shifts are expanded in index order. This preserves the original
behavior where an earlier expiration changes the job subsequently aged at a later index.

### Increment and decrement syntax

Every `++` and `--` operation is written as an ordinary assignment, including queue aging,
`m_queue_misses`, and `doneJobs`. No update is added or removed.

### Finite delay specialization

The queue invariants give dispatched `dline` values in 1-3, while `completion` is always 2. The
miss branch therefore implies `dline == 1`, so `after(dline)` becomes `after(1)`. The completion
branch's `after(completion)` becomes `after(2)`.

### Sender identity

The original `ResourceManager.update` distinguishes `am1`, `am2`, and `am3` through the implicit
sender. The normalized model passes fixed identity tags 1, 2, and 3 through `runJob` and `update`.
`update` frees the corresponding application master, preserving the original routing.

### Local boolean initialization

The parser bridge requires local variables to have simple initializers, so
`boolean deadline_miss;` is written as `boolean deadline_miss = false;`. Both branches assign it
before its first read, making the initializer unobservable.

No heartbeat, traffic, protocol action, queue operation, or termination behavior is added. The
three-master topology, sequential dispatch order, periodic `checkQueue() after(1)`, FIFO behavior,
deadline-miss handling, job-completion cycle, and timing order are retained.
