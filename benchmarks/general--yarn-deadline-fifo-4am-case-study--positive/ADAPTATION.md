# YARN deadline FIFO 4AM - adaptation record

Source: `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-4AMs.rebeca`.

## Property boundary

The shared `yarn.property` file is intentionally excluded. The external property language is not
part of the verified executable translation path, so this fixture evaluates translation and runtime
behavior only.

The `doneJobs` field and its 1-5 cycling update are also omitted. That field is read only by the
excluded `yarn.property`; it does not influence dispatch, timing, queue contents, deadline checks,
messages, or any control-flow decision in the executable model. Removing four independent
observation-only counters avoids multiplying the RMC state space while preserving all behavior
within this fixture's stated property boundary.

## Approved fragment normalizations

### Five-entry FIFO

The fixed `int[5] fifo_queue` is represented by scalar fields `fifo0` through `fifo4`.
`QUEUE_SIZE` is initialized once to 5 and never changed, so every reachable index is 0-4.

### Fixed loop expansion

Each dispatch shift is expanded in source order, followed by appending the default deadline to
`fifo4`. Queue aging and expiration shifts are expanded in index order. This preserves the original
behavior where an earlier expiration changes the job subsequently aged at a later index.

### Increment and decrement syntax

Every retained `++` and `--` operation is written as an ordinary assignment, including queue aging
and `m_queue_misses`. No behaviorally relevant update is added or removed.

### Finite delay specialization

The queue invariants give dispatched positive `dline` values in 1-5, while `completion` is always
2. The miss branch therefore implies `dline == 1`, so `after(dline)` becomes `after(1)`. The
completion branch's `after(completion)` becomes `after(2)`.

### Sender identity

The original `ResourceManager.update` distinguishes `am1` through `am4` using the implicit sender.
The normalized model passes fixed identity tags 1-4 through `runJob` and `update`. `update` frees
the corresponding application master, preserving the original routing.

### Local boolean initialization

The parser bridge requires local variables to have simple initializers, so
`boolean deadline_miss;` is written as `boolean deadline_miss = false;`. Both branches assign it
before its first read, making the initializer unobservable.

No heartbeat, traffic, protocol action, queue operation, or termination behavior is added. The
four-master topology, sequential dispatch order, periodic `checkQueue() after(1)`, FIFO behavior,
deadline-miss handling, job-completion cycle, and timing order are retained.
