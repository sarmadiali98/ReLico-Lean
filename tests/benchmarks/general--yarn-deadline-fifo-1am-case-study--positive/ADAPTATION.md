# YARN deadline FIFO 1AM - adaptation record

Source: `examples.zip:ReLico-main/yarn-prop/yarn-deadline-fifo-1AMs.rebeca`.

## Property boundary

The shared `yarn.property` file is intentionally excluded. The external property language is not
part of the verified executable translation path, so this fixture evaluates translation and runtime
behavior only.

## Approved fragment normalizations

### Two-entry FIFO

The fixed `int[2] fifo_queue` is represented by scalar fields `fifo0` and `fifo1`. `QUEUE_SIZE` is
initialized once to 2 and never changed. Every reachable index is therefore 0 or 1, and the scalar
fields retain the same head and tail values.

### Fixed loop expansion

The dispatch shift loop has exactly one iteration, the queue-aging loop has exactly two iterations,
and the expiration shift has either one iteration for the head or zero for the tail. They are
expanded in the original execution order. This order preserves the case where removing the head
shifts the tail, appends a deadline-3 job, and then ages that new tail to 2.

### Increment and decrement syntax

Every `++` and `--` operation is written as an ordinary assignment, including queue aging,
`m_queue_misses`, and `doneJobs`. No update is added or removed.

### Finite delay specialization

The queue invariants give `dline` the exact reachable set 1-3, while `completion` is always 2. The
miss branch `completion > dline` therefore implies `dline == 1`, so `after(dline)` becomes
`after(1)`. The completion branch's `after(completion)` becomes `after(2)`. Both substitutions retain
the original message tags and ordering.

### Sender identity

`am1` is the only `AppMaster` instance and both calls to `ResourceManager.update` occur in
`am1.runJob`. The guard `sender == am1` is therefore always true in the fixed topology and is
replaced by its body, `appMaster1 = FREE`.

### Local boolean initialization

The parser bridge requires local variables to have simple initializers, so
`boolean deadline_miss;` is written as `boolean deadline_miss = false;`. Both branches assign
`deadline_miss` before its first read, making the initializer unobservable. This is a mechanical
parser compatibility normalization only.

No heartbeat, traffic, protocol action, queue operation, or termination behavior is added. The
`ResourceManager`/`AppMaster` topology, periodic `checkQueue() after(1)`, FIFO behavior, deadline-miss
handling, job-completion cycle, and timing order are retained.
