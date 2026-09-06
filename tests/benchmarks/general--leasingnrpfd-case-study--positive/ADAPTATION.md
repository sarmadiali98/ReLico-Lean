# LeasingNRPFD — adaptation record

Status: **implemented** as `general--leasingnrpfd-case-study--positive`,
all eight stages green including `rmc`, after the approved category-2
transformation (ruling evidence: [`ROUTING_COMPARISON.md`](ROUTING_COMPARISON.md))
and the ping-pending boundedness fix below.

Source: `examples.zip:ReLico-main/LeasingNRPFD/LeasingNRPFD.rebeca`,
359 lines.

## Original blocker

Measured against the unmodified upstream source:

```
unsupported by the ReLico general parser bridge: environment variable
```

## Applied adaptations — category 1, mechanical and semantics-preserving

| adaptation | extent | forced by |
|---|---|---|
| `env` folded into literals (incl. `env byte`, widened first) | 21 declarations, 60 substitutions | the original refusal; D9 for the 14 `after(NAME)` delays |
| array flattened | `int[2] NRPCandidates` → two scalars; 2 constant-index + 2 variable-index sites (`NRP_network` guarded to {0,1}, so the two-way `if` reads the same element) | upstream undeclared-name errors |
| `byte` widened to `int` | 5 sites + the `env byte` declarations | the integer-width exclusion; values are 0–99 |
| self-sends qualified | 8 message-server sites + the two constructor sites | R14's send grammar is `target.method(...)` |
| `@Priority` → `@priority` | 6 instantiation annotations | spelling |
| `v++` → `v = v + 1` | 6 sites (5 statement, 1 inline) | R16 names the rewrite itself |
| empty `if` branches dropped | `if (mode==0);` and `else if (mode==3);` | R14 shape; both bodies were empty, so nothing was dropped but dead code |
| `switch(nodeMode)` → `if`/`else if` chain | 4 cases, every case `break`-terminated, case 3 empty; no fallthrough, no `default` | R14 admits if, not switch; break-termination makes the chain exactly equivalent |
| clamp ternaries → `if` | 4 sites of `v = (v > K)?K:v;` → `if (v > K) { v = K; }` | D5 names the rewrite; the false branch was the no-op `v = v` |
| constructor fail-time delays value-branched | 2 sites: `if (t!=0) self.fail() after(t)` → `if (t == 2500) … after(2500); else if (t == 5000) … after(5000)` | D9 — an LF connection delay is static. The instances pass 2500 or 0; each branch preserves the exact send time for its value, and 0 sends nothing in both forms. The 5000 branch is defensive, matching the original's commented scenario vocabulary |
| `mode` renamed `nodeMode` | 21 sites | `lfc` rejects `mode` as a reserved keyword of its **target language** (modal reactors). Uniform identifier rename |

One **translator defect** surfaced by the last item, recorded here for a
future finding: the verified translator happily emits a state variable
named `mode` and produces LF that `lfc` rejects with five errors. By the
house rule that the target's limits are the translator's refusals, the
emitter should refuse reserved-keyword identifiers with a named
diagnostic instead of emitting uncompilable LF. The benchmark side-steps
it with the rename; the defect stands.

## Applied transformation — category 2, approved 2026-09-07

**The exact proof obligation.** For every `Switch` instance `s` and all
times `t`: `switchTarget1(s, t) = sw1(main(s))` and
`switchTarget2(s, t) = sw2(main(s))` — that is, each rebec-typed state
variable denotes, at every point after construction, exactly the rebec
that `main` passed as the corresponding constructor argument.

**Why it holds here.** Both variables are written exactly once, in the
constructor, from the constructor arguments (`switchTarget1 = sw1;
switchTarget2 = sw2;` — grep-verified: the only two assignment sites in
the class), and never reassigned. A `knownrebecs` binding denotes the
same thing: the rebec `main` bound at instantiation. Therefore replacing
each state-variable read with the knownrebec read substitutes one name
for the same referent — same target, same message, same arguments, same
guard, same delay at every one of the ten routing sites.

**What was applied.**

1. `Switch` declares `knownrebecs { Node nodeTarget1; Switch up; Switch
   down; }`; the two rebec-typed state variables are removed.
2. The ten routing reads are renamed `switchTarget1.` → `up.`,
   `switchTarget2.` → `down.`.
3. The six `main` instantiations bind the same instances the original
   passed as `sw1`/`sw2` — including the self-bindings (`switchA3` is
   passed `switchA2` twice, exactly as the original constructor
   arguments did).
4. The rebec-typed constructor parameters `sw1`/`sw2` are removed
   (forced in turn by A2: a rebec-typed constructor parameter makes the
   topology dynamic); the constructor keeps its integer parameters, and
   the `main` calls pass the same integer arguments as before.

The routing *guards* (`senderNode > id` etc.) are untouched — the
original already selected the target by value; only the reference
channel changed.

## Boundedness fix — the model's own `ping_pending` discipline, enforced

**Measured cause.** RMC reported `queue overflow`, and its
counter-example is diagnostic: thirteen transitions, all at
`executionTime="0"`, with every `after(d)` message queued at
`arrival="0"` — DCN1's `runMe` re-arms itself and its `ping_timed_out`
at time 0 while earlier timeouts sit unconsumed, so the node piles its
own timeout messages into its bound-4 queue. Two control runs pin the
cause on the gate's exploration semantics rather than on this
adaptation: the **unmodified upstream** LeasingNRPFD produces the same
all-zero-time overflow, and so does the **unmodified upstream tcsma**
(362 messages, all `arrival="0"`). Under this checker's exploration,
`after` delays collapse to time 0, so boundedness must hold under
zero-delay scheduling — a strictly stronger requirement than the real
time semantics needs.

The model-level gap that makes it fail: `runMe`'s six ping send sites
re-arm `pingNRP` and `ping_timed_out` unconditionally, and the mode-1
timeout handler performs its failover **without clearing `ping_pending`**
(the mode-2 branch already clears it). So nothing enforces "at most one
ping and one timeout in flight", and under zero-delay scheduling the
re-arms outrun the consumption.

**The fix — two edits, the flag's own semantics.** (1) The mode-1
timeout handler clears `ping_pending` when it consumes a timeout,
exactly as the mode-2 branch already does. (2) All three ping-pair
blocks in `runMe` (mode 1, and both mode-2 escalations — six send sites)
are guarded with `if (!ping_pending)`. At most one ping and one timeout
are in flight per node: the same at-most-one-unacknowledged-message
principle as the tcsma-inspired benchmark, expressed here with the
flag the model itself already carries.

**Why the intent is preserved.** Under real time the original already
has one ping in flight per cycle by construction — the period is 1000
and the timeout 100, so a response or timeout always resolves long
before the next cycle — and the failover sequence is identical: ping
network A, timeout, elect network B, ping B, timeout, give up to
WAITING. The guard enforces that invariant instead of assuming the
timing. One genuine small behavioural delta, recorded: the original
could arm overlapping timeouts within one period (a second
`ping_timed_out` while the first was still in flight), which would
advance `NRP_network` twice in a single cycle and skip a network in the
failover — the guard prevents that, which is what `ping_pending` exists
to express. The periodic relay and heartbeat behaviour continues
unchanged, every queue is bounded, and RMC reports **`satisfied`**.
