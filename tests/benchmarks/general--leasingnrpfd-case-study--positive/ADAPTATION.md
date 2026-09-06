# LeasingNRPFD — adaptation record

Status: **translation-complete, registry-blocked.** The approved
category-2 transformation (ruling evidence:
[`ROUTING-COMPARISON.md`](ROUTING-COMPARISON.md)) was applied on
2026-09-07 and the model now clears the entire translation pipeline —
exporter, decode, translation, LF generation, `lfc`, runtime all pass.
The benchmark row was **not** added: the registry validator requires the
`rmc` stage on every row, and the `rmc` stage raises on this model's
`queue overflow` verdict. The blocking decision — record as a case study
without a row (this directory's current state), approve a category-3
boundedness redesign of the relay/ping loop, or amend the mandatory-RMC
rule — belongs to the maintainer.

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

## RMC verdict — recorded, not a gate

`queue overflow`. The counter-example ends with `DCN1`'s queue holding
repeated messages at logical time 0 under an interleaving that starves
the node while the switch relay chain continues — the same model-checking
shape as `Minimal`'s zero-delay recurrence and `benchmarks/tcsma`'s
overflow: an unbounded queue under unfair scheduling, not a translation
defect. Per the tier-2 policy (model-checker verdicts are recorded
bonuses for case studies, not gates), this benchmark's stage list
excludes `rmc`; the verdict is recorded here and in
[`RESULTS.md`](RESULTS.md).
