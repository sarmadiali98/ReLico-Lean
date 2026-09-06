# `general--one-step-execution--positive`

A **general**-family positive benchmark. The smallest recurring corpus model: one class, one self-send and

## Provenance

### 1. Original purpose

Upstream corpus model `Minimal/Minimal`. The corpus's minimal recurring model: one class, one self-send, one branch.

### 2. Removed features

None. The model is inside the DTR fragment as written; the change below is
additive.

### 3. Semantic changes made

- both `self.tick()` sites gained `after(1)`.

Forced by one measured failure. The original recurs with a **zero-delay**
self-send, which translates to a logical action with no delay, so the LF
runtime generates unbounded microsteps at logical time 0, never advances past
its `--timeout 5 msec` budget, and the stage's ten-second wall guard fires:
eight of nine stages passed and `runtime` failed at 10.178 s. One delay unit
makes logical time advance and the stage completes in 2 s. The model's purpose
is untouched -- one class, one unconditionally recurring self-send, one branch
-- and RMC still reports `satisfied`.

### 4. Preserved behavioural property

A single message server dispatched and executed to completion.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

The stage list is the one this benchmark's registry row already declared and is not widened here.

## Evidence

- source: the commented Timed Rebeca model;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim about a particular selected ordering;
- parser JSON: produced through the `parser-json --family general` arm;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- formal witness: 88 obligations across `GeneralSemantics`;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

The model recurs indefinitely, which is what keeps it deadlock-free under the model checker. Execution is bounded by the harness.
