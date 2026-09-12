# `general--nested-conditional--positive`

This positive benchmark belongs to the **general** family. It is a purpose-built capability
fixture for nested conditionals with branch-local scope lifetime, a semantic claim that was
previously exercised only at elaboration level: no committed general fixture contained a
conditional nested inside a branch, and none read a local after an enclosing branch's inner
conditional closed.

## Capability

The `step` message server's body contains an outer conditional whose then-arm declares a local
`t`, reads it after the inner conditional closes, and whose else-arm redeclares the same name:

- the outer then-arm's `int t = 1` is live across the inner `if`, and both inner arms assign to
  it, exercising assignment to a live local inside nested branches;
- `total = t` after the inner conditional closes demonstrates the local surviving the inner
  branch;
- the outer else-arm's own `int t = 100` is legal only because the then-arm's `t` died with its
  branch: under body-wide scoping the elaborator's `localShadowsDeclaredName` would refuse the
  model, so the model's acceptance is the executable form of the lifetime-death claim;
- the message parameter cycles through 50, 5, and 0, so all three branch paths are explored:
  outer then with inner then, outer then with inner else, and outer else.

The generated LF program preserves the nesting in one line of emitted C++, with the same-name
declarations in sibling arms, which is the translated shape of the same claim.

## Why the re-arms exist

The mandatory RMC stage requires a `satisfied` deadlock-freedom verdict, and a model that sends
one message and then quiesces reaches an empty-queue state, which RMC reports as a deadlock.
Each branch re-arms `self.step` with `after(1)`, choosing the next parameter value so the cycle
50, 5, 0 covers all three paths while the state space stays finite: `total` and `v` range over
fixed value sets.

## Stages

9 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`.

## Evidence

- source: the commented Timed Rebeca model above;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim
  about a particular runtime ordering;
- parser JSON: recorded from a real exporter run and reviewed;
- decoded DTR AST, translated LF AST, LF source, and the formal witness over this benchmark's
  pin module `Relico/Tests/GeneralNestedConditional.lean`, which pins the compiled nesting
  shape and the two branch-local declarations;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target;
- runtime: the generated binary runs in fast mode to the 5 msec logical-time timeout and exits
  0.

## Keep-alive

This model never terminates on its own; the runtime stage's fast-mode timeout is the bounded-run
policy.
