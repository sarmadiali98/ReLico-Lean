# `general--actor-priority--positive`

A **general**-family positive benchmark. Two stations contend for a shared
medium in the same round, and instance-level `@priority` decides which actor the
scheduler selects first.

This is a DTR-fragment benchmark **inspired by** the upstream `tcsma` model. It
is **not** a translation of `tcsma`, and it does not reproduce that model's
protocol. What it carries over is the research objective: contention for a
shared medium, resolved by arbitration.

## Provenance

### 1. Original purpose

`tcsma` is a time-division CSMA model. A `Controller` polls stations in
round-robin order over a shared `Medium`; a polled station may or may not have
data to send; the medium serialises transmission; the polled station transmits
to its peer. The research objective is **medium access under contention, with
centralised arbitration deciding who transmits**.

### 2. Removed features

| removed | why |
|---|---|
| `?(0,1)` nondeterministic choice | outside the DTR fragment |
| `delay(n)` as a statement | not in the fragment's statement set; expressed instead as a delayed self-send, `self.release() after(1)` |
| the `Interface` and `User` layers | protocol plumbing that exercises no DTR construct; stations address the medium directly |
| full frame payloads `(sender, receiver, msg)` | a station identifier is all the arbitration decision needs |

`tcsma` also fails **upstream Timed Rebeca 2.14** itself, with `Timed Rebeca
parsing or semantic checking failed`, so no faithful port of it exists to
compare against at any fragment width.

### 3. Preserved behavioural property

Everything the objective depends on is still here, and one thing is sharper:

- **several actors competing for one shared resource** — two stations, one
  medium;
- **centralised arbitration** — the `Arbiter` grants, and observes the outcome;
- **contention resolution** — both stations are granted in the same round, so
  exactly one finds the medium free and the other finds it busy and backs off;
- **bounded, recurring execution** — rounds continue indefinitely and every
  state variable ranges over a finite set;
- **meaningful message passing** — grant, acquire, collide or hold, release,
  report.

Sharper than the original: `lastHolder` records **which** station held the
medium, so the benchmark *checks* the arbitration outcome instead of merely
performing arbitration. Under the fragment's semantics that value is decided by
instance priority, which is the capability this row exists to exercise.

### 4. New assumptions introduced

Four, each of them a real change from the original rather than a simplification
of it. Three were forced by measurement, and the notes say which.

1. **Contention is certain, not probabilistic.** `tcsma` randomised whether a
   polled station had data. Here both stations always contend. The interesting
   variable moves from *whether* there is contention to *who wins it*, which is
   what makes the model a witness for actor priority. This is a design choice,
   not a forced one.
2. **The round is clocked by completion, not by a timer.** The arbiter counts
   `resolved` and re-polls only once both stations have resolved. **Forced:** a
   timer-driven arbiter grants faster than the medium drains under some
   interleaving and leaves the loser's `acquire` queued, and RMC reports that as
   `queue overflow`.
3. **Every externally sent message server carries a parameter.** **Forced:** the
   translator refuses a parameterless external target, because the LF port that
   would carry it has no value type and whether the target accepts such a port
   is unmeasured. Hence `grant(int round)` and `backoff(int cause)`.
4. **Every state variable is bounded.** `busy` and `holding` are boolean;
   `id`, `carried` and `lastHolder` range over `{0, 1, 2}`; `resolved` over
   `{0, 1, 2}`; `round` and `slot` over `{0, 1}`. **Forced:** an unbounded
   counter makes the state space infinite and the model checker does not
   terminate.

## Stages

8 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`formal-witness`, `translated-lf-ast`, `lf-source`, `lfc`.

The stage list is the one this benchmark's registry row already declared and is
not widened here. Runtime observation was measured to work for this model during
selection, so adding the `runtime` stage is a registry decision rather than a
capability question.

## Evidence

- source: the commented Timed Rebeca model, 3 reactive classes and 7 message
  servers;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness,
  not a claim about a particular selected ordering;
- parser JSON: produced by `frontend/java-bridge/run-general-from-zip.sh`
  through the `parser-json --family general` arm;
- decoded DTR AST: the two instances decode with `priority := some 1` for
  `stationHigh` and `priority := some 2` for `stationLow`, which is the
  arbitration input the row is about;
- formal witness: 42 obligations in `GeneralActorSelection`, the ready-actor
  selection development;
- translated LF AST and LF source: the remaining two
  `lean-export --family general` modes;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

Rounds recur indefinitely by design, which is what keeps the model
deadlock-free. Execution is bounded by the harness rather than by the model.
