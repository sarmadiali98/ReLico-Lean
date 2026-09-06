# LeasingNRPFD — adaptation record and measured blocker

Status: **blocked on a fragment exclusion.** The mechanical adaptations are
applied and the source is committed here in its mechanically-adapted form;
the pipeline still refuses it at one construct, recorded verbatim below.
No semantic adaptation has been made. The next step requires an explicit
ruling (see the comparison report referenced at the end).

Source: `examples.zip:ReLico-main/LeasingNRPFD/LeasingNRPFD.rebeca`,
359 lines. The adapted source here is 339 lines; the difference is the
removed `env` block. 152 lines differ under whitespace normalization —
all of them the mechanical substitutions below.

## Original blocker

Measured against the unmodified upstream source:

```
unsupported by the ReLico general parser bridge: environment variable
```

## Applied adaptations — mechanical, semantics-preserving

| adaptation | extent |
|---|---|
| `env` folded into literals | 21 declarations, 60 use-site substitutions (comments untouched); 14 `after(NAME)` delays become `after(literal)`, forced by D9 — an LF connection delay is static |
| `env byte` / `byte` widened to `int` | 5 surviving `byte` sites plus the `env byte` declarations (widened before folding); values are 0–99, far inside `int` |
| array flattened | `int [2] NRPCandidates` → `NRPCandidates0`/`NRPCandidates1`; 2 constant-index sites rewritten directly; 2 variable-index sites (`NRPCandidates[NRP_network]`, with `NRP_network` guarded to {0,1} by `NRP_network < NumberOfNetworks`, `NumberOfNetworks = 2`) rewritten as the corresponding two-way `if`/`else` — the same element is read in every case |
| self-sends qualified | 8 statement-position bare calls (`switchFail()` etc.) → `self.switchFail()`; R14's send grammar is `target.method(...)` |

Each substitution is the declaration's own literal; an `env` constant is
its value, so no observable behaviour changes. Two fold defects were
found and fixed by measurement (an `env byte` form the first fold missed;
a variable-index array read the first flattening missed).

## The measured blocker — where the pipeline stops today

After the mechanical adaptations above, the exporter refuses:

```
unsupported by the ReLico general parser bridge: A1: a rebec-typed state
variable of type Switch in Switch, which makes the sender set of a
message server statically uncomputable (line 250)
```

`Switch` declares `Switch switchTarget1;` and `Switch switchTarget2;` as
**state variables**, assigned once in the constructor from its `sw1`/`sw2`
parameters, and every routing decision in the class reads them:
`if (senderNode > id) switchTarget1.pingNRP(...) else
switchTarget2.pingNRP(...)`. The topology is built dynamically in `main`
— for instance `switchA2` is passed itself as both targets — so the
fragment cannot know at parse time which rebecs a message server can
send to.

This is the same A1 exclusion that blocks `AutonomousVehicles` (eight
rebec-typed state variables in `Segment`) and the TinyOS pair
(`senderDevice`/`receiverDevice`).

Also present in the same source, not yet reached by the refusal chain:
`@Priority` (capital P; the fragment spells `@priority` — a mechanical
case fix), and commented-out `if(?(true,false))` nondeterministic sites
that are already inactive and need nothing.

## No semantic adaptation has been applied

The transformation that would unblock this model — binding every
possible routing target as a `knownrebec` and dispatching on a tag — is
**not** part of the approved mechanical set, and per the standing rule it
is not applied here. Whether it counts as a semantics-preserving
transformation (category 2) or a redesign (category 3) is the open
question; the evidence for that ruling is in
[`ROUTING-COMPARISON.md`](ROUTING-COMPARISON.md), which compares the
transformation this model needs against the tcsma adaptation that already
used tag routing.

Until that ruling lands, this benchmark directory intentionally carries
no manifest, no registry row, and no expected artifacts: the source is
committed as the record of how far mechanical adaptation reaches.
