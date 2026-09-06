# Routing transformation comparison — tcsma vs LeasingNRPFD

Purpose: the ruling requested before any semantic adaptation. This report
compares the tag-routing already accepted in the tcsma-inspired benchmark
against the transformation LeasingNRPFD needs, on the single question
that separates category 2 (semantics-preserving transformation) from
category 3 (redesign): **can constructor-assigned rebec-typed state
variables be replaced without changing observable behaviour?**

## 1. The tcsma adaptation that already used tag routing

`tcsma` (the upstream model) routes by **message content, not by rebec
reference**: `Controller.next = next % 2 + 1` computes a *number*, and
`poll()` sends by a chain of `if (next == 1) … if (next == 2) …` over
**knownrebecs** it declares statically. Its A1-class problem was that its
`Station` class holds `Interface` rebec-typed state variables
(`Interface if1; Interface if2;`) which the exporters refuse, plus
`?(0,1)` nondeterministic choice and `delay(1)` statements.

The accepted adaptation (`general--actor-priority--positive`) did not
translate that structure; it **redesigned the model around the research
objective** — two stations contending for one medium, arbitration by
actor priority — with knownrebecs declared statically
(`Medium`'s `knownrebecs { Arbiter arbiter; }`, the `Arbiter`'s
`knownrebecs { Station stationHigh; Station stationLow; }`) and all
routing expressed as `if (station == 1)` dispatch on message values. Its
README says exactly this: *"not a translation of tcsma and does not
reproduce its protocol; it preserves that benchmark's research
objective."*

**Grade: redesign.** It was accepted as one, documented as one, and
reviewed as one — never as a semantics-preserving transformation of the
original program.

## 2. The transformation LeasingNRPFD needs

The mechanical adaptations are done (see
[`ADAPTATION.md`](ADAPTATION.md)). What remains is one structural fact:
`Switch` holds `Switch switchTarget1, switchTarget2` as **state
variables**, assigned exactly once each in the constructor from the
`sw1`/`sw2` constructor parameters, then read at **ten** routing sites
(all of `pingNRP_response`, `pingNRP`, `new_NRP`, `new_NRPBack`,
`heartBeat`):

```rebeca
else if (senderNode > id) switchTarget1.pingNRP(id, senderNode, NRP);
else                      switchTarget2.pingNRP(id, senderNode, NRP);
```

The candidate transformation: declare `knownrebecs { Node nodeTarget1;
Switch up; Switch down; }`, pass the same instances `main` already
passes, and rewrite each read `switchTarget1` → `up`,
`switchTarget2` → `down`. No tags are even required at the dispatch
sites, because the *guard* (`senderNode > id`) already selects the
target; only the reference channel changes.

## 3. Can constructor-assigned rebec statevars be replaced without
observable change?

**For LeasingNRPFD: yes, and here is the argument.** The variables are
**single-assignment** — written once, in the constructor, from
constructor arguments, and never reassigned anywhere in the class (grep-
verified: the only writes are the two constructor lines). Therefore, at
any point after construction, `switchTarget1` denotes exactly the rebec
that `main` passed as `sw1` — which is exactly what a `knownrebecs`
binding denotes. Replacing the state-variable reads with knownrebec
reads substitutes one name for the same referent:

- **same target, same message, same arguments, same guard, same delay**
  at every one of the ten sites;
- the values the model computes (`which`, `amINRP`, `primary`,
  `prevWhich`, …) and the messages it emits are untouched;
- `main` passes the identical instances — including the self-binding
  `switchA2(switchA2, switchA2)`, which knownrebecs also admit (the
  tcsma benchmark's `Arbiter` binds itself into nothing, but
  `main`-level self-reference was fine elsewhere in the corpus).

The one true caveat, stated plainly: knownrebecs **cannot be null**, so
slots the original leaves unbound (if any `sw1`/`sw2` argument were
absent) would need a chosen instance. In this model every `Switch`
constructor call passes both arguments, so no null choice arises.

**Grade: category 2 candidate — a semantics-preserving transformation**
for this model, on the strength of single-assignment. The argument does
not rest on the routing pattern (that part is cosmetic); it rests on the
substitution principle: replacing a never-reassigned reference by the
reference it was initialised to.

## 4. Why the same argument does NOT extend to the other three

| model | rebec statevar writes | extends? |
|---|---|---|
| LeasingNRPFD | 2, both constructor-only, never reassigned | **yes** (above) |
| AutonomousVehicles | 8 in `Segment` — constructor-assigned **but** the routing also uses `instanceof`-dispatch on `sender`, `null` rebecs, and `assertion(false)` | **no** — the statevars alone would transform, but `instanceof` chains and `null` semantics are separate exclusions needing tag design; combined effect is a redesign |
| TinyOSPV6-MACB | `senderDevice`/`receiverDevice` are **locals, reassigned at runtime** (`senderDevice = (CommunicationDevice)sender;`, `senderDevice = null;`) and **passed as message arguments** | **no** — runtime reassignment breaks the single-assignment argument; message-carried rebecs are a different exclusion |
| TinyOSPV6-TDMA | same family, same shapes | **no** |

The single-assignment condition is the whole load-bearing fact. Where it
holds, the transformation is referent substitution; where it does not
(runtime rebinding), there is no static referent to substitute and the
model genuinely needs redesign.

## 5. The three categories, separated

1. **Mechanical adaptations** (applied, no approval needed beyond the
   smarthome ruling): env folding, literal delay conversion, array
   flattening, byte widening, self-send qualification, `@Priority` case
   fix.
2. **Semantics-preserving transformations** (awaiting approval — this
   report is the evidence): constructor-assigned, never-reassigned rebec
   statevars → knownrebec bindings. Valid for LeasingNRPFD by the
   single-assignment argument above; **not** valid for TinyOS (runtime
   reassignment, rebec-valued messages).
3. **True redesigns** (awaiting a separate decision each): the TinyOS
   pair (nondet delays, computed delays, rebec-typed locals with null
   flow, rebec-typed message arguments), AutonomousVehicles (`instanceof`
   dispatch, `null` topology slots, computed delays, `assertion(false)`
   disposal).

## Recommendation

Approve category 2 **for LeasingNRPFD only**, on the single-assignment
argument. If approved, the remaining work is: two knownrebec
declarations, ten reference renames, the `@Priority` case fix, then the
standard benchmark bootstrap with the transformation recorded in
`ADAPTATION.md` under its own heading, separate from the mechanical
list. The other three stay blocked on their category-3 rulings.
