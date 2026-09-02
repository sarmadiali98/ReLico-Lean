# Within-tag partial quotient for the consume transfer conditions

Status: **APPROVED 2026-08-28**

Decision: repair the F76 selection divergence by restating the
correspondence up to within-tag permutation, free permutation among
events targeting **distinct** reactors at one logical tag, order-
**preserving** among events targeting **one** reactor, and prove the
`.consume` transfer conditions against that partial quotient.

## Context

F76 measured that the two semantics deterministically disagree on which
same-tag event fires first:

- the source selects by `(ReadyActor.logicalTime, actor priority)`,
  lexicographic, through `DTR.GeneralActorSelection.selectedActor`;
- the target selects by `(Tag.time, Tag.microstep)`, lexicographic,
  through `LF.GeneralRuntimeState.earliestPendingEvent?`, a key that
  cannot express priority, falling back to queue insertion order.

Two positive-delay sends from two actors landing at one logical time
therefore carry byte-identical tags; the target consumes the
queue-first one and the source the priority-better one, so the forward
transfer condition of Definition 1 is false as stated. The `.timeAdvance`
case is unaffected and already proved
(`generalTimeAdvance_forward_weak`, `_backward_weak`).

The divergence is not cleanly the target's fault. F76's second finding
is that the target model is **over-specified**: real LF leaves same-tag
reactions in independent reactors logically simultaneous, while
`earliestPendingEvent?` totally orders them anyway. The total order is
our artefact. That measurement is what makes a quotient repair faithful
rather than a retreat, and F80 refined it, because real `lfc` *does*
order same-tag reactions within one reactor (by declaration order; six
probes in three trigger shapes), so the quotient must not be total.

## Approved statement

The correspondence for the `.consume` label is stated up to within-tag
permutation, where the quotient is **partial**:

- among events targeting **distinct** reactors at one logical tag,
  permutation is free; no target order is claimed, because none is
  real;
- among events targeting **one** reactor at one logical tag, order is
  **preserved**: the target genuinely enforces one (declaration
  order), and the correspondence must respect it.

The proof obligation this creates is a commutation argument: for
distinct actors at one tag, taking one actor's message while another
actor's body is half-executed commutes, because `take` and `fire` each
update a single store key and remove a single queue element, which for
distinct actors are disjoint. F76 records that whether this yields a
genuine commutation result over interleaved bodies "is not settled
here". Settling it is the content of task `#129` (audit C7), and this
decision commissions exactly that.

## Scope

The decision:

- governs the `.consume` transfer conditions alone; `.timeAdvance` is
  proved unconditionally and stays as is;
- keeps both operational semantics unchanged, no priority term enters
  the target selector, no tie-break is invented;
- refuses nothing: every accepted model remains translated and run;
  contention models become theorem-eligible rather than excluded;
- makes row 9's instantiation (audit C8) a statement about the partial
  quotient, not about Definition 1 verbatim;
- adds one eligibility consequence recorded in
  `docs/supported-fragment-general.md`: no model is excluded from the
  `.consume` correspondence by contention, and the within-one-reactor
  ordering the quotient preserves is exactly the stage-F port-reaction
  declaration order the G5 witness observed.

## Rejected alternatives

- **(a) Guard on absence of cross-actor same-tag contention.** Sound
  and moderate, but it excludes exactly the models where priority does
  work, and F77's reason for calling a guard warranted, that the only
  implementing mechanism costs topology the source does not have, is
  an argument about implementing priority in LF, not about proving
  correspondence over behaviour LF does not order.
- **(b) Priority-aware tie-break on the target.** The attribute route
  is refuted by measurement (F77: `@priority` does not exist, and no
  attribute could serve); the surviving realisation, injected
  zero-delay `uses` edges among receivers, buys ordering at the price
  of ports, connections and forced serialisation the source model does
  not have. Invents target semantics.
- **(c) Drop priority from the source.** Contradicts the standing scope
  decision that actor priorities are in scope and delivered.
- **(d) Fragment restriction.** Doctrine-preferred when the target is
  at fault, but the over-specification finding places part of the fault
  in our own total-ordering fold; and it would refuse the `priorities`
  and `fan-in` fixtures, the two corpus models where actor priority is
  irreducible.
- **(e) as originally stated**: a total within-tag quotient. Too
  coarse: F80 measured that real `lfc` enforces within-one-reactor
  order, so a total quotient would quotient away the one same-tag
  ordering the target genuinely has. Superseded by the approved
  partial form (e′).
