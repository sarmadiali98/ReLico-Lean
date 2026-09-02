# Forward instant-block transfer stays a weak-step theorem

Status: **APPROVED 2026-09-02**

Decision: the general family's forward instant-block result concludes a
`Common.WeakSteps` over `LF.GeneralStepModulo`, and **not** a
`Correctness.GeneralInstantBlockSpine`. `hConsumeAnswer` keeps its current
shape; representative-level `fire` premises are not exposed in the forward
API; no stronger forward spine theorem is added. The backward direction's
constructive spine is retained as an **auxiliary** result rather than being
mirrored forward.

Decision: **no end-to-end bisimulation bundle** is built for the general
family. The pair `Correctness.generalTraceAgreement_of_consumeAnswer` and
`Correctness.generalTraceAgreement_backward_of_answers` is the bisimulation
argument, and is cited as a pair.

## Context

`Correctness.generalInstantBlock_forward` (landed `047a5ef`) answers a source
instant block with a target execution of the quotient system, carrying the
`.consume` answer as a premise. Its conclusion is an execution, not a spine.

`Correctness.GeneralInstantBlockSpine` is an inductive **indexed by the events
it fired**, whose `consume` constructor carries `LF.GeneralStep.fire`'s six
premises at an α-representative. `GeneralInstantBlockSpine.weakSteps` runs
spine → execution; there is no converse, because a `Common.WeakStep` is a
`Prop` recording neither which event fired nor at which representative.

So producing a forward spine is not a matter of proving another lemma. It
requires `hConsumeAnswer` to **return different data** — the representative
package instead of a weak step — which moves a committed theorem's public
premise shape.

An earlier generation of this project's records named the *endpoint transport*
as the forward obstacle, and specifically the "no ready source actor implies
every pending target event is strictly future" half. **That was wrong.** Both
transports are proved (`generalPendingFuture_of_quiescent`,
`generalReactorIdle_of_actorIdle`, commit `0226689`), and the correction is
recorded in the source and in `docs/STAGE_G_FINDINGS.md`'s C7 contribution
section. The obstacle was always the premise's data.

## Approved statement

The forward instant-block theorem is a **weak-step** theorem, and the
paper-level claim it supports is:

> *Instant blocks are preserved by weak correspondence while maintaining the
> state relation.*

Internal τ decomposition stays **hidden inside weak transitions**. That is the
whole point of a weak behavioural correspondence: which internal steps a side
takes, and in which order, is not part of what is claimed.

The backward direction concludes the whole
`Correctness.generalInstantBlock_source` predicate, and that extra strength is
kept because it costs nothing and is useful for construction. The resulting
forward/backward asymmetry is **intentional** and is documented as such.

## Rationale

- The main semantic goal is weak bisimulation / weak behavioural
  correspondence, not a refinement.
- The current forward theorem boundary is the correct abstraction level for
  that goal.
- Internal τ decomposition should remain hidden inside weak transitions.
- The stronger spine theorem is a **constructive refinement artifact**. It is
  the right thing to have on the backward side, where a source execution must
  actually be built, and the wrong thing to make the main semantic interface.

The asymmetry also has a measured cause, which is why mirroring it forward
would not be free even setting the API aside: the endpoint conditions cross
target-to-source but not source-to-target. A *ready source actor* is backed by
a *pending target event at or before the instant*, which the queue pairing's
accessor gives directly; the forward direction would need the converse.

## Scope

The decision:

- governs the forward instant-block API alone. Both instant-block theorems
  keep their current statements; nothing is weakened.
- keeps `hConsumeAnswer` unchanged, so every existing caller and the pins in
  `Relico/Tests/GeneralTraceTransfer.lean` are unaffected.
- leaves the three named residues exactly as they are — the forward
  α-representative package, the backward `hName`, and the backward
  `hTauAnswer`. This decision does not discharge or widen any of them.
- closes what the handoffs called *Open decision 2*. It is decided, not
  deferred.
- implies the C7 **proof surface is complete**: every remaining obligation is
  either proved or is one of the three residues, each recorded with the
  measurement that makes it non-derivable. Remaining C7 work is presentation.

## Rejected alternatives

- **(a) Strengthen `hConsumeAnswer` to return the spine entry.** The
  technically strongest option, and it would close the asymmetry. Rejected
  because it changes a committed theorem's public premise shape to buy a
  refinement-level result that the paper's claim does not need, and because it
  would put representative-level `fire` premises into the forward API, where
  they leak the α′ question into a statement that currently contains it in one
  named premise.
- **(b) Weaken the backward result to match forward.** Symmetry for its own
  sake, at the price of discarding a proved and useful construction. Rejected:
  the backward spine costs nothing to keep, and the asymmetry is explicable.
- **(c) Build an end-to-end bisimulation bundle.** Rejected on three counts. It
  adds no theorem content — the two rows already exist and already compose in
  the only sense a bisimulation requires. `Relico/Correctness/WeakBisimulationTrace.lean`
  records that the four existing `*PhaseWeakBisimulation` declarations are all
  family-specific and that bundling *"would force a caller that holds only the
  forward direction to supply the backward one as well"*. And a general-family
  bundle would carry **four** independent residues in one signature — one
  forward, three backward — making it harder to use than either half. If a
  single citable name is wanted for the paper, that is a presentational request
  and should be justified as one.
- **(d) Add `generalSend_forward_weak` for a uniform statement-lift trio.**
  Rejected separately on 2026-09-02 and recorded here because it belongs to the
  same family of "symmetry looks tidier" arguments. `generalSend_forward` needs
  all four accepted-program premises **plus three** sender-resolution premises,
  while `generalTauSteps_forward` needs a strict subset — so the lift would
  carry three *more* premises than the route it replaces. The two lifts that
  did land (`generalTrace_forward_weak`, `generalAssign_forward_weak`) each
  remove four premises, which is their entire justification.

## Consequences

- `docs/STAGE_G_FINDINGS.md` gains a *C7 contribution* section stating the
  relation, both instant-block directions with the asymmetry explained, trace
  agreement over the shared observable alphabet, the three residues with their
  non-derivability arguments, the partial-quotient setting, and the invariant
  layers.
- A paper claiming this result must state the three residues as premises, and
  must state the claim over decision 0042's **partial** quotient rather than
  Definition 1 verbatim. Claiming "we mechanised Theorem 1" unqualified is
  deflatable in one sentence.
- No coding is planned for C7.
