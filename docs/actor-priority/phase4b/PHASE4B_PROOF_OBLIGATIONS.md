# Phase 4B Integration Surface and Proof Obligations

## Result

Classification:

**UNEXPECTED_EXPLICIT_ACTOR_PRIORITY_INTEGRATION_FOUND_REQUIRES_MANUAL_REVIEW**

The full baseline build and Lean integration-surface probe passed.

## What the current production proof covers

The current production proof includes multi-store and multi-actor dispatch
relations.

It establishes correspondence for a dispatch after the selected message and
message server have been supplied to the dispatch relation.

The audited production surfaces do not currently contain an explicit
actor-priority request, actor-priority eligibility predicate, or translated
actor-priority scheduler.

This is not the same as saying that multi-actor DTR programs are unsupported.

It means that the global choice between simultaneously eligible actors is not
yet justified by an actor-priority policy in the audited correspondence.

## Existing local priority mechanism

The project already contains:

- `Relico.DTR.IsPriorityEligible`;
- `Relico.LF.IsReactionPriorityEligible`;
- source/target selection correspondence for message-server priorities.

These are local message-server or reaction priorities. They do not by
themselves establish actor-level ordering between separate actor instances.

## Evidence already obtained

The pinned RMC witness shows that reversing only actor priorities changes the
reachable actor-dispatch trace language.

The isolated Lean scheduler proves that:

- the base assignment selects `workera`;
- the reversed assignment selects `workerb`;
- tied or absent actor priority retains both actors.

Therefore actor-priority information can be semantically discriminating.

## Decisive theorem

The next theorem must formalize the following argument.

Let `S_base` and `S_reversed` be source systems that differ only in their
actor-priority assignments.

If:

1. their permitted actor selections or trace languages differ; and
2. a translation erases actor-priority information;

then the translation produces the same target representation for both source
systems.

One target behavior cannot be behaviorally equivalent to two distinct source
trace languages.

That theorem would establish the second target conclusion in its precise
form:

> When actor priority changes cross-actor selection, a faithful translation
> must preserve that ordering information, either explicitly or through an
> equivalent compiled mechanism.

It would not prove that a literal actor-priority field is the only possible
encoding.

## Proof obligations

| ID | Name | Required statement | Decisive for |
|---|---|---|---|
| P1 | source actor-priority eligibility | Define actor-level eligibility over simultaneously ready actor instances. | inclusion architecture |
| P2 | priority-reversal discrimination | Prove that the base and reversed assignments produce different eligible actor sets. | semantic relevance |
| P3 | priority-erasure identity | Formalize that a priority-erasing translation maps source programs differing only in actor priority to the same target program or target scheduler state. | necessity |
| P4 | priority-erasure impossibility | Prove that one identical target behavior cannot be trace-equivalent to both priority-reversed source behaviors when those source trace languages differ. | target conclusion 2 |
| P5 | compiled ordering preservation | Provide actor metadata, precedence constraints, microsteps, or another target mechanism preserving the source actor ordering. | faithful implementation |
| P6 | forward actor-selection correspondence | Every source actor-priority-eligible dispatch has a corresponding target-eligible dispatch. | forward simulation |
| P7 | backward actor-selection reflection | Every target dispatch permitted by the encoding reflects a source actor-priority-eligible dispatch. | backward simulation |
| P8 | priority-inertness theorem | Characterize cases where actor priority may be erased safely, such as no simultaneous competition, ties, or an already forced causal order. | target conclusion 1 in a restricted scope |
| P9 | multi-actor benchmark | Implement base, reversed, tied, and absent multi-actor variants and compare source and target actor-dispatch traces. | mechanical validation |

## Status of the two target conclusions

### Conclusion 1

“Actor priorities do not need to be specified.”

**Established only for scopes in which actor priority is excluded or proved
semantically inert.**

It is not established for arbitrary simultaneous multi-actor competition.

### Conclusion 2

“Actor-level ordering must be specified when it determines which actor's
message server precedes another actor's message server.”

**Strongly supported, but the decisive erasure-impossibility theorem is still
pending.**

The necessary object is actor-ordering information. It may be represented by
actor metadata, precedence constraints, a coordinator, LF dependency edges,
microsteps, or another semantics-preserving mechanism.

## Conclusion status

**not yet reached**

## Next phase

**phase4b-manual-review-of-existing-actor-priority-integration**
