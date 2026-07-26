# Conditional finite detailed weak execution correspondence

Status: accepted

Date: 2026-07-27

## Purpose

This checkpoint lifts the phase-indexed detailed weak-simulation interface to
finite executions.

## Result

For a compatible exact finite DTR detailed execution, the development
constructs:

- a finite generated-LF weak execution;
- pointwise representative-label correspondence;
- final detailed-state correspondence;
- paper-level observable-trace correspondence.

The reverse theorem constructs a finite DTR weak execution for a compatible
exact finite generated-LF detailed execution and proves the same three
correspondence properties.

## Compatibility

The finite theorems remain conditional.

Forward compatibility carries the LF scheduler premise required by source
dispatch phases and rejects phase combinations outside the forward interface.

Backward compatibility carries:

- source active-body structural well-formedness;
- the generated-LF zero-microstep queue invariant;
- admissible detailed phase alignment.

Compatibility is indexed recursively by the concrete exact execution. After a
matched weak transition, it supplies compatibility for every continuation
that preserves label and detailed-state correspondence.

## Observable result

The result compares:

```text
DTR.detailedObservableTrace sourceLabels
LF.detailedObservableTrace targetLabels

It does not compare raw detailed traces as equal lists. LF microstep
administration and both sides' tau labels are erased before observable
correspondence is stated.

Scope

This checkpoint does not yet derive finite compatibility from:

source runtime well-formedness;
positive-delay priority timing;
target pending-microstep invariants;
initial model well-formedness.

Those derivations belong to the next checkpoint.

The detailed layer remains specialized to finite store states. Payload-bound
detailed execution remains outside this result.
