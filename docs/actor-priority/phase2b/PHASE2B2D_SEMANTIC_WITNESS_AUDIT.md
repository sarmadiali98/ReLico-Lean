# Phase 2B2D Semantic Witness Audit

## Status

The selected Phase-2B2D verifier executables were rerun independently
three times for each variant:

- base actor priorities;
- reversed actor priorities;
- actor priorities absent.

The original Phase-2B2D artifacts were not modified.

## Reason for the audit

Phase 2B2D reported:

- base violation observed: `True`;
- reversed violation observed: `True`;
- runtime exit difference: `False`;
- generic behavioral-output difference:
  `True`;
- generated-code difference:
  `True`.

A generic text hash difference is not sufficient to establish semantic
discrimination when both variants carry the same violation flag and the
runtime exit signatures agree.

## Accepted witness categories

This audit accepts only:

1. different verifier exit signatures;
2. different explicit property or assertion verdicts;
3. different counterexample or deadlock verdicts;
4. different explicit state or transition counts;
5. different explicit runtime traces or execution-order lines.

Generated source, build output, embedded priority values, filenames, paths,
durations, and generic text hashes are excluded.

## Repetition stability

Base deterministic:
**true**

Reversed deterministic:
**false**

Absent deterministic:
**true**

## Base-versus-reversed comparison

Exit signature differs:
**false**

Strict property or assertion verdict differs:
**false**

Explicit state or transition count differs:
**false**

Explicit runtime trace or order differs:
**true**

Strict semantic evidence present:
**true**

Normalized full runtime transcript differs:
**true**

The full-transcript comparison is diagnostic only.

## Classification

**PHASE2B2D_GENERIC_HASH_DIFFERENCE_NOT_SUFFICIENT_FOR_SEMANTIC_WITNESS**

Semantic witness confirmed:
**false**

## Provisional claims

Claim A:
**OUTSIDE CURRENT FRAGMENT**

Claim B:
**NOT YET PROVED**

Claim C:
**CONDITIONAL — official RMC accepts actor-priority models**

Claim D:
**NOT YET PROVED**

Claims E through G:
**NOT YET PROVED**

## Next phase

**phase2b2e-repair-witness-model-and-property-observation-contract**
