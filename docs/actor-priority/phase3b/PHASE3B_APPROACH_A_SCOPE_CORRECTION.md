# Phase 3B Approach-A Scope Correction

## Frontend cardinality

The production parser bridge supports exactly one main actor.

Payload message servers are supported in that profile.

A second main actor is rejected before actor-priority annotations are
examined.

## Corrected fixture

Approach A uses:

`tests/actor-priority/approach-a-single-main-actor-payload-exclusion`

It tests the actual current frontend profile.

## Wrapper working-directory contract

The production wrapper performs Git discovery against its process working
directory.

The permanent test runner enters the investigation repository before each
wrapper invocation.

## Linked-worktree validation

The investigation repository is a linked Git worktree.

Its `.git` entry is a file rather than a directory.

Validity is therefore checked with:

- `git rev-parse --show-toplevel`;
- `git rev-parse --is-inside-work-tree`.

## Deferred obligation

`global-multi-actor-payload--priority-selection--negative` remains planned.

It is deferred to Approach B.

## Claim discipline

Approach A establishes exclusion from the current supported frontend
profile.

It does not establish that actor priority is unnecessary for multi-actor
Timed Rebeca.
