# Actor-Priority Approach A: Explicit Exclusion

## Objective

Approach A makes the current no-actor-priority theorem and frontend
boundary explicit, permanent, tested, and defensible.

It does not claim that actor priority is semantically unnecessary in
Timed Rebeca.

## Existing semantic boundary

The current correspondence relations use an explicit actor index and do
not autonomously select among enabled actors.

The existing boundary module contains:

- `ActorPriorityAssignment`;
- `ActorPriorityRequest`;
- `RequestWithinSupportedFragment`;
- the requirement that the request equal `none`;
- rejection evidence for nonempty and empty `some` assignments.

Approach A preserves this theorem domain.

## Frontend boundary

The production frontend currently distinguishes:

- local message-server priority, which is accepted and preserved;
- main-actor priority, which is rejected before parser JSON is emitted.

Approach A converts this observed behavior into a stable support contract.

## Permanent negative benchmark

Target benchmark:

`global-multi-actor-payload--priority-selection--negative`

Required behavior:

1. the official parser recognizes the valid integer annotation;
2. the ReLico frontend rejects it with the supported-fragment diagnostic;
3. no parser JSON is emitted;
4. no decoded DTR AST is emitted;
5. no translated LF AST or LF source is emitted;
6. no lfc or runtime artifact is emitted.

## Positive controls

Approach A must retain:

- a source with no actor-priority annotation;
- a source with local message-server priority;
- all current one-step and finite-execution theorem tests;
- the currently accepted tracked benchmark.

## Bypass requirement

Every discovered source-to-parser and source-to-LF entrypoint must enforce
the same boundary.

A single wrapper-level rejection is insufficient when another production
entrypoint can bypass it.

## Proof impact

Approach A must not add:

- actor-priority metadata to the source state;
- an enabled-actor selector;
- actor-priority scheduling to the target;
- priority-aware correspondence lemmas.

Those belong exclusively to Approach B.

## Claims after successful implementation

After Approach A passes, the defensible claim is:

> ReLico’s current supported and proved fragment excludes actor-priority
> requests, while preserving local reaction priority.

The following claim remains invalid:

> Actor priority is unnecessary for Timed Rebeca.

## Implementation readiness

Lean boundary resolved:
**true**

Frontend enforcement paths resolved:
**true**

Parser entrypoints resolved:
**true**

LF bypass surface resolved:
**true**

Benchmark harness resolved:
**true**

Negative expectation schema:
**RESOLVED**

Ready for controlled source mutation:
**true**

## Next phase

**phase3b-approach-a-exclusion-source-and-benchmark-implementation**
