# Phase 4A Approach-B Isolated AST and Scheduler Foundation

## Recovery

The full Lake build and isolated-model elaboration had passed.

The isolated test failed because the model object was stored under a temporary
package root. Lean consequently attempted to resolve the model's transitive
project dependency under that same root.

The repair temporarily compiled the model object into Lake's normal project
object tree, elaborated the test through normal Lake import resolution, and
removed the temporary project object afterward.

## Mechanical result

Twelve closed Lean examples passed.

The isolated scheduler establishes:

- base priorities select `workera`;
- reversed priorities select `workerb`;
- tied priorities retain both actors;
- an absent request retains both actors;
- reversing priorities changes the eligible actor set.

## Validation

Full baseline Lake build:
**passed**

Direct isolated-model elaboration:
**passed**

Direct isolated-test elaboration:
**passed**

Closed Lean examples:
**12/12 passed**

Temporary project build object:
**removed**

## Interpretation

Actor-priority information can alter the eligible actor set when multiple
actors are simultaneously ready.

This is still an isolated result. It has not yet been integrated into:

- production global DTR semantics;
- production LF scheduling;
- the translation;
- the weak-bisimulation theorem;
- the benchmark registry.

## Conclusion status

The final actor-priority necessity conclusion is:
**not yet reached**

## Next phase

**phase4b-approach-b-integration-surface-and-proof-obligation-audit**
