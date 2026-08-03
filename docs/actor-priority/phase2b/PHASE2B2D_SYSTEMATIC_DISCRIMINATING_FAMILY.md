# Phase 2B2D Systematic Actor-Priority Family

## Status

A bounded purpose-built family was generated outside the repository and
executed through the exact successful RMC command recovered from Phase
2B2C.

No tracked source was modified.

## Model design

Each model contains two workers and one observer.

Both workers schedule `fire` at the same logical delay. Worker A sends
identifier `1`; Worker B sends identifier `2`. The observer stores the
first identifier and, upon the second hit, asserts that the stored value
equals the family’s expected first sender.

Dimensions:

- expected first sender: `1` or `2`;
- worker firing delay: `0` or `1`;
- base worker priorities: `1`, `2`;
- reversed worker priorities: `2`, `1`;
- actor-priority-absent control.

Assertion keyword used: `assertion`

## Official assertion evidence

- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/CoreRebecaModelAllExpressions.rebeca:71` — `assertion(10==20);`
- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TinyOSPV6-TDMA.rebeca:51` — `//assertion(tmp >= 0);`
- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TinyOSPV6-TDMA.rebeca:52` — `assertion((period - lag - currentMessageWaitingTime) >= 0);`
- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TinyOSPV6-TDMA.rebeca:185` — `assertion(receiverDevice == null);`
- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TinyOSPV6-TDMA.rebeca:198` — `assertion(tmdaSlotSize - currentMessageWaitingTime > 0);`

## Results

| Family | Expected first | Delay | Base generated | Reversed generated | Runtime variants | Violation differs | Behavior differs | Code generation differs | Discriminating |
|---|---:|---:|---|---|---:|---|---|---|---|
| expected-1-delay-0 | 1 | 0 | true | true | 3 | false | true | true | true |

Planned families: **4**

Executed families: **1**

Families accepted in both base and reversed form:
**1**

Build attempts: **3**

Variants with at least one verifier-runtime execution:
**3**

## Classification

**MINIMAL_SYSTEMATIC_FAMILY_FOUND_ACTOR_PRIORITY_DEPENDENT_BEHAVIOR**

Discriminating family found:
**true**

Selected family:
**expected-1-delay-0**

A family is classified as semantically discriminating only when reversing
the two worker priorities changes an assertion/violation result, verifier
exit signature, or behavior-oriented verifier output.

A generated C/C++ or Java difference is recorded separately and is not
treated as semantic proof.

## Provisional claims

Claim A:
**OUTSIDE CURRENT FRAGMENT**

Claim B:
**NOT YET PROVED**

Claim C:
**CONDITIONAL — official RMC accepts actor-priority models**

Claim D:
**YES**

Claims E through G:
**NOT YET PROVED**

## Interpretation boundary

The earlier official examples were non-discriminating but changed
generated implementation artifacts.

This systematic family tests a deliberately noncommutative race. Failure
to execute the generated verifier or to expose its property result does
not establish that actor priority is unnecessary; it identifies the next
tool-contract question.

## Next phase

**phase2b3-classify-phase2-evidence-before-approach-implementations**
