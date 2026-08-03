# Phase 2B2C Official RMC Actor-Priority Probes

## Status

Official RMC was executed on external copies of official models containing
at least two distinct integer actor-level priorities.

For each selected model, three variants were executed:

1. the original actor-priority assignment;
2. the first two actor-priority values reversed;
3. actor-level priority annotations removed.

No tracked source was modified.

## Candidate selection

Candidate models discovered within the bounded selection set:
**4**

Candidate models executed:
**4**

Models whose base actor-priority form executed successfully:
**4**

## Results

| Candidate | Source | Base | Reversed | Absent | Semantic reversal differs |
|---|---|---|---|---|---|
| candidate-01 | `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/worker_sink.rebeca` | true | true | true | false |
| candidate-02 | `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_and_switch_with_after.rebeca` | true | true | true | false |
| candidate-03 | `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/verifier-benchmarks/TR/src/Alarm/Alarm.rebeca` | true | true | true | false |
| candidate-04 | `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/verifier-benchmarks/TR/src/UnsafeSend/UnsafeSend.rebeca` | true | true | true | false |

## Experiment classification

**ACTOR_PRIORITY_MODELS_ACCEPTED_BUT_NO_DISCRIMINATING_OUTPUT_FOUND_IN_SELECTED_OFFICIAL_MODELS**

Discriminating model found:
**false**

Selected candidate:
**none**

A semantic difference means that the normalized RMC transcript or a
state-, transition-, result-, verdict-, property-, trace-, graph-, or
report-oriented output changed when only the first two actor priorities
were exchanged.

A difference only in generated implementation artifacts is recorded
separately and is not sufficient for the discriminating classification.

## Provisional claims

Claim A:
**OUTSIDE CURRENT FRAGMENT**

Claim B:
**NOT YET PROVED**

Claim C:
**CONDITIONAL**

Claim D:
**NOT_YET_PROVED**

Claims E through G:
**NOT YET PROVED**

## Interpretation boundary

Successful execution of an official actor-priority model establishes that
the intended Timed Rebeca/RMC surface includes such models.

A reversal-dependent semantic result establishes that actor priority is
behaviorally relevant for at least that model. It does not by itself prove
that every actor-priority model is discriminating.

Failure to find a discriminating result in this bounded official-example
set does not establish that actor priority is unnecessary.

## Next phase

**phase2b2d-construct-minimal-systematic-discriminating-family**
