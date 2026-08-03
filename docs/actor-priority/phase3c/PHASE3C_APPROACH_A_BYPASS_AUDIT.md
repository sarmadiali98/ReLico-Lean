# Phase 3C Approach-A Bypass Audit

## Scope

This audit covers the exact current production profile:

- one main actor;
- payload message-server support;
- local message-server priority;
- explicit main-actor priority rejected before JSON;
- no claim about global multi-actor Timed Rebeca semantics.

Manual injection of hand-written parser JSON is outside the trusted
source-entrypoint contract.

## Permanent fixture rerun

Permanent fixture exit:
**0**

Permanent fixture passed:
**true**

## Dynamic parser-entrypoint matrix

| Entrypoint | Applicable | Actor rejected before JSON | Stable diagnostic | Local priority preserved | Bypass | Status |
|---|---|---|---|---|---|---|
| frontend/java-bridge/run-from-zip.sh | false | true | false | false | false | NOT_APPLICABLE_TO_CURRENT_FIXTURE_PROFILE |
| frontend/java-bridge/run-multistore-from-zip.sh | false | true | false | false | false | NOT_APPLICABLE_TO_CURRENT_FIXTURE_PROFILE |
| frontend/java-bridge/run-multistore-payload-from-zip.sh | true | true | true | true | false | CURRENT_PROFILE_EXCLUSION_ENFORCED |
| frontend/java-bridge/run-store-from-zip.sh | false | true | false | false | false | NOT_APPLICABLE_TO_CURRENT_FIXTURE_PROFILE |

Applicable parser wrappers:
**1**

Observed actor-priority bypasses:
**0**

Applicable-wrapper contract failures:
**0**

The payload-wrapper diagnostic contract passed:
**true**

## Local-priority separation

The audit treats local message-server priority and actor priority as separate
features.

Every applicable wrapper must accept the local-priority control and preserve
priority value `1`.

## Empty and nonempty actor-priority syntax evidence

Official nonempty integer actor-priority forms rejected without JSON:
**true**

Tested empty candidate forms rejected:
**true**

The empty candidate tests establish rejection of the tested frontend forms.
They do not establish that Timed Rebeca defines a valid explicit-empty
actor-priority declaration.

## Downstream source-to-LF bypass audit

Tracked accepted-pipeline entrypoints inspected:
**19**

Unresolved direct source-to-LF entrypoints:
**0**

- None.

A downstream component that consumes trusted JSON is not a source parser and
does not by itself bypass source-level rejection.

## Formal boundary

Direct Lean elaboration passed:
**true**

Project `sorry`/`admit`/explicit-`axiom` findings in the audited boundary:
**0**

## Benchmark-harness contract

Negative-stage harness contract tests passed:
**true**

The registered multi-actor priority-selection obligation remains planned.
No registry row was reclassified by this phase.

## Result

Classification:
**APPROACH_A_CURRENT_PROFILE_BYPASS_AUDIT_PASSED**

Claim A:
**OUTSIDE CURRENT FRAGMENT**

Claim B:
**NO**

Claim B is limited to the exact current single-main-actor payload frontend and
the corresponding Lean restriction boundary.

It is not a claim that actor priority is unnecessary for full Timed Rebeca.

Claim C:
**CONDITIONAL**

Claim D:
**YES**

Claim E:
**NOT YET PROVED**

Claim F:
**NOT YET PROVED**

Claim G:
**CONDITIONAL**

Approach-A status:
**current_profile_exclusion_mechanically_enforced**

## Next phase

**phase4a-approach-b-isolated-ast-and-scheduler-foundation**
