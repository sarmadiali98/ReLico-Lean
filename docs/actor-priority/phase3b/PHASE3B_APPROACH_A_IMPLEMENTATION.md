# Phase 3B Approach-A Implementation

## Git-worktree validation repair

The previous command incorrectly required `.git` to be a directory.

The investigation repository is a linked worktree, where `.git` is a
file.

The runner now uses Git-native worktree validation.

## Wrapper-CWD repair

The permanent runner enters the investigation repository before invoking
the production parser wrapper.

It was tested from `/Users/ali`.

## Corrected fixture scope

The current frontend supports one main actor.

The permanent exclusion regression targets that profile.

## Permanent fixture

`tests/actor-priority/approach-a-single-main-actor-payload-exclusion`

## Test result

| Case | Wrapper CWD | Exit | JSON | Parseable | Local priority 1 | Diagnostic |
|---|---|---:|---|---|---|---|
| actor-priority | /Users/ali/Desktop/ReLico-Actor-Priority-Investigation | 1 | false | false | false | true |
| actor-priority-absent | /Users/ali/Desktop/ReLico-Actor-Priority-Investigation | 0 | true | true | false | false |
| local-message-server-priority | /Users/ali/Desktop/ReLico-Actor-Priority-Investigation | 0 | true | true | true | false |

## Build and proof validation

Full `lake build`:
**passed**

Direct actor-priority boundary elaboration:
**passed**

Production wrapper mutation required:
**false**

Production Lean mutation required:
**false**

Production frontend mutation required:
**false**

## Registry status

Published accepted tracked benchmarks:
**1/57**

The multi-actor priority-selection obligation remains **planned** and is
deferred to Approach B.

## Claim status

Claim A:
**OUTSIDE CURRENT FRAGMENT**

Claim B:
**NOT YET PROVED**

The permanent current-profile test passes. The complete entrypoint bypass
audit remains for Phase 3C.

Claim C:
**CONDITIONAL**

Claim D:
**YES**

## Next phase

**phase3c-approach-a-bypass-audit-with-single-main-actor-frontend-scope**
