# Phase 4B False-Positive Classification Correction

## Reason for correction

The original Phase 4B audit conservatively treated three textual
actor-priority hits outside the explicit boundary and frontend as evidence of
production integration.

The exact review removed comments and strings before classification.

All three hits were comment-only:

- one comment states that actor selection and cross-actor priority remain
  outside the dispatch-correspondence layer;
- one comment states that an external-send witness deliberately contains no
  actor-priority claim;
- one comment states that external-send construction performs no
  actor-priority selection.

## Signature review

Eight production declarations were audited through Lean.

None contains an actor-priority parameter or actor-priority term.

The declarations cover:

- source and target multi-store dispatch;
- source and target local-priority selection;
- message-reaction translation;
- selection compatibility;
- forward dispatch correspondence;
- backward dispatch correspondence.

## Corrected finding

Production actor-priority integration:

**false**

The original `true` value was a lexical false positive and is superseded by
this addendum.

The historical Phase 4B report is retained unchanged for auditability.

## Erasure-theorem readiness

The decisive theorem now has all required premises available:

1. the pinned RMC witness shows that reversing only actor priorities changes
   the reachable actor-dispatch trace language;
2. the isolated Lean scheduler shows that reversing priorities changes the
   eligible actor;
3. the current production translation and audited correspondence signatures
   contain no actor-priority information.

The next theorem must establish that a priority-erasing translation cannot be
behaviorally equivalent to both priority-reversed source systems.

## Status of the target conclusions

Conclusion 1 remains established only for scopes where actor priority is
excluded or independently shown to be semantically inert.

Conclusion 2 is ready for its decisive formal theorem:

> When actor priority changes cross-actor selection, a faithful translation
> must preserve the resulting ordering information, explicitly or through an
> equivalent compiled mechanism.

## Final conclusion status

**not yet reached**

## Next phase

**phase4c-actor-priority-erasure-impossibility-theorem**
