# finite-store--well-formedness--positive

Positive finite-store well-formedness benchmark.

The source contains two integer state variables, `x` and `y`. The constructor initializes them to `1` and `2`, then schedules `tick`. Each execution of `tick` performs the cross-variable assignment `y = x` and reschedules itself.

Evidence combines the real eight-stage source-to-LFC route with 28 accepted source-capability obligations across `Relico/Tests/StoreEvaluation.lean` and `Relico/Tests/StoreModelTranslation.lean`. Of those registered obligations, 13 are proof obligations and 15 are test fixtures or helpers.

The formal evidence includes source-model well-formedness, successful translation, preservation of declarations and the cross-variable assignment, translated-program well-formedness, and finite-store expression-evaluation support.

No actor or message-server priority is required by this specific source design. This does not imply that priorities are globally unnecessary.
