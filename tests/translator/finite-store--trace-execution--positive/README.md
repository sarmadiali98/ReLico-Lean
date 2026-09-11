# finite-store--trace-execution--positive

Positive finite-store trace-execution benchmark.

The source contains two integer state variables and a recurring `tick` message server. Each execution of `tick` performs the cross-variable assignment `y = x` and schedules the next `tick`.

Evidence combines the real nine-stage source-to-runtime route with the four accepted source-capability theorems in `Relico/Tests/StoreTrace.lean`.

No actor or message-server priority is required by this benchmark.
