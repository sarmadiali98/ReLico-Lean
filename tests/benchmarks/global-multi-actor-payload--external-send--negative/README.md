# global-multi-actor-payload--external-send--negative

Negative global multi-actor payload external-send benchmark.

The source is grounded in the FMCAD `Sender_and_Receiver.rebeca` model. It preserves the actor-to-actor payload send `receiver0.receiveMessage(data)` from `sender0` to `receiver0`. A parameter-free local `keepAlive` message on `Sender` is added only to prevent the otherwise finite model from terminating in the quiescent state that RMC reports as a deadlock.

The source and RMC stages succeed. The current ReLico `multi-store-payload` parser bridge then rejects the two-reactive-class model with the deterministic diagnostic `unsupported by the ReLico multi-server parser bridge: expected exactly one reactive class, received 2`. The remaining stages record this as canonical expected-absence, expected-boundary, and terminal diagnostic evidence.

Formal coverage consists of the 56 accepted source-capability obligations in `Relico/Tests/GlobalMultiStorePayloadExternalSend.lean`.

This benchmark does not claim that the current source frontend decodes global actor topology. It does not claim a source-level self-resolution counterexample, unrestricted environmental send semantics, or a global absence of priority requirements.
