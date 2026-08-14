# global-multi-actor-payload--external-send-frame--negative

This negative benchmark exercises the source-grounded global multi-actor external-send frame boundary.

The source and RMC stages succeed. The structural `global-multi-store-payload` parser succeeds and `decoded-dtr-ast` succeeds on the same reviewed external-send source used by the implemented positive external-send benchmark.

The expected boundary occurs after decoded DTR evidence is available. The current source benchmark pipeline does not expose a source-grounded external-send frame-transition witness covering sender continuation installation, receiver-state update, exact frame correspondence, history uniqueness, and the registered no-transition failure cases. The authoritative Lean frame module remains valid source-capability evidence.

This benchmark does not claim that external-send parsing is unsupported, that multi-actor parsing is unsupported, that external send itself is unsupported, or that the authoritative Lean frame theorems fail.

It does not claim unrestricted environmental input, universal multi-actor correctness, global irrelevance of priorities, or source self-termination. The canonical paper is not modified.
