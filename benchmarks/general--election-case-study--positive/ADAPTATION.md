# Election - adaptation record

Status: **complete** - the unmodified model semantics pass the full benchmark pipeline.

Source: `examples.zip:ReLico-main/Election/Election.rebeca`, with six reactive classes
(`Checker`, `Node1`, `Router`, `Node0`, `Source`, and `KeepAlive`).

## Property boundary

The original `Election.property` file remains excluded and no semantic correction was applied to
the source. The benchmark-local `rmc-properties` stage independently evaluates two assertions over
the adapted Timed Rebeca source: node 0 is never accepted, and an intentionally false invariant
witnesses election of node 1. These checks do not target the decoded Lean DTR or translated LF
artifacts, and RMC assertions are evaluated after transitions rather than directly on the initial
state.

## Applied adaptation

No semantic adaptation was applied. The source preserves the actors, state, integer message
payloads, message and instance priorities, routing order, and the 100-unit KeepAlive delay. Only a
benchmark provenance header was added.

The independent KeepAlive self-rearming loop remains. RMC 2.14 reports `satisfied` without queue
growth, and the generated LF executable terminates successfully under the runtime stage, so no
timing redesign is justified.
