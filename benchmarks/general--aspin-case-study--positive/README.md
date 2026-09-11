# `general--aspin-case-study--positive`

A **general**-family positive benchmark for ASPIN, a 4x4 torus network-on-chip model. Sixteen
routers use XY routing, per-direction buffers and mutexes, and acknowledgements to carry one packet
from `r00` to `r23`; a manager restarts the designated source path after 700 time units.

## Provenance

- **Original source:** `examples.zip:ReLico-main/ASPIN.rebeca`.
- **Property:** the archive contains no ASPIN `.property` file.
- **Adaptation:** finite array flattening, byte widening, static sender tags, the documented
  deadline-monitor abstraction, and inert marker parameters; see
  [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`,
`translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0;
- RMC 2.14 reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`;
- the generated LF is preserved and SHA-256-pinned in `manifest.json`;
- the generated runtime exits successfully under the benchmark runtime stage.
