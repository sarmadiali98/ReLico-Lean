# Results - `general--yarn-deadline-fifo-4am-case-study--positive`

Measured 2026-09-10 through the repository stage pipeline.

| stage | tool | result |
|---|---|---|
| source validation | `relico_bench_stage.py source` | pass |
| model checker | RMC 2.14, `Deadlock-Freedom and No Deadline Missed` | **`satisfied`** (670,232 states, 2,924,598 transitions) |
| parser JSON | general parser bridge | pass |
| decode | `lean-export --family general --mode decoded-dtr-ast` | pass |
| translation | `lean-export --family general --mode translated-lf-ast` | pass |
| LF generation | `lean-export --family general --mode lf-source` | pass |
| compile | `lfc 0.11.0`, C++ target | pass |
| runtime | generated binary, 5 msec logical-time budget | pass |
| Lean project | `lake build` | pass, 549 jobs |

RMC completed in 15 seconds after projecting out the four `doneJobs` counters used only by the
excluded external property. All eight expected artifacts were copied from the successful pipeline
outputs and SHA-256-pinned in `manifest.json`. Generated C++ compilation emitted warnings only.
