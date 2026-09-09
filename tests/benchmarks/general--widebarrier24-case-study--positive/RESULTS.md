# Results - `general--widebarrier24-case-study--positive`

Measured 2026-09-09 through the repository stage pipeline.

| stage | tool | result |
|---|---|---|
| source validation | `relico_bench_stage.py source` | pass |
| model checker | RMC 2.14, `Deadlock-Freedom and No Deadline Missed` | **`satisfied`** (3,006 states, 39,130 transitions) |
| parser JSON | general parser bridge | pass |
| decode | `lean-export --family general --mode decoded-dtr-ast` | pass |
| translation | `lean-export --family general --mode translated-lf-ast` | pass |
| LF generation | `lean-export --family general --mode lf-source` | pass |
| compile | `lfc 0.11.0`, C++ target | pass |
| runtime | generated binary, 5 msec logical-time budget | pass |

The fixture source is byte-identical to
`examples.zip:ReLico-main/WideBarrier24/WideBarrier24.rebeca`.
`WideBarrier24.property` is intentionally excluded. All eight expected artifacts were copied from
the successful pipeline outputs and SHA-256-pinned in `manifest.json`.
