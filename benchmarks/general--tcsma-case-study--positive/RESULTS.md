# Results — `general--tcsma-case-study--positive`

Measured 2026-09-07. The stage results were confirmed both through the pipeline's stage tool and through the benchmark runner's pinned bootstrap below.

| stage | tool | result |
|---|---|---|
| exporter | `run-general-from-zip.sh` | pass |
| decode | `lean-export --family general --mode decoded-dtr-ast` | pass |
| translation | `lean-export --family general --mode translated-lf-ast` | pass |
| LF generation | `lean-export --family general --mode lf-source` | pass |
| compile | `lfc 0.11.0`, C++ target | pass |
| runtime | generated binary, 5 msec logical-time budget | pass |
| model checker | RMC 2.14, `Deadlock-Freedom and No Deadline Missed` | **`satisfied`** |
