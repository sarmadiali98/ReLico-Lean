# Results — `general--smarthome-case-study--positive`

Demonstration run on 2026-09-07, at the tree of `examples: record the
tier-2 real-corpus runs (K)` plus the adaptation work. The pipeline is the
benchmark suite's own, run stage by stage.

| stage | tool | result |
|---|---|---|
| exporter | `frontend/java-bridge/run-general-from-zip.sh` | pass |
| decode | `lean-export --family general --mode decoded-dtr-ast` | pass |
| translation | `lean-export --family general --mode translated-lf-ast` | pass |
| LF generation | `lean-export --family general --mode lf-source` | pass, 8 reactors |
| compile | `lfc 0.11.0`, C++ target | pass |
| runtime | generated binary, 5 msec logical-time budget | pass |
| model checker (recorded bonus) | RMC 2.14, `Deadlock-Freedom and No Deadline Missed` | `satisfied` |

The benchmark-runner bootstrap (unpinned run, `--regenerate`, SHA-256 pin,
pinned re-run) is recorded below and its pinned artifacts are committed
under `expected/`.
