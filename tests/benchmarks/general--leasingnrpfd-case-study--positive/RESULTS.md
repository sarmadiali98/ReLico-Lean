# Results — `general--leasingnrpfd-case-study--positive`

Demonstration run on 2026-09-07, at the tree of the approved
category-2 transformation.

| stage | tool | result |
|---|---|---|
| exporter | `run-general-from-zip.sh` | pass |
| decode | `lean-export --family general --mode decoded-dtr-ast` | pass |
| translation | `lean-export --family general --mode translated-lf-ast` | pass |
| LF generation | `lean-export --family general --mode lf-source` | pass |
| compile | `lfc 0.11.0`, C++ target | pass |
| runtime | generated binary, 5 msec logical-time budget | pass |
| model checker | RMC 2.14, `Deadlock-Freedom and No Deadline Missed` | **`satisfied`** |

The benchmark-runner bootstrap on 2026-09-07: unpinned run **pass**
(8/8 stages), `--regenerate` **pass**, 8 artifacts SHA-256 pinned
(including the generated LF at `expected/lf-source/TranslatedLFProgram.lf`),
pinned re-run **pass** (8/8 stages, ~54 s per run).
