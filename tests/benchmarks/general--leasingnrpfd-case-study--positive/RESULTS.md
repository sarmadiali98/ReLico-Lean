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
| model checker (recorded bonus, not a gate) | RMC 2.14 | `queue overflow` — the unfair-interleaving accumulation shape; see `ADAPTATION.md` |

No benchmark-runner bootstrap ran: with the `rmc` stage required by the
registry and its `queue overflow` verdict, the benchmark row cannot be
added, so there is no `expected/` tree. The stage results above were
measured directly through the pipeline's stage tool on 2026-09-07.
