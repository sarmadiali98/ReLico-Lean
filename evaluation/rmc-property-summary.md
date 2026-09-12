# RMC assertion evaluation summary

This report consolidates the accepted source-level RMC assertion evidence. The definitive row-level
ledger is [`rmc-property-inventory.tsv`](rmc-property-inventory.tsv). Election is infrastructure
validation only and is excluded from every semantic-corpus total below.

## Semantic corpus

| Measure | Result |
|---|---:|
| Property-bearing semantic benchmarks | 25 |
| Accepted properties | 41 |
| Observed `TRUE` | 25 |
| Observed `FALSE` | 16 |
| Expected/observed matches | 41 |
| Mismatches | 0 |

| Reporting category | Count |
|---|---:|
| Safety invariant | 18 |
| Monitor-contract check | 7 |
| Reachability witness | 14 |
| Negative witness | 2 |
| Total | 41 |

The repository-wide pinned ledger contains 43 rows across 26 directories: the 41-row semantic
corpus plus Election's two infrastructure-validation rows (`1 TRUE`, `1 FALSE`).

## Infrastructure validation

| Benchmark | Property | Category | Expected | Observed | Status |
|---|---|---|---:|---:|---:|
| Election | `election-no-wrong-winner` | safety invariant | `TRUE` | `TRUE` | `MATCH` |
| Election | `election-node1-not-elected` | reachability witness | `FALSE` | `FALSE` | `MATCH` |

These rows exercise generic manifest, assertion, expected-`FALSE`, counterexample, normalization,
and hash-pinning behavior. They are not application-level semantic-corpus results.

## Candidate disposition

Ten rejected or withheld candidate classes are explicitly recorded: AutonomousVehicles completion
reachability (the explored model did not reach `allVehiclesReached`), LeasingNRPFD failover
reachability (RMC exposed no such state), and eight YARN classes. The YARN review rejected per-slot
FIFO bounds, status-domain checks, initialization-only checks, `doneJobs` progress claims,
redundant event witnesses, full scheduling correctness, liveness, and translation preservation.

Fifteen implemented application benchmarks currently have no accepted assertion property:
`general--arbitrary-msgsrv-ordering--positive`, `general--causal-msgsrv-chain--positive`,
`general--causal-rebec-chain--positive`, `general--circular-msgsrv-ordering--positive`,
`general--circular-rebec-ordering--positive`, `general--partial-msgsrv-ordering--positive`,
`general--periodic-circular-composition--positive`, `general--periodic-join-composition--positive`,
`general--periodic-pingpong-composition--positive`,
`general--periodic-sequential-composition--positive`,
`general--tinyosmacb-case-study--positive`, `general--traindoor-case-study--positive`,
`general--trigger-pingpong-composition--positive`,
`general--trigger-sequential-composition--positive`, and
`general--widebarrier24-case-study--positive`. Current documentation does not uniformly establish
that all fifteen lack observable state; it only establishes that no meaningful assertion was
accepted for this evaluation, so no stronger reason is assigned here.

## YARN scaling

RMC checker metrics and whole direct-stage resources are different measurements. Checker states,
transitions, runtime, and consumed memory below are the recorded Stage 5D checker measurements.
Direct-stage wall time and maximum RSS cover property generation, generated C++ compilation, and
both checks. The normalized `results.json` schema pins outcomes and counterexample metadata but does
not contain resource fields.

| Variant | Marker states | Marker transitions | Marker runtime | Marker memory | Witness states | Witness transitions | Witness runtime | Witness memory |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 AM | 236 | 412 | 0s | 1,888 | 7 | 8 | 0s | 56 |
| 2 AM | 10,919 | 27,886 | 0s | 131,028 | 9 | 10 | 0s | 108 |
| 3 AM | 541,164 | 1,850,284 | 5s | 8,658,624 | 11 | 12 | 0s | 176 |
| 4 AM | 670,232 | 2,924,598 | 10s | 13,404,640 | 13 | 14 | 0s | 260 |

| Variant | Direct-stage wall time | Direct-stage maximum RSS |
|---|---:|---:|
| 1 AM | 13.41s | 522,633,216 bytes |
| 2 AM | 14.37s | 655,163,392 bytes |
| 3 AM | 17.15s | 692,944,896 bytes |
| 4 AM | 21.25s | 667,467,776 bytes |

Within the recorded property-level metric subset, the smallest run is the 1AM completion witness
(7 states, 8 transitions, 0s, 56 bytes). The 4AM marker invariant has the largest state space
(670,232), transition count (2,924,598), checker memory value (13,404,640), and checker runtime
(10s). Whole-stage maximum RSS instead peaks at 3AM (692,944,896 bytes), while whole-stage wall time
peaks at 4AM (21.25s). The completion witnesses remain shallow as AM count grows; the invariant
explorations show the substantive scaling cost.

## Interpretation limits

All rows are source-level assertions over adapted Timed Rebeca models. Expected-`FALSE` results are
intentional counterexample witnesses, not liveness results. Monitor-contract success may be vacuous
with respect to event occurrence unless paired with a separate witness. No row establishes TCTL,
complete application correctness, or preservation through the verified Lean-to-LF translation.
