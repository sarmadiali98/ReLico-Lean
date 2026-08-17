# Benchmark registry provenance

This registry was frozen from the reviewed benchmark plan at repository
checkpoint a4201d942d7d30c00f34f135dfe024d9ae30c82c, and has been amended
since. The counts below are the CURRENT registry contents, not the
checkpoint's; `tools/relico_bench_registry.py --validate` enforces them
against benchmarks.tsv and obligations.tsv on every run.

The registry currently contains:

- 172 accepted Lean test modules
- 2,129 mapped test obligations
- 58 planned source benchmarks
- 43 positive benchmarks
- 15 negative benchmarks
- zero unresolved modules
- zero unmapped obligations

Registry inclusion does not mean that a benchmark is implemented,
executable, or passing.

A benchmark becomes implemented only when its directory contains its
manifest, coverage mapping, commented Timed Rebeca source, expected
artifacts, and all required stage definitions.

Every benchmark Timed Rebeca source must first complete the official RMC
gate:

1. Timed Rebeca parsing and C++ generation
2. generated C++ compilation
3. generated model-checker execution
4. verdict and state-space artifact capture

RMC tool success and the semantic model-checking verdict are recorded
separately.

The six obsolete shell acceptance scripts remain scheduled for deletion.
They may be removed only after their assertions have been migrated to
the replacement benchmarks listed in legacy-script-migration.tsv.
