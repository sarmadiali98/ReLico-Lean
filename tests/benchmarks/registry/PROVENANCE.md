# Benchmark registry provenance

This registry freezes the reviewed benchmark plan at repository
checkpoint a4201d942d7d30c00f34f135dfe024d9ae30c82c.

The frozen registry contains:

- 172 accepted Lean test modules
- 1,928 mapped test obligations
- 57 planned source benchmarks
- 42 positive benchmarks
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
