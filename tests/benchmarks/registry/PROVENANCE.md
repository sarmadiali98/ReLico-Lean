# Benchmark registry provenance

This registry was frozen from the reviewed benchmark plan at repository
checkpoint a4201d942d7d30c00f34f135dfe024d9ae30c82c, and has been amended
since. The counts below are the CURRENT registry contents, not the
checkpoint's; `tools/relico_bench_registry.py --validate` enforces them
against benchmarks.tsv and obligations.tsv on every run.

The registry currently contains:

- 183 accepted Lean test modules
- 2,468 mapped test obligations
- 90 planned source benchmarks
- 89 positive benchmarks
- 1 negative benchmark
- zero unresolved modules
- zero unmapped obligations

## The general family, and the obligation-extraction convention

The general family's ten rows and 339 obligations were added after the freeze,
from the eleven `Relico/Tests/General*.lean` modules that the frozen scan had
never covered. `tools/relico_bench_registry.py --validate` enforces their counts
with every other row's.

The scanner that produced the original 2,129 rows was never committed, so its
convention had to be recovered from the frozen rows and falsified against them
before anything was appended. It reproduces 171 of the 172 frozen modules
byte-identically on `obligation_id`, `line_number`, `kind`,
`name_or_expression` and `classification`. The single residual is eight rows in
`Relico/Tests/GlobalMultiStorePayloadActorSelectionCorrespondence.lean`, where
the frozen data itself records `#print axioms` as
`executable_or_computation_check` against `trust_or_declaration_check` on the
other fifty-five such rows.

Two properties of that convention are defects, reproduced deliberately so the
columns keep one meaning across every row rather than two meanings with nothing
marking the boundary:

- **`line_number` is the 1-based line minus the run of blank lines directly above
  it.** So a declaration with one blank line above it is recorded one line early,
  and with two blank lines above it, two lines early.
- **The declaration patterns match an identifier prefix, and comments are not
  stripped.** `className :=` is counted as a `class` declaration, `exampleIsTau`
  inside a theorem statement as an `example`, and a documentation line opening
  with the word `theorem` as a `theorem`. Of the 339 general rows, 23 are
  `class`-prefix artifacts and one is a documentation line; measured, and no real
  `class` declaration exists anywhere under `Relico/Tests`, which makes all 23
  `class` rows in the frozen half the same artifact.

Repairing either would have to move all 2,468 rows in one pass, which is a
separate task from adding a family.

## Candidate source models

`general-corpus-selection.tsv` records the measured construct profile of every
candidate general-family source model, so that benchmark selection is derived
from measurement instead of a hard-coded next benchmark. It keeps two
populations apart because their verdicts have different standing: the 32 in-repo
fixtures under `frontend/fixtures/general/`, whose directory *is* the gate's
verdict, and the 49 upstream corpus models in `examples.zip`, which have never
been through the frontend and therefore carry a static screen against the
exclusion list in `docs/supported-fragment-general.md` rather than a verdict.
The screen clears 28 of the 49 where the project's recorded I0 census put 31 of
49 inside the fragment; the two are different instruments, the disagreement is
left standing rather than tuned away, and it belongs to the wave that runs the
real frontend over the corpus.

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

## The negative suite, re-measured

Stage K re-ran every implemented negative benchmark's own source through the
current verified pipeline. Seven of eight passed every stage and reported
`satisfied` under the model checker: they encoded family-bridge limits
(message-server parameters, a second reactive class, self-resolving external
sends, reordered initialization, arithmetic payloads, a frame witness), not DTR
violations, and were re-polarized into positive benchmarks with their
obligations preserved. The seven planned negatives that had never been sourced
were removed, their 240 obligations re-homed onto same-family, same-capability
positive rows. `core--well-formedness--negative` remains the one genuine
negative: upstream Timed Rebeca itself refuses its source. The rule going
forward is recorded as F95 in `docs/STAGE_K_FINDINGS.md`.

## The examples2 corpus

`examples2.zip` contributes 17 candidate models -- ordering and composition
patterns from the paper's own themes, each ordering case supplied at both the
rebec and the message-server level. All 17 clear the exporter, the Lean
decoder, the verified translation and `lfc` with zero adaptation; nine also
report `satisfied` under the model checker and are implemented now. The other
eight overflow the model checker's queue. Seven have since been redesigned
under the stage K policy -- the overflow is an uncoupled periodic producer,
not a defect in the pattern under test, so each redesign couples every
producer to the consumption of what it produced while keeping the actors,
the communication pattern and the observable purpose -- and all seven pass
the full pipeline with the model checker satisfied. The eighth is
byte-identical to one of the seven and stays planned pending a
differentiating source. These rows own no Lean obligations -- they are
source-evidence rows, so they carry no formal-witness stage.
