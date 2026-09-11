# ReLico test system

This directory is the authoritative, paper-facing entry point for tests of the ReLico translator.
It separates logical software tests, aggregate formal gates, pipeline evidence, and application
benchmarks so that the same assertion is not counted more than once.

## Control plane

- `catalog/catalog.json` defines the logical populations, discovery rules, evidence relationships,
  and counting policy.
- `catalog/stages.json` defines the canonical source-to-runtime workflow stages and trusted-boundary
  evidence.
- `catalog/claims.json` states the paper-facing claims supported by each evidence class and the
  limitations of that support.
- `catalog/validate_catalog.py` checks catalogs, registries, fixture manifests, executable discovery,
  stage names, and the fixed 61 translator-fixture / 41 application-benchmark split.
- `translator/` contains focused software catalogs and source-to-runtime translator fixtures.

The verified object is the executable Lean translation from a DTR model to an LF model. Parser and
JSON export, LF printing, `lfc`, generated C++, runtime, OS, and hardware remain trusted components;
their tests provide integration evidence rather than extending the proof boundary.

## Test tiers

| Tier | Evidence |
|---|---|
| `catalog` | Inventory, identity, ownership, stage, and counting integrity |
| `unit` | Focused Python and individually executable Lean software cases |
| `formal` | Aggregate build of all imported Lean test and proof modules |
| `integration` | Registry-backed source-to-runtime translator fixtures |
| `external` | Separately provisioned parser-boundary cases |

Run the portable tiers with:

```text
tools/relico_test.sh
```

Inspect or select evidence with:

```text
tools/relico_test.sh --list
tools/relico_test.sh --tier unit --polarity negative
tools/relico_test.sh --tier integration --family general
tools/relico_test.sh --case lean-case::core.translation.api.exact-program
```

Generated evidence is written to `.test-results/` as `summary.json`, `cases.jsonl`, `stages.jsonl`,
`coverage-matrix.tsv`, `environment.json`, JUnit XML, and per-case stdout/stderr.

## Paper metrics

Report translator logical cases, formal declarations/obligations, and application benchmarks as
three non-additive populations. A logical case remains one case when it crosses multiple pipeline
stages. The `RelicoTests` aggregate build is formal gate evidence and does not add another logical
case. Missing external tools or artifacts are `unavailable`, never silently omitted or reported as
passing.
