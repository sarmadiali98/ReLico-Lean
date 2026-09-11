# ReLico translator tests

This directory contains purpose-built conformance and regression fixtures for the ReLico
translator. Each fixture isolates a supported capability, formal correspondence claim, runtime
contract, or expected rejection boundary.

These are tests, not empirical benchmarks. Externally sourced application models live under the
top-level `benchmarks/` directory.

The shared execution catalog is `evaluation/registry/benchmarks.tsv`. Test rows resolve their source and
manifest beneath this directory, while application benchmark rows resolve beneath `benchmarks/`.
Generated `actual/` and `.expected-regeneration/` directories are never committed.

## Software-test runner

`tools/relico_test.sh` is the unified test entry point. The authoritative paper-facing control plane
is `tests/catalog/catalog.json`, with canonical workflow stages in `tests/catalog/stages.json`. The
runner discovers individual Python and Lean software cases, the aggregate `RelicoTests` formal gate,
and every implemented translator fixture. The default run executes the portable catalog, unit, and
formal tiers; integration and external cases are selected explicitly because they require pinned
Java, RMC, `lfc`, C++, runtime, or separately provisioned parser artifacts.

```text
tools/relico_test.sh
tools/relico_test.sh --list
tools/relico_test.sh --tier catalog
tools/relico_test.sh --tier unit
tools/relico_test.sh --tier formal
tools/relico_test.sh --tier integration
tools/relico_test.sh --tier external
tools/relico_test.sh --suite python
tools/relico_test.sh --suite lean
tools/relico_test.sh --suite integration --family general
tools/relico_test.sh --suite integration --tag negative
tools/relico_test.sh --case fixture::core--well-formedness--negative
tools/relico_test.sh --junit
```

Generated execution records, captured stdout/stderr, summary JSON, case and stage JSONL, a coverage
matrix, environment metadata, and JUnit XML are written under `.test-results/`. Fixture `expected/`
directories remain committed golden oracles. A fixture passes only when its generated artifacts
match those committed files directly. Missing external prerequisites are reported as `unavailable`,
not as passes or omitted cases.

The externally provisioned `general--main-actor-priority--negative` boundary case is always visible
in the external tier. It executes when `RELICO_PARSER_ARTIFACT` names the required parser archive and
otherwise reports `unavailable`. It remains separate from the 61 registry-backed fixtures.

Negative integration cases must name the boundary expected to reject the input, assert the expected
exit and diagnostic, and forbid downstream artifacts. Formal obligation coverage and executable
behavioral coverage are separate claims; mapping a theorem to a fixture does not substitute for a
focused positive or negative software test.

Focused executable decisions are inventoried separately in
`evaluation/registry/behavioral-coverage.tsv`. The unified runner rejects duplicate feature IDs,
missing test modules, missing named test values, invalid polarities, and non-implemented entries.

Focused software cases are visible in this tree under directories ending in `--software`. Their
`cases.tsv` files are the discovery catalogs; every row maps one stable case ID to its executable
Lean assertion. Current totals are derived by catalog validation rather than copied into prose.

## Counting policy

Each stable logical case is counted once. The aggregate `RelicoTests` build is a formal gate, not an
additional test case, and pipeline stages are evidence attached to a fixture rather than separate
tests. Formal declaration/obligation totals are reported as formal evidence, not software-test
counts. The 41 application benchmarks remain a separate evaluation population under `benchmarks/`
and are never added to the translator-test total.
