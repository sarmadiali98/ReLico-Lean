# ReLico

ReLico is an executable Lean 4 translation framework from a supported fragment of Deterministic Timed Rebeca (DTR) to a generated subset of Lingua Franca (LF) targeting C++.

## Overview

ReLico moves the DTR-to-LF translator into the Lean proof boundary. The same Lean definitions construct the target LF model and appear in structural and semantic correctness results. Parsing, interchange with the existing Timed Rebeca frontend, LF source generation, `lfc`, generated C++, and execution remain outside that proof boundary.

Repository: <https://github.com/sarmadiali98/ReLico>

## Current Status

The active executable path is the **General family**. It supports multiple reactive classes and actor instances, known rebecs and external sends, typed message payloads and constructor arguments, integer and Boolean state, supported unary and binary expressions, assignments, conditionals, local declarations, and nonnegative constant send delays. Actor and message-server priorities are represented by generated reaction declaration order.

The General JSON decoder, elaborator, DTR-to-LF translation, LF printer, focused test catalog, source-to-runtime fixtures, and registry-backed evaluation infrastructure are implemented. Earlier singleton, finite-store, and multi-store families remain as compatibility and regression surfaces with family-specific theorem stacks.

The project is still under active development. The General semantic correspondence interface retains explicit run-level premises, some accepted-fragment decisions lack focused tests, parameterless externally routed messages remain intentionally refused, iteration and several wider Timed Rebeca constructs remain unsupported, and the VMCAI 2027 evaluation suite is not frozen.

## Architecture

```text
Timed Rebeca source
-> trusted parser, type checker, and JSON exporter
-> general-v1 JSON
-> Lean General decoder and elaborator
-> Lean DTR model
-> executable Lean DTR-to-LF translation
-> Lean LF model
-> trusted LF source printer
-> lfc 0.11.0 and generated C++
-> native execution
```

The legacy Java LF generator is not part of this path. See [Verification and trusted boundary](docs/trusted-boundary.md) for the exact boundary.

## Formal Verification

For each semantic family, Lean results apply to that family's declared syntax, semantics, translation, and hypotheses; a theorem from one family is not automatically a theorem about another.

For the active General family, Lean establishes structural properties of generated LF programs, preservation results for supported translation constructs, priority-order properties, source/target state correspondence, weak transfer results, and forward and backward observable-trace agreement through a named label-level weak-bisimulation interface. The correspondence is stated over a **partial within-tag quotient** and three of the interface's six fields retain explicit run-level premises. It is therefore not a premise-free proof of equivalence for the complete parser-to-runtime pipeline.

The precise claims, instruments, and residual premises are listed in [General-family correctness claims](docs/claims/general-family-correctness.md). Integration tests and benchmark runs provide empirical evidence across trusted components; they do not enlarge the Lean proof boundary.

## Supported Fragment

The authoritative accepted-fragment description is [The General Family's Accepted Fragment](docs/supported-fragment-general.md). In brief:

| Feature | Status | Restrictions / Notes |
|---|---|---|
| Classes and actors | Supported | Multiple classes and instances; names and bindings must satisfy the General well-formedness rules |
| State and values | Supported | `int` and `boolean` |
| Expressions | Supported | Literals, state/parameter/local reads, 13 binary and 2 unary operators |
| Statements | Supported | Assignment, send, conditional, and local declaration |
| Communication | Supported | Self sends and declared known-rebec sends with typed payloads and constant nonnegative delays |
| Priorities | Supported with theorem conditions | Translation preserves ordering; strict uniqueness results require distinctness hypotheses |
| Parameterless external sends | Partially supported | Intentionally refused until target-port behavior is established |
| Iteration | Unsupported | Rejected by the active frontend |
| Arrays, inheritance, environmental inputs, physical actions, broadcast | Unsupported | Outside the represented fragment |

The Lean General AST also contains an internal `trace` witness statement. It has no Timed Rebeca or `general-v1` frontend spelling and is not part of the accepted source-language fragment.

## Usage

The Lean toolchain is pinned in `lean-toolchain`. Stable current entry points include:

```bash
lake build
tools/relico_test.sh --list
tools/relico_test.sh --tier unit
python3 tools/relico_bench.py --validate-registry
python3 tools/relico_bench.py --list
```

The active Lean APIs are `Relico.Frontend.decodeGeneralModelText` and `Relico.Translation.compileGeneralModel`. Source-to-runtime execution additionally requires separately installed external tools and, for parser-backed runs, the upstream parser artifact. These workflows are still being refined; final artifact reproduction instructions do not yet exist.

## Testing

The test system distinguishes logical software cases, aggregate Lean gates, translator fixtures, application benchmarks, and external prerequisites. The authoritative catalog is under `tests/catalog/`, translator fixtures are under `tests/translator/`, and unified test results are written under `.test-results/`. See [ReLico test system](tests/README.md) for tiers, selection, evidence classes, and counting rules.

## Evaluation

The registry-backed evaluation infrastructure separates 61 translator fixtures from 41 application and source-evidence benchmarks. Registry status and committed manifests describe what is currently implemented; the suite is not a frozen VMCAI artifact evaluation. See [ReLico executable evaluation catalog](evaluation/README.md) and [application benchmarks](benchmarks/README.md).

## Repository Structure

- `Relico/`: Lean source syntax, target syntax, translation, semantics, and correctness developments
- `frontend/`: trusted parser/export bridge, General schema, fixtures, and boundary checks
- `tests/`: authoritative test catalog and translator fixtures
- `benchmarks/`: application and source-evidence benchmarks
- `evaluation/`: shared benchmark registry and evaluation metadata
- `tools/`: catalog-backed test and benchmark interfaces
- `docs/`: current scope, claims, trusted boundary, decision records, and historical development notes
- `examples/`: unregistered empirical demonstration runs

## Documentation

- [Documentation index](docs/README.md)
- [Supported General fragment](docs/supported-fragment-general.md)
- [Verification and trusted boundary](docs/trusted-boundary.md)
- [General-family correctness claims](docs/claims/general-family-correctness.md)
- [Test and evidence model](tests/README.md)
- [Evaluation catalog](evaluation/README.md)
- [General frontend fixtures](frontend/fixtures/general/README.md)

## Limitations and Work in Progress

- The upstream parser, type checker, JSON exporter, LF printer, `lfc`, generated C++, runtime, OS, and hardware are trusted rather than formally verified.
- General observable correspondence is conditional and uses a partial quotient, as recorded in the claim document.
- The accepted Timed Rebeca fragment assumes successful upstream parsing and type checking; arbitrary JSON accepted by the Lean decoder is not a substitute for that source-language judgment.
- Iteration, arrays, inheritance, environmental inputs, physical actions, and broadcast are not supported by the active translation path.
- External sends to parameterless message servers are refused.
- Benchmark implementation, evaluation methodology, and artifact-facing documentation remain under active development.

## VMCAI 2027

ReLico is being prepared as the artifact associated with a VMCAI 2027 submission. Final artifact-specific setup, reproduction, resource, and paper-result instructions will be added after the implementation and evaluation are frozen.

## License

ReLico is licensed under the [MIT License](LICENSE). Third-party tools and dependencies retain their own license terms.
