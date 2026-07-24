# ReLico-Lean

ReLico-Lean is an executable Lean 4 translation from a supported fragment of Deterministic Timed Rebeca to a generated subset of Lingua Franca with the C++ target.

The translation is implemented in Lean and connected directly to structural and semantic correctness theorems.

## Supported executable fragment

The current generalized source fragment supports:

- one reactive class and one actor instance;
- a finite nonempty list of integer state variables;
- one constructor and one message server;
- integer literals and references to any declared state variable;
- assignments to any declared state variable;
- cross-variable assignments;
- delayed self-sends with nonnegative constant delays.

The generated LF subset contains:

- one reactor and one reactor instance;
- one LF state declaration for every source state variable;
- one logical action;
- one startup reaction;
- one message reaction.

The original singleton vertical slice remains available as the schema-version-1 compatibility path.

## Executable pipeline

```text
Timed Rebeca source
→ existing Java Timed Rebeca parser and semantic checker
→ versioned JSON bridge
→ Lean JSON decoder
→ Lean DTR model
→ executable verified Lean translation
→ Lean LF program
→ trusted LF/C++ source printer
→ official lfc compiler
→ generated C++
→ native executable
```

The previous Java Lingua Franca generator is not used in this path.

## Formal results

For the supported finite-store fragment, the Lean development establishes:

1. finite-store lookup and update laws;
2. declared-variable store coverage and preservation;
3. expression evaluation over finite stores;
4. preservation of expression evaluation under translation;
5. forward and backward statement correspondence;
6. finite statement-trace correspondence;
7. occurrence-preserving message/action queue correspondence;
8. DTR minimum-logical-time scheduling;
9. LF lexicographic tag scheduling;
10. conditional forward dispatch correspondence;
11. unconditional backward dispatch correspondence under the declared runtime invariants;
12. combined statement-and-dispatch machine semantics;
13. runtime well-formedness preservation;
14. conditional finite forward machine-trace correspondence;
15. unconditional finite backward machine-trace correspondence;
16. generalized source-model and generated-program structural well-formedness;
17. preservation of state-variable declaration names, order, and initial values;
18. structural correctness connected to the executable `Translation.translateStore` function;
19. exact singleton compatibility with the original executable `Translation.translate` function.

The original singleton theorem stack additionally establishes constructor/startup initial-state correspondence.

Forward dispatch correspondence is conditional because LF microsteps may refine equal-logical-time choices that remain unresolved in the DTR semantics. The development does not claim that all permitted equal-time source schedules are observationally equivalent.

## Main executable functions

Finite-store path:

- Verified AST translation: `Relico.Translation.translateStore`
- LF/C++ source backend: `Relico.Translation.translateStoreToCppSource`
- Frontend JSON decoder: `Relico.Frontend.decodeStoreModelText`

Schema-version-1 compatibility path:

- Singleton AST translation: `Relico.Translation.translate`
- Singleton LF/C++ backend: `Relico.Translation.translateToCppSource`
- Singleton JSON decoder: `Relico.Frontend.decodeModelText`

## Build

Install Lean through `elan`, then run:

```bash
lake build
```

The Lean version is pinned in `lean-toolchain`.

## End-to-end integration checks

The integration checks require Java, Apache Maven, Lingua Franca `lfc`, CMake, a C++ compiler, and the ReLico artifact ZIP containing the existing Timed Rebeca parser.

When another command shadows Apache Maven, set `RELICO_MAVEN` explicitly:

```bash
export RELICO_MAVEN="$(brew --prefix maven)/bin/mvn"
```

Run the schema-version-1 recurring-source compatibility check:

```bash
frontend/java-bridge/check-v0.sh /path/to/ReLico-fmcad-2026-artifact-v1.zip
```

Compile and execute the terminating schema-version-1 fixture:

```bash
frontend/java-bridge/check-v0-runtime.sh /path/to/ReLico-fmcad-2026-artifact-v1.zip
```

Run the generalized two-variable parser-to-native check:

```bash
frontend/java-bridge/check-store.sh /path/to/ReLico-fmcad-2026-artifact-v1.zip
```

## Verification boundary

The formal proof covers:

```text
well-formed supported Lean DTR model
→ executable Lean translator
→ generated Lean LF program
→ declared operational-semantics correspondence
```

The following remain trusted or outside the proof:

- textual Timed Rebeca parsing;
- the existing Java semantic checker;
- Java parser-AST-to-JSON export;
- JSON parsing infrastructure;
- LF source printing;
- `lfc`;
- generated C++;
- the C++ compiler;
- the LF C++ runtime;
- the operating system and hardware;
- unsupported source-language constructs.

The integration tests exercise these components but do not formally verify them.

## Repository structure

- `Relico/Common`: names, values, occurrences, logical time, and finite stores
- `Relico/DTR`: source syntax, state, semantics, and well-formedness
- `Relico/LF`: generated syntax, state, semantics, and LF/C++ printers
- `Relico/Translation`: executable translations and concrete backends
- `Relico/Correctness`: structural and semantic proofs
- `Relico/Frontend`: bridge schemas, decoders, and executable bridge checks
- `Relico/Tests`: Lean regression tests
- `frontend/fixtures`: checked Timed Rebeca and JSON fixtures
- `frontend/java-bridge`: trusted adapters around the existing Java parser
- `docs`: decisions, scope, claims, and proof boundaries

## Reproducible fixtures

- Schema-version-1 recurring model: `frontend/fixtures/v0-controller.rebeca`
- Schema-version-1 terminating model: `frontend/fixtures/v0-once.rebeca`
- Schema-version-2 two-variable model: `frontend/fixtures/store-two-variable.rebeca`
- Checked schema-version-2 JSON: `frontend/fixtures/store-two-variable.json`

## Milestones

The end-to-end singleton baseline is tagged:

```text
milestone-v0-end-to-end
```

The generalized finite-store parser-to-native milestone is tagged:

```text
milestone-finite-store-end-to-end
```

## Current status

The generalized executable path supports multiple declared integer state variables and cross-variable assignments.

The trusted Java parser adapter, schema-version-2 Lean decoder, verified Lean store translator, LF/C++ printer, official `lfc` compiler, generated C++, and native execution have been exercised together on the committed two-variable fixture.
