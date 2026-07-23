# ReLico-Lean

ReLico-Lean is an executable Lean 4 translation from a supported fragment of Deterministic Timed Rebeca to a generated subset of Lingua Franca with the C++ target.

The translation is implemented in Lean and connected directly to structural and semantic correctness theorems.

## Vertical slice v0

The current source fragment supports:

- one reactive class and one actor instance;
- one integer state variable;
- one constructor and one message server;
- integer literals and state-variable references;
- assignments;
- delayed self-sends with nonnegative constant delays.

The generated LF subset contains one reactor instance, one integer state variable, one logical action, a startup reaction, and a message reaction.

## Executable pipeline

```text
Timed Rebeca source
→ existing Java Timed Rebeca parser and semantic checker
→ versioned JSON bridge
→ Lean JSON decoder
→ Lean DTR AST
→ executable verified Lean translation
→ Lean LF AST
→ LF/C++ source printer
→ official lfc compiler
→ generated C++
→ native executable
```

The old Java Lingua Franca generator is not used in this path.

## Formal results

For the declared v0 fragment, the Lean development establishes:

1. source-model and generated-program well-formedness;
2. preservation of expression evaluation;
3. forward and backward statement correspondence;
4. occurrence-preserving message/action queue correspondence;
5. DTR minimum-logical-time scheduling;
6. LF lexicographic tag scheduling;
7. unconditional backward dispatch correspondence;
8. conditional forward dispatch correspondence;
9. combined statement-and-dispatch machine semantics;
10. runtime well-formedness preservation;
11. finite backward machine-trace correspondence;
12. conditional finite forward machine-trace correspondence;
13. constructor/startup state correspondence;
14. correctness connected to the executable `Translation.translate` function.

Forward dispatch correspondence is conditional because LF microsteps may refine equal-logical-time choices that remain unresolved in the DTR semantics. The development does not claim that all permitted equal-time source schedules are observationally equivalent.

## Main executable functions

- Verified AST translation: `Relico.Translation.translate`
- LF/C++ source backend: `Relico.Translation.translateToCppSource`
- Frontend JSON decoder: `Relico.Frontend.decodeModelText`

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
export RELICO_MAVEN="$(brew --prefix maven)/libexec/bin/mvn"
```

Parse a recurring source and compile the generated LF/C++:

```bash
frontend/java-bridge/check-v0.sh /path/to/ReLico-fmcad-2026-artifact-v1.zip
```

Compile and execute the finite fixture:

```bash
frontend/java-bridge/check-v0-runtime.sh /path/to/ReLico-fmcad-2026-artifact-v1.zip
```

## Verification boundary

The formal proof covers:

```text
well-formed supported Lean DTR AST
→ executable Lean translator
→ generated Lean LF AST
→ declared operational-semantics correspondence
```

The following remain trusted or outside the proof:

- textual Timed Rebeca parsing and the Java semantic checker;
- Java AST-to-JSON export;
- JSON parsing infrastructure;
- LF source printing;
- `lfc`, generated C++, the C++ compiler, and the LF C++ runtime;
- the operating system and hardware;
- unsupported source-language constructs.

The integration tests exercise these components but do not formally verify them.

## Repository structure

- `Relico/Common`: names, values, occurrences, logical time
- `Relico/DTR`: source syntax, state, semantics, and well-formedness
- `Relico/LF`: generated syntax, state, semantics, and LF/C++ printer
- `Relico/Translation`: executable translation and backend
- `Relico/Correctness`: structural and semantic proofs
- `Relico/Frontend`: bridge schema, decoder, and executable bridge check
- `Relico/Tests`: Lean tests
- `frontend/fixtures`: checked Timed Rebeca and JSON fixtures
- `frontend/java-bridge`: trusted adapter around the existing Java parser
- `docs`: decisions, scope, claims, and proof boundary

## Reproducible fixtures

- Recurring: `frontend/fixtures/v0-controller.rebeca`
- Finite: `frontend/fixtures/v0-once.rebeca`

## Milestone

The end-to-end v0 baseline is tagged:

```text
milestone-v0-end-to-end
```

## Next semantic milestone

Replace the single integer state value with a finite store supporting multiple declared state variables. This requires coordinated changes to syntax, well-formedness, runtime state, expression evaluation, assignment semantics, translation, correspondence, proofs, and the parser bridge.
