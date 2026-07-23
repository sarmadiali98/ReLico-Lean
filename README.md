# ReLico-Lean

ReLico-Lean is an executable Lean 4 translation from a supported
fragment of Deterministic Timed Rebeca to a generated subset of
Lingua Franca with the C++ target.

The translation function is implemented in Lean and is connected
directly to the structural and semantic correctness theorems.

## Current result

Vertical slice v0 supports:

- one reactive class;
- one actor instance;
- one integer state variable;
- one constructor;
- one message server;
- integer literals;
- references to the state variable;
- assignments;
- delayed self-sends with nonnegative constant delays.

The generated LF subset contains:

- one reactor;
- one reactor instance;
- one integer state variable;
- one logical action;
- one startup reaction;
- one message reaction;
- assignment and logical-action scheduling statements.

## Executable pipeline

The current integration path is:

```text
Timed Rebeca source
→ existing Java Timed Rebeca parser and semantic checker
→ stable versioned JSON bridge
→ Lean JSON decoder
→ Lean DTR AST
→ executable verified Lean translation
→ Lean LF AST
→ LF/C++ source printer
→ official lfc compiler
→ generated C++
→ native executable

The old Java Lingua Franca generator is not used in this translation
path.

Formal results

For the declared v0 fragment, the Lean development establishes:

source-model well-formedness;
structural well-formedness of generated LF programs;
preservation of expression evaluation;
forward and backward statement correspondence;
occurrence-preserving message/action queue correspondence;
DTR minimum-logical-time scheduling;
LF lexicographic tag scheduling;
unconditional backward dispatch correspondence;
conditional forward dispatch correspondence;
combined statement-and-dispatch machine semantics;
runtime well-formedness preservation;
finite backward machine-trace correspondence;
conditional finite forward machine-trace correspondence;
constructor/startup state correspondence;
correctness results connected to the executable
Translation.translate function.

Forward dispatch correspondence is conditional because LF microsteps
may refine equal-logical-time choices that remain unresolved in the DTR
semantics.

The development does not claim that all permitted equal-time source
schedules are observationally equivalent.

Main executable functions

The verified AST translation entry point is:

Relico.Translation.translate

The LF/C++ source backend entry point is:

Relico.Translation.translateToCppSource

The frontend JSON decoder entry point is:

Relico.Frontend.decodeModelText
Build

Install Lean through elan, then run:

lake build

The Lean version is pinned in lean-toolchain.

End-to-end integration checks

The integration checks require:

Java;
Apache Maven;
Lingua Franca lfc;
CMake;
a C++ compiler;
the ReLico artifact ZIP containing the existing Timed Rebeca parser.

On systems where another command shadows Apache Maven, set
RELICO_MAVEN explicitly.

For example:

export RELICO_MAVEN="$(brew --prefix maven)/libexec/bin/mvn"
Recurring source: parse and compile
frontend/java-bridge/check-v0.sh \
  /path/to/ReLico-fmcad-2026-artifact-v1.zip

This checks:

real Timed Rebeca source
→ parser AST
→ bridge JSON
→ Lean DTR AST
→ LF/C++ source
→ lfc
→ native C++ executable
Finite source: compile and execute
frontend/java-bridge/check-v0-runtime.sh \
  /path/to/ReLico-fmcad-2026-artifact-v1.zip

This also executes the generated native program and requires successful
termination with exit code zero.

Verified boundary

The formal proof covers:

well-formed supported Lean DTR AST
→ executable Lean translator
→ generated Lean LF AST
→ declared operational-semantics correspondence

The following remain trusted or outside the proof:

textual Timed Rebeca parsing;
the Java parser semantic checker;
Java AST-to-JSON export;
JSON parsing infrastructure;
LF source-code printing;
the LF compiler and C++ runtime;
generated C++;
the C++ compiler;
the operating system and hardware;
unsupported source-language constructs.

The integration tests exercise these components but do not formally
verify them.

Repository structure
Relico/Common
    Shared names, values, occurrences, and logical time

Relico/DTR
    DTR syntax, well-formedness, runtime state, and semantics

Relico/LF
    Generated LF syntax, well-formedness, runtime state, semantics,
    and LF/C++ printer

Relico/Translation
    Executable DTR-to-LF translation and concrete backend

Relico/Correctness
    Structural and semantic correctness proofs

Relico/Frontend
    Stable JSON schema, decoder, and executable bridge check

Relico/Tests
    Lean unit and regression tests

frontend/fixtures
    Checked Timed Rebeca and JSON fixtures

frontend/java-bridge
    Trusted adapter around the existing Java parser

docs
    Decisions, supported scope, claims, and proof boundary
Reproducible v0 fixtures

The recurring fixture is:

frontend/fixtures/v0-controller.rebeca

The finite executable fixture is:

frontend/fixtures/v0-once.rebeca
Next semantic milestone

The next major extension is to replace the single integer state value
with a finite store supporting multiple declared state variables.

That extension will require coordinated changes to:

source and target syntax
→ model well-formedness
→ runtime states
→ expression evaluation
→ assignment semantics
→ translation
→ state correspondence
→ preservation and simulation proofs
→ parser bridge schema and exporter
