# Verification and Trusted Boundary

## Verification Goal

ReLico implements the DTR-AST-to-LF-AST translation as executable Lean definitions. Correctness results refer to the same translation definitions used by the executable pipeline rather than to a separate handwritten translator.

The active General-family entry points are:

```lean
Relico.Frontend.decodeGeneralModelText
Relico.Translation.compileGeneralModel
```

Earlier singleton, finite-store, and multi-store entry points remain in the repository as compatibility and regression families. Their theorems have family-specific scopes and must not be treated as General-family results.

## Verified Boundary

```text
well-formed supported Lean DTR model
        -> executable Lean translator
        -> generated Lean LF model
        -> declared structural and operational-semantics results
```

Within this boundary, the project has executable DTR and LF representations, executable translations, source and target operational semantics, structural preservation results, and semantic correspondence results. The exact accepted General fragment is declared in [supported-fragment-general.md](supported-fragment-general.md).

For the General family, the formal development includes:

- successful translation and target well-formedness results for the declared accepted fragment;
- preservation results for supported state, expressions, statements, communication, logical time, and generated priority order;
- a source/target state correspondence;
- forward and backward weak transfer results;
- forward and backward observable-trace agreement derived from `GeneralLabelWeakBisimulation`.

These semantic results are qualified. They are stated over a partial within-tag quotient that permits reordering among distinct reactors at one tag while preserving order within each reactor. Three of the six fields of the General label-level weak-bisimulation interface retain explicit run-level premises: a forward consume representative package, backward per-step actor agreement, and a backward internal-step answer. The formal result is therefore not premise-free equivalence and is not the paper's source-level theorem verbatim.

See [general-family-correctness.md](claims/general-family-correctness.md) for the theorem-by-theorem claim map and all residual premises.

## Components Outside the Verified Boundary

The Lean proof does not cover:

- textual Timed Rebeca parsing and upstream type checking;
- conversion from the external parser AST to `general-v1` JSON;
- generic JSON parsing infrastructure;
- LF source serialization;
- `lfc` 0.11.0;
- generated C++ and its compiler;
- the LF C++ runtime;
- the operating system and hardware;
- source constructs outside the declared fragment.

The repository contains focused tests, integration fixtures, and application benchmarks that exercise some of these components. This is testing or experimental evidence, not formal verification of those components.

## Current Claim

> The executable DTR-AST-to-LF-AST translation core implemented in ReLico is formally verified in Lean for each family's declared fragment and theorem hypotheses. For the active General family, correspondence is conditional over the documented partial within-tag quotient.

This claim does not imply that the complete Timed Rebeca parser-to-native-runtime stack is formally verified, nor that all source programs or all LF programs are supported.
