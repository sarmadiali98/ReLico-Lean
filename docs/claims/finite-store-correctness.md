# Finite-store correctness claim

## Supported source fragment

The generalized executable fragment contains:

- one reactive class;
- one actor instance of that class;
- a finite nonempty list of integer state-variable declarations;
- one constructor;
- one message server;
- integer literals;
- references to any declared state variable;
- assignments to any declared state variable;
- cross-variable assignments;
- delayed self-sends with nonnegative constant delays.

The generated LF subset contains one reactor, one reactor instance, one
state declaration for every source state variable, one logical action,
one startup reaction, and one message reaction.

## Executable translation path

The generalized verified translation entry point is:

```lean
Relico.Translation.translateStore
```

A successful result has the form:

```lean
Translation.translateStore model = Except.ok program
```

The concrete LF/C++ backend entry point is:

```lean
Relico.Translation.translateStoreToCppSource
```

It invokes `Translation.translateStore` and then applies the trusted
finite-store LF/C++ printer.

The parser-to-native path is:

```text
Timed Rebeca source
→ existing Java Timed Rebeca parser and semantic checker
→ schema-version-2 JSON
→ Lean finite-store decoder
→ Lean DTR store model
→ executable verified Lean store translation
→ Lean LF store program
→ trusted LF/C++ source printer
→ official lfc compiler
→ generated C++
→ native executable
```

The previous Java Lingua Franca generator is not part of this path.

## Established finite-store results

The Lean development establishes:

- finite-store lookup and update laws;
- declared-variable store coverage and preservation;
- expression evaluation over finite stores;
- expression-evaluation preservation under translation;
- finite-store statement semantics;
- forward and backward statement correspondence;
- finite statement-trace correspondence;
- finite-store dispatch semantics;
- conditional forward dispatch correspondence;
- unconditional backward dispatch correspondence under the declared pending-target invariant;
- combined statement-and-dispatch machine semantics;
- runtime well-formedness preservation;
- conditional finite forward machine-trace correspondence;
- unconditional finite backward machine-trace correspondence;
- generalized DTR and LF model well-formedness;
- preservation of declaration order, names, and initial values;
- structural well-formedness of programs returned by `Translation.translateStore`;
- exact singleton compatibility with the original executable `Translation.translate` function.

## Scheduling and nondeterminism boundary

DTR scheduling selects a minimum-logical-time pending occurrence. LF
scheduling additionally uses microsteps.

Backward correspondence is unconditional for the supported generated
LF subset once the source runtime invariants are supplied: a permitted
generated execution maps to a permitted source execution.

Forward dispatch and machine correspondence are conditional. The source
occurrence selected by a DTR execution must be compatible with the
target's lexicographic tag ordering.

The formalization does not claim that all equal-time source schedules
are observationally equivalent.

## Trusted and excluded components

The formal proof covers the Lean ASTs, the executable Lean translation,
the declared finite-store operational semantics, and their
correspondence theorems.

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

The real integration check exercises these components but does not
formally verify them.

## Current integration evidence

The reusable command is:

```text
frontend/java-bridge/check-store.sh <artifact.zip>
```

The committed fixture declares `x` and `y`, initializes both in the
constructor, schedules one delayed self-message, and executes the
cross-variable assignment `y = x`.

The check succeeds only when:

- the existing Timed Rebeca parser and semantic checker accept the source;
- parser-generated schema-version-2 JSON matches the committed fixture;
- the Lean decoder accepts the generated JSON;
- the executable generalized Lean translator produces the LF store program;
- the LF source contains both state declarations and the cross-variable assignment;
- `lfc` generates and compiles C++;
- the native executable terminates with exit code zero.

## Remaining language exclusions

The current claim does not include:

- multiple actors;
- multiple reactive classes;
- multiple message servers;
- actor-to-actor communication;
- message parameters;
- constructor parameters;
- deadlines;
- environmental inputs;
- non-integer state variables;
- declaration initializers in the Java parser bridge;
- unsupported statements and expressions.
