# Vertical-slice v0 correctness claim

This document records the original singleton milestone. The current
generalized claim is documented in
`docs/claims/finite-store-correctness.md`.

## Executable translation path

The verified translation entry point is:

```lean
Relico.Translation.translate
```

A successful result has the form:

Translation.translate model = Except.ok program

The correctness theorems apply to that returned program. The Java
translator is not part of the verified semantic path.

Supported source fragment

Vertical slice v0 contains:

one reactive class;
one actor instance;
one integer state variable;
one message server;
constructor and message-server bodies;
integer literals and references to the single state variable;
assignments;
delayed self-sends.

The generated LF subset contains one reactor, one instance, one logical
action, one startup reaction, and one message reaction.

Established results

The Lean development currently establishes:

Source-model well-formedness.
Structural well-formedness of generated LF programs.
Preservation of expression evaluation.
Forward and backward correspondence for assignment and scheduling
statements.
Occurrence-preserving pending-message and pending-action relations.
DTR minimum-logical-time scheduling.
LF lexicographic tag scheduling using logical time and microstep.
Unconditional backward correspondence for dispatch.
Conditional forward correspondence for dispatch.
Combined statement-and-dispatch machine semantics.
Runtime well-formedness preservation.
Finite backward machine-trace correspondence.
Conditional finite forward machine-trace correspondence.
Constructor/startup initial-state correspondence.
The same initial machine results for programs returned by the
executable Translation.translate function.
Direction of the execution results

Backward correspondence is unconditional for the supported generated LF
subset: every permitted generated-LF execution maps to a permitted DTR
execution.

Forward dispatch correspondence is conditional. The target occurrence
corresponding to a selected DTR message must be eligible under LF
lexicographic tag ordering.

This condition is necessary because DTR exposes logical arrival time,
while LF additionally orders same-time actions using microsteps.

Nondeterminism boundary

The formalization does not claim that all same-time DTR schedules are
observationally equivalent.

DTR may permit multiple minimum-time message occurrences. LF may refine
their order through microsteps. The forward theorem therefore preserves
only source executions compatible with that target ordering.

The backward theorem prevents the generated LF semantics from
introducing executions outside the permitted DTR execution space.

Trusted and excluded components

The current proof covers the Lean DTR AST, Lean LF AST, executable
translation function, and the declared operational semantics.

The following remain outside the proof:

text parsing and AST import;
LF source-code printing;
the LF compiler and runtime implementation;
generated C++ compilation;
operating systems and hardware;
the previous Java translator;
unsupported source-language constructs;
multiple actors, multiple message servers, communication, and
environmental inputs.


## Concrete LF/C++ source backend

The executable concrete backend entry point is:

```lean
Relico.Translation.translateToCppSource
```

It invokes the verified AST translator and renders the resulting LF AST
as source for the Lingua Franca C++ target.

Generated source begins with:

target Cpp

The concrete printer and LF/C++ toolchain remain trusted components.
The verified semantic result continues to apply to the generated LF AST.

Toolchain integration tests

The artifact includes executable integration checks using the official
LF C++ toolchain.

One recurring fixture confirms source acceptance and native C++
compilation. A second finite fixture confirms that the generated native
executable starts, processes its scheduled action, and terminates
successfully.

These checks validate integration but do not extend the formal proof
through lfc, generated C++, the C++ compiler, or the LF runtime.
