# ReLico-Lean

ReLico-Lean is an early-stage formalization and executable verified translator from a supported fragment of Deterministic Timed Rebeca to a generated subset of Lingua Franca.

The project is being developed in Lean 4.

## Objective

The final translator will be an executable Lean function of the form:

~~~lean
def translate :
    DTR.Model → Except TranslationError LF.Program
~~~

The main correctness theorem will refer directly to this executable function. The project will not use an abstract proof that is disconnected from a separately handwritten production translator.

For every well-formed model in the declared supported fragment, the intended proof covers:

- successful translation;
- well-formed generated LF;
- state preservation;
- message and payload preservation;
- logical-time and delay preservation;
- causality preservation;
- priority preservation;
- source-to-target execution correspondence;
- target-to-source execution correspondence.

The purpose is to preserve the permitted source execution structure. The formalization does not assume that every permitted concurrent schedule is observationally equivalent.

## Current status

The repository currently contains:

- strongly typed source and target identifiers;
- logical-time and delay definitions;
- runtime values for the first fragment;
- the typed DTR abstract syntax for vertical slice v0;
- the typed generated-LF abstract syntax for vertical slice v0;
- documentation of the intended verification boundary;
- documentation of the initial supported fragment.

The executable translator, operational semantics, and correctness proofs are not implemented yet.

## Vertical slice v0

The first proof milestone intentionally supports a small fragment:

- one reactive class;
- one actor instance;
- one integer state variable;
- one constructor;
- one message server;
- assignments;
- internal self-sends;
- nonnegative constant delays.

The complete scope is documented in:

~~~text
docs/supported-fragment.md
~~~

## Verified boundary

The initial verified boundary is:

~~~text
well-formed supported DTR AST
        ↓
executable Lean translator
        ↓
well-formed generated LF AST
~~~

Parsing textual Timed Rebeca, serialization to textual LF, the LF compiler, runtime, downstream C or C++ compiler, operating system, and hardware are initially outside the verified boundary.

See:

~~~text
docs/trusted-boundary.md
~~~

## Repository structure

~~~text
Relico/Common
    Shared names, values, and logical time

Relico/DTR
    DTR syntax, well-formedness, states, and semantics

Relico/LF
    Generated LF syntax, well-formedness, states, and semantics

Relico/Translation
    Executable DTR-to-LF translator

Relico/Correctness
    Structural and semantic correctness proofs

Relico/Frontend
    Future external AST decoding and validation

Relico/Tests
    Unit, regression, and translation tests

docs
    Scope, architecture, theorem tracking, and proof decisions
~~~

## Build

Install Lean through `elan`, then run:

~~~bash
lake build
~~~

The Lean version is pinned by `lean-toolchain`.

## Development principle

The compiler and its proof are developed together, one language feature at a time:

~~~text
source syntax
→ target syntax
→ executable translation
→ source semantics
→ target semantics
→ local correctness lemmas
→ end-to-end theorem
~~~

The existing Java implementation and previous artifact remain outside this repository and may only be consulted as external reference material.
