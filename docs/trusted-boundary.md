# Trusted Boundary

## Verification goal

ReLico-Lean will implement the actual DTR-to-LF translation as an executable Lean function.

The correctness theorem will refer directly to that same executable function. The project will not use a separate handwritten translator whose connection to the Lean proof is assumed.

The intended compiler interface is:

```lean
def translate :
    DTR.Model → Except TranslationError LF.Program
Verified boundary

The initial verified boundary is:

well-formed supported DTR AST
        ↓
executable Lean translator
        ↓
well-formed generated LF AST

For every well-formed source model in the supported fragment, the project aims to prove that:

translation succeeds;
the generated LF model is well formed;
source state variables are preserved;
message occurrences and payloads are preserved;
logical time and delays are preserved;
source causality is preserved;
designer-specified priorities are preserved;
every permitted source execution has a corresponding target execution;
every target execution corresponds to a permitted source execution.

The correctness theorem must preserve the permitted source execution structure. It must not assume that every permitted schedule is observationally equivalent.

Initially trusted components

The initial proof does not cover:

parsing textual Timed Rebeca;
conversion from an external parser AST into the Lean DTR AST;
serialization of the LF AST into textual LF;
the LF compiler;
generated C or C++ code;
the C or C++ compiler;
the LF runtime;
the operating system;
hardware.

These components must be stated explicitly as being outside the verified boundary.

Intended claim

After the executable translator, correctness theorem and tool integration are complete, the intended claim is:

The executable DTR-AST-to-LF-AST translation core implemented in ReLico-Lean is formally verified for the declared supported fragment.

This does not mean that the complete Rebeca parser, LF toolchain, runtime or deployed system is formally verified.
