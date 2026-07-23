# Decision 0002: LF/C++ concrete backend

## Status

Accepted for vertical slice v0.

## Target

The concrete Lingua Franca execution target is C++.

Generated LF source begins with:

```lf
target Cpp

The C target is not the deployment target of the ReLico translator.

Executable path

The executable backend entry point is:

Relico.Translation.translateToCppSource

It performs:

DTR AST
→ verified Translation.translate
→ generated LF AST
→ LF.CppPrinter.renderProgram
→ LF/C++ source text
Delay convention

The abstract v0 Delay.value is rendered as milliseconds:

1 → 1ms

This convention must later be checked against the concrete Timed Rebeca
parser and source-language timing representation.

Trust boundary

The DTR-to-LF AST translation is covered by the current Lean
correctness results.

The LF/C++ text printer is executable but is not yet proved to produce
text accepted by the official LF parser. It remains part of the trusted
backend boundary until parser or compiler validation is integrated.

The LF compiler, generated C++ code, C++ compiler, LF C++ runtime,
operating system, and hardware remain outside the current proof.

## Main reactor naming

The generated main reactor is unnamed:

```lf
main reactor {

Lingua Franca otherwise requires a named main reactor to match the LF
source filename. Omitting the name makes generated source independent
of the output filename.

## Reaction action effects

A logical action scheduled by reaction target code is included in that
reaction's LF effect list.

For example:

```lf
reaction(startup) -> tick_action {=
  tick_action.schedule(1ms);
=}

This gives the LF C++ reaction a schedulable action handle.

Generated filename

Toolchain checks store the generated source as:

V0Controller.lf

The filename avoids characters such as hyphens that would produce an
invalid generated C++ class identifier.
