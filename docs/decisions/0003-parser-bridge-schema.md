# Decision 0003: Stable parser bridge schema

## Status

Accepted for vertical slice v0.

## Context

The existing Timed Rebeca parser is implemented in Java and produces a
large parser-specific object model.

The verified translator consumes the independent Lean `DTR.Model`
representation. Directly exposing Java parser classes to the Lean
translation would make the verified core depend on unstable frontend
implementation details.

## Decision

The trusted frontend exports a small, versioned JSON representation.

The path is:

```text
.rebeca source
→ existing Timed Rebeca parser
→ stable bridge JSON
→ Lean Frontend.decodeModelText
→ Lean DTR.Model

Schema version 1 contains:

one reactive class;
one actor instance;
one integer state variable;
one constructor body;
one message server and its body;
integer-literal expressions;
state-variable-reference expressions;
assignments;
delayed self-sends.
Validation

The Lean decoder rejects:

unknown schema versions;
malformed JSON;
missing required fields;
empty names;
actor/class mismatches;
references to undeclared state variables;
assignments to undeclared variables;
self-sends to undeclared message servers;
unsupported expression and statement kinds.
Trust boundary

The existing Java parser and the Java-to-JSON exporter remain trusted
frontend components.

The JSON parser and decoder are executable Lean code. The parser bridge
does not call the previous Java Lingua Franca generator.

The DTR-to-LF translation continues to be performed only by the
executable Lean translator.
