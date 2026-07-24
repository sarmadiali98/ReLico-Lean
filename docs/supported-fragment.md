# Supported Fragment

This document defines the first vertical slice of ReLico-Lean.

The initial fragment is intentionally small. We will complete an executable translator and an end-to-end correctness theorem for this fragment before adding more language features.

## Vertical slice v0

A source model contains:

- one reactive class;
- one actor instance of that class;
- one integer state variable;
- one constructor;
- one message server;
- finite constructor and message-server bodies;
- assignment statements;
- internal self-send statements;
- nonnegative constant delays.

## Expressions

The initial expression language contains:

- integer literals;
- references to the declared state variable.

Arithmetic operators will be added after the initial end-to-end result unless they are required by the first example.

## Statements

The initial statement language contains:

~~~text
assign variable expression
selfSend messageServer delay
~~~

A constructor or message-server body is a finite list of statements.

## Messages

The initial fragment has:

- one message-server name;
- no parameters;
- no payload values;
- occurrence-preserving pending messages;
- nonnegative constant arrival delays.

Message multiplicity must be preserved. Two identical pending messages represent two distinct message occurrences.

## Time

The initial source time domain is the natural numbers.

A delayed self-send with delay `d` schedules a message occurrence at:

~~~text
current logical time + d
~~~

Zero-delay behavior and its relation to LF microsteps must be defined explicitly.

## Well-formedness

A source model in vertical slice v0 is well formed when:

- the class name is valid;
- the actor instance refers to the declared class;
- the state-variable name is unique;
- the message-server name is unique;
- every variable reference refers to the declared state variable;
- every self-send refers to the declared message server;
- every delay belongs to the supported time domain;
- every statement belongs to the supported grammar.

## Initially excluded

The following are not included in vertical slice v0:

- multiple classes;
- multiple actor instances;
- known rebecs;
- external sends;
- ports and inter-reactor connections;
- message parameters and payloads;
- conditionals;
- loops;
- arrays;
- inheritance;
- physical actions;
- environmental inputs;
- actor priorities;
- message-server priorities;
- broadcast;
- arbitrary LF programs.

These are temporary exclusions for the first proof milestone, not necessarily exclusions from the final translator.

## Completion criterion

Vertical slice v0 is complete only when the repository contains:

1. a typed DTR AST;
2. a typed generated-LF AST;
3. a source well-formedness definition or checker;
4. an executable Lean translation function;
5. DTR operational semantics;
6. generated-LF operational semantics;
7. a source-target state correspondence relation;
8. a forward simulation theorem;
9. a backward simulation theorem;
10. an end-to-end compiler correctness theorem about the executable translation function;
11. no `sorry`, `admit`, or project-specific axioms in the final theorem dependency.


## Finite-store executable extension

The current generalized path extends the v0 fragment with a finite
nonempty list of integer state variables.

Expressions may reference any declared state variable. Assignments may
target any declared state variable, including cross-variable
assignments.

The remaining model restrictions are unchanged:

- one reactive class;
- one actor instance;
- one constructor;
- one message server;
- delayed self-sends with nonnegative constant delays;
- the explicitly supported expression and statement forms.

The generalized bridge uses schema version 2 and decodes to
`DTR.StoreModel`.

The singleton schema-version-1 path remains available for regression
and compatibility checks.
