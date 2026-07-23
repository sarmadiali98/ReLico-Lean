# Contributing

## Build requirement

Every committed change must preserve:

~~~bash
lake build
~~~

## Formal integrity

Do not commit final proof code containing:

- `sorry`;
- `admit`;
- project-specific axioms used to bypass proof obligations.

Temporary experimental files must be clearly separated from the verified development.

## Development workflow

The project currently develops on `main`.

Create a separate branch when:

- two contributors are working on overlapping files;
- a change is risky or experimental;
- two alternative definitions need to be compared;
- a large change requires review before integration.

Before editing shared syntax or semantics, coordinate with the other contributor.

## Feature completion

A language feature is not complete merely because its translator code runs.

A complete feature should eventually include:

1. source syntax;
2. source well-formedness;
3. source semantics;
4. target syntax;
5. executable translation;
6. target semantics;
7. structural correctness;
8. semantic correctness;
9. a minimal regression model;
10. corresponding documentation.

## Commit messages

Use focused commit subjects such as:

~~~text
syntax: add DTR conditional statements
translation: compile internal sends
semantics: define DTR message-take step
proof: preserve assignment evaluation
docs: clarify zero-delay assumptions
~~~
