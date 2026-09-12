# `general--constructor-arguments--positive`

This positive benchmark belongs to the **general** family. It is a purpose-built capability
fixture for constructor argument positional binding, previously exercised only incidentally
through the actor-priority fixture's station identifiers: literal constructor arguments of both
admitted value types flowing positionally into reactor parameters and instance parameter values.

## Capability

The `Configured` class declares an integer and a boolean constructor formal, `bound` and
`active`, and its constructor assigns both to state variables. Two instances carry the literal
argument pairs `(7, true)` and `(0, false)`. The generated LF program carries both formals as
reactor parameters with their types' default values, `reactor Configured(bound: int = 0,
active: bool = false)`, and both instances as parameterized instantiations,
`configuredOn = new Configured(bound=7, active=true)` and
`configuredOff = new Configured(bound=0, active=false)`. Boolean reactor parameter flow through
`lfc 0.11.0` C++ generation is measured by this fixture for the first time; integer parameter
flow was already exercised by the actor-priority fixture.

## Source provenance

The source is the frontend fixture `frontend/fixtures/general/constructor-arguments.rebeca`
verbatim, with no benchmark header added, so the exporter's document is byte-identical to the
committed, hand-authored, exporter-confirmed anchor
`frontend/fixtures/general/constructor-arguments.parser.json`. That anchor is one of the four
documents the frontend gate trusts as an independent prediction, which is why this fixture keeps
the source untouched rather than adding the usual header comment.

## No runtime observation

The `reconfigure` message server is never sent and the fragment has no trace spelling, so no
observable runtime behavior depends on a parameter value. This fixture declares translation
correctness of parameter binding only, supported by the parser artifact, the decoded DTR AST,
the translated LF AST, the LF source, and `lfc` acceptance. No artificial runtime observation
is fabricated; the terminal stage is `lfc`, following the `general--local-declaration--positive`
precedent for models without runtime observables.

## Stages

8 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `formal-witness`,
`translated-lf-ast`, `lf-source`, `lfc`.

## Evidence

- source: the frontend fixture verbatim;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied; the model never sends a message,
  so its only reachable state is the initial one;
- parser JSON: byte-identical to the committed anchor document;
- decoded DTR AST, translated LF AST, LF source, and the formal witness over this benchmark's
  pin module `Relico/Tests/GeneralConstructorArguments.lean`, which pins the reactor parameters
  and the instance argument values in the assembled program;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

This model has no message traffic at all; no bounded-run policy is needed.
