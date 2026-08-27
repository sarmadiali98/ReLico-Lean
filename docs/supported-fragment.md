# Supported Fragment

This document defines the first vertical slice of ReLico-Lean.

The initial fragment is intentionally small. We will complete an executable translator and an end-to-end correctness theorem for this fragment before adding more language features.

> **SCOPE MARKER, added 2026-08-23. Read this before quoting anything below.**
>
> This document declares **vertical slice v0**, the project's first proof milestone. It is retained as
> the historical record of that declaration, **not** as a description of what the translator now
> accepts, and the two are far apart. On 2026-08-17 the project turned to generalizing the translator
> over the paper's DTR fragment, and stages A through F have since delivered **half of the *Initially
> excluded* list below**: multiple classes, multiple actor instances, known rebecs, external sends,
> ports and inter-reactor connections, message parameters and payloads, actor priorities, and
> message-server priorities. Every clause of v0 below is still true *of v0*; none of it bounds the
> general family.
>
> This matters because three sites quantify the project's claim over "the supported fragment" and this
> is the only document that declares one — `README.md:3`, and `docs/trusted-boundary.md` at `:28`
> ("For every well-formed source model in the supported fragment, the project aims to prove that:")
> and at `:62` ("formally verified for the declared supported fragment"). Resolving those pointers to
> v0 both understates what the tool accepts and misdescribes what is verified; in particular
> `trusted-boundary.md`'s aim 7, *"designer-specified priorities are preserved"*, is claimed for a
> fragment whose own exclusion list names actor priorities and message-server priorities. Recorded as
> **F63** in [`STAGE_G_FINDINGS.md`](STAGE_G_FINDINGS.md).
>
> The repair — a tracked declaration of the general family's accepted fragment, together with the
> theorem-eligibility boundary inside it — is specified in `docs/STAGE_G_DESIGN.md`. Its first half
> landed on 2026-08-27 as [`supported-fragment-general.md`](supported-fragment-general.md), which is
> now the declaration the sites above resolve to; its second half, the theorem-eligibility table
> naming the tie fixtures and the hypotheses each theorem family carries, landed 2026-08-28 as that
> document's final section. F63 is discharged in full.

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

The following are not included in vertical slice v0. **Delivery status appended 2026-08-23** — the item
text is unchanged, and "delivered" always means delivered for the **general** family, never for v0,
which is closed as declared. Stage attributions are given only where a single stage owns the item:

- multiple classes — **delivered**, stage B;
- multiple actor instances — **delivered**, stage B;
- known rebecs — **delivered**, stages C–E;
- external sends — **delivered**, stages C–E;
- ports and inter-reactor connections — **delivered**, stages C–E;
- message parameters and payloads — **delivered**, stages D and E;
- conditionals — still excluded; stage H;
- loops — still excluded; stage H;
- arrays — still excluded;
- inheritance — still excluded;
- physical actions — still excluded;
- environmental inputs — still excluded;
- actor priorities — **delivered**, stage F level 1;
- message-server priorities — **delivered**, stage F level 2;
- broadcast — still excluded;
- arbitrary LF programs — still excluded, and by design rather than by schedule: the LF subset is
  generated and never parsed, so this one is not a milestone exclusion at all.

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
