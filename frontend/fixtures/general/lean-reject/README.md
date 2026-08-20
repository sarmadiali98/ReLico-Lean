# `lean-reject` — documents no producer emits

Twelve malformed `general-v1` documents, each of which the Lean decoder must
refuse, and each paired in
`frontend/lean-bridge/GeneralFrontendTestMain.lean` with the exact
`GeneralDiagnosticReason` it must be refused for.

## Why this directory exists

`frontend/fixtures/general/` now records three layers of rejection, one per
directory, and this is the third:

| directory | who rejects | what a fixture there is |
| --- | --- | --- |
| `upstream-reject/` | the Rebeca parser and typechecker | a source model that never reaches the exporter |
| `reject/` | `RebecaGeneralJsonExporter` | a source model the exporter refuses to translate |
| `lean-reject/` | `Relico.Frontend.decodeGeneralModelText` | a *document* the exporter would never produce |

The first two hold `.rebeca` sources, because there is a compiler upstream to
run them through. This one holds `.json`, because there is not: a document that
the exporter would refuse to emit is a document it never hands to Lean, so no
source model can carry these cases across the boundary. The only way to hand the
decoder a document with a missing field, a duplicated class name or a broken
envelope is to write one.

That is also why these cannot be `#guard` tests. The decoder reads a file, so
exercising it needs `IO`, and a `#guard` is pure. Between the Java gate, which
cannot reach these paths, and `#guard`, which cannot perform them, the frontend
test runner is the only place in the project where the decoder's rejection
behaviour can be executed at all. Before this directory existed, all four decode
steps and all five well-formedness clauses were code that elaborated and never
ran.

## Every fixture is one mutation of an accepted document

Each file is an accepted document with a single change. Eleven of the twelve
mutate `minimal-class.parser.json`; that document is
accepted by the same test run that rejects these, so the pair is a controlled
experiment: the mutation is the claim being tested, and

```
diff frontend/fixtures/general/minimal-class.parser.json \
     frontend/fixtures/general/lean-reject/<fixture>
```

shows exactly what that claim is. A fixture that later starts failing for a
second, unrelated reason cannot do so quietly, because the diff would have to
grow first.

`invalid-parameter-shadows-state.json` is the exception, and the exception is
about the base rather than the rule. Its claim is that a constructor formal may
not be named after a state variable, which needs a class that has one of each;
`minimal-class` has an empty `stateVariables` and an empty parameter list, so
expressing the collision there would mean adding two declarations *and* colliding
them — three changes, of which only the third is the claim. Mutating
`constructor-arguments.parser.json` instead keeps the mutation at one thing, so
the controlled-experiment property is preserved by changing the base:

```
diff frontend/fixtures/general/constructor-arguments.parser.json \
     frontend/fixtures/general/lean-reject/invalid-parameter-shadows-state.json
```

is two lines, both the same rename. Prefer this move to a growing mutation if a
future fixture needs a richer base than `minimal-class` provides.

The documents are formatted the way the exporter formats its own output — two
space indentation, keys sorted, one trailing newline — so a diff shows the
mutation and nothing else.

## The twelve, by the decode step each one reaches

`decodeGeneralModelText` runs four steps in order, and a fixture can only test a
step the previous three let it reach. That ordering is why, for instance, the
`schemaVersion` fixture carries the correct `family`: `family` is checked first,
so a fixture wrong in both respects would silently test the wrong one.

### Step 1, the parse

| fixture | mutation | reason |
| --- | --- | --- |
| `invalid-json.json` | the final `}` deleted | `invalidJson` |

An unterminated object rather than a trailing comma or a stray token, because it
is invalid under every JSON parser rather than under a strict reading of one.

### Step 2, the schema

| fixture | mutation | reason |
| --- | --- | --- |
| `invalid-missing-classes.json` | top-level `classes` removed | `schemaDecodeFailed` |
| `invalid-missing-queue-bound.json` | the class's `queueBound` removed | `schemaDecodeFailed` |

Two fixtures rather than one because `FromJson` is derived independently at each
level of the schema, so a required field is only required where it is declared.
The nested one also pins `queueBound` as genuinely required: it is decoded and
then dropped, and a field that is read but unused is exactly the kind of field
someone later makes optional without noticing anything depends on it.

### Step 3, the envelope

| fixture | mutation | reason |
| --- | --- | --- |
| `invalid-family.json` | `family` set to `multi-store` | `unexpectedFamily` |
| `invalid-schema-version.json` | `schemaVersion` set to `2` | `unsupportedSchemaVersion` |

`multi-store` rather than a nonsense string, because the failure being guarded
against is a real one: four sibling families emit documents of their own, and
handing one of theirs to this decoder must fail on the envelope rather than
half-decode.

### Elaboration, which runs before any clause

`decodeRawGeneralModel` calls `elaborateGeneralModel` and only then
`requireGeneralWellFormed` (`Relico/Frontend/GeneralDecoder.lean:236–239`), so an
elaborator reason pre-empts all five clause reasons. This is the only fixture here
that reaches that layer.

| fixture | mutation | reason |
| --- | --- | --- |
| `invalid-parameter-shadows-state.json` | the constructor's first formal renamed `bound` → `limit`, the name of an existing state variable, at its declaration and its one use | `parameterShadowsStateVariable` |

Both sites are renamed rather than only the declaration. Renaming just the
declaration would leave the body reading a `bound` that no longer exists, giving
the document a second defect and making the test depend on the elaborator checking
shadowing before it elaborates bodies. It does — `elaborateConstructor` returns at
`GeneralElaborator.lean:793–796`, before any statement is looked at — but a
fixture that passes *because* of a check order it does not assert is a fixture that
starts lying the moment that order changes. The same reasoning is why
`invalid-empty-class-name.json` blanks the instance's `className` too.

The message server `reconfigure` keeps its own formal named `bound`, untouched.
That is not an oversight: `elaborateMessageServer` runs the identical
`firstShadowedName?` check at `GeneralElaborator.lean:746`, so renaming it as well
would have produced a document with two independent collisions, of which the
constructor's is raised first because `elaborateClass` reaches it first
(`:849` before `:854`). One collision, one reason.

Why this document belongs here rather than as a `.rebeca` source, measured in the
artifact's own compiler rather than assumed, because the obvious guess is wrong:

- **Timed Rebeca permits the collision.** `semanticCheckOfMethod` pushes a fresh
  scope *before* declaring the formals (`CoreRebecaCompleteCompilerFacade.java:391`,
  reached for constructors at `:344`), state variables having been added to the
  enclosing `REACTIVE_CLASS` scope at `:278`; and `addVariableToCurrentScope`
  rejects a redeclaration only within `scopeStack.peek()`
  (`ScopeHandler.java:54–75`). The compiler contains no hiding check of any kind.
  So the typechecker accepts `Configured(int limit)` alongside `statevars { int
  limit; }`, and inside the body `limit` resolves to the formal.
- **`RebecaGeneralJsonExporter` refuses it.** `declareParameters` runs
  `Scope.declare` over every constructor and message-server formal
  (`:1124`, `:1158`), and `declare` throws `unsupported("a local name shadowing
  state variable …")` when the name is a state variable (`:417–421`).

The second is what licenses this directory: the exporter never emits a document
carrying the collision, so no source fixture can deliver one to the decoder. The
first is why the fixture is interesting at all — the pipeline narrows a construct
the source language allows, and the narrowing is the exporter's and this layer's,
not Rebeca's.

Note that the exporter's own parameter-shadowing branch is, as of this fixture,
**unexercised**: `reject/` holds eleven sources and none of them shadows a state
variable with a formal. `local-declaration.rebeca` reaches `Scope.declare` by the
`declare`-statement path only. A `reject/` source for the formal path would close
that on the Java side, and it is the natural companion to this file.

Note that `PASS_REJECT_PARAMETER_SHADOWS_STATE_VARIABLE` here and stage D's
`PASS_REJECT_PARAMETER_STATE_COLLISION` in the printer runner are different
claims about the same shape of mistake, and both are wanted. This one says a
*document* carrying the collision never becomes a model. That one says a
hand-built model carrying it is refused by `LF.GeneralProgram.wellFormed` after
translation — which is finding F32, and is only interesting because
`DTR.GeneralModel.wellFormed` accepts what this fixture proves the elaborator
rejects.

### Step 4, the assembled model

The five well-formedness clauses are tried in a fixed order and the first false
one names the reason, so which reason a document receives is decided by clause
order and not by which clause is the most specific description of the mistake.
Both fixtures here depend on that, and say so.

| fixture | mutation | reason |
| --- | --- | --- |
| `invalid-unknown-class.json` | the instance's `className` set to `Missing` | `bindingsMatchDeclarationsFailed` |
| `invalid-argument-arity.json` | one `intLiteral` argument added to an instance whose class takes none | `argumentsMatchConstructorFailed` |

A dangling `className` fails four of the five clauses, since each looks the class
up; `bindingsMatchDeclarations` is simply the one tried first. The arity fixture
reaches the model at all only because `intLiteral` is a shape the elaborator
accepts — arity is not an elaborator question, so a well-shaped argument list of
the wrong length must survive elaboration to be caught here.

### Step 4, the fifth clause

`namesUniqueAndValid` was not in the approved stage-B design; it was added
because every lookup in `GeneralSyntax` returns the first match, so a repeated
name makes a model mean something the frontend did not say.

| fixture | mutation | reason |
| --- | --- | --- |
| `invalid-empty-class-name.json` | class `name` and the instance's `className` both set to `""` | `namesUniqueAndValidFailed` |
| `invalid-empty-instance-name.json` | the instance's `name` set to `""` | `namesUniqueAndValidFailed` |
| `invalid-duplicate-class-name.json` | the class duplicated, second copy at a different line | `namesUniqueAndValidFailed` |
| `invalid-duplicate-instance-name.json` | the instance duplicated, second copy at a different line | `namesUniqueAndValidFailed` |

All four share one reason, because the reason is per clause and the clause is a
conjunction of four requirements: unique topology keys, distinct class names,
non-empty instance names, non-empty class names. A test that asserts the reason
therefore cannot tell which of the four sub-requirements did the rejecting, and
these four fixtures do not claim to. What they establish is that each mistake is
refused at all — which is the requirement, and which is not something any other
check in the project would notice.

Two details worth keeping in mind when editing these. The empty-class-name
fixture sets `className` too, so that the instance still resolves and the
document reaches the fifth clause instead of failing the first; blanking only the
class name would test `bindingsMatchDeclarations` again. And the two duplicate
fixtures change `line` in the second copy, so that the mutation cannot be
mistaken for a document with one declaration written twice by accident — the
duplication is of a name, not of a whole record.

## What this corpus does not cover

Twelve fixtures is not coverage of the decoder, and it would be easy to read a
directory of negatives as if it were. Measured: `GeneralDiagnosticReason` declares
**32** reasons, and the runner asserts **9** of them — the six reached from here
plus `iterationNotSupported`, which `control-flow` reaches, and the two
model-level clauses above. **Twenty-three are asserted nowhere.**

One of the twenty-three, `modelNotWellFormed`, is unreachable by construction and
documented as such: `wellFormed` is exactly the conjunction of the five clauses,
so nothing is left over. It exists so that classification is total without the
classifier being trusted to agree with the gate.

The other twenty-two are reachable and untested. They fall into three groups,
which matters because the groups need different work:

Reachable from a document, so a fixture here would test them:
`unknownDeclaredType`, `emptyName`, `duplicateStateVariable`,
`duplicateParameter`,
`unsupportedExpressionKind`, `missingField`, `expectedIntegerLiteral`,
`expectedBooleanLiteral`, `unknownBinaryOperator`, `unknownUnaryOperator`,
`undeclaredVariable`, `unsupportedStatementKind`, `expectedAssignTargetName`,
`assignmentTargetNotStateVariable`, `unsupportedSendTargetKind`,
`nonConstantDelay`, `negativeDelay`, `nonLiteralInstanceArgument`,
`sendTargetsDeclaredFailed`, `sendsResolveToMessageServersFailed`.

`parameterShadowsStateVariable` was in this group until
`invalid-parameter-shadows-state.json` landed. It was taken first, ahead of the
nineteen still listed, for a reason that does not apply to most of them: two
other predicates are written to *not* check what it checks, and their docstrings
name the elaborator as the reason that is safe. It was the only unexercised reason
another layer's correctness argument depended on. That is the criterion for
picking the next one, rather than working down the list in order.

Reachable only from a document the exporter really emits, so testing it needs a
new *source* fixture rather than one here: `branchingNotSupported`. The exporter
translates `if` faithfully and this stage refuses it, exactly as with `for` — but
`control-flow.rebeca` contains a `for`, and the elaborator stops at the first
statement it cannot admit, so the `if` path is shadowed. An `if`-only positive
model would reach it.

Reachable only through a `for` body, so it is shadowed until stage H admits
iteration: `localDeclarationNotSupported`. The exporter emits `declare` only as a
loop counter, so the enclosing `for` is always refused first. This is recorded as
finding F12.

Nothing here should be taken to mean the untested reasons are wrong. It means
they are unexercised, which is a different and smaller claim, and the honest one.
The number to watch is 9 of 32: if a future change to this directory does not
move it, the change added fixtures rather than coverage.

## Adding to this directory

Mutate an accepted document, keep the mutation to one thing, add the fixture to
`GeneralFrontendTestMain.lean` with the reason it must produce, and add a row
here. If a new fixture's reason turns out to be one that is already covered,
that is worth saying in its row rather than leaving a reader to wonder why two
fixtures assert the same thing.

Do not add `.rebeca` sources here. A source model belongs in `reject/` or
`upstream-reject/` depending on which layer catches it; the whole point of this
directory is the cases that no source model can express.
