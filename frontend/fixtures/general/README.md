# `general-v1` frontend fixtures

These models are the acceptance surface of the general family's two frontend
layers. Between them the nine positives exercise every production
`frontend/java-bridge/RebecaGeneralJsonExporter.java` admits, and the thirty-three
negatives pin one rejection each — nineteen against the exporter and the Rebeca
compiler upstream of it, fourteen against the Lean decoder.

Two gates read this directory, and they read different parts of it.
`frontend/java-bridge/check-general.sh` owns the Rebeca-to-JSON boundary: it runs
the `.rebeca` sources through the exporter and checks what comes out.
`frontend/check-general-lean.sh` owns the JSON-to-Lean boundary: it feeds the
committed `.parser.json` documents to the Lean decoder and checks the models they
produce. The documents in this directory are the contract between the two, which
is why neither gate regenerates what the other one checks.

The negatives are split across three directories by *which layer* rejects them:
eleven in `reject/` that this exporter refuses, eight in `upstream-reject/`
that the Rebeca parser and typechecker refuse before the exporter is handed an
AST, and fourteen in `lean-reject/` that the Lean decoder refuses. That split was
measured, not guessed, and the reason it is worth recording
is in "Which layer enforces what" below.

`lean-reject/` holds `.json` rather than `.rebeca`, because its cases are
documents **no producer emits** — a broken envelope, a missing field, a duplicated
class name. No source model can carry those across the boundary, since a document
the exporter would refuse to emit is one it never hands to Lean. That directory
has its own README covering what it does and does not cover.

## Layout

A positive fixture is `<name>.rebeca` plus `<name>.parser.json`, holding the
exact document the exporter must emit for it. A negative fixture is
`<directory>/<name>.rebeca` plus `<directory>/<name>.diagnostic`, a single line
holding a substring that the rejection message must contain. The diagnostic
files are substrings rather than whole messages so that rewording a message's
framing does not break a test, while the part that identifies *which* rule fired
still does. For `upstream-reject/` the message belongs to the upstream compiler,
so the recorded substring omits its volatile `line:`/`column:` prefix and keeps
only the sentence.

`check-general.sh` runs every fixture through the exporter in three loops:
positives must exit zero and match their expected document; both kinds of
negative must exit non-zero, write no output file, and print the diagnostic they
claim, from the layer they claim.

## Which expected documents are hand-authored

Four are, and they are the anchors that make the others trustworthy:
`two-classes`, `control-flow`, `keep-alive`, `constructor-arguments`. They were
written by hand, from the source models, before the exporter had ever run — so
when the exporter agrees with them, that agreement is evidence.

Between them the anchors cover every statement kind (`assign`, `send`, `if`
with and without `else`, `for` in both initializer forms, `declare`), a self
send and a known-rebec send, an `after` delay, priorities in both positions,
constructor parameters of both value types, boolean and integer instance
arguments, and the deliberate line-number asymmetry described below.

The one node shape no anchor covers is `unary`. It is exercised, by
`expressions`, but that is a recorded fixture rather than a predicted one, which
makes `unary` the single node shape in this schema whose emitted form rests on
the exporter's own output instead of on an independent prediction. Across the
whole corpus every other kind the schema defines — `assign`, `send`, `if`, `for`,
`declare`, `intLiteral`, `boolLiteral`, `variable`, `binary`, and both send
targets — appears in at least one anchor.

Five are not hand-authored: `expressions`, `fan-in`, `minimal-class`,
`priorities`, `two-instances`. Their expected documents were **recorded from the
first real exporter run and then reviewed**, for a specific reason.

## Why five are recorded rather than predicted, and what stops that from being circular

Every node in this schema carries a `line`, and line numbers are parser trivia:
they come from the Rebeca compiler's own AST, and **no other exporter in this
repository reads them at all**, so there is no precedent to predict from. A
hand-authored document can be structurally perfect and still differ in a dozen
`line` fields, and there is no way to find out from a machine with no Java
compiler on it.

Recording an expected file from the tool under test is normally worthless — it
makes the test assert only that the tool is deterministic. Three things stop
that here:

1. The four anchors were written first and are never re-recorded. If the
   exporter's structure is wrong, they fail, and no amount of recording
   elsewhere hides that.
2. `validate_general_v1.py` checks every recorded document against the schema
   and, more importantly, against every cross-reference invariant — binding
   order, send arity, message-server existence, variable scope. It was written
   from `docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md`, independently of
   the Java, so it can disagree with the exporter.
3. The comparator reports **structural differences and line-number differences
   separately**, and only line-number differences can be accepted wholesale
   (`--accept-lines`, which rewrites `line` fields and nothing else). A
   structural mismatch can never be rubber-stamped by re-recording.

Once recorded and reviewed, those five files are committed and are as binding
as the anchors. The distinction is historical, not permanent.

### What the first run actually showed

The exporter had never been compiled when the anchors were written — there is no
JDK on the machine they were authored on — so the anchors were a genuine
prediction. On the first run all four came back matching, **including every one
of their line numbers**, and all nine positives were accepted. That is the
evidence the argument above was reaching for: the agreement could have failed and
did not.

## The line-number asymmetry, which is deliberate

A literal in expression position carries a `line`. The same literal as an
instance constructor argument or as an `after` delay does **not** — the
exporter builds those from a different code path. It would have been tidier to
make it uniform, but the fixtures pin the behaviour as it is rather than as it
ought to be, and both directions are tested: an argument or delay that grows a
`line`, and an expression literal that loses one, each fail.

## Comparison must be canonical text, not parsed equality

The three older frontend checks (`check-v0.sh`, `check-multistore.sh`,
`check-multistore-payload-frontend.sh`) compare `json.loads(expected) ==
json.loads(actual)`. That is unsound for this family, because Python holds
`True == 1`: a document whose integer literal `1` was emitted as `true`
compares **equal** to the correct document while differing in the bytes.

This has never mattered before because no earlier family emits a boolean at
all — the existing expected fixtures contain neither `true` nor `false`.
`general-v1` introduces `boolLiteral`, and puts boolean and integer payloads
under the same `value` key, so the confusion becomes reachable exactly here.
`check-general.sh` therefore compares canonical serializations
(`json.dumps(..., indent=2, sort_keys=True)`), which is strictly stronger and
costs nothing. `test_validate_general_v1.py` pins the reason so it cannot be
undone by someone tidying the comparison back to `==`, and
`test_compare_general_v1.py` states `assertEqual(1, True)` outright so the
motivation is executable rather than a claim in this file.

Key order and whitespace are still normalized away, because the staging harness
re-serializes anyway. **List order is not**, and must never be sorted:
declaration order decides same-tag firing order in the LF target, and binding
order decides the topology.

## Which layer enforces what

A negative fixture is only a test of *this* exporter if the exporter is what
rejects it. When the corpus was first written, five fixtures were flagged as
likely to be caught earlier, by the Rebeca parser or typechecker, before the
exporter ever sees an AST. The first run settled it: **eight** were, and they
were not the five that had been guessed.

Those eight now live in `upstream-reject/`, with the upstream compiler's own
message recorded rather than ours. They are kept rather than deleted because
which layer enforces a restriction is itself a fact worth pinning, and it is
precisely the fact stage B needs: the Lean side decodes JSON and has no Rebeca
typechecker anywhere upstream of it, so every one of these eight restrictions
has to be re-enforced there, in a well-formedness predicate, or the fragment
quietly admits models the Java pipeline never could.

This does not conflict with the project's standing rule that a negative the
model checker catches first is a benchmark for the model checker and not for us.
That rule is about rows in the benchmark registry, which are claims about the
translation. These are frontend fixtures, and their claim is narrower and still
true: this model does not reach Lean, and here is the layer that stops it.

The two layers are distinguishable in the log, which is what lets the gate hold
each corpus to its own claim rather than merely checking that *something*
rejected the model:

| | `reject/` (11) | `upstream-reject/` (8) |
|---|---|---|
| `unsupported by the ReLico general parser bridge` | required | forbidden |
| `Timed Rebeca parsing or semantic checking failed` | forbidden | required |

Measured across a full run, the banner appears in all eight upstream logs and
none of the exporter ones, and the marker exactly the other way round. So a
restriction that migrates between layers — because the upstream compiler was
upgraded, or because a rejection site was added or removed here — fails the gate
with `CAUGHT UPSTREAM` or `NOT CAUGHT UPSTREAM` instead of silently changing
what the fixture proves.

### The third layer

`lean-reject/` is the same idea one boundary further on, and it is where the
argument above finishes. The eight relocated restrictions had to be re-enforced
on the Lean side because nothing typechecks JSON; that re-enforcement is what
`GeneralModel.wellFormed` and the decoder's four steps are, and until stage B's
tests existed none of it had ever been run.

It differs from the other two in one respect worth stating. Those hold `.rebeca`
sources, because there is a compiler upstream to feed them to. This one holds
`.json`, because there is not: a document the exporter would refuse to emit is a
document it never hands to Lean, so no source model can express these cases. Each
fixture is instead a single mutation of an accepted document — eleven of them
mutate `minimal-class.parser.json`, one mutates
`constructor-arguments.parser.json`, and two mutate `two-classes.parser.json` — so
the mutation is the claim and `diff` shows it. The base varies because the rule is
one mutation, not one base: a claim about a constructor formal shadowing a state
variable needs a class that has both, and a claim about a send needs a model that
contains one, neither of which `minimal-class` provides.

Layer is pinned by *reason* rather than by log grepping here, because the Lean
side has something the Java side does not: `GeneralDiagnosticReason` derives
`BEq`, so a test can compare the reason as a value instead of searching a rendered
message for a substring. That is a stronger check than the table above, and it is
available only because the diagnostic vocabulary is an inductive type rather than
a string.

`lean-reject/README.md` records each fixture's mutation and, importantly, what
the corpus does **not** cover: eleven of the thirty-two diagnostic reasons are
asserted, and twenty-one are not.

## A fixture that cannot parse proves nothing

`read-clock` spent its whole first life asserting nothing. It declared
`msgsrv record()`, and `record` is a reserved token in `CoreRebecaLexer.g4`, so
the model failed to parse and never reached the `now` rejection site it existed
to exercise. It still "failed to be accepted", which is all a naive negative
test asks, so it read as coverage.

Two things came out of that. The message server is now called `capture`, and
`test_validate_general_v1.py` checks every fixture in every directory against
the lexer's reserved words, so the same mistake fails a test that runs anywhere
rather than waiting for a machine with a JDK.

It also settled a related question by measurement:
`TimedRebecaCompleteCompilerFacade` injects four reserved `int` variables into
every message server's scope — `now`, `currentMessageArrival`,
`currentMessageDeadline` and `currentMessageWaitingTime`. All four typecheck
upstream, so all four reach the exporter. Only `now` has a named rejection site;
the other three fall through to the general undeclared-name check, which does
reject them, but says "undeclared name" about something that is in fact
reserved. `read-message-arrival` pins that behaviour so the fail-closed part is
guaranteed rather than incidental, and so improving the message later is a
visible change instead of a silent one.

## Running the checks

```
python3 frontend/validate_general_v1.py frontend/fixtures/general/*.parser.json
python3 frontend/test_validate_general_v1.py
python3 frontend/test_compare_general_v1.py
frontend/java-bridge/check-general.sh <artifact.zip>
frontend/check-general-lean.sh
```

The first three need nothing but a Python interpreter and run in any
environment. The fourth needs Maven, a JDK, and the upstream parser artifact, so
it runs on the machine that holds the toolchain; it re-runs the other three
first, because a green gate resting on an unchecked checker is worth nothing.

The fifth needs a Lean toolchain and nothing else — no Maven, no JDK, no
artifact. That is deliberate rather than incidental: it means the Lean side of
this boundary stays checkable when the upstream artifact is unavailable, and it is
why the two gates split the way they do. `check-general.sh` regenerates the
`.parser.json` documents from source and compares them; `check-general-lean.sh`
takes those same committed documents as given and checks what Lean makes of them.
Neither re-does the other's work, and the documents in this directory are the
contract between them.

Note that the glob on the first line matches only the nine positives. The fourteen
documents in `lean-reject/` are deliberately invalid against `general-v1` — one of
them is not even JSON — so validating them would fail by design. They are named
`invalid-*.json` rather than `*.parser.json` partly for that reason.
