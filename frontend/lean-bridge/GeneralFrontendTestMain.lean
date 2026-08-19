import Relico.Frontend.GeneralDecoder

set_option autoImplicit false

/-!
# `general-v1` frontend tests, pinning the layer boundary in both directions

Runs the general decoder over every committed positive fixture and asserts, for
each one, the outcome that fixture is supposed to have — accepted with a stated
class and instance count, or rejected for a stated reason.

## Why this file is not in `Relico/Tests/`

The sibling family puts its frontend tests in `Relico/Tests/MultiStorePayloadFrontend.lean`
and keeps a thin `main` here. That is deliberately not copied, for a bookkeeping
reason rather than a technical one. Every module under `Relico/Tests/` is scanned
by the obligation registry, and every obligation it produces must carry a
`final_benchmark_id` drawn from the 58 benchmarks in
`tests/benchmarks/registry/benchmarks.tsv`. The general family has no benchmark
yet — it cannot translate anything until stage D — so every row this module
generated would have to be mapped to some *other* family's benchmark, and the
registry would then assert that these obligations are evidence for a benchmark
they have nothing to do with.

So the tests live outside `Relico/`, where the registry does not look, and the
registry stays honest at 172 modules and 2129 obligations. When the general
family acquires a benchmark, this file is the natural thing to move into
`Relico/Tests/` and register in the same commit.

Being outside the build closure also means this file costs no `lake build` jobs;
it is compiled on demand by `lake env lean --run`, which is how
`frontend/check-general-lean.sh` invokes it.

## Why the expectations are written out rather than derived

Fixture layout already encodes the exporter's verdict: a model under
`frontend/fixtures/general/reject/` is one the Java exporter refuses, and one at
the top level is one it accepts. It cannot also encode the *Lean* layer's
verdict, because the two layers legitimately disagree — `control-flow` is
accepted by the exporter, which supports `if` and `for` under D4 and D7, and
refused by this layer, which does not implement them until stage H. That
disagreement is the three-layer design working, not a defect.

Writing each expectation out by hand means adding a fixture forces a decision
about which layer should accept it. Deriving the expectation from a directory
name would let a new fixture silently inherit whatever the code currently does,
which is the one thing a layer-boundary test must not do.

The class and instance counts are asserted for the same reason
`GeneralBridgeCheck` prints them: an elaborator that silently dropped a
declaration would still produce a well-formed model, and no other check in the
project would notice.

## The two kinds of negative

`control-flow` is a document the Java exporter really emits, refused here because
`for` is not admitted before stage H. It is the only negative of that kind, and
it is what makes the fixture tree unable to encode this layer's verdict on its
own.

The eleven fixtures in `frontend/fixtures/general/lean-reject/` are the other
kind: documents **no producer emits**. They exist because nothing else in the
project can reach the decoder's rejection paths. The Java gate cannot — a
document the exporter would refuse to emit is a document it never hands to Lean.
`#guard` cannot either: the decoder's input is a file, so exercising it needs
`IO`, and a `#guard` is pure. So this runner is not merely the convenient place
for these checks, it is the only possible one, and without them the four decode
steps and the five well-formedness clauses are unexecuted code that happens to
elaborate.

Each of the eleven is a single mutation of `minimal-class.parser.json` — the
document the first assertion in this run accepts. That is deliberate: the
mutation *is* the claim, so `diff` against the accepted document shows exactly
what is being tested, and a fixture cannot drift into failing for an unrelated
second reason without the diff growing. `frontend/fixtures/general/lean-reject/README.md`
lists each mutation.
-/

namespace Relico
namespace GeneralFrontendTests

/--
Fail a test, matching `Relico/Tests/MultiStorePayloadFrontend.lean`'s
`frontendFailure`: an `IO.userError` thrown so that the single `try` in the
runner catches the first failure and reports it.
-/
private def testFailure
    {α : Type}
    (message : String) :
    IO α :=
  throw
    (IO.userError message)

/--
Assert that a fixture decodes, and that it yields exactly the stated number of
classes and instances.
-/
private def expectAccept
    (label path : String)
    (classes instances : Nat) :
    IO Unit := do

  let text ←
    IO.FS.readFile path

  match Frontend.decodeGeneralModelText text with

  | .error diagnostic =>
      testFailure
        ("expected " ++ label ++
          " to decode, but it was rejected: " ++
          diagnostic.render)

  | .ok model =>
      if model.classes.length != classes then
        testFailure
          ("expected " ++ label ++ " to have " ++
            toString classes ++ " classes, found " ++
            toString model.classes.length)
      else if model.instances.length != instances then
        testFailure
          ("expected " ++ label ++ " to have " ++
            toString instances ++ " instances, found " ++
            toString model.instances.length)
      else
        IO.println
          ("PASS_ACCEPT_" ++ label)

/--
Assert that a fixture is rejected, and that it is rejected for exactly the
stated reason.

The reason is compared as a value, using the `BEq` derived on
`GeneralDiagnosticReason`, rather than by searching the rendered message for a
substring. A message is prose and may be reworded; the reason is the claim being
tested. Comparing the reason also keeps this test from passing for the wrong
cause — a `for` loop rejected as an unknown statement kind would satisfy a
substring search for "statement" while meaning something quite different.
-/
private def expectReject
    (label path : String)
    (reason : Frontend.GeneralDiagnosticReason) :
    IO Unit := do

  let text ←
    IO.FS.readFile path

  match Frontend.decodeGeneralModelText text with

  | .ok _ =>
      testFailure
        ("expected " ++ label ++
          " to be rejected, but it decoded")

  | .error diagnostic =>
      if diagnostic.reason == reason then
        IO.println
          ("PASS_REJECT_" ++ label)
      else
        testFailure
          ("expected " ++ label ++
            " to be rejected for a different reason; got: " ++
            diagnostic.render)

/--
Run every fixture expectation.

The calls are written out rather than folded over a list, following
`Relico/Tests/MultiStorePayloadFrontend.lean`. Counts are the ones measured at
the stage-B compile gate on 2026-08-19.
-/
def runGeneralFrontendTests
    (fixtureDirectory : String) :
    IO UInt32 := do

  try
    expectAccept
      "MINIMAL_CLASS"
      (fixtureDirectory ++ "/minimal-class.parser.json")
      1
      1

    expectAccept
      "TWO_CLASSES"
      (fixtureDirectory ++ "/two-classes.parser.json")
      2
      2

    expectAccept
      "TWO_INSTANCES"
      (fixtureDirectory ++ "/two-instances.parser.json")
      2
      3

    expectAccept
      "CONSTRUCTOR_ARGUMENTS"
      (fixtureDirectory ++ "/constructor-arguments.parser.json")
      1
      2

    expectAccept
      "EXPRESSIONS"
      (fixtureDirectory ++ "/expressions.parser.json")
      1
      1

    expectAccept
      "PRIORITIES"
      (fixtureDirectory ++ "/priorities.parser.json")
      1
      2

    expectAccept
      "FAN_IN"
      (fixtureDirectory ++ "/fan-in.parser.json")
      2
      4

    expectAccept
      "KEEP_ALIVE"
      (fixtureDirectory ++ "/keep-alive.parser.json")
      1
      1

    -- A document the exporter emits and this layer refuses. The only negative
    -- of that kind, and the reason the expectations here cannot be derived from
    -- which directory a fixture sits in.
    expectReject
      "CONTROL_FLOW"
      (fixtureDirectory ++ "/control-flow.parser.json")
      .iterationNotSupported

    -- Documents no producer emits. Each is a single mutation of
    -- `minimal-class.parser.json`, which this same run accepts; see
    -- `frontend/fixtures/general/lean-reject/README.md`.

    -- Step 1, the parse.
    expectReject
      "INVALID_JSON"
      (fixtureDirectory ++ "/lean-reject/invalid-json.json")
      .invalidJson

    -- Step 2, the schema. One missing field at the top level and one nested
    -- inside a class, because `FromJson` is derived separately at every level
    -- and a required field is only required where it is declared.
    expectReject
      "MISSING_CLASSES"
      (fixtureDirectory ++ "/lean-reject/invalid-missing-classes.json")
      .schemaDecodeFailed

    expectReject
      "MISSING_QUEUE_BOUND"
      (fixtureDirectory ++ "/lean-reject/invalid-missing-queue-bound.json")
      .schemaDecodeFailed

    -- Step 3, the envelope. Both orderings matter: `family` is checked before
    -- `schemaVersion`, so the version fixture has to carry the right family for
    -- its own reason to be the one raised.
    expectReject
      "UNEXPECTED_FAMILY"
      (fixtureDirectory ++ "/lean-reject/invalid-family.json")
      .unexpectedFamily

    expectReject
      "UNSUPPORTED_SCHEMA_VERSION"
      (fixtureDirectory ++ "/lean-reject/invalid-schema-version.json")
      .unsupportedSchemaVersion

    -- Step 4, the assembled model. `bindingsMatchDeclarations` is the first
    -- clause the classifier tries, and it is where a missing class is caught:
    -- every other clause looks a class up too, so the reason a dangling
    -- `className` receives is decided by clause order, not by which check is
    -- most specific.
    expectReject
      "UNKNOWN_CLASS"
      (fixtureDirectory ++ "/lean-reject/invalid-unknown-class.json")
      .bindingsMatchDeclarationsFailed

    expectReject
      "ARGUMENT_ARITY"
      (fixtureDirectory ++ "/lean-reject/invalid-argument-arity.json")
      .argumentsMatchConstructorFailed

    -- The fifth clause, the one that was not in the approved design. Four
    -- fixtures share its reason because the reason is per-clause and the clause
    -- is a conjunction of four separate requirements: unique topology keys,
    -- distinct class names, non-empty instance names, non-empty class names.
    -- Sharing a reason is the honest limit of the diagnostic vocabulary here;
    -- what these four pin is that each mistake is refused at all, which is what
    -- the empty-name requirement asks for.
    expectReject
      "EMPTY_CLASS_NAME"
      (fixtureDirectory ++ "/lean-reject/invalid-empty-class-name.json")
      .namesUniqueAndValidFailed

    expectReject
      "EMPTY_INSTANCE_NAME"
      (fixtureDirectory ++ "/lean-reject/invalid-empty-instance-name.json")
      .namesUniqueAndValidFailed

    expectReject
      "DUPLICATE_CLASS_NAME"
      (fixtureDirectory ++ "/lean-reject/invalid-duplicate-class-name.json")
      .namesUniqueAndValidFailed

    expectReject
      "DUPLICATE_INSTANCE_NAME"
      (fixtureDirectory ++ "/lean-reject/invalid-duplicate-instance-name.json")
      .namesUniqueAndValidFailed

    IO.println
      "GENERAL_FRONTEND_TESTS_OK"

    pure 0

  catch exception => do
    IO.eprintln
      (toString exception)

    pure 1

end GeneralFrontendTests
end Relico

def main
    (arguments : List String) :
    IO UInt32 :=
  match arguments with

  | [fixtureDirectory] =>
      Relico.GeneralFrontendTests.runGeneralFrontendTests
        fixtureDirectory

  | _ => do
      IO.eprintln
        "usage: GeneralFrontendTestMain <fixture-directory>"

      pure 2
