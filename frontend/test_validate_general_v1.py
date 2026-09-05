#!/usr/bin/env python3
"""Adversarial tests for ``frontend/validate_general_v1.py``.

A validator is only worth what it rejects. This file takes the four
hand-authored ``general-v1`` anchors, confirms they pass clean, then applies
one surgical mutation at a time and requires that the validator name the
specific violation. Every rule class in the validator has at least one
mutation here, so a rule that is quietly deleted or weakened fails a test
rather than silently widening what the exporter is allowed to emit.

The mutations are deliberately expressed as small edits to a deep copy of a
real anchor rather than as bespoke documents, because a bespoke document can
drift away from the schema for reasons unrelated to the rule under test and
then pass for the wrong reason.

Run it standalone, following the convention of the other tests in this
repository::

    python3 frontend/test_validate_general_v1.py
"""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import pathlib
import re
import sys
import unittest


FRONTEND = pathlib.Path(__file__).resolve().parent

FIXTURES = FRONTEND / "fixtures" / "general"

VALIDATOR_SOURCE = FRONTEND / "validate_general_v1.py"

ANCHORS = (
    "two-classes",
    "control-flow",
    "keep-alive",
    "constructor-arguments",
    "branching",
)

# Recorded from a real exporter run and then reviewed, rather than predicted.
# Kept as a named list because the provenance of an expected document is worth
# knowing even after the distinction stops mattering: the anchors are
# evidence that the exporter is right, and these six are not. Five of the six
# were recorded by the first `--record` run; `send-sites` was recorded by the
# later run that added it, which is why this comment says "a real run" rather
# than "the first" — a provenance note that names one event goes stale the first
# time a second event of the same kind happens. `branching` is an anchor rather
# than a recording by necessity, not choice: it was written by hand in stage I0
# because no exporter run is possible on this machine (F90 records the gap), so
# its expected document is a prediction the Lean layer confirmed, not evidence
# about the exporter.
RECORDED = (
    "expressions",
    "fan-in",
    "minimal-class",
    "priorities",
    "send-sites",
    "two-instances",
)

# Hand-authored like an anchor but for a construct the exporter does not yet
# emit: `locals` was written in stage I against the exporter's *document shape*
# (`declare` as a for counter) while the exporter's own body-declaration
# refusal is still in place. It is a prediction of what the widened exporter
# will emit, pending the S-I6 host run; until then its evidence value is the
# Lean and Python layers, not the exporter.
HAND_AUTHORED_PENDING_EXPORTER = (
    "locals",
)

# The two negative corpora, and the layer each one holds responsible. A fixture
# in the wrong directory is a test that passes for the wrong reason, so the
# split is checked here as well as at the gate.
REJECT_DIRECTORIES = ("reject", "upstream-reject")

# Set by `check-general.sh --record`, the one run whose purpose is to create
# expected documents that do not exist yet. Exactly one assertion below relaxes
# under it, and only in the direction of a file not existing yet; nothing about
# the content of a document that does exist is affected. See finding F55 for why
# this flag has to exist: without it the gate could not record a new positive,
# because its preflight failed on the absence the recording loop was about to
# fix.
RECORDING = os.environ.get("RELICO_GENERAL_RECORDING") == "1"

# Reserved words of the Core and Timed Rebeca lexers that a fixture could
# plausibly reach for as an identifier. `record` is the reason this list exists:
# read-clock.rebeca declared `msgsrv record()`, which is a lexer token, so the
# model never parsed and the rejection site it was written to exercise was
# never reached. The fixture looked like coverage and was not, and nothing in
# the corpus would have caught that.
RESERVED_WORDS = (
    "abstract",
    "break",
    "case",
    "class",
    "continue",
    "default",
    "env",
    "extends",
    "featurevar",
    "goto",
    "implements",
    "import",
    "instanceof",
    "interface",
    "new",
    "null",
    "package",
    "private",
    "protected",
    "public",
    "record",
    "return",
    "super",
    "switch",
    "this",
    "while",
)


def load_validator():
    """Import the validator by path; it is a script, not an installed module."""
    # Loading it would otherwise leave a frontend/__pycache__ behind. This
    # repository does not gitignore __pycache__, so tools/__pycache__ is a
    # standing nuisance that every gate has to remember to exclude from a
    # commit; there is no reason to create a second one.
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True

    try:
        specification = importlib.util.spec_from_file_location(
            "relico_validate_general_v1_under_test",
            VALIDATOR_SOURCE,
        )

        if specification is None or specification.loader is None:
            raise RuntimeError("could not load " + str(VALIDATOR_SOURCE))

        module = importlib.util.module_from_spec(specification)
        sys.modules[specification.name] = module
        specification.loader.exec_module(module)

        return module
    finally:
        sys.dont_write_bytecode = previous


VALIDATOR = load_validator()


def anchor(name: str) -> dict:
    path = FIXTURES / (name + ".parser.json")

    return json.loads(path.read_text(encoding="utf-8"))


def violations(document: object) -> list[str]:
    report = VALIDATOR.Report()
    VALIDATOR.validate(document, report)

    return report.violations


def canonical(document: object) -> str:
    """The exact form the staging harness writes, and the only sound way to
    compare two of these documents.

    ``json.loads`` equality — which the older frontend checks use — is *not*
    sound here, because Python holds ``True == 1``. A document whose integer
    literal carried ``true`` instead of ``1`` compares equal to the correct one
    under ``==`` while differing in the emitted JSON. ``general-v1`` puts
    boolean and integer literal payloads under the same ``value`` key, so that
    is a live confusion rather than a theoretical one, and it is the reason
    ``check-general.sh`` must compare canonical text.
    """
    return json.dumps(document, indent=2, sort_keys=True) + "\n"


def replace(node: dict, contents: dict) -> None:
    """Swap a node's whole contents.

    ``dict.update`` merges, which leaves keys from the old shape behind and
    makes a mutation fail the key check for the wrong reason.
    """
    node.clear()
    node.update(contents)


# SECTION: mutation table


def tick_body(document: dict) -> list:
    """`Producer.tick`: [0] is an assignment, [1] is the send to `sink`."""
    return document["classes"][0]["messageServers"][0]["body"]


def producer_constructor(document: dict) -> list:
    """`Producer()`: [0] is an assignment, [1] is the self send of `tick`."""
    return document["classes"][0]["constructor"]["body"]


def scan_body(document: dict) -> list:
    """`Looper.scan`: [0] declares its counter, [1] assigns an existing one."""
    return document["classes"][0]["messageServers"][0]["body"]


def keep_alive_send(document: dict) -> dict:
    """The self send in `Ticker.keepAlive`, the one carrying `after(1)`."""
    return document["classes"][0]["messageServers"][0]["body"][1]


# label, anchor, mutation applied to a deep copy, required substring.
MUTATIONS = (
    # -------- document shape --------
    (
        "missing top-level key",
        "two-classes",
        lambda d: d.pop("family"),
        "missing family",
    ),
    (
        "extra top-level key",
        "two-classes",
        lambda d: d.update({"metadata": {}}),
        "unexpected metadata",
    ),
    (
        "wrong schema version",
        "two-classes",
        lambda d: d.update({"schemaVersion": 2}),
        "schemaVersion must be 1",
    ),
    (
        "wrong family",
        "two-classes",
        lambda d: d.update({"family": "multi-store-payload"}),
        'family must be "general"',
    ),
    (
        "no classes",
        "two-classes",
        lambda d: d.update({"classes": []}),
        "no reactive class (R1)",
    ),
    (
        "no instances",
        "two-classes",
        lambda d: d.update({"instances": []}),
        "no instance",
    ),
    # -------- class shape --------
    (
        "queue bound of zero",
        "two-classes",
        lambda d: d["classes"][0].update({"queueBound": 0}),
        "must be an integer of at least 1",
    ),
    (
        "queue bound written as a boolean",
        "two-classes",
        lambda d: d["classes"][0].update({"queueBound": True}),
        "must be an integer of at least 1",
    ),
    (
        "state variable of an unsupported type",
        "two-classes",
        lambda d: d["classes"][0]["stateVariables"][0].update({"type": "double"}),
        "must be one of boolean, int, found 'double'",
    ),
    (
        "initialized state variable",
        "two-classes",
        lambda d: d["classes"][0]["stateVariables"][0].update({"value": 0}),
        "unexpected value",
    ),
    (
        "duplicate class",
        "two-classes",
        lambda d: d["classes"].append(copy.deepcopy(d["classes"][1])),
        "duplicate class Consumer",
    ),
    (
        "duplicate message server",
        "two-classes",
        lambda d: d["classes"][1]["messageServers"].append(
            copy.deepcopy(d["classes"][1]["messageServers"][0])
        ),
        "duplicate message server accept",
    ),
    (
        "negative message server priority",
        "two-classes",
        lambda d: d["classes"][1]["messageServers"][0].update({"priority": -1}),
        "must be null or a non-negative integer",
    ),
    (
        "duplicate parameter",
        "constructor-arguments",
        lambda d: d["classes"][0]["messageServers"][0]["parameters"].append(
            {"name": "bound", "type": "int", "line": 10}
        ),
        "duplicate parameter bound",
    ),
    (
        "state variable colliding with a known rebec",
        "two-classes",
        lambda d: d["classes"][0]["stateVariables"].append(
            {"name": "sink", "type": "int", "line": 6}
        ),
        "declared twice, as known rebec and as state variable",
    ),
    (
        "known rebec of a non-actor type",
        "two-classes",
        lambda d: d["classes"][0]["knownRebecs"][0].update({"className": "int"}),
        "has non-actor type int",
    ),
    # -------- statements --------
    (
        "a while loop",
        "two-classes",
        lambda d: tick_body(d)[0].update({"kind": "while"}),
        "unknown statement kind 'while'",
    ),
    (
        "a read of a local after its branch ends",
        "two-classes",
        # One lambda, because `list.insert` returns `None` and an `and` chain
        # short-circuits on it — the first draft of this mutation silently
        # applied only its first edit and the document was accepted for no
        # reason the reader could see.
        lambda d: (
            tick_body(d).insert(
                0,
                {
                    "kind": "declare", "name": "temporary", "type": "int",
                    "value": {"kind": "intLiteral", "value": 0, "line": 13},
                    "line": 13,
                }
            ),
            tick_body(d).insert(
                1,
                {
                    "kind": "if",
                    "condition": {
                        "kind": "boolLiteral", "value": True, "line": 14
                    },
                    "then": [
                        {
                            "kind": "declare", "name": "branchLocal",
                            "type": "int",
                            "value": {
                                "kind": "intLiteral", "value": 1, "line": 15
                            },
                            "line": 15,
                        }
                    ],
                    "else": [],
                    "line": 14,
                }
            ),
            tick_body(d).append(
                {
                    "kind": "assign", "target": "sent",
                    "value": {
                        "kind": "variable", "name": "branchLocal",
                        "line": 16
                    },
                    "line": 16,
                }
            ),
        ),
        "a read of undeclared name branchLocal",
    ),
    (
        "assignment to a known rebec",
        "two-classes",
        lambda d: tick_body(d)[0].update({"target": "sink"}),
        "assignment to known rebec sink",
    ),
    (
        "assignment to an undeclared name",
        "two-classes",
        lambda d: tick_body(d)[0].update({"target": "nowhere"}),
        "assignment to undeclared name nowhere",
    ),
    (
        "read of an undeclared name",
        "two-classes",
        lambda d: tick_body(d)[0]["value"]["left"].update({"name": "nowhere"}),
        "a read of undeclared name nowhere",
    ),
    (
        "known rebec read as a value",
        "two-classes",
        lambda d: tick_body(d)[0]["value"]["left"].update({"name": "sink"}),
        "a use of known rebec sink as a value",
    ),
    (
        "loop counter read after its loop closed",
        "control-flow",
        lambda d: replace(
            scan_body(d)[1]["body"][0]["value"]["right"],
            {"kind": "variable", "name": "index", "line": 17},
        ),
        "a read of undeclared name index",
    ),
    (
        "parameter read from the wrong message server",
        "control-flow",
        lambda d: d["classes"][0]["messageServers"][1]["body"][0][
            "condition"
        ]["left"].update({"name": "bound"}),
        "a read of undeclared name bound",
    ),
    # -------- expressions --------
    (
        "an operator outside D5",
        "two-classes",
        lambda d: tick_body(d)[0]["value"].update({"operator": "**"}),
        "D5 admits",
    ),
    (
        "a ternary conditional",
        "two-classes",
        lambda d: tick_body(d)[0]["value"].update({"kind": "ternary"}),
        "unknown expression kind 'ternary'",
    ),
    (
        "a negative integer literal",
        "two-classes",
        lambda d: tick_body(d)[0]["value"]["right"].update({"value": -1}),
        "an integer literal must be non-negative",
    ),
    (
        "an integer literal holding a boolean",
        "two-classes",
        lambda d: tick_body(d)[0]["value"]["right"].update({"value": True}),
        "an integer literal must be non-negative",
    ),
    (
        "an expression literal with no line",
        "two-classes",
        lambda d: tick_body(d)[0]["value"]["right"].pop("line"),
        "missing line",
    ),
    (
        "a line of zero",
        "two-classes",
        lambda d: d["classes"][0].update({"line": 0}),
        "line must be null or a positive integer",
    ),
    # -------- sends --------
    (
        "a self send naming another class",
        "two-classes",
        lambda d: producer_constructor(d)[1].update(
            {"targetClassName": "Consumer"}
        ),
        "a self send whose targetClassName is Consumer",
    ),
    (
        "a send to a rebec that is not known",
        "two-classes",
        lambda d: tick_body(d)[1]["target"].update({"name": "stranger"}),
        "D6: a send to stranger",
    ),
    (
        "a send whose target class contradicts the known rebec",
        "two-classes",
        lambda d: tick_body(d)[1].update({"targetClassName": "Producer"}),
        "carrying targetClassName Producer",
    ),
    (
        "a send target that is neither self nor a known rebec",
        "two-classes",
        lambda d: tick_body(d)[1].update(
            {"target": {"kind": "variable", "name": "sink", "line": 14}}
        ),
        "R18 admits self or a known rebec",
    ),
    (
        "a send of an undeclared message server",
        "two-classes",
        lambda d: tick_body(d)[1].update({"messageServer": "absorb"}),
        "which class Consumer does not declare",
    ),
    (
        "a send with too few arguments",
        "two-classes",
        lambda d: tick_body(d)[1].update({"arguments": []}),
        "with 0 arguments where 1 are declared",
    ),
    (
        "a negative after delay",
        "keep-alive",
        lambda d: keep_alive_send(d)["after"].update({"value": -1}),
        "an after delay must be a non-negative integer",
    ),
    (
        "a boolean after delay",
        "keep-alive",
        lambda d: keep_alive_send(d)["after"].update({"kind": "boolLiteral"}),
        "an after delay must be an integer literal",
    ),
    (
        "an after delay carrying a line",
        "keep-alive",
        lambda d: keep_alive_send(d)["after"].update({"line": 11}),
        "unexpected line",
    ),
    (
        "an absent after rewritten to zero",
        "two-classes",
        lambda d: tick_body(d)[1].update({"after": 0}),
        "expected an object, found int",
    ),
    # -------- instances --------
    (
        "an instance of an undeclared class",
        "two-classes",
        lambda d: d["instances"][0].update({"className": "Ghost"}),
        "of undeclared reactive class Ghost",
    ),
    (
        "an unbound known rebec",
        "two-classes",
        lambda d: d["instances"][0].update({"bindings": []}),
        "binding 0 known rebecs where class Producer declares 1",
    ),
    (
        "a binding to an undeclared instance",
        "two-classes",
        lambda d: d["instances"][0]["bindings"][0].update({"instance": "ghost"}),
        "bound to undeclared instance ghost",
    ),
    (
        "a binding whose class contradicts the instance",
        "two-classes",
        lambda d: d["instances"][0]["bindings"][0].update(
            {"className": "Producer"}
        ),
        "claims class Producer but instance consumer0 has class Consumer",
    ),
    (
        "a binding naming the wrong known rebec",
        "two-classes",
        lambda d: d["instances"][0]["bindings"][0].update({"knownRebec": "peer"}),
        "out of order: names peer where the class declares sink",
    ),
    (
        "duplicate instance",
        "two-classes",
        lambda d: d["instances"].append(copy.deepcopy(d["instances"][1])),
        "duplicate instance consumer0",
    ),
    (
        "negative instance priority",
        "two-classes",
        lambda d: d["instances"][0].update({"priority": -1}),
        "must be null or a non-negative integer",
    ),
    (
        "an argument to a constructor that takes none",
        "two-classes",
        lambda d: d["instances"][0].update(
            {"arguments": [{"kind": "intLiteral", "value": 1}]}
        ),
        "passing 1 constructor arguments where Producer declares 0",
    ),
    (
        "an integer argument for a boolean parameter",
        "constructor-arguments",
        lambda d: d["instances"][0]["arguments"].__setitem__(
            1, {"kind": "intLiteral", "value": 1}
        ),
        "a intLiteral where parameter active is declared boolean",
    ),
    (
        "an instance argument carrying a line",
        "constructor-arguments",
        lambda d: d["instances"][0]["arguments"][0].update({"line": 17}),
        "unexpected line",
    ),
    (
        "a non-literal instance argument",
        "constructor-arguments",
        lambda d: d["instances"][0]["arguments"].__setitem__(
            0, {"kind": "variable", "name": "seven", "line": 17}
        ),
        "R4 admits a literal only",
    ),
)


# SECTION: test cases


class AnchorsAreClean(unittest.TestCase):
    """The hand-authored anchors must pass with nothing reported."""

    def test_every_anchor_validates(self) -> None:
        for name in ANCHORS:
            with self.subTest(anchor=name):
                self.assertEqual(violations(anchor(name)), [])

    def test_every_anchor_has_a_source_model(self) -> None:
        for name in ANCHORS:
            with self.subTest(anchor=name):
                self.assertTrue((FIXTURES / (name + ".rebeca")).is_file())

    def test_anchors_are_serialized_the_way_the_harness_serializes(self) -> None:
        # The staging harness re-serializes with indent=2, sort_keys=True. If a
        # committed anchor is not already in that form, a diff at the gate
        # would be pure formatting noise.
        for name in ANCHORS:
            with self.subTest(anchor=name):
                path = FIXTURES / (name + ".parser.json")
                text = path.read_text(encoding="utf-8")

                self.assertEqual(
                    text,
                    json.dumps(
                        json.loads(text), indent=2, sort_keys=True
                    ) + "\n",
                )


class MutationsAreCaught(unittest.TestCase):
    """Each mutation must produce a violation that names it."""

    def test_every_mutation_is_reported(self) -> None:
        for label, name, mutate, fragment in MUTATIONS:
            with self.subTest(mutation=label):
                document = anchor(name)
                mutate(document)

                found = violations(document)

                self.assertTrue(
                    found,
                    "mutation " + repr(label) + " was accepted",
                )

                self.assertTrue(
                    any(fragment in violation for violation in found),
                    "mutation " + repr(label) + " reported "
                    + repr(found) + " which does not mention "
                    + repr(fragment),
                )

    def test_mutations_actually_change_the_document(self) -> None:
        # A mutation that is a no-op would pass the test above only if the
        # anchor were already broken, but it would silently stop testing its
        # rule. Cheap to rule out.
        #
        # Compared as canonical text, not with ``==``: one of these mutations
        # swaps the integer literal 1 for ``true``, and ``True == 1`` holds in
        # Python, so dict equality would call that mutation a no-op. See the
        # note on ``canonical``.
        for label, name, mutate, _ in MUTATIONS:
            with self.subTest(mutation=label):
                original = anchor(name)
                document = copy.deepcopy(original)
                mutate(document)

                self.assertNotEqual(
                    canonical(document), canonical(original), label
                )

    def test_boolean_and_integer_payloads_are_distinguishable(self) -> None:
        # Pins the reason ``canonical`` exists, so that a future change to the
        # comparison protocol cannot quietly reintroduce the confusion.
        document = anchor("two-classes")
        tick_body(document)[0]["value"]["right"].update({"value": True})

        self.assertEqual(document, anchor("two-classes"))
        self.assertNotEqual(canonical(document), canonical(anchor("two-classes")))

    def test_labels_are_unique(self) -> None:
        labels = [label for label, _, _, _ in MUTATIONS]

        self.assertEqual(len(labels), len(set(labels)))


class RejectionCorpusIsWellFormed(unittest.TestCase):
    """Every negative fixture must carry the diagnostic it expects."""

    def test_each_rejected_model_has_a_diagnostic(self) -> None:
        for directory in REJECT_DIRECTORIES:
            reject = FIXTURES / directory

            self.assertTrue(reject.is_dir(), str(reject))

            models = sorted(reject.glob("*.rebeca"))

            self.assertTrue(models, "no fixtures found in " + directory)

            for model in models:
                with self.subTest(fixture=directory + "/" + model.stem):
                    diagnostic = model.with_suffix(".diagnostic")

                    self.assertTrue(diagnostic.is_file(), str(diagnostic))

                    text = diagnostic.read_text(encoding="utf-8")

                    self.assertEqual(
                        text,
                        text.strip() + "\n",
                        "a diagnostic file must hold one trimmed line",
                    )

                    self.assertNotEqual(text.strip(), "")

    def test_no_orphan_diagnostics(self) -> None:
        for directory in REJECT_DIRECTORIES:
            reject = FIXTURES / directory

            for diagnostic in sorted(reject.glob("*.diagnostic")):
                with self.subTest(fixture=directory + "/" + diagnostic.stem):
                    self.assertTrue(
                        diagnostic.with_suffix(".rebeca").is_file(),
                        "diagnostic without a model: " + diagnostic.name,
                    )

    def test_diagnostics_are_distinct(self) -> None:
        # Two fixtures sharing an expected substring means one of them is not
        # pinning the diagnostic it thinks it is. Checked across both corpora
        # rather than within each, because the substrings are matched against
        # the same log either way.
        seen: dict[str, str] = {}

        for directory in REJECT_DIRECTORIES:
            reject = FIXTURES / directory

            for diagnostic in sorted(reject.glob("*.diagnostic")):
                text = diagnostic.read_text(encoding="utf-8").strip()

                self.assertNotIn(
                    text,
                    seen,
                    "same expected diagnostic as " + seen.get(text, ""),
                )

                seen[text] = directory + "/" + diagnostic.name

    def test_no_fixture_appears_in_both_corpora(self) -> None:
        # The two directories make opposite claims about which layer rejects a
        # model, so a name in both is a contradiction rather than duplication.
        names = {}

        for directory in REJECT_DIRECTORIES:
            for model in sorted((FIXTURES / directory).glob("*.rebeca")):
                self.assertNotIn(
                    model.stem,
                    names,
                    model.stem + " is also in " + names.get(model.stem, ""),
                )

                names[model.stem] = directory

    def test_no_fixture_uses_a_reserved_word_as_an_identifier(self) -> None:
        # A negative fixture that fails to parse still "passes" a test that only
        # asks whether something rejected it, which is how read-clock sat in the
        # corpus asserting nothing. Every fixture is checked, positives too: for
        # a positive the failure would be loud, but the cost of checking is one
        # regex.
        pattern = re.compile(r"\b[A-Za-z_][A-Za-z_0-9]*\b")

        directories = ("",) + REJECT_DIRECTORIES

        for directory in directories:
            for model in sorted((FIXTURES / directory).glob("*.rebeca")):
                text = model.read_text(encoding="utf-8")

                for match in pattern.finditer(text):
                    word = match.group(0)

                    if word not in RESERVED_WORDS:
                        continue

                    line = text[: match.start()].count("\n") + 1

                    self.fail(
                        model.name
                        + " line "
                        + str(line)
                        + " uses the reserved word "
                        + word
                        + " as an identifier, so the model cannot parse and the"
                        + " fixture asserts nothing"
                    )


class PositiveFixturesAreAccountedFor(unittest.TestCase):
    """Every positive model has an expected document, with known provenance."""

    def test_every_positive_has_an_expected_document(self) -> None:
        # Before the first gate run this asked something weaker: a fixture
        # either was an anchor or was named in the README as not yet recorded.
        # Recording has happened, so the invariant tightens. A positive with no
        # expected document would now be a fixture that asserts only that the
        # exporter does not crash.
        #
        # The tightening had a cost that took a second new positive to notice.
        # The failure message below says to run the gate with --record, and that
        # gate runs this suite before the loop that records, so on the very run
        # the message asks for, this assertion fired first and the recording never
        # happened. Finding F55. The exemption is therefore narrow on purpose: it
        # applies only under RECORDING, only to a document that does not exist,
        # and it skips rather than passes, so a recording run still says out loud
        # which positive it has yet to account for.
        for model in sorted(FIXTURES.glob("*.rebeca")):
            with self.subTest(fixture=model.stem):
                document = model.with_suffix(".parser.json")

                if RECORDING and not document.is_file():
                    self.skipTest(
                        model.stem + " has no expected document yet; this run"
                        " is the one recording it"
                    )

                self.assertTrue(
                    document.is_file(),
                    model.stem + " has no expected document; run the gate with"
                    " --record, then review what it wrote",
                )

    def test_provenance_covers_exactly_the_positives(self) -> None:
        # ANCHORS, RECORDED and HAND_AUTHORED_PENDING_EXPORTER partition the
        # positives. If a model is added and assigned to none of them, its
        # provenance is undocumented and the anti-circularity argument in the
        # README no longer describes the corpus.
        declared = (
            set(ANCHORS)
            | set(RECORDED)
            | set(HAND_AUTHORED_PENDING_EXPORTER)
        )

        self.assertEqual(
            len(declared),
            len(ANCHORS) + len(RECORDED)
            + len(HAND_AUTHORED_PENDING_EXPORTER),
            "a fixture is listed in two provenance lists",
        )

        present = {model.stem for model in FIXTURES.glob("*.rebeca")}

        self.assertEqual(
            present,
            declared,
            "the positives on disk and the declared provenance disagree",
        )

    def test_the_readme_names_every_positive(self) -> None:
        readme = FIXTURES / "README.md"

        self.assertTrue(readme.is_file(), "fixtures/general/README.md is missing")

        text = readme.read_text(encoding="utf-8")

        for name in sorted(
            set(ANCHORS)
            | set(RECORDED)
            | set(HAND_AUTHORED_PENDING_EXPORTER)
        ):
            with self.subTest(fixture=name):
                self.assertIn(
                    name,
                    text,
                    name + " is not mentioned in the fixtures README, so a"
                    " reader has no way to learn where its expected document"
                    " came from",
                )


if __name__ == "__main__":
    unittest.main()
