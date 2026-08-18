#!/usr/bin/env python3
"""Adversarial tests for ``frontend/compare_general_v1.py``.

The comparator carries the load-bearing claim of the whole stage-A fixture
scheme: that recording an expected document from the tool under test is not
circular, because line-number differences and structural differences are sorted
into separate buckets and only the first kind can ever be accepted wholesale.
If ``--accept-lines`` could be talked into rewriting an expected document while
a structural difference remained, every recorded fixture would become a
tautology. That single property is what the ``AcceptLinesCannotRubberStamp``
class below exists to pin.

The other half of the file pins type-awareness. Python holds ``True == 1``, so
the naive ``json.loads(a) == json.loads(b)`` comparison used by the three older
frontend checks cannot tell an integer literal from a boolean one -- and
``general-v1`` files both under the same ``value`` key. See
``frontend/fixtures/general/README.md``.

Tests drive ``main`` in process against temporary files rather than shelling
out, so a non-zero exit is observed as a return value and stdout is captured
rather than printed. Run it standalone, following the convention of the other
tests in this repository::

    python3 frontend/test_compare_general_v1.py
"""

from __future__ import annotations

import contextlib
import copy
import importlib.util
import io
import json
import pathlib
import sys
import tempfile
import unittest


FRONTEND = pathlib.Path(__file__).resolve().parent

FIXTURES = FRONTEND / "fixtures" / "general"

COMPARATOR_SOURCE = FRONTEND / "compare_general_v1.py"

# The base document for every scenario is a real committed anchor rather than a
# bespoke one, so the paths the tests mutate are paths the exporter will really
# emit -- in particular, real `.line` fields at real depths.
BASE_ANCHOR = "keep-alive"


def load_comparator():
    """Import the comparator by path; it is a script, not an installed module."""
    # Importing it would otherwise leave a frontend/__pycache__ behind. This
    # repository does not gitignore __pycache__, so tools/__pycache__ is a
    # standing nuisance that every gate has to remember to exclude from a
    # commit; there is no reason to create a second one.
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True

    try:
        specification = importlib.util.spec_from_file_location(
            "relico_compare_general_v1_under_test",
            COMPARATOR_SOURCE,
        )

        if specification is None or specification.loader is None:
            raise RuntimeError("could not load " + str(COMPARATOR_SOURCE))

        module = importlib.util.module_from_spec(specification)
        sys.modules[specification.name] = module
        specification.loader.exec_module(module)

        return module
    finally:
        sys.dont_write_bytecode = previous


COMPARATOR = load_comparator()


def load_validator_for_composition_check():
    """Load the schema validator, for the one test that needs both.

    The comparator does not depend on the validator; ``check-general.sh``
    composes them. One test asserts a property of that composition, and loading
    the validator lazily keeps the dependency confined to it.
    """
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True

    try:
        specification = importlib.util.spec_from_file_location(
            "relico_validate_general_v1_for_composition_check",
            FRONTEND / "validate_general_v1.py",
        )

        if specification is None or specification.loader is None:
            raise RuntimeError("could not load the general-v1 validator")

        module = importlib.util.module_from_spec(specification)
        sys.modules[specification.name] = module
        specification.loader.exec_module(module)

        return module
    finally:
        sys.dont_write_bytecode = previous


# SECTION: harness


def anchor(name: str = BASE_ANCHOR) -> dict:
    path = FIXTURES / (name + ".parser.json")

    return json.loads(path.read_text(encoding="utf-8"))


def canonical(document: object) -> str:
    return json.dumps(document, indent=2, sort_keys=True) + "\n"


class Scenario:
    """A temporary directory holding an expected and an actual document.

    ``expected`` may be ``None``, which is how the not-yet-recorded case is
    expressed: the file is simply never written.
    """

    def __init__(self, expected: object, actual: object) -> None:
        self.directory = tempfile.TemporaryDirectory(
            prefix="relico-compare-test."
        )

        root = pathlib.Path(self.directory.name)

        self.expected_path = root / (BASE_ANCHOR + ".parser.json")
        self.actual_path = root / "actual.json"

        if expected is not None:
            self.expected_path.write_text(canonical(expected), encoding="utf-8")

        self.actual_path.write_text(canonical(actual), encoding="utf-8")

    def expected_text(self) -> str:
        return self.expected_path.read_text(encoding="utf-8")

    def run(self, *options: str) -> tuple[int, str]:
        """Call ``main`` in process, capturing both streams together."""
        argv = ["compare_general_v1.py"]
        argv.extend(options)
        argv.append(str(self.expected_path))
        argv.append(str(self.actual_path))

        captured = io.StringIO()

        with contextlib.redirect_stdout(captured):
            with contextlib.redirect_stderr(captured):
                status = COMPARATOR.main(argv)

        return status, captured.getvalue()

    def __enter__(self) -> "Scenario":
        return self

    def __exit__(self, *unused: object) -> None:
        self.directory.cleanup()


def first_message_server(document: dict) -> dict:
    return document["classes"][0]["messageServers"][0]



# SECTION: identical


class IdenticalDocumentsMatch(unittest.TestCase):
    def test_the_anchor_matches_itself(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.IDENTICAL)
        self.assertIn("matches", output)

    def test_a_matching_expected_document_is_left_alone(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            before = scenario.expected_text()
            scenario.run()

            self.assertEqual(scenario.expected_text(), before)

    def test_a_non_canonical_expected_document_is_reformatted(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            # Same content, stored badly: compact, unsorted, no trailing
            # newline. A gate that reported this as a difference would be
            # useless; one that reported it as "matches" and left it alone
            # would let the repository drift out of canonical form, which
            # test_validate_general_v1.py separately forbids.
            scenario.expected_path.write_text(
                json.dumps(anchor(), separators=(",", ":")),
                encoding="utf-8",
            )

            status, output = scenario.run()

            self.assertEqual(status, COMPARATOR.IDENTICAL)
            self.assertIn("not stored canonically", output)
            self.assertEqual(scenario.expected_text(), canonical(anchor()))

    def test_agreeing_walk_but_disagreeing_bytes_is_a_reported_defect(
        self,
    ) -> None:
        # If the walk finds no difference, the two documents must serialize
        # identically; otherwise `compare` has a hole and the gate would print
        # "matches" over a real difference. The only input that reaches this
        # today is negative zero -- `type(-0.0) is type(0.0)` and
        # `-0.0 == 0.0`, yet json.dumps writes `-0.0` and `0.0`. `general-v1`
        # has no float anywhere, so this is a guard rather than a live case,
        # and it must fail closed rather than fail quiet.
        expected = anchor()
        actual = copy.deepcopy(expected)

        first_message_server(expected)["line"] = -0.0
        first_message_server(actual)["line"] = 0.0

        with Scenario(expected, actual) as scenario:
            before = scenario.expected_text()
            status, output = scenario.run()

            self.assertEqual(status, COMPARATOR.STRUCTURAL)
            self.assertIn("defect in compare_general_v1.py", output)
            self.assertEqual(scenario.expected_text(), before)




# SECTION: separation


class LineDifferencesAreSeparatedFromStructure(unittest.TestCase):
    def test_a_line_only_difference_exits_two(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["line"] = expected["classes"][0]["line"] + 40

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.LINES_ONLY)
        self.assertIn("LINE-NUMBER differences (1)", output)
        self.assertNotIn("STRUCTURAL", output)

    def test_a_nested_line_only_difference_exits_two(self) -> None:
        # Line fields appear at every depth, so the suffix test must work on a
        # deep path and not just on a top-level one.
        expected = anchor()
        actual = copy.deepcopy(expected)

        body = first_message_server(actual)["body"]

        self.assertTrue(body, "the anchor's first msgsrv must have a body")

        body[0]["line"] = body[0]["line"] + 7

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.LINES_ONLY)
        self.assertIn(".body[0].line", output)

    def test_a_structural_difference_exits_one(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["queueBound"] = 99

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("STRUCTURAL differences (1)", output)
        self.assertIn("queueBound", output)

    def test_a_field_merely_named_like_a_line_is_still_structural(self) -> None:
        # The separation is by exact path suffix `.line`, not by substring. A
        # value called `deadline` or `lines` must never be waved through.
        expected = anchor()
        actual = copy.deepcopy(expected)

        expected["classes"][0]["deadline"] = 3
        actual["classes"][0]["deadline"] = 4

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("deadline", output)

    def test_both_kinds_at_once_report_both_and_exit_one(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["line"] = 42
        actual["classes"][0]["queueBound"] = 99

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("STRUCTURAL differences (1)", output)
        self.assertIn("LINE-NUMBER differences (1)", output)
        self.assertIn("--accept-lines refuses", output)

    def test_a_missing_key_is_structural(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        del actual["classes"][0]["queueBound"]

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("missing from actual", output)

    def test_an_extra_key_is_structural(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["surprise"] = 1

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("present in actual, not expected", output)

    def test_null_against_a_value_is_structural(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["constructor"] = None

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("null", output)



# SECTION: accept-lines


class AcceptLinesCannotRubberStamp(unittest.TestCase):
    """The keystone of the anti-circularity argument.

    Recording an expected document from the tool under test is defensible only
    because the *structure* of that document was pinned in advance by a
    hand-authored anchor and cannot be re-recorded away. If ``--accept-lines``
    ever adopted an actual document while a structural difference remained, a
    structural regression could be laundered into the expected fixture and the
    gate would go green on it forever.
    """

    def test_it_adopts_a_line_only_difference(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["line"] = 42

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run("--accept-lines")

            self.assertEqual(status, COMPARATOR.IDENTICAL)
            self.assertIn("accepted 1 line-number correction", output)
            self.assertEqual(scenario.expected_text(), canonical(actual))
            self.assertEqual(
                json.loads(scenario.expected_text())["classes"][0]["line"],
                42,
            )

    def test_it_refuses_while_a_structural_difference_remains(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["line"] = 42
        actual["classes"][0]["queueBound"] = 99

        with Scenario(expected, actual) as scenario:
            before = scenario.expected_text()
            status, output = scenario.run("--accept-lines")

            self.assertEqual(status, COMPARATOR.STRUCTURAL)
            self.assertIn("refuses", output)
            # The assertion that matters: not one byte was written.
            self.assertEqual(scenario.expected_text(), before)

    def test_a_structural_difference_alone_is_not_accepted(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["queueBound"] = 99

        with Scenario(expected, actual) as scenario:
            before = scenario.expected_text()
            status, _ = scenario.run("--accept-lines")

            self.assertEqual(status, COMPARATOR.STRUCTURAL)
            self.assertEqual(scenario.expected_text(), before)

    def test_it_writes_nothing_when_there_is_nothing_to_accept(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            before = scenario.expected_text()
            status, _ = scenario.run("--accept-lines")

            self.assertEqual(status, COMPARATOR.IDENTICAL)
            self.assertEqual(scenario.expected_text(), before)

    def test_accepting_lines_changes_only_line_fields(self) -> None:
        # The soundness claim written in the comparator's own comment: after an
        # --accept-lines run the expected document differs from what it was in
        # `line` fields alone. Checked by stripping every `line` from both and
        # requiring the remainder to be untouched.
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["line"] = 42
        first_message_server(actual)["line"] = 43

        with Scenario(expected, actual) as scenario:
            scenario.run("--accept-lines")
            written = json.loads(scenario.expected_text())

        self.assertEqual(strip_lines(written), strip_lines(expected))
        self.assertNotEqual(written, expected)


def strip_lines(node: object) -> object:
    """A deep copy with every ``line`` key removed at every depth."""
    if isinstance(node, dict):
        return {
            key: strip_lines(value)
            for key, value in node.items()
            if key != "line"
        }

    if isinstance(node, list):
        return [strip_lines(element) for element in node]

    return node



# SECTION: recording


class RecordingRequiresOptIn(unittest.TestCase):
    def test_a_missing_expected_document_exits_three(self) -> None:
        with Scenario(None, anchor()) as scenario:
            status, output = scenario.run()

            self.assertEqual(status, COMPARATOR.NOT_RECORDED)
            self.assertIn("rerun with --record", output)
            self.assertFalse(
                scenario.expected_path.exists(),
                "a plain comparison must never create an expected document",
            )

    def test_record_writes_the_document_canonically(self) -> None:
        with Scenario(None, anchor()) as scenario:
            status, output = scenario.run("--record")

            self.assertEqual(status, COMPARATOR.IDENTICAL)
            self.assertIn("REVIEW IT BEFORE COMMIT", output)
            self.assertEqual(scenario.expected_text(), canonical(anchor()))

    def test_record_does_not_overwrite_an_existing_document(self) -> None:
        # --record is for the first run of a new fixture only. Left able to
        # overwrite, it would be a one-flag laundering route for exactly the
        # structural regression --accept-lines refuses to launder.
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["queueBound"] = 99

        with Scenario(expected, actual) as scenario:
            before = scenario.expected_text()
            status, _ = scenario.run("--record")

            self.assertEqual(status, COMPARATOR.STRUCTURAL)
            self.assertEqual(scenario.expected_text(), before)

    def test_record_does_not_absorb_line_differences_either(self) -> None:
        # The two flags are distinct: --record is not a superset of
        # --accept-lines, so a stale expected document still has to be accepted
        # deliberately.
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["line"] = 42

        with Scenario(expected, actual) as scenario:
            before = scenario.expected_text()
            status, _ = scenario.run("--record")

            self.assertEqual(status, COMPARATOR.LINES_ONLY)
            self.assertEqual(scenario.expected_text(), before)

    def test_a_recorded_document_then_matches_itself(self) -> None:
        with Scenario(None, anchor()) as scenario:
            scenario.run("--record")
            status, _ = scenario.run()

            self.assertEqual(status, COMPARATOR.IDENTICAL)


# SECTION: type-awareness


class TypesAreDistinguished(unittest.TestCase):
    """The `True == 1` hole, which is live for ``general-v1``.

    ``general-v1`` puts an integer literal's payload and a boolean literal's
    payload under the same ``value`` key, so a `boolLiteral`/`intLiteral`
    confusion in the exporter shows up as `true` where `1` was expected. Under
    ``json.loads(a) == json.loads(b)`` -- what the three older frontend checks
    use -- that comparison comes back *equal*.
    """

    def test_python_really_does_hold_true_equal_to_one(self) -> None:
        # Stated as an assertion rather than a comment so that the reason this
        # whole class exists is executable.
        self.assertEqual(1, True)
        self.assertEqual(0, False)
        self.assertEqual({"value": 1}, {"value": True})

    def test_an_integer_one_is_not_a_boolean_true(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        expected["classes"][0]["queueBound"] = 1
        actual["classes"][0]["queueBound"] = True

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("expected integer 1", output)
        self.assertIn("found boolean True", output)

    def test_an_integer_zero_is_not_a_boolean_false(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        expected["classes"][0]["queueBound"] = 0
        actual["classes"][0]["queueBound"] = False

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("expected integer 0", output)
        self.assertIn("found boolean False", output)

    def test_a_confused_literal_payload_is_caught_in_place(self) -> None:
        # The same confusion where it would really occur: inside a literal node
        # in a message-server body.
        expected = anchor()
        actual = copy.deepcopy(expected)

        for document, payload in ((expected, 1), (actual, True)):
            first_message_server(document)["body"].append(
                {
                    "kind": "assign",
                    "line": 999,
                    "target": {"kind": "variable", "name": "x", "line": 999},
                    "value": {"kind": "intLiteral", "value": payload,
                              "line": 999},
                }
            )

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("boolean True", output)

    def test_a_boolean_line_is_forgiven_here_but_caught_upstream(self) -> None:
        # Honest about a real gap. The buckets are chosen by path suffix before
        # anything is known about type, so a `line` holding `true` lands in the
        # forgivable bucket and --accept-lines would adopt it.
        #
        # That is safe only as a composition: check-general.sh runs
        # validate_general_v1.py *before* the comparator, and the validator
        # requires every line to be a positive integer and explicitly excludes
        # bool. So the document never reaches the comparator. The claim is
        # asserted rather than merely commented, because it is the only reason
        # this gap is acceptable.
        expected = anchor()
        actual = copy.deepcopy(expected)

        expected["classes"][0]["line"] = 1
        actual["classes"][0]["line"] = True

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.LINES_ONLY)
        self.assertIn("found boolean True", output)

        validator = load_validator_for_composition_check()
        report = validator.Report()
        validator.validate(actual, report)

        self.assertTrue(
            report.violations,
            "the validator must reject a boolean line, or the comparator's"
            " path-suffix bucketing becomes unsound",
        )
        self.assertTrue(
            any("line must be" in violation for violation in report.violations),
            "expected the validator's own line-type diagnostic, found "
            + repr(report.violations),
        )


    def test_a_string_is_not_an_integer(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["queueBound"] = str(
            expected["classes"][0]["queueBound"]
        )

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("string", output)



# SECTION: order


class ListOrderAndLengthAreStructural(unittest.TestCase):
    """List order carries semantics here and is never normalized away.

    Reaction declaration order decides same-tag firing order in the Lingua
    Franca target, and binding order decides the topology, so a reordered list
    is a different model -- not a formatting difference.
    """

    def test_a_length_mismatch_is_structural(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["messageServers"].append(
            copy.deepcopy(first_message_server(actual))
        )

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("elements, found", output)

    def test_a_length_mismatch_is_structural_even_under_a_line_path(
        self,
    ) -> None:
        # A list can never be forgiven as a line difference, whatever it is
        # called, because the bucketing only ever applies to scalars.
        expected = anchor()
        actual = copy.deepcopy(expected)

        expected["classes"][0]["line"] = [1, 2]
        actual["classes"][0]["line"] = [1]

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("expected 2 elements, found 1", output)

    def test_a_reordered_list_is_structural(self) -> None:
        # `control-flow` rather than the usual base anchor: it is the one anchor
        # that declares two message servers, and swapping them is the mutation
        # that matters most here. Reaction declaration order is what decides
        # same-tag firing order downstream, so a comparator that normalized
        # list order would hide a real semantic change.
        expected = anchor("control-flow")

        servers = expected["classes"][0]["messageServers"]

        self.assertEqual(
            len(servers),
            2,
            "control-flow is expected to declare exactly two message servers;"
            " if that changed, this test needs a new base",
        )

        actual = copy.deepcopy(expected)
        actual["classes"][0]["messageServers"] = list(reversed(servers))

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("messageServers[0].name", output)

    def test_a_list_against_a_scalar_is_structural(self) -> None:
        expected = anchor()
        actual = copy.deepcopy(expected)

        actual["classes"][0]["messageServers"] = 3

        with Scenario(expected, actual) as scenario:
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("integer 3", output)


# SECTION: errors


class BadInvocationsExitOne(unittest.TestCase):
    """Every failure route must be non-zero, so no gate can mistake it for ok."""

    def test_an_unknown_option(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            status, output = scenario.run("--pretty-please")

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("unknown option", output)

    def test_too_few_arguments(self) -> None:
        captured = io.StringIO()

        with contextlib.redirect_stdout(captured):
            with contextlib.redirect_stderr(captured):
                status = COMPARATOR.main(["compare_general_v1.py", "only-one"])

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("usage:", captured.getvalue())

    def test_a_missing_actual_document(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            scenario.actual_path.unlink()
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("cannot read", output)

    def test_a_malformed_actual_document(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            scenario.actual_path.write_text("{ not json", encoding="utf-8")
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("cannot read", output)

    def test_a_malformed_expected_document(self) -> None:
        with Scenario(anchor(), anchor()) as scenario:
            scenario.expected_path.write_text("{ not json", encoding="utf-8")
            status, output = scenario.run()

        self.assertEqual(status, COMPARATOR.STRUCTURAL)
        self.assertIn("cannot read", output)

    def test_a_malformed_expected_document_is_not_overwritten_by_record(
        self,
    ) -> None:
        # The file exists, so --record must not treat it as unrecorded. A
        # corrupt fixture is a thing for a human to look at, not something to
        # quietly replace with whatever the tool under test just produced.
        with Scenario(anchor(), anchor()) as scenario:
            scenario.expected_path.write_text("{ not json", encoding="utf-8")
            status, _ = scenario.run("--record")

            self.assertEqual(status, COMPARATOR.STRUCTURAL)
            self.assertEqual(scenario.expected_text(), "{ not json")


class ExitCodesAreDistinct(unittest.TestCase):
    def test_the_four_outcomes_have_four_codes(self) -> None:
        codes = (
            COMPARATOR.IDENTICAL,
            COMPARATOR.STRUCTURAL,
            COMPARATOR.LINES_ONLY,
            COMPARATOR.NOT_RECORDED,
        )

        self.assertEqual(len(set(codes)), 4)
        self.assertEqual(COMPARATOR.IDENTICAL, 0)
        # check-general.sh switches on these three by literal number.
        self.assertEqual(COMPARATOR.STRUCTURAL, 1)
        self.assertEqual(COMPARATOR.LINES_ONLY, 2)
        self.assertEqual(COMPARATOR.NOT_RECORDED, 3)



if __name__ == "__main__":
    unittest.main(verbosity=2)
