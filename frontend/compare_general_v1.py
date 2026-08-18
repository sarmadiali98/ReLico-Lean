#!/usr/bin/env python3
"""Compare an emitted ``general-v1`` document against its expected fixture.

Structural differences and line-number differences are reported **separately**,
and only line-number differences can be accepted wholesale. That separation is
the reason recording an expected document from the tool under test is not
circular here: parser line numbers cannot be predicted from a machine with no
Java compiler on it, but structure can, and structure is what the four
hand-authored anchors pin. A structural mismatch must never be resolvable by
re-recording.

Comparison is type-aware, and deliberately not ``json.loads`` equality. Python
holds ``True == 1``, so a document whose integer literal ``1`` was emitted as
``true`` compares equal under ``==`` while differing in the emitted JSON.
``general-v1`` puts boolean and integer literal payloads under the same
``value`` key, so that confusion is reachable. See
``frontend/fixtures/general/README.md``.

Usage::

    compare_general_v1.py <expected.json> <actual.json>
    compare_general_v1.py --record <expected.json> <actual.json>
    compare_general_v1.py --accept-lines <expected.json> <actual.json>

Exit codes are distinct so a caller can act on them:

    0   identical
    1   structural differences, or a usage or file error
    2   line-number differences only
    3   no expected document exists yet and --record was not given
"""

from __future__ import annotations

import json
import pathlib
import sys

IDENTICAL = 0
STRUCTURAL = 1
LINES_ONLY = 2
NOT_RECORDED = 3


def canonical(document: object) -> str:
    """The exact serialization every committed fixture is stored in."""
    return json.dumps(document, indent=2, sort_keys=True) + "\n"


def describe(value: object) -> str:
    if isinstance(value, bool):
        # Spelled out because `1` and `True` render identically to a reader
        # skimming a diff, and telling them apart is the point.
        return "boolean " + repr(value)

    if isinstance(value, int):
        return "integer " + repr(value)

    if isinstance(value, str):
        return "string " + repr(value)

    if value is None:
        return "null"

    return type(value).__name__ + " " + repr(value)


def compare(
    expected: object,
    actual: object,
    path: str,
    structural: list[str],
    lines: list[str],
) -> None:
    """Walk both documents together, sorting each difference into one bucket."""
    if isinstance(expected, dict) and isinstance(actual, dict):
        for key in sorted(set(expected) - set(actual)):
            structural.append(path + "." + key + ": missing from actual")

        for key in sorted(set(actual) - set(expected)):
            structural.append(
                path + "." + key + ": present in actual, not expected"
            )

        for key in sorted(set(expected) & set(actual)):
            compare(
                expected[key], actual[key], path + "." + key, structural, lines
            )

        return

    if isinstance(expected, list) and isinstance(actual, list):
        if len(expected) != len(actual):
            # Never a line difference: list order and length carry meaning here
            # (declaration order decides same-tag firing order, binding order
            # decides the topology), so a length change is always structural.
            structural.append(
                path + ": expected " + str(len(expected))
                + " elements, found " + str(len(actual))
            )

        for index in range(min(len(expected), len(actual))):
            compare(
                expected[index],
                actual[index],
                path + "[" + str(index) + "]",
                structural,
                lines,
            )

        return

    if isinstance(expected, (dict, list)) or isinstance(actual, (dict, list)):
        structural.append(
            path + ": expected " + describe(expected)
            + ", found " + describe(actual)
        )

        return

    # Scalars. `type(...) is not type(...)` is what separates 1 from True.
    if type(expected) is type(actual) and expected == actual:
        return

    difference = (
        path + ": expected " + describe(expected)
        + ", found " + describe(actual)
    )

    if path.endswith(".line"):
        lines.append(difference)
    else:
        structural.append(difference)


def report(label: str, differences: list[str]) -> None:
    print(label + " (" + str(len(differences)) + "):")

    for difference in differences:
        print("  " + difference)


def main(argv: list[str]) -> int:
    mode = "compare"
    arguments = list(argv[1:])

    while arguments and arguments[0].startswith("--"):
        flag = arguments.pop(0)

        if flag == "--record":
            mode = "record"
        elif flag == "--accept-lines":
            mode = "accept-lines"
        else:
            print("unknown option " + flag, file=sys.stderr)

            return STRUCTURAL

    if len(arguments) != 2:
        print(
            "usage: compare_general_v1.py [--record|--accept-lines] "
            "<expected.json> <actual.json>",
            file=sys.stderr,
        )

        return STRUCTURAL

    expected_path = pathlib.Path(arguments[0])
    actual_path = pathlib.Path(arguments[1])

    try:
        actual = json.loads(actual_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print("cannot read " + str(actual_path) + ": " + str(error))

        return STRUCTURAL

    if not expected_path.exists():
        if mode != "record":
            print(
                "no expected document at " + expected_path.name
                + "; rerun with --record to write one, then review it"
            )

            return NOT_RECORDED

        expected_path.write_text(canonical(actual), encoding="utf-8")
        print("recorded " + expected_path.name + " — REVIEW IT BEFORE COMMIT")

        return IDENTICAL

    try:
        expected_text = expected_path.read_text(encoding="utf-8")
        expected = json.loads(expected_text)
    except (OSError, json.JSONDecodeError) as error:
        print("cannot read " + str(expected_path) + ": " + str(error))

        return STRUCTURAL

    structural: list[str] = []
    lines: list[str] = []

    compare(expected, actual, "", structural, lines)

    if not structural and not lines:
        if canonical(expected) != canonical(actual):
            # The walk found no difference, yet the two documents do not
            # serialize alike. That is a hole in `compare` above, not a problem
            # with the fixture, and swallowing it would let a real difference
            # through under a "matches" banner -- exactly the failure mode the
            # `True == 1` hole is. Report it and fail.
            print(
                expected_path.name
                + ": the comparison found no difference, but the two documents"
                + " do not serialize identically. That is a defect in"
                + " compare_general_v1.py itself, not in the fixture."
            )

            return STRUCTURAL

        if expected_text != canonical(expected):
            # A committed fixture that is not stored in canonical form. This is
            # pure reformatting, so `expected` is what gets rewritten, not
            # `actual`: that makes the rewrite provably content-preserving.
            print(
                expected_path.name
                + " matches but is not stored canonically; reformatting"
            )
            expected_path.write_text(canonical(expected), encoding="utf-8")

        print(expected_path.name + ": matches")

        return IDENTICAL

    if structural:
        report("STRUCTURAL differences", structural)

    if lines:
        report("LINE-NUMBER differences", lines)

    if structural:
        print()
        print(
            "Structural differences are never acceptable and --accept-lines "
            "refuses to run while any remain."
        )

        return STRUCTURAL

    if mode == "accept-lines":
        # Sound only because there are no structural differences: the actual
        # document then differs from the expected one in `line` fields alone,
        # so adopting it wholesale rewrites nothing else.
        expected_path.write_text(canonical(actual), encoding="utf-8")
        print()
        print("accepted " + str(len(lines)) + " line-number correction(s) in "
              + expected_path.name)

        return IDENTICAL

    print()
    print(
        "Line numbers only. If the source model was edited, rerun with "
        "--accept-lines."
    )

    return LINES_ONLY


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
