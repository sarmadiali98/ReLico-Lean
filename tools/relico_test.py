#!/usr/bin/env python3

from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from typing import Sequence
import argparse
import csv
import json
import os
import shutil
import subprocess
import sys
import time
import unittest
import xml.etree.ElementTree as ET


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
RESULTS_ROOT = REPOSITORY_ROOT / ".test-results"
PYTHON_PATTERNS = (
    "tools/test_*.py",
    "tests/test_*.py",
    "frontend/test_*.py",
)
DIRECT_LEAN_MODULES = {
    "Relico/Tests/FrontendDecoder.lean",
    "Relico/Tests/Translation.lean",
    "frontend/lean-bridge/GeneralFocusedTestMain.lean",
}


@dataclass(frozen=True)
class TestCase:
    test_id: str
    suite: str
    family: str
    layer: str
    polarity: str
    tags: tuple[str, ...]
    command: tuple[str, ...]
    cwd: Path = REPOSITORY_ROOT
    tier: str = "unit"
    provider: str = "unknown"
    logical: bool = True
    prerequisite_env: str = ""


@dataclass(frozen=True)
class TestResult:
    test_id: str
    suite: str
    family: str
    layer: str
    polarity: str
    status: str
    duration_ms: int
    exit_code: int
    command: list[str]
    stdout_path: str
    stderr_path: str
    message: str = ""
    tier: str = "unit"
    provider: str = "unknown"
    logical: bool = True
    reason_code: str = ""


def discover_python_modules() -> list[Path]:
    modules: set[Path] = set()

    for pattern in PYTHON_PATTERNS:
        modules.update(REPOSITORY_ROOT.glob(pattern))

    return sorted(path for path in modules if path.is_file())


def discover_python_cases() -> list[TestCase]:
    cases: list[TestCase] = []
    loader = unittest.TestLoader()

    for module_path in discover_python_modules():
        relative = module_path.relative_to(REPOSITORY_ROOT)
        directory = str(module_path.parent)
        discovered = loader.discover(
            start_dir=directory,
            pattern=module_path.name,
            top_level_dir=directory,
        )

        for suite in discovered:
            for nested in suite:
                for test in iter_unittest_cases(nested):
                    method = getattr(test, test._testMethodName)
                    tags = tuple(
                        sorted(set(getattr(method, "relico_tags", ())))
                    )
                    identifier = (
                        f"python::{relative.as_posix()}::"
                        f"{test.__class__.__name__}::{test._testMethodName}"
                    )
                    cases.append(TestCase(
                        test_id=identifier,
                        suite="python",
                        family="harness",
                        layer="contract",
                        polarity=(
                            "negative" if "negative" in tags else "positive"
                        ),
                        tags=("fast", "unit", *tags),
                        command=(
                            sys.executable,
                            str(module_path),
                            f"{test.__class__.__name__}.{test._testMethodName}",
                        ),
                        tier="unit",
                        provider="python",
                    ))

    return cases


def iter_unittest_cases(suite: unittest.TestSuite):
    for test in suite:
        if isinstance(test, unittest.TestSuite):
            yield from iter_unittest_cases(test)
        else:
            yield test


def discover_lean_case() -> TestCase:
    return TestCase(
        test_id="lean::RelicoTests",
        suite="lean",
        family="all",
        layer="unit-and-formal",
        polarity="mixed",
        tags=("fast", "lean", "unit", "formal"),
        command=("lake", "build", "RelicoTests"),
        tier="formal",
        provider="lean-aggregate",
        logical=False,
    )


def discover_catalog_case() -> TestCase:
    return TestCase(
        test_id="catalog::translator-tests",
        suite="catalog",
        family="all",
        layer="catalog-integrity",
        polarity="mixed",
        tags=("fast", "catalog"),
        command=(sys.executable, "tests/catalog/validate_catalog.py"),
        tier="catalog",
        provider="catalog-validator",
        logical=False,
    )


def load_behavioral_coverage() -> list[dict[str, str]]:
    path = (
        REPOSITORY_ROOT
        / "evaluation"
        / "registry"
        / "behavioral-coverage.tsv"
    )
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def load_direct_software_cases() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    root = REPOSITORY_ROOT / "tests" / "translator"

    for path in sorted(root.glob("*--software/cases.tsv")):
        with path.open(encoding="utf-8", newline="") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                rows.append({**row, "catalog": str(path.relative_to(REPOSITORY_ROOT))})

    return rows


def discover_lean_software_cases() -> list[TestCase]:
    catalogs = {
        row["case_id"]: row
        for row in load_direct_software_cases()
    }
    cases: list[TestCase] = []
    for row in load_behavioral_coverage():
        if row["test_module"] not in DIRECT_LEAN_MODULES:
            continue
        if row["feature_id"] not in catalogs:
            continue
        command = (
            (
                "/bin/bash",
                str(REPOSITORY_ROOT / "frontend" / "run-general-focused-test.sh"),
                row["test_value"],
            )
            if row["test_module"] == "frontend/lean-bridge/GeneralFocusedTestMain.lean"
            else (
                "lake",
                "exe",
                "relico-translator-test",
                row["test_value"],
            )
        )
        cases.append(TestCase(
            test_id=f"lean-case::{row['feature_id']}",
            suite="lean",
            family=row["family"],
            layer=row["layer"],
            polarity=row["polarity"],
            tags=("fast", "lean", "unit", row["polarity"]),
            command=command,
            tier="unit",
            provider="lean-focused",
        ))
    return cases


def discover_fixture_cases() -> list[TestCase]:
    registry_path = (
        REPOSITORY_ROOT / "evaluation" / "registry" / "benchmarks.tsv"
    )

    with registry_path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))

    return [
        TestCase(
            test_id=f"fixture::{row['benchmark_id']}",
            suite="integration",
            family=row["semantic_layer"],
            layer=row["primary_capability"],
            polarity=row["polarity"],
            tags=(
                "fixture",
                "integration",
                "external-toolchain",
                row["polarity"],
            ),
            command=(
                "/bin/bash",
                str(REPOSITORY_ROOT / "tools" / "relico_bench.sh"),
                "--benchmark",
                row["benchmark_id"],
            ),
            tier="integration",
            provider="translator-fixture",
        )
        for row in rows
        if (
            row["suite"] == "test"
            and row["implementation_status"] == "implemented"
        )
    ]


def discover_external_actor_priority_case() -> TestCase:
    case_root = (
        REPOSITORY_ROOT
        / "tests"
        / "translator"
        / "general--main-actor-priority--negative"
    )
    runner = case_root / "run-test.sh"
    return TestCase(
        test_id="fixture::general--main-actor-priority--negative",
        suite="integration",
        family="general",
        layer="actor-priority-frontend-boundary",
        polarity="negative",
        tags=(
            "fixture",
            "integration",
            "external-toolchain",
            "negative",
        ),
        command=(
            "/bin/bash",
            str(runner),
            os.environ.get("RELICO_PARSER_ARTIFACT", ""),
            str(RESULTS_ROOT / "legacy-actor-priority.json"),
        ),
        tier="external",
        provider="legacy-external",
        prerequisite_env="RELICO_PARSER_ARTIFACT",
    )


def discover_cases() -> list[TestCase]:
    external_case = discover_external_actor_priority_case()
    cases = [
        discover_catalog_case(),
        *discover_python_cases(),
        discover_lean_case(),
        *discover_lean_software_cases(),
        *discover_fixture_cases(),
        external_case,
    ]
    identifiers = [case.test_id for case in cases]

    if len(set(identifiers)) != len(identifiers):
        raise RuntimeError("duplicate test identifiers were discovered")

    return sorted(cases, key=lambda case: case.test_id)


def validate_behavioral_coverage() -> None:
    path = (
        REPOSITORY_ROOT
        / "evaluation"
        / "registry"
        / "behavioral-coverage.tsv"
    )
    rows = load_behavioral_coverage()

    required = {
        "feature_id",
        "family",
        "layer",
        "polarity",
        "test_module",
        "test_value",
        "status",
    }
    if not rows or set(rows[0]) != required:
        raise RuntimeError("behavioral coverage registry columns are invalid")

    identifiers = [row["feature_id"] for row in rows]
    if len(set(identifiers)) != len(identifiers):
        raise RuntimeError("duplicate behavioral feature identifiers exist")

    direct_rows = load_direct_software_cases()
    direct_identifiers = [row["case_id"] for row in direct_rows]
    if len(set(direct_identifiers)) != len(direct_identifiers):
        raise RuntimeError("duplicate direct translator case identifiers exist")

    expected_direct = {
        row["feature_id"]
        for row in rows
        if row["test_module"] in DIRECT_LEAN_MODULES
    }
    if set(direct_identifiers) != expected_direct:
        raise RuntimeError(
            "direct translator case catalogs differ from behavioral coverage"
        )

    for row in rows:
        feature = row["feature_id"]
        if row["polarity"] not in {"positive", "negative"}:
            raise RuntimeError(f"{feature}: invalid behavioral polarity")
        if row["status"] != "implemented":
            raise RuntimeError(f"{feature}: behavioral test is not implemented")
        module = REPOSITORY_ROOT / row["test_module"]
        if not module.is_file():
            raise RuntimeError(f"{feature}: behavioral test module is absent")
        test_value = row["test_value"]
        if test_value.startswith("fixture::"):
            available = (
                test_value == "fixture::general--main-actor-priority--negative"
                and (
                    REPOSITORY_ROOT
                    / "tests"
                    / "translator"
                    / "general--main-actor-priority--negative"
                ).is_dir()
            )
        else:
            available = test_value in module.read_text(encoding="utf-8")
        if not available:
            raise RuntimeError(f"{feature}: behavioral test value is absent")


def direct_translator_case_directories() -> list[Path]:
    root = REPOSITORY_ROOT / "tests" / "translator"
    return sorted(
        path
        for path in root.iterdir()
        if path.is_dir() and (path / "case.json").is_file()
    )


def parse_arguments(arguments: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="relico-test",
        description="Discover and execute ReLico software tests.",
    )
    parser.add_argument("--list", action="store_true")
    parser.add_argument(
        "--suite",
        action="append",
        choices=("catalog", "python", "lean", "integration"),
        help="select one or more suites; defaults to fast python and Lean tests",
    )
    parser.add_argument(
        "--tier",
        action="append",
        choices=("catalog", "unit", "formal", "integration", "external"),
        help="select one or more paper-facing test tiers",
    )
    parser.add_argument("--family", action="append")
    parser.add_argument("--layer", action="append")
    parser.add_argument(
        "--polarity",
        action="append",
        choices=("positive", "negative", "mixed"),
    )
    parser.add_argument("--tag", action="append")
    parser.add_argument("--case", action="append", dest="case_ids")
    parser.add_argument("--keep-going", action="store_true")
    parser.add_argument("--junit", action="store_true")
    return parser.parse_args(arguments)


def select_cases(
    cases: Sequence[TestCase],
    options: argparse.Namespace,
) -> list[TestCase]:
    requested_suites = set(options.suite or ())
    requested_tiers = set(getattr(options, "tier", None) or ())
    families = set(options.family or ())
    layers = set(options.layer or ())
    polarities = set(options.polarity or ())
    tags = set(options.tag or ())
    identifiers = set(options.case_ids or ())

    if not requested_suites and not requested_tiers and not identifiers:
        requested_tiers = {"catalog", "unit", "formal"}

    if identifiers:
        known = {case.test_id for case in cases}
        unknown = identifiers - known

        if unknown:
            raise RuntimeError(
                "unknown test identifiers: " + ", ".join(sorted(unknown))
            )

    return [
        case
        for case in cases
        if (
            (not requested_suites and not requested_tiers)
            or case.suite in requested_suites
            or case.tier in requested_tiers
        )
        and (not families or case.family in families)
        and (not layers or case.layer in layers)
        and (not polarities or case.polarity in polarities)
        and (not tags or tags.issubset(case.tags))
        and (not identifiers or case.test_id in identifiers)
    ]


def safe_result_name(identifier: str) -> str:
    slug = "".join(
        character if character.isalnum() or character in {"-", "_"} else "-"
        for character in identifier
    ).strip("-")[:80]
    return f"{slug}-{sha256(identifier.encode('utf-8')).hexdigest()[:12]}"


def report_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPOSITORY_ROOT))
    except ValueError:
        return str(path)


def run_case(case: TestCase) -> TestResult:
    case_root = RESULTS_ROOT / "cases" / safe_result_name(case.test_id)
    case_root.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()

    if case.prerequisite_env:
        value = os.environ.get(case.prerequisite_env, "")
        if not value or not Path(value).is_file():
            duration_ms = round((time.monotonic() - started) * 1000)
            stdout_path = case_root / "stdout.txt"
            stderr_path = case_root / "stderr.txt"
            message = f"missing required artifact: {case.prerequisite_env}"
            stdout_path.write_text("", encoding="utf-8")
            stderr_path.write_text(message + "\n", encoding="utf-8")
            return TestResult(
                test_id=case.test_id,
                suite=case.suite,
                family=case.family,
                layer=case.layer,
                polarity=case.polarity,
                status="unavailable",
                duration_ms=duration_ms,
                exit_code=127,
                command=list(case.command),
                stdout_path=report_path(stdout_path),
                stderr_path=report_path(stderr_path),
                message=message,
                tier=case.tier,
                provider=case.provider,
                logical=case.logical,
                reason_code=f"missing_environment_path:{case.prerequisite_env}",
            )

    try:
        completed = subprocess.run(
            case.command,
            cwd=case.cwd,
            text=True,
            capture_output=True,
            check=False,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        )
        exit_code = completed.returncode
        stdout = completed.stdout
        stderr = completed.stderr
        message = "" if exit_code == 0 else first_failure_line(stderr, stdout)
        status = "pass" if exit_code == 0 else "fail"
        reason_code = "" if exit_code == 0 else "nonzero_exit"
        if case.provider == "python" and exit_code == 0:
            combined = stdout + "\n" + stderr
            if "skipped=" in combined or " (skipped=" in combined:
                status = "skip"
                reason_code = "native_skip"
                message = first_failure_line(stderr, stdout)
    except FileNotFoundError as error:
        exit_code = 127
        stdout = ""
        stderr = str(error) + "\n"
        message = str(error)
        status = "unavailable"
        reason_code = "missing_executable"
    except OSError as error:
        exit_code = 126
        stdout = ""
        stderr = str(error) + "\n"
        message = str(error)
        status = "fail"
        reason_code = "launch_error"

    duration_ms = round((time.monotonic() - started) * 1000)
    stdout_path = case_root / "stdout.txt"
    stderr_path = case_root / "stderr.txt"
    stdout_path.write_text(stdout, encoding="utf-8")
    stderr_path.write_text(stderr, encoding="utf-8")

    return TestResult(
        test_id=case.test_id,
        suite=case.suite,
        family=case.family,
        layer=case.layer,
        polarity=case.polarity,
        status=status,
        duration_ms=duration_ms,
        exit_code=exit_code,
        command=list(case.command),
        stdout_path=report_path(stdout_path),
        stderr_path=report_path(stderr_path),
        message=message,
        tier=case.tier,
        provider=case.provider,
        logical=case.logical,
        reason_code=reason_code,
    )


def first_failure_line(*outputs: str) -> str:
    for output in outputs:
        for line in output.splitlines():
            if line.strip():
                return line.strip()
    return "test process exited nonzero"


def write_reports(
    discovered: Sequence[TestCase],
    selected: Sequence[TestCase],
    results: Sequence[TestResult],
) -> None:
    logical_results = sorted(
        (result for result in results if result.logical),
        key=lambda result: result.test_id,
    )
    gate_results = sorted(
        (result for result in results if not result.logical),
        key=lambda result: result.test_id,
    )
    statuses = ("pass", "fail", "skip", "unavailable")
    counts = {
        status: sum(result.status == status for result in logical_results)
        for status in statuses
    }
    payload = {
        "schema_version": 2,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "discovered_logical_case_count": sum(case.logical for case in discovered),
        "selected_logical_case_count": len(logical_results),
        "counts": counts,
        "gate_counts": {
            status: sum(result.status == status for result in gate_results)
            for status in statuses
        },
        "overall_status": (
            "fail" if counts["fail"] or any(r.status == "fail" for r in gate_results)
            else "unavailable" if counts["unavailable"] else "pass"
        ),
        "artifacts": {
            "cases": ".test-results/cases.jsonl",
            "stages": ".test-results/stages.jsonl",
            "coverage_matrix": ".test-results/coverage-matrix.tsv",
            "environment": ".test-results/environment.json",
            "junit": ".test-results/junit.xml",
        },
    }
    summary = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    (RESULTS_ROOT / "summary.json").write_text(summary, encoding="utf-8")
    (RESULTS_ROOT / "results.json").write_text(summary, encoding="utf-8")

    (RESULTS_ROOT / "cases.jsonl").write_text(
        "".join(json.dumps(asdict(result), sort_keys=True) + "\n" for result in logical_results),
        encoding="utf-8",
    )
    (RESULTS_ROOT / "stages.jsonl").write_text(
        "".join(
            json.dumps({
                "schema_version": 1,
                "owner_kind": "case" if result.logical else "gate",
                "owner_id": result.test_id,
                "stage_id": result.layer,
                "tier": result.tier,
                "status": result.status,
                "reason_code": result.reason_code,
                "duration_ms": result.duration_ms,
                "exit_code": result.exit_code,
                "command": result.command,
                "stdout_path": result.stdout_path,
                "stderr_path": result.stderr_path,
            }, sort_keys=True) + "\n"
            for result in sorted(results, key=lambda result: result.test_id)
        ),
        encoding="utf-8",
    )
    status_by_id = {result.test_id: result.status for result in results}
    matrix_lines = ["case_id\ttier\tprovider\tfamily\tlayer\tpolarity\tselected\tstatus\n"]
    for case in sorted((case for case in discovered if case.logical), key=lambda case: case.test_id):
        matrix_lines.append("\t".join((
            case.test_id,
            case.tier,
            case.provider,
            case.family,
            case.layer,
            case.polarity,
            "yes" if case.test_id in status_by_id else "no",
            status_by_id.get(case.test_id, "not-selected"),
        )) + "\n")
    (RESULTS_ROOT / "coverage-matrix.tsv").write_text(
        "".join(matrix_lines),
        encoding="utf-8",
    )
    environment = {
        "schema_version": 1,
        "platform": sys.platform,
        "python_executable": sys.executable,
        "python_version": sys.version.split()[0],
        "repository_root": str(REPOSITORY_ROOT),
        "parser_artifact": {
            "configured": bool(os.environ.get("RELICO_PARSER_ARTIFACT")),
            "exists": bool(
                os.environ.get("RELICO_PARSER_ARTIFACT")
                and Path(os.environ["RELICO_PARSER_ARTIFACT"]).is_file()
            ),
        },
    }
    (RESULTS_ROOT / "environment.json").write_text(
        json.dumps(environment, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def write_junit_report(results: Sequence[TestResult]) -> None:
    root = ET.Element(
        "testsuite",
        name="ReLico",
        tests=str(len(results)),
        failures=str(sum(result.status == "fail" for result in results)),
        skipped=str(sum(result.status in {"skip", "unavailable"} for result in results)),
        time=f"{sum(result.duration_ms for result in results) / 1000:.3f}",
    )

    for result in results:
        case = ET.SubElement(
            root,
            "testcase",
            classname=f"{result.suite}.{result.family}.{result.layer}",
            name=result.test_id,
            time=f"{result.duration_ms / 1000:.3f}",
        )
        if result.status == "fail":
            failure = ET.SubElement(
                case,
                "failure",
                message=result.message,
                type="AssertionError",
            )
            failure.text = (
                f"exit code: {result.exit_code}\n"
                f"stdout: {result.stdout_path}\n"
                f"stderr: {result.stderr_path}"
            )
        elif result.status in {"skip", "unavailable"}:
            skipped = ET.SubElement(case, "skipped")
            skipped.set("message", result.message or result.reason_code)

    tree = ET.ElementTree(root)
    ET.indent(tree, space="  ")
    tree.write(
        RESULTS_ROOT / "junit.xml",
        encoding="utf-8",
        xml_declaration=True,
    )


def print_cases(cases: Sequence[TestCase]) -> None:
    print("test_id\ttier\tsuite\tprovider\tfamily\tlayer\tpolarity\ttags")
    for case in cases:
        print("\t".join((
            case.test_id,
            case.tier,
            case.suite,
            case.provider,
            case.family,
            case.layer,
            case.polarity,
            ",".join(case.tags),
        )))


def main(arguments: Sequence[str]) -> int:
    options = parse_arguments(arguments)
    catalog_error = ""
    try:
        validate_behavioral_coverage()
    except RuntimeError as error:
        catalog_error = str(error)
        if options.list:
            raise
    cases = discover_cases()
    selected = select_cases(cases, options)

    if options.list:
        print_cases(selected)
        return 0

    if not selected:
        raise RuntimeError("no tests matched the selected filters")

    if RESULTS_ROOT.exists():
        shutil.rmtree(RESULTS_ROOT)
    (RESULTS_ROOT / "cases").mkdir(parents=True)

    results: list[TestResult] = []
    for index, case in enumerate(selected):
        if case.test_id == "catalog::translator-tests" and catalog_error:
            case_root = RESULTS_ROOT / "cases" / safe_result_name(case.test_id)
            case_root.mkdir(parents=True, exist_ok=False)
            stdout_path = case_root / "stdout.txt"
            stderr_path = case_root / "stderr.txt"
            stdout_path.write_text("", encoding="utf-8")
            stderr_path.write_text(catalog_error + "\n", encoding="utf-8")
            result = TestResult(
                test_id=case.test_id,
                suite=case.suite,
                family=case.family,
                layer=case.layer,
                polarity=case.polarity,
                status="fail",
                duration_ms=0,
                exit_code=2,
                command=list(case.command),
                stdout_path=report_path(stdout_path),
                stderr_path=report_path(stderr_path),
                message=catalog_error,
                tier=case.tier,
                provider=case.provider,
                logical=case.logical,
                reason_code="catalog_invalid",
            )
        else:
            result = run_case(case)
        results.append(result)
        print(
            f"{result.status.upper()} {result.test_id} "
            f"duration_ms={result.duration_ms}"
        )
        if result.status == "fail" and not options.keep_going:
            for remaining in selected[index + 1:]:
                case_root = RESULTS_ROOT / "cases" / safe_result_name(remaining.test_id)
                case_root.mkdir(parents=True, exist_ok=False)
                stdout_path = case_root / "stdout.txt"
                stderr_path = case_root / "stderr.txt"
                stdout_path.write_text("", encoding="utf-8")
                stderr_path.write_text("skipped after earlier failure\n", encoding="utf-8")
                results.append(TestResult(
                    test_id=remaining.test_id,
                    suite=remaining.suite,
                    family=remaining.family,
                    layer=remaining.layer,
                    polarity=remaining.polarity,
                    status="skip",
                    duration_ms=0,
                    exit_code=0,
                    command=list(remaining.command),
                    stdout_path=report_path(stdout_path),
                    stderr_path=report_path(stderr_path),
                    message="skipped after earlier failure",
                    tier=remaining.tier,
                    provider=remaining.provider,
                    logical=remaining.logical,
                    reason_code="fail_fast",
                ))
            break

    write_reports(cases, selected, results)
    write_junit_report(results)

    logical_results = [result for result in results if result.logical]
    pass_count = sum(result.status == "pass" for result in logical_results)
    failure_count = sum(result.status == "fail" for result in logical_results)
    skip_count = sum(result.status == "skip" for result in logical_results)
    unavailable_count = sum(result.status == "unavailable" for result in logical_results)
    gate_failure_count = sum(
        result.status == "fail" for result in results if not result.logical
    )
    print(f"TEST_COUNT={len(logical_results)}")
    print(f"PASS_COUNT={pass_count}")
    print(f"FAILURE_COUNT={failure_count}")
    print(f"SKIP_COUNT={skip_count}")
    print(f"UNAVAILABLE_COUNT={unavailable_count}")
    print(f"RESULTS_JSON={RESULTS_ROOT / 'summary.json'}")
    print(f"JUNIT_XML={RESULTS_ROOT / 'junit.xml'}")
    if failure_count or gate_failure_count:
        return 1
    return 3 if unavailable_count else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except RuntimeError as error:
        print(f"relico-test: {error}", file=sys.stderr)
        raise SystemExit(2)
