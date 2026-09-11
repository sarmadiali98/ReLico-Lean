from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import importlib.util
import json
import sys
import tempfile
import unittest
from unittest import mock


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
RUNNER = REPOSITORY_ROOT / "tools" / "relico_test.py"


def load_runner():
    specification = importlib.util.spec_from_file_location(
        "relico_test_contract",
        RUNNER,
    )
    if specification is None or specification.loader is None:
        raise RuntimeError("could not load relico test runner")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


class DiscoveryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runner = load_runner()
        cls.cases = cls.runner.discover_cases()

    def test_identifiers_are_unique(self) -> None:
        identifiers = [case.test_id for case in self.cases]
        self.assertEqual(len(identifiers), len(set(identifiers)))

    def test_all_suites_are_discovered(self) -> None:
        self.assertEqual(
            {case.suite for case in self.cases},
            {"catalog", "python", "lean", "integration"},
        )

    def test_focused_lean_cases_are_individually_discovered(self) -> None:
        cases = [
            case
            for case in self.cases
            if case.test_id.startswith("lean-case::")
        ]
        self.assertGreaterEqual(len(cases), 20)
        self.assertIn(
            "lean-case::core.frontend.expression.unsupported",
            {case.test_id for case in cases},
        )
        self.assertIn(
            "lean-case::general.translation.statement.external-send",
            {case.test_id for case in cases},
        )

    def test_direct_translator_catalogs_cover_focused_cases(self) -> None:
        rows = self.runner.load_direct_software_cases()
        behavioral_rows = [
            row
            for row in self.runner.load_behavioral_coverage()
            if row["test_module"] in self.runner.DIRECT_LEAN_MODULES
        ]
        self.assertEqual(len(rows), len(behavioral_rows))
        self.assertEqual(
            len({row["case_id"] for row in rows}),
            len(rows),
        )

    def test_every_translator_fixture_is_discovered(self) -> None:
        fixtures = [
            case
            for case in self.cases
            if case.provider == "translator-fixture"
        ]
        self.assertEqual(len(fixtures), 61)

    def test_external_fixture_is_stably_discovered(self) -> None:
        case = self.runner.discover_external_actor_priority_case()
        self.assertEqual(
            case.test_id,
            "fixture::general--main-actor-priority--negative",
        )
        self.assertEqual(case.tier, "external")
        self.assertEqual(case.prerequisite_env, "RELICO_PARSER_ARTIFACT")

    def test_default_selection_excludes_external_toolchains(self) -> None:
        options = SimpleNamespace(
            suite=None,
            tier=None,
            family=None,
            layer=None,
            polarity=None,
            tag=None,
            case_ids=None,
        )
        selected = self.runner.select_cases(self.cases, options)
        self.assertTrue(selected)
        self.assertEqual(
            {case.tier for case in selected},
            {"catalog", "unit", "formal"},
        )

    def test_tag_filter_requires_every_requested_tag(self) -> None:
        options = SimpleNamespace(
            suite=["integration"],
            tier=None,
            family=None,
            layer=None,
            polarity=None,
            tag=["integration", "negative"],
            case_ids=None,
        )
        selected = self.runner.select_cases(self.cases, options)
        self.assertEqual(
            [case.test_id for case in selected],
            [
                "fixture::core--well-formedness--negative",
                "fixture::general--main-actor-priority--negative",
            ],
        )

    def test_unknown_case_is_rejected(self) -> None:
        options = SimpleNamespace(
            suite=None,
            tier=None,
            family=None,
            layer=None,
            polarity=None,
            tag=None,
            case_ids=["missing"],
        )
        with self.assertRaisesRegex(RuntimeError, "unknown test identifiers"):
            self.runner.select_cases(self.cases, options)

    def test_direct_case_selection_searches_all_tiers(self) -> None:
        options = SimpleNamespace(
            suite=None,
            tier=None,
            family=None,
            layer=None,
            polarity=None,
            tag=None,
            case_ids=["fixture::core--well-formedness--negative"],
        )
        selected = self.runner.select_cases(self.cases, options)
        self.assertEqual(
            [case.test_id for case in selected],
            ["fixture::core--well-formedness--negative"],
        )

    def test_aggregate_formal_gate_is_not_logical(self) -> None:
        aggregate = next(
            case for case in self.cases if case.test_id == "lean::RelicoTests"
        )
        self.assertFalse(aggregate.logical)
        self.assertEqual(aggregate.tier, "formal")

    def test_safe_result_names_do_not_collide(self) -> None:
        self.assertNotEqual(
            self.runner.safe_result_name("a::b"),
            self.runner.safe_result_name("a--b"),
        )

    def test_missing_external_artifact_is_unavailable(self) -> None:
        case = self.runner.discover_external_actor_priority_case()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with (
                mock.patch.object(self.runner, "RESULTS_ROOT", root),
                mock.patch.dict("os.environ", {}, clear=True),
            ):
                result = self.runner.run_case(case)
        self.assertEqual(result.status, "unavailable")
        self.assertEqual(
            result.reason_code,
            "missing_environment_path:RELICO_PARSER_ARTIFACT",
        )

    def test_reports_count_only_logical_cases(self) -> None:
        logical = self.runner.TestResult(
            test_id="lean-case::one",
            suite="lean",
            family="core",
            layer="translation",
            polarity="positive",
            status="pass",
            duration_ms=1,
            exit_code=0,
            command=["true"],
            stdout_path="stdout.txt",
            stderr_path="stderr.txt",
            tier="unit",
            provider="lean-focused",
            logical=True,
        )
        gate = self.runner.TestResult(
            test_id="lean::RelicoTests",
            suite="lean",
            family="all",
            layer="unit-and-formal",
            polarity="mixed",
            status="pass",
            duration_ms=1,
            exit_code=0,
            command=["true"],
            stdout_path="stdout.txt",
            stderr_path="stderr.txt",
            tier="formal",
            provider="lean-aggregate",
            logical=False,
        )
        specs = [
            self.runner.TestCase(
                test_id=result.test_id,
                suite=result.suite,
                family=result.family,
                layer=result.layer,
                polarity=result.polarity,
                tags=(),
                command=("true",),
                tier=result.tier,
                provider=result.provider,
                logical=result.logical,
            )
            for result in (logical, gate)
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with mock.patch.object(self.runner, "RESULTS_ROOT", root):
                self.runner.write_reports(specs, specs, [logical, gate])
            summary = json.loads((root / "summary.json").read_text())
        self.assertEqual(summary["selected_logical_case_count"], 1)
        self.assertEqual(summary["counts"]["pass"], 1)
        self.assertEqual(summary["gate_counts"]["pass"], 1)

    def test_behavioral_coverage_registry_is_valid(self) -> None:
        self.runner.validate_behavioral_coverage()

    def test_actor_priority_case_is_under_translator_root(self) -> None:
        directories = self.runner.direct_translator_case_directories()
        self.assertIn(
            self.runner.REPOSITORY_ROOT
            / "tests"
            / "translator"
            / "general--main-actor-priority--negative",
            directories,
        )


if __name__ == "__main__":
    unittest.main()
