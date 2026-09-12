from __future__ import annotations

from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch
import json
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parent

if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import relico_bench as cli
import relico_bench_execution as execution
import relico_bench_registry as registry_module
from relico_bench_properties import validate_properties


class ExecutionContractTest(unittest.TestCase):
    def test_manifest_without_properties_remains_valid(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            benchmark = Path(temporary) / "probe"
            source = benchmark / "source/model.rebeca"
            source.parent.mkdir(parents=True)
            source.write_text("main {}\n", encoding="utf-8")
            (benchmark / "manifest.json").write_text(json.dumps({
                "schema_version": 1,
                "benchmark_id": "probe",
                "description": "probe",
                "polarity": "positive",
                "expected_terminal_stage": "rmc",
                "source_files": ["source/model.rebeca"],
                "stages": [{"name": "rmc", "command": ["/usr/bin/true"]}],
            }), encoding="utf-8")
            execution.load_manifest("probe", benchmark)

    def test_terminal_stage_must_be_final(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            benchmark = root / "probe"
            source = benchmark / "source/model.rebeca"
            source.parent.mkdir(parents=True)
            source.write_text("main {}\\n", encoding="utf-8")

            manifest = {
                "schema_version": 1,
                "benchmark_id": "probe",
                "description": "probe",
                "polarity": "positive",
                "expected_terminal_stage": "source",
                "source_files": ["source/model.rebeca"],
                "stages": [
                    {
                        "name": "source",
                        "command": ["/usr/bin/true"],
                    },
                    {
                        "name": "rmc",
                        "command": ["/usr/bin/true"],
                    },
                ],
                "expected_artifacts": [
                    {
                        "path": "result.txt",
                        "required": True,
                    }
                ],
            }

            expected = benchmark / "expected/result.txt"
            expected.parent.mkdir(parents=True)
            expected.write_text("ok\n", encoding="utf-8")

            manifest["stages"][1]["command"] = [
                sys.executable,
                "-c",
                (
                    "from pathlib import Path; "
                    f"Path({str(benchmark / 'actual/result.txt')!r})"
                    ".write_text('ok\\n', encoding='utf-8')"
                ),
            ]

            (benchmark / "manifest.json").write_text(
                json.dumps(manifest),
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                execution.ExecutionError,
                "must be the final declared stage",
            ):
                execution.load_manifest("probe", benchmark)

    def test_successful_terminal_stage_is_recorded(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            benchmark = root / "probe"
            source = benchmark / "source/model.rebeca"
            source.parent.mkdir(parents=True)
            source.write_text("main {}\\n", encoding="utf-8")

            manifest = {
                "schema_version": 1,
                "benchmark_id": "probe",
                "description": "probe",
                "polarity": "positive",
                "expected_terminal_stage": "rmc",
                "source_files": ["source/model.rebeca"],
                "stages": [
                    {
                        "name": "source",
                        "command": ["/usr/bin/true"],
                    },
                    {
                        "name": "rmc",
                        "command": ["/usr/bin/true"],
                    },
                ],
            }

            (benchmark / "manifest.json").write_text(
                json.dumps(manifest),
                encoding="utf-8",
            )

            registry = {
                "benchmarks": [
                    {
                        "benchmark_id": "probe",
                        "suite": "test",
                        "semantic_layer": "core",
                        "polarity": "positive",
                        "implementation_status": "implemented",
                    }
                ]
            }

            with patch.object(
                execution,
                "benchmark_directory",
                return_value=benchmark,
            ):
                result = execution.run_benchmark(
                    registry=registry,
                    benchmark_id="probe",
                    dry_run=False,
                    regenerate=False,
                )
            self.assertEqual(result.exit_code, 0)

            summary = json.loads(
                (
                    benchmark
                    / "actual/run-summary.json"
                ).read_text(encoding="utf-8")
            )

            self.assertEqual(
                summary["actual_terminal_stage"],
                "rmc",
            )

            self.assertTrue(
                summary["terminal_stage_reached"]
            )

    def test_regeneration_copies_only_declared_artifacts(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            benchmark = root / "probe"
            actual = benchmark / "actual"

            declared = actual / "lf-source/model.lf"
            declared.parent.mkdir(parents=True)
            declared.write_text(
                "target Cpp\\n",
                encoding="utf-8",
            )

            noise = actual / "01-source/duration-ms.txt"
            noise.parent.mkdir(parents=True)
            noise.write_text(
                "123\\n",
                encoding="utf-8",
            )

            manifest = {
                "expected_artifacts": [
                    {
                        "path": "lf-source/model.lf",
                        "required": True,
                    }
                ]
            }

            execution.regenerate_expected_artifacts(
                benchmark_id="probe",
                benchmark_directory=benchmark,
                manifest=manifest,
                actual_root=actual,
            )

            self.assertTrue(
                (
                    benchmark
                    / "expected/lf-source/model.lf"
                ).is_file()
            )

            self.assertFalse(
                (
                    benchmark
                    / "expected/01-source/duration-ms.txt"
                ).exists()
            )

    def test_artifacts_are_compared_with_committed_goldens(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            actual = root / "actual"
            expected = root / "expected"
            actual.mkdir()
            expected.mkdir()
            (actual / "result.txt").write_text("actual\n", encoding="utf-8")
            (expected / "result.txt").write_text("expected\n", encoding="utf-8")

            failures = execution.verify_expected_artifacts(
                "probe",
                {
                    "expected_artifacts": [
                        {"path": "result.txt", "required": True}
                    ]
                },
                actual,
                expected,
            )

            self.assertEqual(
                failures,
                ["artifact differs from committed expected file: result.txt"],
            )


class ExecutionImplementationStatusTest(unittest.TestCase):
    def test_planned_benchmark_is_rejected(self) -> None:
        registry = {
            "benchmarks": [
                {
                    "benchmark_id": "probe",
                    "suite": "test",
                    "polarity": "positive",
                    "implementation_status": "planned",
                }
            ]
        }

        with self.assertRaisesRegex(
            execution.ExecutionError,
            "expected 'implemented'",
        ):
            execution.run_benchmark(
                registry=registry,
                benchmark_id="probe",
                dry_run=False,
                regenerate=False,
            )


class PropertyManifestValidationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.benchmark = Path(self.temporary.name) / "probe"
        property_directory = self.benchmark / "property"
        property_directory.mkdir(parents=True)
        (property_directory / "probe.property").write_text(
            "property { Assertion { Probe_Assertion : true; } }\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def property(self) -> dict[str, object]:
        return {
            "property_id": "probe",
            "logic": "Assertion",
            "rmc_name": "Probe_Assertion",
            "expected": "TRUE",
            "source": "property/probe.property",
            "required": True,
        }

    def validate(self, properties: list[dict[str, object]]) -> None:
        validate_properties(
            benchmark_id="probe",
            benchmark_directory=self.benchmark,
            properties=properties,
            error_type=execution.ExecutionError,
        )

    def test_valid_single_assertion(self) -> None:
        self.validate([self.property()])

    def test_duplicate_property_ids_rejected(self) -> None:
        other = self.property()
        other["rmc_name"] = "Other_Assertion"
        with self.assertRaisesRegex(execution.ExecutionError, "duplicate property_id"):
            self.validate([self.property(), other])

    def test_duplicate_rmc_names_rejected(self) -> None:
        other = self.property()
        other["property_id"] = "other"
        with self.assertRaisesRegex(execution.ExecutionError, "duplicate rmc_name"):
            self.validate([self.property(), other])

    def test_unsafe_path_rejected(self) -> None:
        value = self.property()
        value["source"] = "../probe.property"
        with self.assertRaisesRegex(execution.ExecutionError, "unsafe property source"):
            self.validate([value])

    def test_missing_source_rejected(self) -> None:
        value = self.property()
        value["source"] = "property/missing.property"
        with self.assertRaisesRegex(execution.ExecutionError, "property source is missing"):
            self.validate([value])

    def test_wrong_logic_or_name_rejected(self) -> None:
        value = self.property()
        value["logic"] = "TCTL"
        with self.assertRaisesRegex(execution.ExecutionError, "exactly one TCTL"):
            self.validate([value])

    def test_trailing_property_container_rejected(self) -> None:
        path = self.benchmark / "property/probe.property"
        path.write_text(
            "property { Assertion { Probe_Assertion : true; } } property {}\n",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(execution.ExecutionError, "exactly one Assertion"):
            self.validate([self.property()])


class RegistryImplementationStatusTest(unittest.TestCase):
    def test_implemented_without_manifest_is_rejected(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            row = {
                "benchmark_id": "probe",
                "suite": "test",
                "semantic_layer": "core",
            }
            with patch.object(
                registry_module,
                "benchmark_directory",
                return_value=Path(temporary) / "probe",
            ):
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "manifest.json is absent",
                ):
                    registry_module.validate_implementation_status(
                        row,
                        "implemented",
                    )

    def test_planned_with_manifest_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = root / "probe/manifest.json"
            manifest.parent.mkdir(parents=True)
            manifest.write_text(
                "{}\n",
                encoding="utf-8",
            )

            row = {
                "benchmark_id": "probe",
                "suite": "test",
                "semantic_layer": "core",
            }
            with patch.object(
                registry_module,
                "benchmark_directory",
                return_value=root / "probe",
            ):
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "registry status is planned",
                ):
                    registry_module.validate_implementation_status(
                        row,
                        "planned",
                    )


class CliImplementationStatusTest(unittest.TestCase):
    def test_run_all_skips_planned_benchmark(self) -> None:
        registry = {
            "benchmarks": [
                {
                    "benchmark_id": "probe",
                    "implementation_status": "planned",
                }
            ]
        }

        output = StringIO()

        with (
            patch.object(cli, "run_benchmark") as run_mock,
            redirect_stdout(output),
        ):
            exit_code = cli.run_all(
                registry=registry,
                dry_run=False,
                regenerate=False,
                keep_going=False,
            )

        self.assertEqual(exit_code, 3)
        run_mock.assert_not_called()
        self.assertIn(
            "NOT_IMPLEMENTED probe",
            output.getvalue(),
        )


if __name__ == "__main__":
    unittest.main()
