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


class ExecutionContractTest(unittest.TestCase):
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
            }

            (benchmark / "manifest.json").write_text(
                json.dumps(manifest),
                encoding="utf-8",
            )

            original_root = execution.BENCHMARK_ROOT
            execution.BENCHMARK_ROOT = root

            try:
                with self.assertRaisesRegex(
                    execution.ExecutionError,
                    "must be the final declared stage",
                ):
                    execution.load_manifest("probe")
            finally:
                execution.BENCHMARK_ROOT = original_root

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
                        "polarity": "positive",
                        "implementation_status": "implemented",
                    }
                ]
            }

            original_root = execution.BENCHMARK_ROOT
            execution.BENCHMARK_ROOT = root

            try:
                result = execution.run_benchmark(
                    registry=registry,
                    benchmark_id="probe",
                    dry_run=False,
                    regenerate=False,
                )
            finally:
                execution.BENCHMARK_ROOT = original_root

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


class ExecutionImplementationStatusTest(unittest.TestCase):
    def test_planned_benchmark_is_rejected(self) -> None:
        registry = {
            "benchmarks": [
                {
                    "benchmark_id": "probe",
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


class RegistryImplementationStatusTest(unittest.TestCase):
    def test_implemented_without_manifest_is_rejected(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            original_root = registry_module.BENCHMARK_ROOT
            registry_module.BENCHMARK_ROOT = Path(temporary)

            try:
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "manifest.json is absent",
                ):
                    registry_module.validate_implementation_status(
                        "probe",
                        "implemented",
                    )
            finally:
                registry_module.BENCHMARK_ROOT = original_root

    def test_planned_with_manifest_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = root / "probe/manifest.json"
            manifest.parent.mkdir(parents=True)
            manifest.write_text(
                "{}\n",
                encoding="utf-8",
            )

            original_root = registry_module.BENCHMARK_ROOT
            registry_module.BENCHMARK_ROOT = root

            try:
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "registry status is planned",
                ):
                    registry_module.validate_implementation_status(
                        "probe",
                        "planned",
                    )
            finally:
                registry_module.BENCHMARK_ROOT = original_root


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
