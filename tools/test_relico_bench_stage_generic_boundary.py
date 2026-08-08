from __future__ import annotations

from pathlib import Path
import sys
import unittest

TOOLS = Path(__file__).resolve().parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import relico_bench_stage as stage


class GenericExpectedBoundaryTest(unittest.TestCase):
    def test_legacy_parser_boundary_is_unchanged(self) -> None:
        benchmark_id = "bound-payload--dispatch--negative"
        diagnostic = (
            "unsupported by the ReLico v0 parser bridge: "
            "message-server parameters"
        )
        rejection = {
            "benchmark_id": benchmark_id,
            "boundary_stage": "parser-json",
            "expected_exit_code": 1,
            "forbidden_artifact_count": 2,
            "observed_exit_code": 1,
            "required_diagnostic": diagnostic,
            "schema_version": 1,
            "status": "expected-rejection",
        }
        boundary = stage.expected_boundary_value(benchmark_id, rejection)
        self.assertEqual(
            boundary,
            {
                "benchmark_id": benchmark_id,
                "boundary_code": (
                    "V0_PARSER_BRIDGE_MESSAGE_SERVER_PARAMETERS_UNSUPPORTED"
                ),
                "boundary_stage": "parser-json",
                "expected_rejection": True,
                "schema_version": 1,
                "status": "pass",
            },
        )
        self.assertEqual(
            stage.diagnostics_value(benchmark_id, boundary),
            {
                "benchmark_id": benchmark_id,
                "diagnostic_code": (
                    "V0_PARSER_BRIDGE_MESSAGE_SERVER_PARAMETERS_UNSUPPORTED"
                ),
                "expected_rejection": True,
                "message": (
                    "Bound-payload message-server parameters are "
                    "intentionally rejected by the current ReLico v0 "
                    "parser bridge."
                ),
                "schema_version": 1,
                "status": "pass",
            },
        )

    def test_generic_rmc_boundary_preserves_evidence(self) -> None:
        benchmark_id = "core--well-formedness--negative"
        diagnostic = (
            "The method missing() is undefined for the type Controller"
        )
        rejection = {
            "benchmark_id": benchmark_id,
            "boundary_stage": "rmc",
            "expected_exit_code": 1,
            "forbidden_artifact_count": 3,
            "observed_exit_code": 1,
            "required_diagnostic": diagnostic,
            "schema_version": 1,
            "status": "expected-rejection",
        }
        boundary = stage.expected_boundary_value(benchmark_id, rejection)
        self.assertEqual(
            boundary,
            {
                "benchmark_id": benchmark_id,
                "boundary_code": "EXPECTED_REJECTION",
                "boundary_stage": "rmc",
                "expected_exit_code": 1,
                "expected_rejection": True,
                "observed_exit_code": 1,
                "required_diagnostic": diagnostic,
                "schema_version": 1,
                "status": "pass",
            },
        )
        self.assertEqual(
            stage.diagnostics_value(benchmark_id, boundary),
            {
                "benchmark_id": benchmark_id,
                "boundary_stage": "rmc",
                "diagnostic_code": "EXPECTED_REJECTION",
                "expected_rejection": True,
                "message": diagnostic,
                "schema_version": 1,
                "status": "pass",
            },
        )

    def test_generic_boundary_rejects_exit_mismatch(self) -> None:
        with self.assertRaisesRegex(
            stage.StageError,
            "observed rejection exit code differs",
        ):
            stage.expected_boundary_value(
                "core--well-formedness--negative",
                {
                    "benchmark_id": "core--well-formedness--negative",
                    "boundary_stage": "rmc",
                    "expected_exit_code": 1,
                    "observed_exit_code": 2,
                    "required_diagnostic": "diagnostic",
                    "schema_version": 1,
                    "status": "expected-rejection",
                },
            )

    def test_generic_boundary_rejects_missing_diagnostic(self) -> None:
        with self.assertRaisesRegex(
            stage.StageError,
            "required rejection diagnostic is missing",
        ):
            stage.expected_boundary_value(
                "core--well-formedness--negative",
                {
                    "benchmark_id": "core--well-formedness--negative",
                    "boundary_stage": "rmc",
                    "expected_exit_code": 1,
                    "observed_exit_code": 1,
                    "required_diagnostic": "",
                    "schema_version": 1,
                    "status": "expected-rejection",
                },
            )


if __name__ == "__main__":
    unittest.main()
