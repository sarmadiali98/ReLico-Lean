from __future__ import annotations

from pathlib import Path
import sys
import unittest


TOOLS = Path(__file__).resolve().parent

if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import relico_bench_stage as stage


def valid_coverage() -> dict[str, object]:
    return {
        "benchmark_id": "example--generic--positive",
        "obligation_count": 2,
        "test_modules": [
            "Relico/Tests/Alpha.lean",
            "Relico/Tests/Beta.lean",
        ],
        "obligations": [
            {
                "obligation_id": "example-alpha",
                "mapping_status": "accepted",
                "final_benchmark_id": "example--generic--positive",
                "test_file": "Relico/Tests/Alpha.lean",
            },
            {
                "obligation_id": "example-beta",
                "mapping_status": "accepted",
                "final_benchmark_id": "example--generic--positive",
                "test_file": "Relico/Tests/Beta.lean",
            },
        ],
    }


class FormalWitnessValueTest(unittest.TestCase):
    def test_uses_coverage_metadata_without_benchmark_constants(
        self,
    ) -> None:
        result = stage.formal_witness_value(valid_coverage())

        self.assertEqual(
            result["benchmark_id"],
            "example--generic--positive",
        )
        self.assertEqual(result["obligation_count"], 2)
        self.assertEqual(
            result["elaborated_modules"],
            [
                "Relico/Tests/Alpha.lean",
                "Relico/Tests/Beta.lean",
            ],
        )
        self.assertEqual(
            result["obligation_ids"],
            [
                "example-alpha",
                "example-beta",
            ],
        )

    def test_rejects_module_evidence_disagreement(self) -> None:
        coverage = valid_coverage()
        coverage["test_modules"] = [
            "Relico/Tests/Alpha.lean",
        ]

        with self.assertRaisesRegex(
            stage.StageError,
            "differ from obligation evidence",
        ):
            stage.formal_witness_value(coverage)

    def test_rejects_cross_benchmark_obligation(self) -> None:
        coverage = valid_coverage()
        obligations = coverage["obligations"]
        assert isinstance(obligations, list)
        obligation = obligations[0]
        assert isinstance(obligation, dict)
        obligation["final_benchmark_id"] = "another-benchmark"

        with self.assertRaisesRegex(
            stage.StageError,
            "maps elsewhere",
        ):
            stage.formal_witness_value(coverage)


class ExpectedBoundaryValueTest(unittest.TestCase):
    def stage_result(self) -> dict[str, object]:
        return {
            "benchmark_id": (
                "bound-payload--dispatch--negative"
            ),
            "stage": "parser-json",
            "status": "pass",
            "exit_code": 1,
        }

    def test_expected_rejection_chain_is_deterministic(
        self,
    ) -> None:
        diagnostic = (
            "unsupported by the ReLico v0 parser bridge: "
            "message-server parameters"
        )

        rejection = stage.expected_absence_value(
            benchmark_id=(
                "bound-payload--dispatch--negative"
            ),
            failed_stage="parser-json",
            stage_result=self.stage_result(),
            combined_output=diagnostic,
            expected_exit_code=1,
            required_diagnostic=diagnostic,
            forbidden_artifact_count=2,
            present_artifact_count=0,
        )

        boundary = stage.expected_boundary_value(
            "bound-payload--dispatch--negative",
            rejection,
        )

        diagnostics = stage.diagnostics_value(
            "bound-payload--dispatch--negative",
            boundary,
        )

        self.assertEqual(
            rejection["status"],
            "expected-rejection",
        )
        self.assertEqual(
            boundary["boundary_code"],
            (
                "V0_PARSER_BRIDGE_MESSAGE_SERVER_"
                "PARAMETERS_UNSUPPORTED"
            ),
        )
        self.assertEqual(
            diagnostics["status"],
            "pass",
        )

    def test_rejects_missing_required_diagnostic(
        self,
    ) -> None:
        diagnostic = (
            "unsupported by the ReLico v0 parser bridge: "
            "message-server parameters"
        )

        with self.assertRaisesRegex(
            stage.StageError,
            "diagnostic was not observed",
        ):
            stage.expected_absence_value(
                benchmark_id=(
                    "bound-payload--dispatch--negative"
                ),
                failed_stage="parser-json",
                stage_result=self.stage_result(),
                combined_output="different failure",
                expected_exit_code=1,
                required_diagnostic=diagnostic,
                forbidden_artifact_count=2,
                present_artifact_count=0,
            )

    def test_rejects_post_boundary_artifact(
        self,
    ) -> None:
        diagnostic = (
            "unsupported by the ReLico v0 parser bridge: "
            "message-server parameters"
        )

        with self.assertRaisesRegex(
            stage.StageError,
            "artifact exists beyond",
        ):
            stage.expected_absence_value(
                benchmark_id=(
                    "bound-payload--dispatch--negative"
                ),
                failed_stage="parser-json",
                stage_result=self.stage_result(),
                combined_output=diagnostic,
                expected_exit_code=1,
                required_diagnostic=diagnostic,
                forbidden_artifact_count=2,
                present_artifact_count=1,
            )


if __name__ == "__main__":
    unittest.main()
