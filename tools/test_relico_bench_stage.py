from __future__ import annotations

from pathlib import Path
from unittest.mock import patch
import argparse
import json
import subprocess
import sys
import tempfile
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


class RmcPropertyNormalizationTest(unittest.TestCase):
    def metadata(self, expected: str = "TRUE", required: bool = True) -> dict[str, object]:
        return {
            "property_id": "probe",
            "logic": "Assertion",
            "rmc_name": "Probe_Assertion",
            "expected": expected,
            "source": "property/probe.property",
            "required": required,
        }

    def test_boolean_match_and_mismatch_matrix(self) -> None:
        self.assertEqual(stage._property_result(self.metadata("TRUE"), actual="TRUE", phase="complete")["comparison"], "MATCH")
        self.assertEqual(stage._property_result(self.metadata("FALSE"), actual="FALSE", phase="checker")["comparison"], "MATCH")
        self.assertEqual(stage._property_result(self.metadata("TRUE"), actual="FALSE", phase="checker")["comparison"], "MISMATCH")
        self.assertEqual(stage._property_result(self.metadata("FALSE"), actual="TRUE", phase="complete")["comparison"], "MISMATCH")

    def test_satisfied_and_expected_assertion_failure(self) -> None:
        satisfied = "<model-checking-report><checked-property><result>satisfied</result></checked-property></model-checking-report>"
        failed = "<model-checking-report><checked-property><result>assertion failed</result><message>Probe_Assertion</message></checked-property></model-checking-report>"
        self.assertEqual(stage.normalize_assertion_xml(satisfied, "Probe_Assertion")[:2], ("TRUE", "complete"))
        self.assertEqual(stage.normalize_assertion_xml(failed, "Probe_Assertion")[:2], ("FALSE", "checker"))

    def test_wrong_assertion_name_is_error(self) -> None:
        failed = "<model-checking-report><checked-property><result>assertion failed</result><message>Other_Assertion</message></checked-property></model-checking-report>"
        self.assertEqual(stage.normalize_assertion_xml(failed, "Probe_Assertion")[0], "ERROR")

    def test_malformed_and_invalid_identifier_generation_are_errors(self) -> None:
        for diagnostic in (
            "Errors:\nline:4, column:4, no viable alternative",
            "Errors:\nline:3, column:23, Undefiend variable missing",
        ):
            completed = subprocess.CompletedProcess(["java"], 0, diagnostic, "")
            self.assertEqual(stage.normalize_generation(completed, generated_cpp=False)[0], "ERROR")

    def test_timeout_is_timeout(self) -> None:
        self.assertEqual(stage.normalize_generation(None, generated_cpp=False)[0], "TIMEOUT")

    def test_tctl_is_unsupported_and_required_mismatch_fails(self) -> None:
        metadata = self.metadata()
        metadata["logic"] = "TCTL"
        result = stage._property_result(metadata, actual="UNSUPPORTED", phase="unsupported")
        self.assertEqual(result["actual"], "UNSUPPORTED")
        self.assertEqual(result["comparison"], "MISMATCH")
        self.assertEqual(stage.required_property_mismatches([result]), [result])

    def test_tctl_manifest_entry_is_not_executed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            benchmark = Path(temporary) / "probe"
            property_path = benchmark / "property/probe.property"
            property_path.parent.mkdir(parents=True)
            property_path.write_text(
                "property { TCTL { Probe_TCTL : AG(time <= 1, true); } }\n",
                encoding="utf-8",
            )
            manifest = {
                "properties": [{
                    "property_id": "probe-tctl",
                    "logic": "TCTL",
                    "rmc_name": "Probe_TCTL",
                    "expected": "TRUE",
                    "source": "property/probe.property",
                    "required": True,
                }]
            }
            (benchmark / "manifest.json").write_text(
                json.dumps(manifest), encoding="utf-8"
            )
            source = benchmark / "source/model.rebeca"
            source.parent.mkdir()
            source.write_text("main {}\n", encoding="utf-8")
            jar = benchmark / "rmc.jar"
            java = benchmark / "java"
            cxx = benchmark / "cxx"
            for path in (jar, java, cxx):
                path.write_text("probe\n", encoding="utf-8")
            output = benchmark / "actual/rmc-properties/results.json"
            options = argparse.Namespace(
                benchmark_id="probe",
                benchmark=str(benchmark),
                source=str(source),
                actual=str(benchmark / "actual"),
                rmc_jar=str(jar),
                java=str(java),
                cxx=str(cxx),
                output=str(output),
                generation_timeout=1,
                compilation_timeout=1,
                checker_timeout=1,
            )
            with (
                patch.object(stage, "require_hash"),
                self.assertRaisesRegex(stage.StageError, "probe-tctl"),
            ):
                stage.rmc_properties_stage(options)
            result = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(result["properties"][0]["actual"], "UNSUPPORTED")
            self.assertEqual(result["properties"][0]["comparison"], "MISMATCH")

    def test_optional_mismatch_does_not_fail_stage(self) -> None:
        metadata = self.metadata(required=False)
        result = stage._property_result(
            metadata, actual="TIMEOUT", phase="checker"
        )
        self.assertEqual(result["comparison"], "MISMATCH")
        self.assertEqual(stage.required_property_mismatches([result]), [])

    def test_assertions_are_not_initial_state_checks(self) -> None:
        self.assertEqual(stage.normalize_assertion_xml(
            "<model-checking-report><checked-property><result>satisfied</result></checked-property></model-checking-report>",
            "Probe_Assertion",
        )[0], "TRUE")

if __name__ == "__main__":
    unittest.main()
