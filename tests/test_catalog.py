from __future__ import annotations

from pathlib import Path
import importlib.util
import sys
import unittest


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = REPOSITORY_ROOT / "tests" / "catalog" / "validate_catalog.py"


def load_validator():
    specification = importlib.util.spec_from_file_location("test_catalog_validator", VALIDATOR)
    if specification is None or specification.loader is None:
        raise RuntimeError("could not load catalog validator")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


class CatalogTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.validator = load_validator()
        cls.counts = cls.validator.validate_catalog()

    def test_preserves_distinct_fixture_and_application_populations(self) -> None:
        self.assertEqual(self.counts["translator_fixtures"], 61)
        self.assertEqual(self.counts["application_benchmarks"], 41)

    def test_multiple_evidence_records_do_not_inflate_logical_cases(self) -> None:
        self.assertNotEqual(
            self.counts["logical_cases"],
            self.counts["evidence_records"],
        )

    def test_aggregate_lean_build_does_not_add_a_logical_case(self) -> None:
        runner = self.validator.load_runner()
        cases = runner.discover_cases()
        focused = sum(case.test_id.startswith("lean-case::") for case in cases)
        aggregate = sum(case.test_id == "lean::RelicoTests" for case in cases)
        self.assertEqual(focused, self.counts["lean_logical_cases"])
        self.assertEqual(aggregate, 1)

    def test_claim_catalog_covers_verified_and_trusted_evidence(self) -> None:
        claims = self.validator.read_json(
            self.validator.CATALOG_ROOT / "claims.json"
        )["claims"]
        identifiers = {claim["id"] for claim in claims}
        self.assertIn("translator.formal.correspondence", identifiers)
        self.assertIn("translator.target.acceptance", identifiers)
        self.assertIn("source.independent.model-check", identifiers)

    def test_general_matrix_is_present_and_names_uncovered_decisions(self) -> None:
        rows = self.validator.read_tsv(
            self.validator.CATALOG_ROOT / "general-accepted-fragment.tsv"
        )
        self.assertEqual(self.counts["general_matrix_features"], len(rows))
        self.assertTrue(
            any("uncovered" in row["evidence_classes"].split(";") for row in rows)
        )

    def test_general_focused_cases_do_not_change_formal_module_population(self) -> None:
        rows = self.validator.read_tsv(
            self.validator.REPOSITORY_ROOT
            / "tests/translator/general--focused--software/cases.tsv"
        )
        self.assertEqual(len(rows), 13)
        self.assertTrue(
            all(not row["lean_module"].startswith("Relico/Tests/") for row in rows)
        )


if __name__ == "__main__":
    unittest.main()
