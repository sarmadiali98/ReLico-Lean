#!/usr/bin/env python3

from __future__ import annotations

from collections import Counter
from pathlib import Path
import csv
import fnmatch
import importlib.util
import json
import sys


REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
CATALOG_ROOT = Path(__file__).resolve().parent
DIRECT_LEAN_MODULES = {
    "Relico/Tests/FrontendDecoder.lean",
    "Relico/Tests/Translation.lean",
    "frontend/lean-bridge/GeneralFocusedTestMain.lean",
}
MATRIX_COLUMNS = {
    "feature_id",
    "component",
    "disposition",
    "production_refs",
    "focused_cases",
    "translator_fixtures",
    "application_benchmarks",
    "external_cases",
    "formal_refs",
    "evidence_classes",
    "limitation",
}


class CatalogError(RuntimeError):
    pass


def read_json(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CatalogError(f"cannot read {path.relative_to(REPOSITORY_ROOT)}: {error}") from error
    if not isinstance(value, dict):
        raise CatalogError(f"{path.relative_to(REPOSITORY_ROOT)} must contain an object")
    return value


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def relative_glob(pattern: str) -> list[Path]:
    return sorted(path for path in REPOSITORY_ROOT.glob(pattern) if path.is_file())


def load_runner():
    path = REPOSITORY_ROOT / "tools" / "relico_test.py"
    specification = importlib.util.spec_from_file_location("catalog_relico_test", path)
    if specification is None or specification.loader is None:
        raise CatalogError("could not load tools/relico_test.py")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


def split_refs(value: str) -> list[str]:
    return [entry for entry in value.split(";") if entry]


def validate_code_ref(reference: str, feature_id: str) -> None:
    path_text, separator, symbol = reference.partition("#")
    path = REPOSITORY_ROOT / path_text
    if not separator or not symbol or not path.is_file():
        raise CatalogError(f"{feature_id}: stale code reference: {reference}")
    if symbol not in path.read_text(encoding="utf-8"):
        raise CatalogError(f"{feature_id}: code symbol is absent: {reference}")


def validate_general_matrix(
    catalog: dict,
    logical_ids: set[str],
    fixture_ids: set[str],
    runner_ids: set[str],
) -> int:
    matrix_path = REPOSITORY_ROOT / catalog.get("accepted_fragment_matrix", "")
    if not matrix_path.is_file():
        raise CatalogError("accepted-fragment matrix is absent")
    rows = read_tsv(matrix_path)
    if not rows or set(rows[0]) != MATRIX_COLUMNS:
        raise CatalogError("general accepted-fragment matrix columns are invalid")
    identifiers = [row["feature_id"] for row in rows]
    if len(identifiers) != len(set(identifiers)) or any(not value for value in identifiers):
        raise CatalogError("general accepted-fragment feature IDs are empty or duplicated")

    allowed_components = {
        "general-schema", "general-elaborator", "general-decoder",
        "general-translation", "general-routing",
    }
    allowed_dispositions = {"accepted", "rejected", "conditional"}
    allowed_evidence = {"direct-focused", "fixture-integration", "formal", "external", "uncovered"}
    uncovered = 0
    for row in rows:
        feature = row["feature_id"]
        if row["component"] not in allowed_components:
            raise CatalogError(f"{feature}: invalid matrix component")
        if row["disposition"] not in allowed_dispositions:
            raise CatalogError(f"{feature}: invalid matrix disposition")
        evidence = set(split_refs(row["evidence_classes"]))
        if not evidence or not evidence <= allowed_evidence:
            raise CatalogError(f"{feature}: invalid matrix evidence classification")
        if "uncovered" in evidence:
            uncovered += 1
            if len(evidence) != 1 or any(row[column] for column in (
                "focused_cases", "translator_fixtures", "application_benchmarks",
                "external_cases", "formal_refs",
            )):
                raise CatalogError(f"{feature}: uncovered rows cannot claim evidence")
        for reference in split_refs(row["production_refs"]) + split_refs(row["formal_refs"]):
            validate_code_ref(reference, feature)
        unknown_cases = set(split_refs(row["focused_cases"])) - logical_ids
        if unknown_cases:
            raise CatalogError(f"{feature}: unknown focused cases: {', '.join(sorted(unknown_cases))}")
        unknown_fixtures = set(split_refs(row["translator_fixtures"])) - fixture_ids
        if unknown_fixtures:
            raise CatalogError(f"{feature}: unknown translator fixtures: {', '.join(sorted(unknown_fixtures))}")
        for benchmark in split_refs(row["application_benchmarks"]):
            if not (REPOSITORY_ROOT / "benchmarks" / benchmark / "manifest.json").is_file():
                raise CatalogError(f"{feature}: unknown application benchmark: {benchmark}")
        unknown_external = set(split_refs(row["external_cases"])) - runner_ids
        if unknown_external:
            raise CatalogError(f"{feature}: unknown external cases: {', '.join(sorted(unknown_external))}")
        if not row["limitation"]:
            raise CatalogError(f"{feature}: matrix limitation is required")
    if uncovered == 0:
        raise CatalogError("general accepted-fragment matrix names no uncovered decisions")
    return len(rows)


def validate_stage_catalog() -> set[str]:
    payload = read_json(CATALOG_ROOT / "stages.json")
    if payload.get("schema_version") != 1 or not isinstance(payload.get("stages"), list):
        raise CatalogError("tests/catalog/stages.json has an invalid envelope")
    identifiers = [stage.get("id") for stage in payload["stages"] if isinstance(stage, dict)]
    if len(identifiers) != len(payload["stages"]) or any(not value for value in identifiers):
        raise CatalogError("every stage must have a nonempty ID")
    duplicates = [value for value, count in Counter(identifiers).items() if count > 1]
    if duplicates:
        raise CatalogError("duplicate stage IDs: " + ", ".join(sorted(duplicates)))
    return set(identifiers)


def validate_claim_catalog(stages: set[str]) -> set[str]:
    payload = read_json(CATALOG_ROOT / "claims.json")
    if payload.get("schema_version") != 1 or not isinstance(payload.get("claims"), list):
        raise CatalogError("tests/catalog/claims.json has an invalid envelope")
    identifiers = [claim.get("id") for claim in payload["claims"] if isinstance(claim, dict)]
    if len(identifiers) != len(payload["claims"]) or any(not value for value in identifiers):
        raise CatalogError("every claim must have a nonempty ID")
    duplicates = [value for value, count in Counter(identifiers).items() if count > 1]
    if duplicates:
        raise CatalogError("duplicate claim IDs: " + ", ".join(sorted(duplicates)))
    for claim in payload["claims"]:
        unknown = set(claim.get("stages", [])) - stages
        if unknown:
            raise CatalogError(f"{claim['id']}: unknown claim stages: {', '.join(sorted(unknown))}")
        if not claim.get("statement") or not claim.get("evidence"):
            raise CatalogError(f"{claim['id']}: claim statement and evidence are required")
    return set(identifiers)


def validate_catalog() -> dict[str, int]:
    catalog = read_json(CATALOG_ROOT / "catalog.json")
    if catalog.get("schema_version") != 1:
        raise CatalogError("tests/catalog/catalog.json schema_version must be 1")

    stages = validate_stage_catalog()
    claims = validate_claim_catalog(stages)
    fixture_manifests = relative_glob("tests/translator/*/manifest.json")
    application_manifests = relative_glob("benchmarks/*/manifest.json")
    population = catalog.get("population_contract", {})
    expected_fixture_count = population.get("translator_fixtures", {}).get("count")
    expected_application_count = population.get("application_benchmarks", {}).get("count")
    if len(fixture_manifests) != expected_fixture_count:
        raise CatalogError(
            f"translator fixture count differs: expected {expected_fixture_count}, observed {len(fixture_manifests)}"
        )
    if len(application_manifests) != expected_application_count:
        raise CatalogError(
            f"application benchmark count differs: expected {expected_application_count}, observed {len(application_manifests)}"
        )

    registry_rows = read_tsv(REPOSITORY_ROOT / "evaluation" / "registry" / "benchmarks.tsv")
    translator_rows = {
        row["benchmark_id"]: row
        for row in registry_rows
        if row["suite"] == "test" and row["implementation_status"] == "implemented"
    }
    fixture_ids = {path.parent.name for path in fixture_manifests}
    if fixture_ids != set(translator_rows):
        raise CatalogError("translator fixture directories differ from implemented test registry rows")
    for identifier, row in translator_rows.items():
        unknown = set(row["required_stages"].split(",")) - stages
        if unknown:
            raise CatalogError(f"{identifier}: unknown required stages: {', '.join(sorted(unknown))}")
        manifest = read_json(REPOSITORY_ROOT / "tests" / "translator" / identifier / "manifest.json")
        manifest_stages = {stage["name"] for stage in manifest.get("stages", [])}
        unknown = manifest_stages - stages
        if unknown:
            raise CatalogError(f"{identifier}: manifest uses unknown stages: {', '.join(sorted(unknown))}")

    direct_rows = [
        row
        for path in relative_glob("tests/translator/*--software/cases.tsv")
        for row in read_tsv(path)
    ]
    logical_ids = [row["case_id"] for row in direct_rows]
    if len(logical_ids) != len(set(logical_ids)):
        raise CatalogError("focused Lean logical case IDs are not unique")

    behavioral_rows = read_tsv(REPOSITORY_ROOT / "evaluation" / "registry" / "behavioral-coverage.tsv")
    behavioral_ids = {
        row["feature_id"]
        for row in behavioral_rows
        if row["test_module"] in DIRECT_LEAN_MODULES
    }
    if set(logical_ids) != behavioral_ids:
        raise CatalogError("focused Lean catalogs differ from behavioral coverage")

    runner = load_runner()
    discovered = runner.discover_cases()
    runner_ids = {case.test_id for case in discovered}
    focused_runner_ids = {f"lean-case::{identifier}" for identifier in logical_ids}
    if not focused_runner_ids.issubset(runner_ids):
        raise CatalogError("one or more focused Lean logical cases are not discoverable")
    if "lean::RelicoTests" not in runner_ids:
        raise CatalogError("aggregate RelicoTests evidence is not discoverable")
    fixture_runner_ids = {f"fixture::{identifier}" for identifier in fixture_ids}
    discovered_fixture_ids = {
        identifier for identifier in runner_ids if identifier.startswith("fixture::")
    }
    if not fixture_runner_ids.issubset(discovered_fixture_ids):
        raise CatalogError("translator fixture catalog differs from discovered fixture executions")

    matrix_features = validate_general_matrix(
        catalog,
        set(logical_ids),
        fixture_ids,
        runner_ids,
    )

    python_modules = runner.discover_python_modules()
    declared_patterns = next(
        source["discover"]
        for source in catalog["logical_case_sources"]
        if source["kind"] == "python-software-case"
    )
    undeclared_modules = [
        path.relative_to(REPOSITORY_ROOT).as_posix()
        for path in python_modules
        if not any(fnmatch.fnmatch(path.relative_to(REPOSITORY_ROOT).as_posix(), pattern) for pattern in declared_patterns)
    ]
    if undeclared_modules:
        raise CatalogError("Python modules fall outside catalog patterns: " + ", ".join(undeclared_modules))

    fixture_logical_ids = {f"translator.fixture::{identifier}" for identifier in fixture_ids}
    external_ids = {
        f"translator.fixture::{path.parent.name}"
        for path in relative_glob("tests/translator/*/case.json")
        if not (path.parent / "manifest.json").is_file()
    }
    all_logical_ids = fixture_logical_ids | set(logical_ids) | external_ids | {
        case.test_id for case in discovered if case.suite == "python"
    }
    if len(all_logical_ids) != len(fixture_logical_ids) + len(logical_ids) + len(external_ids) + sum(
        case.suite == "python" for case in discovered
    ):
        raise CatalogError("logical case IDs collide across catalog sources")

    evidence_records = (
        len(fixture_ids)
        + (2 * len(logical_ids))
        + len(external_ids)
        + sum(case.suite == "python" for case in discovered)
        + 1
    )

    return {
        "application_benchmarks": len(application_manifests),
        "translator_fixtures": len(fixture_ids),
        "lean_logical_cases": len(logical_ids),
        "python_logical_cases": sum(case.suite == "python" for case in discovered),
        "conditional_external_cases": len(external_ids),
        "logical_cases": len(all_logical_ids),
        "evidence_records": evidence_records,
        "discoverable_executions": len(discovered),
        "paper_claims": len(claims),
        "general_matrix_features": matrix_features,
    }


def main() -> int:
    counts = validate_catalog()
    for name, count in counts.items():
        print(f"{name}={count}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CatalogError as error:
        print(f"catalog validation failed: {error}", file=sys.stderr)
        raise SystemExit(1)
