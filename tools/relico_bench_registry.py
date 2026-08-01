from __future__ import annotations

from collections import Counter
from pathlib import Path
import argparse
import csv
import json
import sys


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
REGISTRY_ROOT = REPOSITORY_ROOT / "tests" / "benchmarks" / "registry"

EXPECTED_BENCHMARKS = 57
EXPECTED_POSITIVE = 42
EXPECTED_NEGATIVE = 15
EXPECTED_OBLIGATIONS = 1928
EXPECTED_SHARED_FORMAL = 2
EXPECTED_LEGACY = 6


class RegistryError(RuntimeError):
    pass


def read_tsv(name: str) -> list[dict[str, str]]:
    path = REGISTRY_ROOT / name

    if not path.is_file():
        raise RegistryError(f"missing registry file: {path}")

    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def load_registry() -> dict[str, list[dict[str, str]]]:
    return {
        "benchmarks": read_tsv("benchmarks.tsv"),
        "obligations": read_tsv("obligations.tsv"),
        "shared": read_tsv("shared-formal-evidence.tsv"),
        "legacy": read_tsv("legacy-script-migration.tsv"),
    }


def require_columns(
    rows: list[dict[str, str]],
    columns: set[str],
    label: str,
) -> None:
    if not rows:
        raise RegistryError(f"{label} registry is empty")

    missing = columns - set(rows[0])

    if missing:
        raise RegistryError(
            f"{label} registry missing columns: "
            + ", ".join(sorted(missing))
        )


def validate(registry: dict[str, list[dict[str, str]]]) -> list[str]:
    benchmarks = registry["benchmarks"]
    obligations = registry["obligations"]
    shared = registry["shared"]
    legacy = registry["legacy"]

    require_columns(
        benchmarks,
        {
            "benchmark_id",
            "semantic_layer",
            "primary_capability",
            "polarity",
            "obligation_count",
            "required_stages",
            "source_path",
            "implementation_status",
        },
        "benchmark",
    )

    require_columns(
        obligations,
        {
            "obligation_id",
            "final_benchmark_id",
            "mapping_status",
        },
        "obligation",
    )

    require_columns(
        shared,
        {
            "test_file",
            "anchor_benchmark",
            "obligation_count",
        },
        "shared formal evidence",
    )

    require_columns(
        legacy,
        {
            "legacy_script",
            "replacement_benchmark",
            "removal_status",
        },
        "legacy migration",
    )

    if len(benchmarks) != EXPECTED_BENCHMARKS:
        raise RegistryError(
            f"benchmark count is {len(benchmarks)}, "
            f"expected {EXPECTED_BENCHMARKS}"
        )

    benchmark_ids = [row["benchmark_id"] for row in benchmarks]
    benchmark_id_set = set(benchmark_ids)

    if len(benchmark_id_set) != len(benchmark_ids):
        raise RegistryError("duplicate benchmark identifiers exist")

    positive_count = sum(
        row["polarity"] == "positive"
        for row in benchmarks
    )

    negative_count = sum(
        row["polarity"] == "negative"
        for row in benchmarks
    )

    if positive_count != EXPECTED_POSITIVE:
        raise RegistryError(
            f"positive count is {positive_count}, "
            f"expected {EXPECTED_POSITIVE}"
        )

    if negative_count != EXPECTED_NEGATIVE:
        raise RegistryError(
            f"negative count is {negative_count}, "
            f"expected {EXPECTED_NEGATIVE}"
        )

    for row in benchmarks:
        benchmark_id = row["benchmark_id"]

        if row["polarity"] not in {"positive", "negative"}:
            raise RegistryError(
                f"{benchmark_id}: invalid polarity"
            )

        expected_source = (
            f"tests/benchmarks/{benchmark_id}/source/model.rebeca"
        )

        if row["source_path"] != expected_source:
            raise RegistryError(
                f"{benchmark_id}: source path differs"
            )

        stages = {
            value.strip()
            for value in row["required_stages"].split(",")
            if value.strip()
        }

        if "source" not in stages:
            raise RegistryError(
                f"{benchmark_id}: source stage is absent"
            )

        if "rmc" not in stages:
            raise RegistryError(
                f"{benchmark_id}: mandatory RMC stage is absent"
            )

    if len(obligations) != EXPECTED_OBLIGATIONS:
        raise RegistryError(
            f"obligation count is {len(obligations)}, "
            f"expected {EXPECTED_OBLIGATIONS}"
        )

    obligation_ids = [
        row["obligation_id"]
        for row in obligations
    ]

    if len(set(obligation_ids)) != len(obligation_ids):
        raise RegistryError(
            "duplicate obligation identifiers exist"
        )

    unmapped = [
        row
        for row in obligations
        if (
            row["mapping_status"] != "accepted"
            or row["final_benchmark_id"] not in benchmark_id_set
        )
    ]

    if unmapped:
        raise RegistryError(
            f"{len(unmapped)} obligations remain unmapped"
        )

    declared_total = sum(
        int(row["obligation_count"])
        for row in benchmarks
    )

    if declared_total != EXPECTED_OBLIGATIONS:
        raise RegistryError(
            f"declared obligation total is {declared_total}, "
            f"expected {EXPECTED_OBLIGATIONS}"
        )

    actual_counts = Counter(
        row["final_benchmark_id"]
        for row in obligations
    )

    for row in benchmarks:
        benchmark_id = row["benchmark_id"]
        declared = int(row["obligation_count"])
        actual = actual_counts[benchmark_id]

        if actual != declared:
            raise RegistryError(
                f"{benchmark_id}: declares {declared} obligations "
                f"but registry contains {actual}"
            )

    if len(shared) != EXPECTED_SHARED_FORMAL:
        raise RegistryError(
            f"shared formal evidence count is {len(shared)}, "
            f"expected {EXPECTED_SHARED_FORMAL}"
        )

    for row in shared:
        if row["anchor_benchmark"] not in benchmark_id_set:
            raise RegistryError(
                "shared formal evidence has an unknown anchor"
            )

    if len(legacy) != EXPECTED_LEGACY:
        raise RegistryError(
            f"legacy migration count is {len(legacy)}, "
            f"expected {EXPECTED_LEGACY}"
        )

    for row in legacy:
        if row["replacement_benchmark"] not in benchmark_id_set:
            raise RegistryError(
                "legacy migration has an unknown replacement"
            )

    return [
        f"BENCHMARK_COUNT={len(benchmarks)}",
        f"POSITIVE_COUNT={positive_count}",
        f"NEGATIVE_COUNT={negative_count}",
        f"OBLIGATION_COUNT={len(obligations)}",
        "UNMAPPED_OBLIGATION_COUNT=0",
        f"SHARED_FORMAL_EVIDENCE_COUNT={len(shared)}",
        f"LEGACY_MIGRATION_COUNT={len(legacy)}",
        "REGISTRY_VALID=yes",
    ]


def find_benchmark(
    registry: dict[str, list[dict[str, str]]],
    benchmark_id: str,
) -> dict[str, str]:
    for row in registry["benchmarks"]:
        if row["benchmark_id"] == benchmark_id:
            return row

    raise RegistryError(f"unknown benchmark: {benchmark_id}")


def parse_arguments(arguments: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="relico-bench-registry"
    )

    action = parser.add_mutually_exclusive_group(required=True)

    action.add_argument("--validate", action="store_true")
    action.add_argument("--list", action="store_true")
    action.add_argument("--show", metavar="BENCHMARK_ID")

    return parser.parse_args(arguments)


def main(arguments: list[str]) -> int:
    options = parse_arguments(arguments)
    registry = load_registry()
    validation = validate(registry)

    if options.validate:
        print("\n".join(validation))
        return 0

    if options.list:
        print(
            "benchmark_id\tpolarity\tsemantic_layer\t"
            "primary_capability\timplementation_status"
        )

        for row in registry["benchmarks"]:
            print(
                "\t".join([
                    row["benchmark_id"],
                    row["polarity"],
                    row["semantic_layer"],
                    row["primary_capability"],
                    row["implementation_status"],
                ])
            )

        return 0

    print(
        json.dumps(
            find_benchmark(registry, options.show),
            indent=2,
            sort_keys=True,
        )
    )

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))

    except RegistryError as error:
        print(
            f"relico-bench-registry: {error}",
            file=sys.stderr,
        )

        raise SystemExit(2)
