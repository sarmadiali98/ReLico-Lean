from __future__ import annotations

from collections import Counter
from pathlib import Path
import argparse
import csv
import json
import re
import sys


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
REGISTRY_ROOT = REPOSITORY_ROOT / "tests" / "benchmarks" / "registry"
BENCHMARK_ROOT = REPOSITORY_ROOT / "tests" / "benchmarks"

EXPECTED_BENCHMARKS = 102
EXPECTED_POSITIVE = 101
# One genuine negative remains: core--well-formedness--negative, whose source is
# refused by upstream Timed Rebeca itself (an undefined message server). Every
# other former negative encoded a family bridge limit that the verified general
# fragment has since lifted, and was re-polarized or removed in stage K.
EXPECTED_NEGATIVE = 1
EXPECTED_OBLIGATIONS = 2468
EXPECTED_SHARED_FORMAL = 2
EXPECTED_LEGACY = 6
EXPECTED_CORPUS_CANDIDATES = 81


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
        "corpus": read_tsv("general-corpus-selection.tsv"),
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


def validate_implementation_status(
    benchmark_id: str,
    implementation_status: str,
) -> None:
    if implementation_status not in {
        "planned",
        "implemented",
    }:
        raise RegistryError(
            f"{benchmark_id}: invalid implementation status "
            f"{implementation_status!r}"
        )

    manifest_path = (
        BENCHMARK_ROOT
        / benchmark_id
        / "manifest.json"
    )

    manifest_present = manifest_path.is_file()

    if (
        implementation_status == "implemented"
        and not manifest_present
    ):
        raise RegistryError(
            f"{benchmark_id}: registry status is implemented "
            "but manifest.json is absent"
        )

    if (
        implementation_status == "planned"
        and manifest_present
    ):
        raise RegistryError(
            f"{benchmark_id}: manifest.json exists but "
            "registry status is planned"
        )


# Every human-readable restatement of a registry counter, and which computed
# value it must equal. The triple-lock below (EXPECTED_* constants, the
# obligation_count column sum, the per-benchmark tallies) guards three integers;
# these files restate the same numbers in prose and in audit output where
# nothing checked them, which is how commit d3cbf63 shipped a narrative saying
# 1,928 obligations against a registry holding 2,129.
#
# NOTE "planned source benchmarks" is historical phrasing for "benchmarks in the
# plan", i.e. ALL rows -- not the subset with implementation_status 'planned'.
NARRATIVE_COUNTER_CHECKS = (
    ("tests/benchmarks/registry/PROVENANCE.md",
     r"^- (\S+) accepted Lean test modules$", "modules"),
    ("tests/benchmarks/registry/PROVENANCE.md",
     r"^- (\S+) mapped test obligations$", "obligations"),
    ("tests/benchmarks/registry/PROVENANCE.md",
     r"^- (\S+) planned source benchmarks$", "benchmarks"),
    ("tests/benchmarks/registry/PROVENANCE.md",
     r"^- (\S+) positive benchmarks$", "positive"),
    ("tests/benchmarks/registry/PROVENANCE.md",
     # Singular: exactly one genuine negative remains after the stage K
     # re-polarization, and the sentence should not claim a plural.
     r"^- (\S+) negative benchmarks?$", "negative"),
    ("tests/benchmarks/README.md",
     r"records the (\S+) planned source benchmarks", "benchmarks"),
    ("tests/benchmarks/README.md",
     r"maps all (\S+) Lean test obligations", "obligations"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^TEST_FILE_COUNT=(\d+)$", "modules"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^TEST_OBLIGATION_COUNT=(\d+)$", "obligations"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^ACCEPTED_TEST_FILE_COUNT=(\d+)$", "modules"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^ACCEPTED_OBLIGATION_COUNT=(\d+)$", "obligations"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^FINAL_SOURCE_BENCHMARK_COUNT=(\d+)$", "benchmarks"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^POSITIVE_BENCHMARK_COUNT=(\d+)$", "positive"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^NEGATIVE_BENCHMARK_COUNT=(\d+)$", "negative"),
    ("tests/benchmarks/registry/coverage-audit.txt",
     r"^CORPUS_CANDIDATE_COUNT=(\d+)$", "corpus"),
    ("tests/benchmarks/registry/final-b1-summary.txt",
     r"^INPUT_TEST_FILE_COUNT=(\d+)$", "modules"),
    ("tests/benchmarks/registry/final-b1-summary.txt",
     r"^INPUT_TEST_OBLIGATION_COUNT=(\d+)$", "obligations"),
    ("tests/benchmarks/registry/final-b1-summary.txt",
     r"^FINAL_SOURCE_BENCHMARK_COUNT=(\d+)$", "benchmarks"),
    ("tests/benchmarks/registry/final-b1-summary.txt",
     r"^FINAL_POSITIVE_BENCHMARK_COUNT=(\d+)$", "positive"),
    ("tests/benchmarks/registry/final-b1-summary.txt",
     r"^FINAL_NEGATIVE_BENCHMARK_COUNT=(\d+)$", "negative"),
)


def validate_narrative_counters(
    registry: dict[str, list[dict[str, str]]],
) -> list[str]:
    benchmarks = registry["benchmarks"]
    obligations = registry["obligations"]

    computed = {
        "benchmarks": len(benchmarks),
        "obligations": len(obligations),
        "modules": len({row["test_file"] for row in obligations}),
        "corpus": len(registry["corpus"]),
        "positive": sum(
            row["polarity"] == "positive" for row in benchmarks
        ),
        "negative": sum(
            row["polarity"] == "negative" for row in benchmarks
        ),
    }

    checked = 0

    for relative_path, pattern, key in NARRATIVE_COUNTER_CHECKS:
        path = REPOSITORY_ROOT / relative_path

        if not path.is_file():
            raise RegistryError(
                f"missing narrative file: {relative_path}"
            )

        matches = re.findall(
            pattern,
            path.read_text(encoding="utf-8"),
            re.MULTILINE,
        )

        if not matches:
            raise RegistryError(
                f"{relative_path}: nothing matches {pattern!r} -- a narrative "
                "counter was renamed or removed, so it is no longer checked"
            )

        for raw in matches:
            stated = int(raw.replace(",", ""))

            if stated != computed[key]:
                raise RegistryError(
                    f"{relative_path}: states {raw} for {key}, but the "
                    f"registry computes {computed[key]}"
                )

            checked += 1

    return [
        f"NARRATIVE_COUNTERS_CHECKED={checked}",
        "NARRATIVE_COUNTERS_CONSISTENT=yes",
    ]


def validate_corpus_candidates(
    registry: dict[str, list[dict[str, str]]],
) -> list[str]:
    """
    Check general-corpus-selection.tsv, which records the measured construct
    profile of every candidate general-family source model so that benchmark
    selection is derived from measurement rather than from a hard-coded next
    benchmark.

    The file mixes two populations whose verdicts have different standing, and
    the checks below keep that distinction enforceable: a 'gate-verdict' row is
    an in-repo fixture whose directory is the gate's answer, and its path must
    exist; a 'static-screen' row is an upstream corpus model that has never been
    through the frontend, so its status is a screen against the documented
    exclusion list and its path names an archive entry rather than a file.
    """
    corpus = registry["corpus"]
    benchmarks = registry["benchmarks"]

    require_columns(
        corpus,
        {
            "model_id",
            "origin",
            "path",
            "fragment_status",
            "status_basis",
            "construct_profile",
            "blocking_constructs",
            "refusal_reason",
            "rmc_verdict",
            "candidate_capabilities",
            "candidate_polarity",
        },
        "corpus candidate",
    )

    if len(corpus) != EXPECTED_CORPUS_CANDIDATES:
        raise RegistryError(
            f"corpus candidate count is {len(corpus)}, "
            f"expected {EXPECTED_CORPUS_CANDIDATES}"
        )

    model_ids = [row["model_id"] for row in corpus]

    if len(set(model_ids)) != len(model_ids):
        raise RegistryError("duplicate corpus model identifiers exist")

    known_capabilities = {
        row["primary_capability"] for row in benchmarks
    }

    gate_verdicts = {
        "accepted",
        "refused-by-fragment",
        "refused-upstream",
    }

    # The upstream population no longer carries a static screen. Every one of
    # those rows has been through the real exporter and, where the exporter
    # accepted it, the Lean decoder, so its column is a verdict and its values
    # name the layer that refused.
    frontend_verdicts = {
        "inside-fragment",
        "exporter-refused",
        "lean-refused",
    }

    accepting_verdicts = {"accepted", "inside-fragment"}

    # RMC is the second mandatory gate and is independent of the first: the
    # general fixtures were authored for the frontend and most of them fail the
    # model checker. 'not-measured' is honest rather than absent, and applies to
    # the negative fixtures, which never become a benchmark source.
    rmc_verdicts = {
        "satisfied",
        "deadlock",
        "queue-overflow",
        "no-report",
        "not-measured",
    }

    fixture_count = 0
    upstream_count = 0

    for row in corpus:
        model_id = row["model_id"]

        if row["candidate_polarity"] not in {"positive", "negative"}:
            raise RegistryError(
                f"{model_id}: invalid candidate polarity"
            )

        if row["rmc_verdict"] not in rmc_verdicts:
            raise RegistryError(
                f"{model_id}: unknown RMC verdict "
                f"{row['rmc_verdict']!r}"
            )

        for capability in row["candidate_capabilities"].split(";"):
            if capability not in known_capabilities:
                raise RegistryError(
                    f"{model_id}: candidate capability "
                    f"{capability!r} is not a benchmark capability"
                )

        if row["status_basis"] == "gate-verdict":
            fixture_count += 1

            if row["fragment_status"] not in gate_verdicts:
                raise RegistryError(
                    f"{model_id}: gate verdict "
                    f"{row['fragment_status']!r} is not a gate outcome"
                )

            if not (REPOSITORY_ROOT / row["path"]).is_file():
                raise RegistryError(
                    f"{model_id}: fixture path is absent: {row['path']}"
                )

        elif row["status_basis"] == "frontend-verdict":
            upstream_count += 1

            if row["fragment_status"] not in frontend_verdicts:
                raise RegistryError(
                    f"{model_id}: frontend verdict "
                    f"{row['fragment_status']!r} is not a frontend outcome"
                )

        else:
            raise RegistryError(
                f"{model_id}: unknown status basis "
                f"{row['status_basis']!r}"
            )

        # One rule across both populations: a refused candidate owes a reason
        # and an accepted one must not invent it.
        accepted = row["fragment_status"] in accepting_verdicts

        if accepted != (row["refusal_reason"] == "none"):
            raise RegistryError(
                f"{model_id}: refusal reason disagrees with the verdict "
                f"{row['fragment_status']!r}"
            )

        if accepted != (row["candidate_polarity"] == "positive"):
            raise RegistryError(
                f"{model_id}: candidate polarity disagrees with the verdict "
                f"{row['fragment_status']!r}"
            )

    return [
        f"CORPUS_CANDIDATE_COUNT={len(corpus)}",
        f"CORPUS_FIXTURE_COUNT={fixture_count}",
        f"CORPUS_UPSTREAM_COUNT={upstream_count}",
        "CORPUS_CANDIDATES_CONSISTENT=yes",
    ]


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

        validate_implementation_status(
            benchmark_id,
            row["implementation_status"],
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

    implemented_count = sum(
        row["implementation_status"] == "implemented"
        for row in benchmarks
    )

    planned_count = sum(
        row["implementation_status"] == "planned"
        for row in benchmarks
    )

    narrative = validate_narrative_counters(registry)
    corpus = validate_corpus_candidates(registry)

    return [
        f"BENCHMARK_COUNT={len(benchmarks)}",
        f"IMPLEMENTED_BENCHMARK_COUNT={implemented_count}",
        f"PLANNED_BENCHMARK_COUNT={planned_count}",
        "IMPLEMENTATION_STATUS_AGREEMENT=yes",
        f"POSITIVE_COUNT={positive_count}",
        f"NEGATIVE_COUNT={negative_count}",
        f"OBLIGATION_COUNT={len(obligations)}",
        "UNMAPPED_OBLIGATION_COUNT=0",
        f"SHARED_FORMAL_EVIDENCE_COUNT={len(shared)}",
        f"LEGACY_MIGRATION_COUNT={len(legacy)}",
        *narrative,
        *corpus,
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
