#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import sys

from relico_bench_execution import (
    BenchmarkResult,
    ExecutionError,
    run_benchmark,
)
from relico_bench_registry import (
    RegistryError,
    find_benchmark,
    load_registry,
    validate,
)


def parse_arguments(
    arguments: list[str],
) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="relico-bench",
        description=(
            "Validate and execute the ReLico "
            "Timed Rebeca benchmark corpus."
        ),
    )

    action = parser.add_mutually_exclusive_group(
        required=True,
    )

    action.add_argument(
        "--validate-registry",
        action="store_true",
        help="validate the frozen benchmark registry",
    )

    action.add_argument(
        "--list",
        action="store_true",
        help="list all planned benchmarks",
    )

    action.add_argument(
        "--show",
        metavar="BENCHMARK_ID",
        help="show one planned benchmark",
    )

    action.add_argument(
        "--benchmark",
        metavar="BENCHMARK_ID",
        help="execute one implemented benchmark",
    )

    action.add_argument(
        "--all",
        action="store_true",
        help="execute every implemented benchmark",
    )

    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="record commands without executing stages",
    )

    parser.add_argument(
        "--regenerate",
        action="store_true",
        help=(
            "replace expected artifacts after "
            "a successful benchmark execution"
        ),
    )

    parser.add_argument(
        "--keep-going",
        action="store_true",
        help="continue after a benchmark failure",
    )

    return parser.parse_args(arguments)


def print_benchmark_list(
    benchmarks: list[dict[str, str]],
) -> None:
    print(
        "benchmark_id\tpolarity\tsemantic_layer\t"
        "primary_capability\timplementation_status"
    )

    for row in benchmarks:
        print(
            "\t".join([
                row["benchmark_id"],
                row["polarity"],
                row["semantic_layer"],
                row["primary_capability"],
                row["implementation_status"],
            ])
        )


def run_all(
    *,
    registry: dict[str, list[dict[str, str]]],
    dry_run: bool,
    regenerate: bool,
    keep_going: bool,
) -> int:
    results: list[BenchmarkResult] = []
    not_implemented_count = 0

    for row in registry["benchmarks"]:
        benchmark_id = row["benchmark_id"]

        implementation_status = row[
            "implementation_status"
        ]

        if implementation_status != "implemented":
            not_implemented_count += 1

            print(
                f"NOT_IMPLEMENTED {benchmark_id}"
            )

            continue

        try:
            result = run_benchmark(
                registry=registry,
                benchmark_id=benchmark_id,
                dry_run=dry_run,
                regenerate=regenerate,
            )

        except (
            ExecutionError,
            RegistryError,
        ) as error:
            print(
                f"ERROR {benchmark_id}: {error}",
                file=sys.stderr,
            )

            result = BenchmarkResult(
                benchmark_id=benchmark_id,
                status="fail",
                exit_code=1,
            )

        results.append(result)

        if (
            result.exit_code != 0
            and not keep_going
        ):
            break

    pass_count = sum(
        result.exit_code == 0
        for result in results
    )

    failure_count = sum(
        result.exit_code != 0
        for result in results
    )

    print(
        f"IMPLEMENTED_EXECUTION_COUNT={len(results)}"
    )

    print(
        f"IMPLEMENTED_PASS_COUNT={pass_count}"
    )

    print(
        f"IMPLEMENTED_FAILURE_COUNT={failure_count}"
    )

    print(
        f"NOT_IMPLEMENTED_COUNT={not_implemented_count}"
    )

    corpus_complete = (
        failure_count == 0
        and not_implemented_count == 0
    )

    print(
        "CORPUS_COMPLETE="
        + ("yes" if corpus_complete else "no")
    )

    if failure_count:
        return 1

    if not_implemented_count:
        return 3

    return 0


def main(arguments: list[str]) -> int:
    options = parse_arguments(arguments)

    registry = load_registry()
    validation = validate(registry)

    if options.validate_registry:
        print("\n".join(validation))
        return 0

    if options.list:
        print_benchmark_list(
            registry["benchmarks"]
        )

        return 0

    if options.show:
        print(
            json.dumps(
                find_benchmark(
                    registry,
                    options.show,
                ),
                indent=2,
                sort_keys=True,
            )
        )

        return 0

    if options.regenerate and options.dry_run:
        raise ExecutionError(
            "--regenerate and --dry-run cannot be combined"
        )

    if options.benchmark:
        result = run_benchmark(
            registry=registry,
            benchmark_id=options.benchmark,
            dry_run=options.dry_run,
            regenerate=options.regenerate,
        )

        print(
            "BENCHMARK_RESULT="
            f"{result.benchmark_id}:"
            f"{result.status}:"
            f"{result.exit_code}"
        )

        return result.exit_code

    return run_all(
        registry=registry,
        dry_run=options.dry_run,
        regenerate=options.regenerate,
        keep_going=options.keep_going,
    )


if __name__ == "__main__":
    try:
        raise SystemExit(
            main(sys.argv[1:])
        )

    except (
        ExecutionError,
        RegistryError,
    ) as error:
        print(
            f"relico-bench: {error}",
            file=sys.stderr,
        )

        raise SystemExit(2)
