from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any
import hashlib
import json
import os
import shlex
import shutil
import subprocess
import time

from relico_bench_registry import (
    REPOSITORY_ROOT,
    RegistryError,
    find_benchmark,
)


BENCHMARK_ROOT = (
    REPOSITORY_ROOT
    / "tests"
    / "benchmarks"
)


class ExecutionError(RuntimeError):
    pass


@dataclass(frozen=True)
class BenchmarkResult:
    benchmark_id: str
    status: str
    exit_code: int


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()

    with path.open("rb") as stream:
        for block in iter(
            lambda: stream.read(1024 * 1024),
            b"",
        ):
            digest.update(block)

    return digest.hexdigest()


def render(
    value: str,
    variables: dict[str, str],
) -> str:
    try:
        return value.format_map(variables)

    except KeyError as error:
        raise ExecutionError(
            "unknown manifest placeholder: "
            f"{error.args[0]}"
        ) from error


def safe_stage_name(value: str) -> str:
    result = "".join(
        character
        if (
            character.isalnum()
            or character in {"-", "_"}
        )
        else "-"
        for character in value
    ).strip("-")

    if not result:
        raise ExecutionError(
            f"invalid stage name: {value!r}"
        )

    return result


def probe_tool(
    command: list[str],
) -> dict[str, Any]:
    executable = shutil.which(command[0])

    if executable is None:
        return {
            "available": False,
            "command": command,
        }

    try:
        completed = subprocess.run(
            command,
            cwd=REPOSITORY_ROOT,
            text=True,
            capture_output=True,
            timeout=20,
            check=False,
        )

        return {
            "available": True,
            "path": executable,
            "exit_code": completed.returncode,
            "output": (
                completed.stdout
                + completed.stderr
            ).strip(),
        }

    except subprocess.TimeoutExpired:
        return {
            "available": True,
            "path": executable,
            "timeout": True,
        }


def capture_toolchain(actual_root: Path) -> None:
    commands = {
        "python3": [
            "python3",
            "--version",
        ],
        "java": [
            "java",
            "-version",
        ],
        "lake": [
            "lake",
            "--version",
        ],
        "lean": [
            "lean",
            "--version",
        ],
        "lfc": [
            "lfc",
            "--version",
        ],
        "git": [
            "git",
            "--version",
        ],
        "g++": [
            "g++",
            "--version",
        ],
        "clang++": [
            "clang++",
            "--version",
        ],
    }

    result = {
        name: probe_tool(command)
        for name, command in commands.items()
    }

    (actual_root / "toolchain.json").write_text(
        json.dumps(
            result,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def write_artifact_index(actual_root: Path) -> None:
    output = actual_root / "artifact-index.tsv"
    records = [
        "sha256\tsize\tpath"
    ]

    for path in sorted(actual_root.rglob("*")):
        if not path.is_file() or path == output:
            continue

        records.append(
            "\t".join([
                sha256_file(path),
                str(path.stat().st_size),
                str(path.relative_to(actual_root)),
            ])
        )

    output.write_text(
        "\n".join(records) + "\n",
        encoding="utf-8",
    )


def load_manifest(
    benchmark_id: str,
) -> tuple[Path, dict[str, Any]]:
    benchmark_directory = (
        BENCHMARK_ROOT
        / benchmark_id
    )

    manifest_path = (
        benchmark_directory
        / "manifest.json"
    )

    if not manifest_path.is_file():
        raise ExecutionError(
            f"{benchmark_id}: manifest is not implemented"
        )

    try:
        with manifest_path.open(
            encoding="utf-8",
        ) as stream:
            manifest = json.load(stream)

    except json.JSONDecodeError as error:
        raise ExecutionError(
            f"{benchmark_id}: invalid manifest JSON: {error}"
        ) from error

    if not isinstance(manifest, dict):
        raise ExecutionError(
            f"{benchmark_id}: manifest root is not an object"
        )

    required_fields = {
        "schema_version",
        "benchmark_id",
        "description",
        "polarity",
        "expected_terminal_stage",
        "source_files",
        "stages",
    }

    missing = required_fields - set(manifest)

    if missing:
        raise ExecutionError(
            f"{benchmark_id}: manifest is missing "
            + ", ".join(sorted(missing))
        )

    if manifest["schema_version"] != 1:
        raise ExecutionError(
            f"{benchmark_id}: unsupported manifest version"
        )

    if manifest["benchmark_id"] != benchmark_id:
        raise ExecutionError(
            f"{benchmark_id}: manifest identifier differs"
        )

    if manifest["polarity"] not in {
        "positive",
        "negative",
    }:
        raise ExecutionError(
            f"{benchmark_id}: invalid polarity"
        )

    sources = manifest["source_files"]

    if (
        not isinstance(sources, list)
        or not sources
        or not all(
            isinstance(value, str)
            for value in sources
        )
    ):
        raise ExecutionError(
            f"{benchmark_id}: source_files is invalid"
        )

    for relative in sources:
        if (
            not relative.startswith("source/")
            or not relative.endswith(".rebeca")
        ):
            raise ExecutionError(
                f"{benchmark_id}: invalid source path "
                f"{relative!r}"
            )

        source_path = (
            benchmark_directory
            / relative
        )

        if not source_path.is_file():
            raise ExecutionError(
                f"{benchmark_id}: source is missing: "
                f"{relative}"
            )

    stages = manifest["stages"]

    if not isinstance(stages, list) or not stages:
        raise ExecutionError(
            f"{benchmark_id}: no stages are declared"
        )

    stage_names: set[str] = set()

    for stage in stages:
        if not isinstance(stage, dict):
            raise ExecutionError(
                f"{benchmark_id}: stage is not an object"
            )

        name = stage.get("name")

        if not isinstance(name, str) or not name:
            raise ExecutionError(
                f"{benchmark_id}: invalid stage name"
            )

        if name in stage_names:
            raise ExecutionError(
                f"{benchmark_id}: duplicate stage {name}"
            )

        stage_names.add(name)

        has_command = "command" in stage
        has_shell = "shell" in stage

        if has_command == has_shell:
            raise ExecutionError(
                f"{benchmark_id}/{name}: exactly one of "
                "command or shell is required"
            )

        if has_command:
            command = stage["command"]

            if (
                not isinstance(command, list)
                or not command
                or not all(
                    isinstance(value, str)
                    for value in command
                )
            ):
                raise ExecutionError(
                    f"{benchmark_id}/{name}: command is invalid"
                )

        if (
            has_shell
            and not isinstance(stage["shell"], str)
        ):
            raise ExecutionError(
                f"{benchmark_id}/{name}: shell is invalid"
            )

    if "rmc" not in stage_names:
        raise ExecutionError(
            f"{benchmark_id}: mandatory RMC stage is absent"
        )

    expected_terminal_stage = manifest[
        "expected_terminal_stage"
    ]

    if (
        not isinstance(expected_terminal_stage, str)
        or not expected_terminal_stage
    ):
        raise ExecutionError(
            f"{benchmark_id}: expected terminal stage is invalid"
        )

    if expected_terminal_stage not in stage_names:
        raise ExecutionError(
            f"{benchmark_id}: expected terminal stage "
            f"{expected_terminal_stage!r} is not declared"
        )

    final_declared_stage = str(stages[-1]["name"])

    if final_declared_stage != expected_terminal_stage:
        raise ExecutionError(
            f"{benchmark_id}: expected terminal stage "
            f"{expected_terminal_stage!r} must be the final "
            f"declared stage, not {final_declared_stage!r}"
        )

    artifacts = manifest.get(
        "expected_artifacts",
        [],
    )

    if not isinstance(artifacts, list):
        raise ExecutionError(
            f"{benchmark_id}: expected_artifacts is invalid"
        )

    for artifact in artifacts:
        if not isinstance(artifact, dict):
            raise ExecutionError(
                f"{benchmark_id}: artifact entry is invalid"
            )

        relative = artifact.get("path")

        if not isinstance(relative, str) or not relative:
            raise ExecutionError(
                f"{benchmark_id}: artifact path is invalid"
            )

        relative_path = Path(relative)

        if (
            relative_path.is_absolute()
            or relative_path == Path(".")
            or ".." in relative_path.parts
        ):
            raise ExecutionError(
                f"{benchmark_id}: unsafe artifact path "
                f"{relative!r}"
            )

        required = artifact.get("required", True)

        if not isinstance(required, bool):
            raise ExecutionError(
                f"{benchmark_id}: artifact required flag "
                "is invalid"
            )

        expected_sha256 = artifact.get("sha256")

        if (
            expected_sha256 is not None
            and (
                not isinstance(expected_sha256, str)
                or len(expected_sha256) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in expected_sha256
                )
            )
        ):
            raise ExecutionError(
                f"{benchmark_id}: artifact SHA-256 is invalid"
            )

    return benchmark_directory, manifest


def run_stage(
    *,
    benchmark_id: str,
    benchmark_directory: Path,
    actual_root: Path,
    stage: dict[str, Any],
    index: int,
    variables: dict[str, str],
    dry_run: bool,
) -> tuple[str, int]:
    name = str(stage["name"])

    stage_directory = (
        actual_root
        / f"{index:02d}-{safe_stage_name(name)}"
    )

    stage_directory.mkdir(
        parents=True,
        exist_ok=True,
    )

    timeout_seconds = int(
        stage.get(
            "timeout_seconds",
            300,
        )
    )

    if timeout_seconds < 1:
        raise ExecutionError(
            f"{benchmark_id}/{name}: timeout must be positive"
        )

    expected_exit_codes = stage.get(
        "expected_exit_codes",
        [0],
    )

    if (
        not isinstance(expected_exit_codes, list)
        or not expected_exit_codes
        or not all(
            isinstance(value, int)
            for value in expected_exit_codes
        )
    ):
        raise ExecutionError(
            f"{benchmark_id}/{name}: "
            "expected_exit_codes is invalid"
        )

    cwd_text = render(
        str(
            stage.get(
                "cwd",
                "{benchmark}",
            )
        ),
        variables,
    )

    cwd = Path(cwd_text)

    if not cwd.is_absolute():
        cwd = (
            benchmark_directory
            / cwd
        )

    cwd = cwd.resolve()

    environment = os.environ.copy()
    declared_environment = stage.get(
        "environment",
        {},
    )

    if not isinstance(
        declared_environment,
        dict,
    ):
        raise ExecutionError(
            f"{benchmark_id}/{name}: environment is invalid"
        )

    for key, value in declared_environment.items():
        if (
            not isinstance(key, str)
            or not isinstance(value, str)
        ):
            raise ExecutionError(
                f"{benchmark_id}/{name}: "
                "environment entry is invalid"
            )

        environment[key] = render(
            value,
            variables,
        )

    if "command" in stage:
        command = [
            render(
                value,
                variables,
            )
            for value in stage["command"]
        ]

    else:
        command = [
            "/bin/bash",
            "-lc",
            render(
                stage["shell"],
                variables,
            ),
        ]

    (stage_directory / "command.json").write_text(
        json.dumps(
            command,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    (stage_directory / "command.txt").write_text(
        shlex.join(command) + "\n",
        encoding="utf-8",
    )

    (stage_directory / "cwd.txt").write_text(
        str(cwd) + "\n",
        encoding="utf-8",
    )

    if dry_run:
        result = {
            "schema_version": 1,
            "benchmark_id": benchmark_id,
            "stage": name,
            "status": "not-run",
            "exit_code": None,
            "duration_ms": 0,
            "command": command,
        }

        (stage_directory / "stage-result.json").write_text(
            json.dumps(
                result,
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )

        (stage_directory / "status.txt").write_text(
            "not-run\n",
            encoding="utf-8",
        )

        print(
            f"DRY_RUN {benchmark_id}/{name}: "
            f"{shlex.join(command)}"
        )

        return "not-run", 0

    stdout_path = (
        stage_directory
        / "stdout.txt"
    )

    stderr_path = (
        stage_directory
        / "stderr.txt"
    )

    start = time.monotonic()

    try:
        with (
            stdout_path.open(
                "w",
                encoding="utf-8",
            ) as stdout_stream,
            stderr_path.open(
                "w",
                encoding="utf-8",
            ) as stderr_stream,
        ):
            completed = subprocess.run(
                command,
                cwd=cwd,
                env=environment,
                stdout=stdout_stream,
                stderr=stderr_stream,
                timeout=timeout_seconds,
                check=False,
            )

        exit_code = completed.returncode

        status = (
            "pass"
            if exit_code in expected_exit_codes
            else "fail"
        )

    except subprocess.TimeoutExpired:
        exit_code = 124
        status = "timeout"

        with stderr_path.open(
            "a",
            encoding="utf-8",
        ) as stream:
            stream.write(
                "\nPROCESS_TIMEOUT_SECONDS="
                f"{timeout_seconds}\n"
            )

    except OSError as error:
        exit_code = 127
        status = "fail"

        stderr_path.write_text(
            f"{type(error).__name__}: {error}\n",
            encoding="utf-8",
        )

    duration_ms = round(
        (
            time.monotonic()
            - start
        )
        * 1000
    )

    result = {
        "schema_version": 1,
        "benchmark_id": benchmark_id,
        "stage": name,
        "status": status,
        "exit_code": exit_code,
        "duration_ms": duration_ms,
        "command": command,
    }

    (stage_directory / "stage-result.json").write_text(
        json.dumps(
            result,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    (stage_directory / "exit-code.txt").write_text(
        f"{exit_code}\n",
        encoding="utf-8",
    )

    (stage_directory / "duration-ms.txt").write_text(
        f"{duration_ms}\n",
        encoding="utf-8",
    )

    (stage_directory / "status.txt").write_text(
        status + "\n",
        encoding="utf-8",
    )

    print(
        f"{status.upper()} {benchmark_id}/{name} "
        f"exit={exit_code} duration_ms={duration_ms}"
    )

    return status, exit_code


def verify_expected_artifacts(
    benchmark_id: str,
    manifest: dict[str, Any],
    actual_root: Path,
) -> list[str]:
    artifacts = manifest.get(
        "expected_artifacts",
        [],
    )

    if not isinstance(artifacts, list):
        raise ExecutionError(
            f"{benchmark_id}: expected_artifacts is invalid"
        )

    failures: list[str] = []

    for artifact in artifacts:
        if not isinstance(artifact, dict):
            raise ExecutionError(
                f"{benchmark_id}: artifact entry is invalid"
            )

        relative = artifact.get("path")

        if not isinstance(relative, str) or not relative:
            raise ExecutionError(
                f"{benchmark_id}: artifact path is invalid"
            )

        path = actual_root / relative
        required = bool(
            artifact.get(
                "required",
                True,
            )
        )

        if required and not path.is_file():
            failures.append(
                f"missing required artifact: {relative}"
            )

            continue

        expected_sha256 = artifact.get(
            "sha256"
        )

        if (
            expected_sha256 is not None
            and path.is_file()
            and sha256_file(path) != expected_sha256
        ):
            failures.append(
                f"artifact SHA-256 differs: {relative}"
            )

    return failures


def regenerate_expected_artifacts(
    *,
    benchmark_id: str,
    benchmark_directory: Path,
    manifest: dict[str, Any],
    actual_root: Path,
) -> None:
    artifacts = manifest.get(
        "expected_artifacts",
        [],
    )

    if not artifacts:
        raise ExecutionError(
            f"{benchmark_id}: --regenerate requires at "
            "least one declared expected artifact"
        )

    expected_root = (
        benchmark_directory
        / "expected"
    )

    temporary_root = (
        benchmark_directory
        / ".expected-regeneration"
    )

    if temporary_root.exists():
        shutil.rmtree(temporary_root)

    temporary_root.mkdir(
        parents=True,
        exist_ok=False,
    )

    copied_count = 0

    try:
        for artifact in artifacts:
            relative = Path(
                str(artifact["path"])
            )

            source = actual_root / relative

            if not source.is_file():
                if bool(
                    artifact.get(
                        "required",
                        True,
                    )
                ):
                    raise ExecutionError(
                        f"{benchmark_id}: cannot regenerate "
                        f"missing artifact {relative}"
                    )

                continue

            destination = (
                temporary_root
                / relative
            )

            destination.parent.mkdir(
                parents=True,
                exist_ok=True,
            )

            shutil.copy2(
                source,
                destination,
            )

            copied_count += 1

        if copied_count == 0:
            raise ExecutionError(
                f"{benchmark_id}: regeneration selected "
                "no existing artifacts"
            )

        if expected_root.exists():
            shutil.rmtree(expected_root)

        temporary_root.replace(
            expected_root
        )

    except Exception:
        if temporary_root.exists():
            shutil.rmtree(temporary_root)

        raise


def run_benchmark(
    *,
    registry: dict[str, list[dict[str, str]]],
    benchmark_id: str,
    dry_run: bool,
    regenerate: bool,
) -> BenchmarkResult:
    try:
        registry_row = find_benchmark(
            registry,
            benchmark_id,
        )

    except RegistryError as error:
        raise ExecutionError(str(error)) from error

    implementation_status = registry_row.get(
        "implementation_status"
    )

    if implementation_status != "implemented":
        raise ExecutionError(
            f"{benchmark_id}: registry status is "
            f"{implementation_status!r}, expected "
            "'implemented'"
        )

    benchmark_directory, manifest = load_manifest(
        benchmark_id
    )

    if manifest["polarity"] != registry_row["polarity"]:
        raise ExecutionError(
            f"{benchmark_id}: manifest polarity "
            "differs from registry"
        )

    actual_root = (
        benchmark_directory
        / "actual"
    )

    if actual_root.exists():
        shutil.rmtree(actual_root)

    actual_root.mkdir(
        parents=True,
        exist_ok=True,
    )

    capture_toolchain(actual_root)

    variables = {
        "repo": str(REPOSITORY_ROOT),
        "benchmark": str(benchmark_directory),
        "actual": str(actual_root),
        "expected": str(
            benchmark_directory
            / "expected"
        ),
        "source": str(
            benchmark_directory
            / manifest["source_files"][0]
        ),
    }

    overall_status = "pass"
    overall_exit_code = 0
    last_stage_name: str | None = None

    for index, stage in enumerate(
        manifest["stages"],
        start=1,
    ):
        last_stage_name = str(stage["name"])

        status, exit_code = run_stage(
            benchmark_id=benchmark_id,
            benchmark_directory=benchmark_directory,
            actual_root=actual_root,
            stage=stage,
            index=index,
            variables=variables,
            dry_run=dry_run,
        )

        if status in {
            "fail",
            "timeout",
        }:
            if bool(
                stage.get(
                    "required",
                    True,
                )
            ):
                overall_status = status
                overall_exit_code = (
                    exit_code
                    if exit_code != 0
                    else 1
                )

            if not bool(
                stage.get(
                    "continue_on_failure",
                    False,
                )
            ):
                break

    expected_terminal_stage = str(
        manifest["expected_terminal_stage"]
    )

    terminal_stage_reached = (
        not dry_run
        and overall_status == "pass"
        and last_stage_name == expected_terminal_stage
    )

    if not dry_run and not terminal_stage_reached:
        overall_status = "fail"

        if overall_exit_code == 0:
            overall_exit_code = 1

        (
            actual_root
            / "terminal-stage-validation.txt"
        ).write_text(
            "expected_terminal_stage="
            + expected_terminal_stage
            + "\nactual_terminal_stage="
            + str(last_stage_name)
            + "\nterminal_stage_reached=no\n",
            encoding="utf-8",
        )

    artifact_failures = (
        []
        if dry_run or not terminal_stage_reached
        else verify_expected_artifacts(
            benchmark_id,
            manifest,
            actual_root,
        )
    )

    if artifact_failures:
        overall_status = "fail"
        overall_exit_code = 1

        (
            actual_root
            / "artifact-validation.txt"
        ).write_text(
            "\n".join(artifact_failures) + "\n",
            encoding="utf-8",
        )

    summary = {
        "schema_version": 1,
        "benchmark_id": benchmark_id,
        "status": (
            "dry-run"
            if dry_run
            else overall_status
        ),
        "exit_code": overall_exit_code,
        "polarity": manifest["polarity"],
        "expected_terminal_stage": (
            manifest[
                "expected_terminal_stage"
            ]
        ),
        "actual_terminal_stage": last_stage_name,
        "terminal_stage_reached": (
            terminal_stage_reached
        ),
    }

    (actual_root / "run-summary.json").write_text(
        json.dumps(
            summary,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    write_artifact_index(actual_root)

    if (
        regenerate
        and not dry_run
        and overall_status == "pass"
    ):
        regenerate_expected_artifacts(
            benchmark_id=benchmark_id,
            benchmark_directory=benchmark_directory,
            manifest=manifest,
            actual_root=actual_root,
        )

        print(
            f"REGENERATED {benchmark_id}"
        )

    return BenchmarkResult(
        benchmark_id=benchmark_id,
        status=(
            "dry-run"
            if dry_run
            else overall_status
        ),
        exit_code=overall_exit_code,
    )
