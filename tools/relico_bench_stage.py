from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET

RMC_SHA256 = "a39112046d99e0895cf47f890242ace21db896e609f7eef86751a0d416d477f5"
PARSER_ZIP_SHA256 = "b58052952cb753d554696dd1c23dc4c43f43648228221a8ff2f494311dc41586"
LFC_SHA256 = "a8e277076ef578a677fdf7731d95d3ee745e47266ea68d37a673f44bf069cf8a"
class StageError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_file(path: Path, label: str) -> None:
    if not path.is_file():
        raise StageError(f"{label} is missing: {path}")


def require_hash(path: Path, expected: str, label: str) -> None:
    require_file(path, label)
    actual = sha256_file(path)
    if actual != expected:
        raise StageError(
            f"{label} SHA-256 differs: expected {expected}, observed {actual}"
        )


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def run_checked(
    command: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int,
    capture: bool = False,
) -> subprocess.CompletedProcess[str]:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            env=env,
            text=True,
            capture_output=capture,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise StageError(
            f"command timed out after {timeout} seconds: {command!r}"
        ) from error
    except OSError as error:
        raise StageError(f"command could not start: {command!r}: {error}") from error

    if capture:
        if completed.stdout:
            sys.stdout.write(completed.stdout)
        if completed.stderr:
            sys.stderr.write(completed.stderr)

    if completed.returncode != 0:
        raise StageError(
            f"command exited {completed.returncode}: {command!r}"
        )

    return completed


def source_stage(options: argparse.Namespace) -> None:
    source = Path(options.source).resolve()
    require_file(source, "benchmark source")
    write_json(
        Path(options.output),
        {
            "benchmark_id": options.benchmark_id,
            "schema_version": 1,
            "sha256": sha256_file(source),
            "status": "pass",
        },
    )


def rmc_stage(options: argparse.Namespace) -> None:
    source = Path(options.source).resolve()
    actual = Path(options.actual).resolve()
    jar = Path(options.rmc_jar).resolve()
    java = Path(options.java).resolve()
    cxx = Path(options.cxx).resolve()
    output = Path(options.output).resolve()

    require_file(source, "benchmark source")
    require_hash(jar, RMC_SHA256, "RMC 2.14 JAR")
    require_file(java, "Java executable")
    require_file(cxx, "C++ compiler")

    work = actual / "work" / "rmc"
    generated = work / "generated"
    checker = work / "rmc-model-checker"
    if work.exists():
        shutil.rmtree(work)
    generated.mkdir(parents=True)

    run_checked(
        [
            str(java),
            "-jar",
            str(jar),
            "-s",
            str(source),
            "-o",
            str(generated),
            "-v",
            "2.1",
            "-e",
            "TIMED_REBECA",
        ],
        timeout=180,
    )

    cpp_files = sorted(generated.glob("*.cpp"))
    if not cpp_files:
        raise StageError("RMC generated no C++ translation units")

    run_checked(
        [
            str(cxx),
            "-std=c++17",
            "-O2",
            "-pthread",
            "-I",
            str(generated),
            *[str(path) for path in cpp_files],
            "-o",
            str(checker),
        ],
        timeout=180,
    )

    model_run = run_checked(
        [str(checker)],
        timeout=60,
        capture=True,
    )

    try:
        report = ET.fromstring(model_run.stdout)
        property_name = report.findtext("./checked-property/name")
        result = report.findtext("./checked-property/result")
    except ET.ParseError as error:
        raise StageError("RMC model-checker output is not valid XML") from error

    if not property_name or not result:
        raise StageError("RMC report lacks checked-property name or result")
    if result.strip() != "satisfied":
        raise StageError(f"RMC checked-property verdict is {result!r}")

    write_json(
        output,
        {
            "checked_property": property_name.strip(),
            "result": result.strip(),
            "rmc_version": "2.14",
            "schema_version": 1,
        },
    )


def parser_json_stage(options: argparse.Namespace) -> None:
    repo = Path(options.repo).resolve()
    source = Path(options.source).resolve()
    artifact_zip = Path(options.artifact_zip).resolve()
    maven = Path(options.maven).resolve()
    output = Path(options.output).resolve()

    require_file(source, "benchmark source")
    require_hash(artifact_zip, PARSER_ZIP_SHA256, "trusted parser ZIP")
    require_file(maven, "Apache Maven executable")

    script = repo / "frontend/java-bridge/run-from-zip.sh"
    require_file(script, "parser bridge runner")

    version = run_checked(
        [str(maven), "-version"],
        timeout=30,
        capture=True,
    )
    if "Apache Maven" not in version.stdout + version.stderr:
        raise StageError(f"not an Apache Maven executable: {maven}")

    work = Path(options.actual).resolve() / "work" / "parser"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    raw_output = work / "model.json"

    environment = os.environ.copy()
    environment["RELICO_MAVEN"] = str(maven)
    environment["PATH"] = "/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin"

    run_checked(
        [
            "/bin/bash",
            str(script),
            str(artifact_zip),
            str(source),
            str(raw_output),
        ],
        cwd=repo,
        env=environment,
        timeout=300,
    )

    try:
        value = json.loads(raw_output.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise StageError("parser bridge did not produce valid JSON") from error

    write_json(output, value)


def lean_export_stage(options: argparse.Namespace) -> None:
    repo = Path(options.repo).resolve()
    input_path = Path(options.input).resolve()
    output = Path(options.output).resolve()
    lake = Path(options.lake).resolve()

    require_file(input_path, "Lean exporter input")
    require_file(lake, "Lake executable")
    exporter = repo / "Relico/Benchmark/ArtifactExporter.lean"
    require_file(exporter, "Lean artifact exporter")
    output.parent.mkdir(parents=True, exist_ok=True)

    run_checked(
        [
            str(lake),
            "env",
            "lean",
            "--run",
            "Relico/Benchmark/ArtifactExporter.lean",
            options.mode,
            str(input_path),
            str(output),
        ],
        cwd=repo,
        timeout=300,
    )
    require_file(output, f"Lean {options.mode} output")


def formal_witness_value(
    coverage: dict[str, object],
) -> dict[str, object]:
    benchmark_id = coverage.get("benchmark_id")
    if not isinstance(benchmark_id, str) or not benchmark_id:
        raise StageError("coverage benchmark identifier is invalid")

    declared_count = coverage.get("obligation_count")
    if not isinstance(declared_count, int) or declared_count < 1:
        raise StageError("coverage obligation count is invalid")

    declared_modules = coverage.get("test_modules")
    if (
        not isinstance(declared_modules, list)
        or not declared_modules
        or not all(
            isinstance(module, str) and module
            for module in declared_modules
        )
    ):
        raise StageError("coverage test modules are invalid")

    if len(set(declared_modules)) != len(declared_modules):
        raise StageError("coverage test modules contain duplicates")

    if declared_modules != sorted(declared_modules):
        raise StageError("coverage test modules are not deterministic")

    for module in declared_modules:
        module_path = Path(module)
        if (
            module_path.is_absolute()
            or ".." in module_path.parts
            or module_path.suffix != ".lean"
        ):
            raise StageError(
                f"coverage test module path is unsafe: {module}"
            )

    obligations = coverage.get("obligations")
    if not isinstance(obligations, list):
        raise StageError("coverage obligations are invalid")

    obligation_ids: list[str] = []
    obligation_modules: list[str] = []

    for obligation in obligations:
        if not isinstance(obligation, dict):
            raise StageError("coverage obligation entry is invalid")

        obligation_id = obligation.get("obligation_id")
        if not isinstance(obligation_id, str) or not obligation_id:
            raise StageError(
                "coverage obligation identifier is invalid"
            )

        if obligation.get("mapping_status") != "accepted":
            raise StageError(
                f"coverage obligation is not accepted: {obligation_id}"
            )

        if obligation.get("final_benchmark_id") != benchmark_id:
            raise StageError(
                f"coverage obligation maps elsewhere: {obligation_id}"
            )

        test_file = obligation.get("test_file")
        if not isinstance(test_file, str) or not test_file:
            raise StageError(
                f"coverage obligation test file is invalid: "
                f"{obligation_id}"
            )

        test_path = Path(test_file)
        if (
            test_path.is_absolute()
            or ".." in test_path.parts
            or test_path.suffix != ".lean"
        ):
            raise StageError(
                f"coverage obligation test path is unsafe: "
                f"{test_file}"
            )

        obligation_ids.append(obligation_id)
        obligation_modules.append(test_file)

    if len(obligation_ids) != declared_count:
        raise StageError(
            f"formal witness coverage is {len(obligation_ids)}, "
            f"expected {declared_count}"
        )

    if len(set(obligation_ids)) != len(obligation_ids):
        raise StageError(
            "coverage obligation identifiers contain duplicates"
        )

    observed_modules = sorted(set(obligation_modules))
    if observed_modules != declared_modules:
        raise StageError(
            "coverage test modules differ from obligation evidence"
        )

    return {
        "benchmark_id": benchmark_id,
        "elaborated_modules": declared_modules,
        "obligation_count": declared_count,
        "obligation_ids": obligation_ids,
        "schema_version": 1,
        "status": "pass",
    }


def formal_witness_stage(options: argparse.Namespace) -> None:
    repo = Path(options.repo).resolve()
    coverage_path = Path(options.coverage).resolve()
    output = Path(options.output).resolve()
    lake = Path(options.lake).resolve()

    require_file(coverage_path, "coverage manifest")
    require_file(lake, "Lake executable")

    try:
        coverage = json.loads(
            coverage_path.read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError) as error:
        raise StageError(
            "coverage manifest is not valid JSON"
        ) from error

    if not isinstance(coverage, dict):
        raise StageError("coverage manifest root is not an object")

    witness = formal_witness_value(coverage)
    modules = witness["elaborated_modules"]

    if not isinstance(modules, list):
        raise StageError("formal witness module list is invalid")

    for module in modules:
        if not isinstance(module, str):
            raise StageError("formal witness module is invalid")

        module_path = repo / module
        require_file(module_path, "formal witness module")

        run_checked(
            [str(lake), "env", "lean", module],
            cwd=repo,
            timeout=300,
        )

    write_json(output, witness)


def lfc_stage(options: argparse.Namespace) -> None:
    lf_source = Path(options.lf_source).resolve()
    work = Path(options.work_directory).resolve()
    lfc = Path(options.lfc).resolve()
    output = Path(options.output).resolve()

    require_file(lf_source, "LF source")
    require_hash(lfc, LFC_SHA256, "lfc executable")
    if work.exists():
        shutil.rmtree(work)
    source_directory = work / "src"
    source_directory.mkdir(parents=True)
    staged_source = source_directory / "V0Controller.lf"
    shutil.copy2(lf_source, staged_source)

    run_checked(
        [str(lfc), "src/V0Controller.lf"],
        cwd=work,
        timeout=600,
    )

    executable = work / "bin" / "V0Controller"
    require_file(executable, "generated V0Controller executable")
    if not os.access(executable, os.X_OK):
        raise StageError(f"generated executable is not executable: {executable}")

    version = run_checked(
        [str(lfc), "--version"],
        timeout=30,
        capture=True,
    )
    version_text = (version.stdout + version.stderr).strip()
    if version_text != "lfc 0.11.0":
        raise StageError(f"unexpected lfc version: {version_text!r}")

    write_json(
        output,
        {
            "binary": "V0Controller",
            "compiler": version_text,
            "schema_version": 1,
            "status": "pass",
        },
    )


def runtime_stage(options: argparse.Namespace) -> None:
    executable = Path(options.executable).resolve()
    output = Path(options.output).resolve()
    require_file(executable, "native executable")
    if not os.access(executable, os.X_OK):
        raise StageError(f"native executable is not executable: {executable}")

    arguments = ["--timeout", "5 msec", "--fast"]
    run_checked(
        [str(executable), *arguments],
        timeout=10,
        capture=True,
    )

    write_json(
        output,
        {
            "arguments": arguments,
            "exit_code": 0,
            "external_timeout": False,
            "schema_version": 1,
            "status": "pass",
        },
    )



def load_json_object(
    path: Path,
    label: str,
) -> dict[str, object]:
    require_file(path, label)

    try:
        value = json.loads(
            path.read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError) as error:
        raise StageError(
            f"{label} is not valid JSON: {path}"
        ) from error

    if not isinstance(value, dict):
        raise StageError(
            f"{label} root is not an object: {path}"
        )

    return value


def expected_absence_value(
    *,
    benchmark_id: str,
    failed_stage: str,
    stage_result: dict[str, object],
    combined_output: str,
    expected_exit_code: int,
    required_diagnostic: str,
    forbidden_artifact_count: int,
    present_artifact_count: int,
) -> dict[str, object]:
    if stage_result.get("benchmark_id") != benchmark_id:
        raise StageError(
            "failed-stage result benchmark identifier differs"
        )

    if stage_result.get("stage") != failed_stage:
        raise StageError(
            "failed-stage result stage identifier differs"
        )

    if stage_result.get("status") != "pass":
        raise StageError(
            "failed-stage result was not accepted by the runner"
        )

    if stage_result.get("exit_code") != expected_exit_code:
        raise StageError(
            "failed-stage exit code differs: expected "
            f"{expected_exit_code}, observed "
            f"{stage_result.get('exit_code')!r}"
        )

    if not required_diagnostic:
        raise StageError(
            "required boundary diagnostic is empty"
        )

    if required_diagnostic not in combined_output:
        raise StageError(
            "required boundary diagnostic was not observed"
        )

    if forbidden_artifact_count < 1:
        raise StageError(
            "no forbidden post-rejection artifacts were declared"
        )

    if present_artifact_count != 0:
        raise StageError(
            "an artifact exists beyond the expected rejection boundary"
        )

    return {
        "benchmark_id": benchmark_id,
        "boundary_stage": failed_stage,
        "expected_exit_code": expected_exit_code,
        "forbidden_artifact_count": forbidden_artifact_count,
        "observed_exit_code": expected_exit_code,
        "required_diagnostic": required_diagnostic,
        "schema_version": 1,
        "status": "expected-rejection",
    }


def expected_absence_stage(
    options: argparse.Namespace,
) -> None:
    stage_result_path = Path(
        options.stage_result
    ).resolve()

    stdout_path = Path(options.stdout).resolve()
    stderr_path = Path(options.stderr).resolve()

    stage_result = load_json_object(
        stage_result_path,
        "failed-stage result",
    )

    require_file(
        stdout_path,
        "failed-stage stdout",
    )

    require_file(
        stderr_path,
        "failed-stage stderr",
    )

    forbidden_artifacts = [
        Path(value).resolve()
        for value in options.forbidden_artifact
    ]

    present_artifacts = [
        path
        for path in forbidden_artifacts
        if path.exists()
    ]

    value = expected_absence_value(
        benchmark_id=options.benchmark_id,
        failed_stage=options.failed_stage,
        stage_result=stage_result,
        combined_output=(
            stdout_path.read_text(
                encoding="utf-8",
                errors="replace",
            )
            + "\n"
            + stderr_path.read_text(
                encoding="utf-8",
                errors="replace",
            )
        ),
        expected_exit_code=options.expected_exit_code,
        required_diagnostic=options.required_diagnostic,
        forbidden_artifact_count=len(
            forbidden_artifacts
        ),
        present_artifact_count=len(
            present_artifacts
        ),
    )

    write_json(
        Path(options.output),
        value,
    )


def expected_boundary_value(
    benchmark_id: str,
    rejection: dict[str, object],
) -> dict[str, object]:
    expected_diagnostic = (
        "unsupported by the ReLico v0 parser bridge: "
        "message-server parameters"
    )

    if rejection.get("benchmark_id") != benchmark_id:
        raise StageError(
            "rejection benchmark identifier differs"
        )

    if rejection.get("status") != "expected-rejection":
        raise StageError(
            "input does not record an expected rejection"
        )

    if rejection.get("boundary_stage") != "parser-json":
        raise StageError(
            "expected rejection did not occur at parser-json"
        )

    if rejection.get("observed_exit_code") != 1:
        raise StageError(
            "expected parser-json exit code 1"
        )

    if rejection.get("required_diagnostic") != expected_diagnostic:
        raise StageError(
            "expected rejection diagnostic differs"
        )

    if rejection.get("forbidden_artifact_count") != 2:
        raise StageError(
            "expected exactly two forbidden post-boundary artifacts"
        )

    return {
        "benchmark_id": benchmark_id,
        "boundary_code": (
            "V0_PARSER_BRIDGE_MESSAGE_SERVER_PARAMETERS_UNSUPPORTED"
        ),
        "boundary_stage": "parser-json",
        "expected_rejection": True,
        "schema_version": 1,
        "status": "pass",
    }


def expected_boundary_stage(
    options: argparse.Namespace,
) -> None:
    rejection = load_json_object(
        Path(options.input).resolve(),
        "expected-absence result",
    )

    write_json(
        Path(options.output),
        expected_boundary_value(
            options.benchmark_id,
            rejection,
        ),
    )


def diagnostics_value(
    benchmark_id: str,
    boundary: dict[str, object],
) -> dict[str, object]:
    expected_code = (
        "V0_PARSER_BRIDGE_MESSAGE_SERVER_PARAMETERS_UNSUPPORTED"
    )

    if boundary.get("benchmark_id") != benchmark_id:
        raise StageError(
            "boundary benchmark identifier differs"
        )

    if boundary.get("status") != "pass":
        raise StageError(
            "boundary validation did not pass"
        )

    if boundary.get("boundary_code") != expected_code:
        raise StageError(
            "boundary diagnostic code differs"
        )

    if boundary.get("boundary_stage") != "parser-json":
        raise StageError(
            "boundary stage differs"
        )

    if boundary.get("expected_rejection") is not True:
        raise StageError(
            "boundary was not classified as expected"
        )

    return {
        "benchmark_id": benchmark_id,
        "diagnostic_code": expected_code,
        "expected_rejection": True,
        "message": (
            "Bound-payload message-server parameters are "
            "intentionally rejected by the current ReLico v0 "
            "parser bridge."
        ),
        "schema_version": 1,
        "status": "pass",
    }


def diagnostics_stage(
    options: argparse.Namespace,
) -> None:
    boundary = load_json_object(
        Path(options.input).resolve(),
        "expected-boundary result",
    )

    write_json(
        Path(options.output),
        diagnostics_value(
            options.benchmark_id,
            boundary,
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="relico-bench-stage")
    subparsers = parser.add_subparsers(dest="stage", required=True)

    source = subparsers.add_parser("source")
    source.add_argument("--benchmark-id", required=True)
    source.add_argument("--source", required=True)
    source.add_argument("--output", required=True)
    source.set_defaults(handler=source_stage)

    rmc = subparsers.add_parser("rmc")
    rmc.add_argument("--source", required=True)
    rmc.add_argument("--actual", required=True)
    rmc.add_argument("--rmc-jar", required=True)
    rmc.add_argument("--java", required=True)
    rmc.add_argument("--cxx", required=True)
    rmc.add_argument("--output", required=True)
    rmc.set_defaults(handler=rmc_stage)

    parser_json = subparsers.add_parser("parser-json")
    parser_json.add_argument("--repo", required=True)
    parser_json.add_argument("--source", required=True)
    parser_json.add_argument("--actual", required=True)
    parser_json.add_argument("--artifact-zip", required=True)
    parser_json.add_argument("--maven", required=True)
    parser_json.add_argument("--output", required=True)
    parser_json.set_defaults(handler=parser_json_stage)

    lean_export = subparsers.add_parser("lean-export")
    lean_export.add_argument(
        "--mode",
        required=True,
        choices=["decoded-dtr-ast", "translated-lf-ast", "lf-source"],
    )
    lean_export.add_argument("--repo", required=True)
    lean_export.add_argument("--lake", required=True)
    lean_export.add_argument("--input", required=True)
    lean_export.add_argument("--output", required=True)
    lean_export.set_defaults(handler=lean_export_stage)

    formal = subparsers.add_parser("formal-witness")
    formal.add_argument("--repo", required=True)
    formal.add_argument("--lake", required=True)
    formal.add_argument("--coverage", required=True)
    formal.add_argument("--output", required=True)
    formal.set_defaults(handler=formal_witness_stage)

    lfc = subparsers.add_parser("lfc")
    lfc.add_argument("--lf-source", required=True)
    lfc.add_argument("--work-directory", required=True)
    lfc.add_argument("--lfc", required=True)
    lfc.add_argument("--output", required=True)
    lfc.set_defaults(handler=lfc_stage)

    runtime = subparsers.add_parser("runtime")
    runtime.add_argument("--executable", required=True)
    runtime.add_argument("--output", required=True)
    runtime.set_defaults(handler=runtime_stage)


    expected_absence = subparsers.add_parser(
        "expected-absence"
    )
    expected_absence.add_argument(
        "--benchmark-id",
        required=True,
    )
    expected_absence.add_argument(
        "--failed-stage",
        required=True,
    )
    expected_absence.add_argument(
        "--stage-result",
        required=True,
    )
    expected_absence.add_argument(
        "--stdout",
        required=True,
    )
    expected_absence.add_argument(
        "--stderr",
        required=True,
    )
    expected_absence.add_argument(
        "--expected-exit-code",
        required=True,
        type=int,
    )
    expected_absence.add_argument(
        "--required-diagnostic",
        required=True,
    )
    expected_absence.add_argument(
        "--forbidden-artifact",
        action="append",
        default=[],
    )
    expected_absence.add_argument(
        "--output",
        required=True,
    )
    expected_absence.set_defaults(
        handler=expected_absence_stage
    )

    expected_boundary = subparsers.add_parser(
        "expected-boundary-stage"
    )
    expected_boundary.add_argument(
        "--benchmark-id",
        required=True,
    )
    expected_boundary.add_argument(
        "--input",
        required=True,
    )
    expected_boundary.add_argument(
        "--output",
        required=True,
    )
    expected_boundary.set_defaults(
        handler=expected_boundary_stage
    )

    diagnostics = subparsers.add_parser(
        "diagnostics"
    )
    diagnostics.add_argument(
        "--benchmark-id",
        required=True,
    )
    diagnostics.add_argument(
        "--input",
        required=True,
    )
    diagnostics.add_argument(
        "--output",
        required=True,
    )
    diagnostics.set_defaults(
        handler=diagnostics_stage
    )

    return parser


def main(arguments: list[str]) -> int:
    options = build_parser().parse_args(arguments)
    options.handler(options)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except StageError as error:
        print(f"relico-bench-stage: {error}", file=sys.stderr)
        raise SystemExit(1)
