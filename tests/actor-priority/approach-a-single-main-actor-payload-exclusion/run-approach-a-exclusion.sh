#!/bin/bash
set -euo pipefail

export PYTHONDONTWRITEBYTECODE=1

if test "$#" -ne 2
then
  printf '%s\n' \
    'usage: run-approach-a-exclusion.sh PARSER_ARTIFACT RESULT_JSON' \
    >&2
  exit 64
fi

PARSER_ARTIFACT="$1"
RESULT_JSON="$2"

FIXTURE_ROOT="$(
  cd "$(
    dirname "$0"
  )"
  pwd
)"

if test -n "${RELICO_REPO_ROOT:-}"
then
  REPO_ROOT="$(
    cd "$RELICO_REPO_ROOT"
    pwd
  )"
else
  REPO_ROOT="$(
    /usr/bin/git -C "$FIXTURE_ROOT" \
      rev-parse --show-toplevel
  )"
fi

RESOLVED_TOPLEVEL="$(
  /usr/bin/git -C "$REPO_ROOT" \
    rev-parse --show-toplevel
)"

INSIDE_WORKTREE="$(
  /usr/bin/git -C "$REPO_ROOT" \
    rev-parse --is-inside-work-tree
)"

if test "$RESOLVED_TOPLEVEL" != "$REPO_ROOT"
then
  printf 'ERROR: repository top-level differs: expected=%s observed=%s\n' \
    "$REPO_ROOT" \
    "$RESOLVED_TOPLEVEL" \
    >&2
  exit 65
fi

if test "$INSIDE_WORKTREE" != 'true'
then
  printf 'ERROR: path is not inside a Git worktree: %s\n' \
    "$REPO_ROOT" \
    >&2
  exit 66
fi

WRAPPER="$REPO_ROOT/frontend/java-bridge/run-multistore-payload-from-zip.sh"
SOURCE="$FIXTURE_ROOT/source/model.rebeca"
EXPECTED="$FIXTURE_ROOT/expected/frontend-output-required-substring.txt"

PYTHON_BIN="$(
  command -v python3
)"

if ! test -x "$WRAPPER"
then
  printf 'ERROR: parser wrapper is not executable: %s\n' \
    "$WRAPPER" \
    >&2
  exit 67
fi

test -f "$PARSER_ARTIFACT"
test -s "$SOURCE"
test -s "$EXPECTED"
test -n "$PYTHON_BIN"

TMP_ROOT="$(
  /usr/bin/mktemp -d \
    /tmp/relico-approach-a-single-actor.XXXXXX
)"

trap '/bin/rm -rf "$TMP_ROOT"' EXIT

ACTOR_SOURCE="$TMP_ROOT/actor.rebeca"
ABSENT_SOURCE="$TMP_ROOT/absent.rebeca"
LOCAL_SOURCE="$TMP_ROOT/local.rebeca"

/bin/cp "$SOURCE" "$ACTOR_SOURCE"

"$PYTHON_BIN" - \
  "$SOURCE" \
  "$ABSENT_SOURCE" \
  "$LOCAL_SOURCE" <<'PY_CONTROLS'
from __future__ import annotations

from pathlib import Path
import re
import sys

source_path = Path(sys.argv[1])
absent_path = Path(sys.argv[2])
local_path = Path(sys.argv[3])

text = source_path.read_text(
    encoding="utf-8"
)

priority_line = re.compile(
    r"^\s*@priority\s*\(\s*[0-9]+\s*\)\s*$",
    re.IGNORECASE,
)

main_line = re.compile(
    r"^\s*main\b",
    re.IGNORECASE,
)

msgsrv_line = re.compile(
    r"^\s*msgsrv\b",
    re.IGNORECASE,
)

output: list[str] = []
inside_main = False
opened = False
depth = 0

for line in text.splitlines():
    if (
        not inside_main
        and main_line.match(line)
    ):
        inside_main = True

    if inside_main:
        opening = line.count("{")
        closing = line.count("}")

        if opening:
            opened = True

        if priority_line.match(line):
            depth += opening
            depth -= closing
            continue

        depth += opening
        depth -= closing
        output.append(line)

        if opened and depth <= 0:
            inside_main = False
            opened = False
            depth = 0

        continue

    output.append(line)

absent = "\n".join(output).rstrip() + "\n"

absent_path.write_text(
    absent,
    encoding="utf-8",
)

absent_lines = absent.splitlines()

for index, line in enumerate(absent_lines):
    if msgsrv_line.match(line):
        indentation = re.match(
            r"^(\s*)",
            line,
        ).group(1)

        local = (
            "\n".join(
                [
                    *absent_lines[:index],
                    indentation + "@priority(1)",
                    *absent_lines[index:],
                ]
            ).rstrip()
            + "\n"
        )

        local_path.write_text(
            local,
            encoding="utf-8",
        )
        break
else:
    raise SystemExit(
        "fixture contains no message-server declaration"
    )
PY_CONTROLS

run_case() {
  local case_name="$1"
  local source_path="$2"
  local case_root="$TMP_ROOT/$case_name"
  local json_path="$case_root/model.json"

  /bin/mkdir -p "$case_root"

  set +e
  (
    cd "$REPO_ROOT"

    /bin/bash "$WRAPPER" \
      "$PARSER_ARTIFACT" \
      "$source_path" \
      "$json_path"
  ) \
    >"$case_root/stdout.txt" \
    2>"$case_root/stderr.txt"
  local exit_code="$?"
  set -e

  printf '%s\n' "$exit_code" \
    >"$case_root/exit-code.txt"
}

run_case \
  'actor-priority' \
  "$ACTOR_SOURCE"

run_case \
  'actor-priority-absent' \
  "$ABSENT_SOURCE"

run_case \
  'local-message-server-priority' \
  "$LOCAL_SOURCE"

"$PYTHON_BIN" - \
  "$TMP_ROOT" \
  "$EXPECTED" \
  "$RESULT_JSON" \
  "$REPO_ROOT" <<'PY_VALIDATE'
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
from typing import Any

root = Path(sys.argv[1]).resolve()
expected_path = Path(sys.argv[2]).resolve()
result_path = Path(sys.argv[3]).resolve()
repository_root = Path(sys.argv[4]).resolve()

expected = " ".join(
    expected_path.read_text(
        encoding="utf-8"
    ).strip().split()
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(
        path.read_bytes()
    ).hexdigest()


def collect_priorities(
    value: Any,
    path: str = "$",
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []

    if isinstance(value, dict):
        for key, item in value.items():
            child = f"{path}.{key}"

            if "priority" in key.lower():
                rows.append(
                    {
                        "path": child,
                        "value": item,
                    }
                )

            rows.extend(
                collect_priorities(
                    item,
                    child,
                )
            )

    elif isinstance(value, list):
        for index, item in enumerate(value):
            rows.extend(
                collect_priorities(
                    item,
                    f"{path}[{index}]",
                )
            )

    return rows


records = []

for case_name in [
    "actor-priority",
    "actor-priority-absent",
    "local-message-server-priority",
]:
    case_root = root / case_name
    stdout_path = case_root / "stdout.txt"
    stderr_path = case_root / "stderr.txt"
    exit_path = case_root / "exit-code.txt"
    json_path = case_root / "model.json"

    exit_code = int(
        exit_path.read_text(
            encoding="utf-8"
        ).strip()
    )

    stdout = stdout_path.read_text(
        encoding="utf-8"
    )

    stderr = stderr_path.read_text(
        encoding="utf-8"
    )

    combined = " ".join(
        (
            stdout
            + "\n"
            + stderr
        ).split()
    )

    parsed: Any = None
    json_parseable = False

    if json_path.is_file():
        parsed = json.loads(
            json_path.read_text(
                encoding="utf-8"
            )
        )
        json_parseable = True

    priority_fields = (
        collect_priorities(parsed)
        if json_parseable
        else []
    )

    records.append(
        {
            "case": case_name,
            "wrapper_working_directory": str(
                repository_root
            ),
            "exit_code": exit_code,
            "stdout_sha256": sha256_file(
                stdout_path
            ),
            "stderr_sha256": sha256_file(
                stderr_path
            ),
            "json_exists": json_path.is_file(),
            "json_parseable": json_parseable,
            "priority_fields": priority_fields,
            "priority_one_observed": any(
                row["value"] in {1, "1"}
                for row in priority_fields
            ),
            "expected_diagnostic_observed": (
                expected.lower()
                in combined.lower()
            ),
        }
    )

by_case = {
    row["case"]: row
    for row in records
}

actor = by_case["actor-priority"]
absent = by_case["actor-priority-absent"]
local = by_case[
    "local-message-server-priority"
]

failures: list[str] = []

if actor["exit_code"] == 0:
    failures.append(
        "actor-priority case exited zero"
    )

if actor["json_exists"]:
    failures.append(
        "actor-priority case emitted JSON"
    )

if not actor[
    "expected_diagnostic_observed"
]:
    failures.append(
        "required main-actor diagnostic was absent"
    )

if (
    absent["exit_code"] != 0
    or absent["json_parseable"] is not True
):
    failures.append(
        "actor-priority-absent control failed"
    )

if (
    local["exit_code"] != 0
    or local["json_parseable"] is not True
    or local["priority_one_observed"] is not True
):
    failures.append(
        "local-message-server-priority control failed"
    )

actor_root = root / "actor-priority"

for path in actor_root.rglob("*"):
    if not path.is_file():
        continue

    relative = path.relative_to(
        actor_root
    ).as_posix().lower()

    if (
        path.name == "model.json"
        or path.suffix.lower() == ".lf"
        or any(
            token in relative
            for token in [
                "decoded-dtr",
                "translated-lf",
                "formal-witness",
                "runtime",
            ]
        )
    ):
        failures.append(
            "rejected case emitted downstream artifact: "
            + relative
        )

result = {
    "schema_version": 1,
    "phase": (
        "approach-a-single-main-actor-"
        "payload-exclusion-test"
    ),
    "repository_root": str(
        repository_root
    ),
    "linked_worktree_validation": (
        "git-rev-parse"
    ),
    "wrapper_invocation_contract": (
        "repository-working-directory"
    ),
    "expected_diagnostic_fragment": expected,
    "cases": records,
    "failure_count": len(failures),
    "failures": failures,
    "passed": not failures,
}

result_path.write_text(
    json.dumps(
        result,
        indent=2,
        sort_keys=True,
    )
    + "\n",
    encoding="utf-8",
)

for row in records:
    print(
        "APPROACH_A_CASE="
        f"{row['case']}:"
        f"cwd={row['wrapper_working_directory']}:"
        f"exit={row['exit_code']}:"
        f"json={row['json_exists']}:"
        f"parseable={row['json_parseable']}:"
        f"priority_one="
        f"{row['priority_one_observed']}:"
        f"diagnostic="
        f"{row['expected_diagnostic_observed']}"
    )

print(
    "APPROACH_A_SINGLE_MAIN_ACTOR_TEST="
    + (
        "pass"
        if not failures
        else "fail"
    )
)

for failure in failures:
    print(
        "APPROACH_A_FAILURE="
        + failure
    )

if failures:
    raise SystemExit(1)
PY_VALIDATE
