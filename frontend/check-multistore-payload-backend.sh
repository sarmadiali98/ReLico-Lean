#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 1; then
  echo "usage: check-multistore-payload-backend.sh <artifact.zip>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"

REPOSITORY_ROOT="$(
  git rev-parse --show-toplevel
)"

cd "$REPOSITORY_ROOT"

POSITIVE_INPUT="$REPOSITORY_ROOT/frontend/fixtures/multi-store-payload/payload-single.rebeca"
POSITIVE_EXPECTED="$REPOSITORY_ROOT/frontend/fixtures/multi-store-payload/payload-single.parser.json"

SCOPE_INPUT="$REPOSITORY_ROOT/frontend/fixtures/multi-store-payload/payload-scope.rebeca"
SCOPE_EXPECTED="$REPOSITORY_ROOT/frontend/fixtures/multi-store-payload/payload-scope.parser.json"

GENERATED_DIRECTORY="$REPOSITORY_ROOT/.lake/frontend-multistore-payload-backend"

POSITIVE_DIRECTORY="$GENERATED_DIRECTORY/payload-single"
SCOPE_DIRECTORY="$GENERATED_DIRECTORY/payload-scope"

POSITIVE_JSON="$POSITIVE_DIRECTORY/payload-single.parser.json"
SCOPE_JSON="$SCOPE_DIRECTORY/payload-scope.parser.json"

POSITIVE_LF="$POSITIVE_DIRECTORY/src/PayloadSingle.lf"
SCOPE_LF="$SCOPE_DIRECTORY/src/PayloadScope.lf"

POSITIVE_EXECUTABLE="$POSITIVE_DIRECTORY/bin/PayloadSingle"
SCOPE_EXECUTABLE="$SCOPE_DIRECTORY/bin/PayloadScope"

BACKEND_MAIN="$REPOSITORY_ROOT/frontend/lean-bridge/MultiStorePayloadCppBackendMain.lean"

rm -rf "$GENERATED_DIRECTORY"

mkdir -p \
  "$POSITIVE_DIRECTORY/src" \
  "$SCOPE_DIRECTORY/src"

"$REPOSITORY_ROOT/frontend/java-bridge/run-multistore-payload-from-zip.sh" \
  "$ARTIFACT_ZIP" \
  "$POSITIVE_INPUT" \
  "$POSITIVE_JSON"

"$REPOSITORY_ROOT/frontend/java-bridge/run-multistore-payload-from-zip.sh" \
  "$ARTIFACT_ZIP" \
  "$SCOPE_INPUT" \
  "$SCOPE_JSON"

python3 - \
  "$POSITIVE_EXPECTED" \
  "$POSITIVE_JSON" \
  "$SCOPE_EXPECTED" \
  "$SCOPE_JSON" <<'JSON_CONTRACT_PY'
from __future__ import annotations

import json
from pathlib import Path
import sys


positive_expected = json.loads(
    Path(sys.argv[1]).read_text(
        encoding="utf-8",
    )
)

positive_actual = json.loads(
    Path(sys.argv[2]).read_text(
        encoding="utf-8",
    )
)

scope_expected = json.loads(
    Path(sys.argv[3]).read_text(
        encoding="utf-8",
    )
)

scope_actual = json.loads(
    Path(sys.argv[4]).read_text(
        encoding="utf-8",
    )
)


if positive_actual != positive_expected:
    raise SystemExit(
        "Parser-generated single-payload JSON differs from the checked fixture."
    )


if scope_actual != scope_expected:
    raise SystemExit(
        "Parser-generated scope JSON differs from the checked fixture."
    )


print(
    "MULTI_STORE_PAYLOAD_BACKEND_JSON_CONTRACT_OK"
)
JSON_CONTRACT_PY

lake build \
  Relico.Translation.MultiStorePayloadCppBackend \
  Relico.Frontend.MultiStorePayloadCppBackend \
  Relico.Tests.MultiStorePayloadCppBackend

for object in \
  ".lake/build/lib/lean/Relico/Translation/MultiStorePayloadCppBackend.olean" \
  ".lake/build/lib/lean/Relico/Frontend/MultiStorePayloadCppBackend.olean" \
  ".lake/build/lib/lean/Relico/Tests/MultiStorePayloadCppBackend.olean"
do
  test -f "$object"
  test -s "$object"
done

lake env lean \
  --run \
  "$BACKEND_MAIN" \
  "$POSITIVE_JSON" \
  "$POSITIVE_LF"

lake env lean \
  --run \
  "$BACKEND_MAIN" \
  "$SCOPE_JSON" \
  "$SCOPE_LF"

test -f "$POSITIVE_LF"
test -s "$POSITIVE_LF"

test -f "$SCOPE_LF"
test -s "$SCOPE_LF"

python3 - \
  "$POSITIVE_LF" \
  "$SCOPE_LF" <<'LF_CONTRACT_PY'
from __future__ import annotations

from pathlib import Path
import re
import sys


positive = Path(sys.argv[1]).read_text(
    encoding="utf-8",
)

scope = Path(sys.argv[2]).read_text(
    encoding="utf-8",
)


def require(
    source: str,
    fragment: str,
    label: str,
) -> None:
    if fragment not in source:
        raise SystemExit(
            f"{label}: missing {fragment!r}"
        )


deliver_action = "deliver_action"
first_action = "first_action"
second_action = "second_action"


require(
    positive,
    "target Cpp",
    "positive target",
)

require(
    positive,
    "reactor PayloadController",
    "positive reactor",
)

require(
    positive,
    f"logical action {deliver_action}: int",
    "positive action declaration",
)

require(
    positive,
    f"{deliver_action}.schedule(7, 1ms);",
    "positive payload-before-delay schedule",
)

require(
    positive,
    f"reaction({deliver_action})",
    "positive reaction trigger",
)

require(
    positive,
    f"auto value = *{deliver_action}.get();",
    "positive payload extraction",
)

require(
    positive,
    "x = value;",
    "positive payload assignment",
)


required_scope_fragments = [
    "reactor ScopedController",
    f"logical action {first_action}: int",
    f"logical action {second_action}: int",
    f"reaction({first_action})",
    f"reaction({second_action})",
    f"auto value = *{first_action}.get();",
    f"auto other = *{second_action}.get();",
    f"{first_action}.schedule(7, 1ms);",
    f"{second_action}.schedule(9, 2ms);",
    f"{second_action}.schedule(value, 1ms);",
]

for fragment in required_scope_fragments:
    require(
        scope,
        fragment,
        "scope source",
    )


declared_actions = re.findall(
    r"logical action\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)"
    r":\s*int",
    scope,
)

if set(declared_actions) != {
    first_action,
    second_action,
}:
    raise SystemExit(
        "Unexpected scope action declarations: "
        + repr(declared_actions)
    )


if scope.index(
    f"reaction({first_action})"
) >= scope.index(
    f"reaction({second_action})"
):
    raise SystemExit(
        "Expected first-action reaction before second-action reaction."
    )


print(
    "MULTI_STORE_PAYLOAD_BACKEND_LF_CONTRACT_OK"
)

print(
    "PAYLOAD_BEFORE_DELAY_OK"
)

print(
    "REACTION_LOCAL_PARAMETER_SCOPE_OK"
)
LF_CONTRACT_PY

command -v lfc >/dev/null

(
  cd "$POSITIVE_DIRECTORY"
  lfc src/PayloadSingle.lf
)

test -f "$POSITIVE_EXECUTABLE"
test -x "$POSITIVE_EXECUTABLE"

python3 - \
  "$POSITIVE_EXECUTABLE" <<'POSITIVE_RUNTIME_PY'
from __future__ import annotations

import subprocess
import sys


result = subprocess.run(
    [sys.argv[1]],
    timeout=20,
    check=False,
)

print(
    "Generated single-payload executable exit code:",
    result.returncode,
)

raise SystemExit(
    result.returncode
)
POSITIVE_RUNTIME_PY

(
  cd "$SCOPE_DIRECTORY"
  lfc src/PayloadScope.lf
)

test -f "$SCOPE_EXECUTABLE"
test -x "$SCOPE_EXECUTABLE"

echo "MULTI_STORE_PAYLOAD_CPP_BACKEND_RUNTIME_GATE_OK"
echo "Generated positive JSON: $POSITIVE_JSON"
echo "Generated positive LF: $POSITIVE_LF"
echo "Generated positive executable: $POSITIVE_EXECUTABLE"
echo "Generated scope JSON: $SCOPE_JSON"
echo "Generated scope LF: $SCOPE_LF"
echo "Generated scope executable: $SCOPE_EXECUTABLE"
