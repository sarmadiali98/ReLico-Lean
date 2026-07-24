#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: check-store.sh <artifact.zip>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"

REPOSITORY_ROOT="$(
  git rev-parse --show-toplevel
)"

cd "$REPOSITORY_ROOT"

GENERATED_DIRECTORY="$REPOSITORY_ROOT/.lake/frontend-store-check"
GENERATED_JSON="$GENERATED_DIRECTORY/store-two-variable.parser.json"
GENERATED_LF="$GENERATED_DIRECTORY/StoreProgram.lf"

LFC_DIRECTORY="$REPOSITORY_ROOT/.lake/lfc-store-check"

EXPECTED_JSON="$REPOSITORY_ROOT/frontend/fixtures/store-two-variable.json"
INPUT_REBECA="$REPOSITORY_ROOT/frontend/fixtures/store-two-variable.rebeca"

rm -rf "$GENERATED_DIRECTORY"
rm -rf "$LFC_DIRECTORY"

mkdir -p "$GENERATED_DIRECTORY"
mkdir -p "$LFC_DIRECTORY/src"

"$REPOSITORY_ROOT/frontend/java-bridge/run-store-from-zip.sh" \
  "$ARTIFACT_ZIP" \
  "$INPUT_REBECA" \
  "$GENERATED_JSON"

python3 - \
  "$EXPECTED_JSON" \
  "$GENERATED_JSON" <<'PY'
import json
from pathlib import Path
import sys

expected = json.loads(
    Path(sys.argv[1]).read_text()
)

actual = json.loads(
    Path(sys.argv[2]).read_text()
)

if actual != expected:
    print(
        "Parser-generated finite-store JSON differs from the checked fixture."
    )
    print()
    print("Expected:")
    print(
        json.dumps(
            expected,
            indent=2,
            sort_keys=True,
        )
    )
    print()
    print("Actual:")
    print(
        json.dumps(
            actual,
            indent=2,
            sort_keys=True,
        )
    )
    raise SystemExit(1)

print(
    "Parser-generated JSON matches the two-variable fixture."
)
PY

lake build Relico.Tests.StoreFrontendDecoder
lake build Relico.Tests.StoreCppBackend
lake build Relico.Frontend.StoreBridgeCheck

lake env lean \
  --run \
  Relico/Frontend/StoreBridgeCheck.lean \
  "$GENERATED_JSON" \
  "$GENERATED_LF"

grep -qF "target Cpp" "$GENERATED_LF"
grep -qF "reactor TwoStateController" "$GENERATED_LF"
grep -qF "state x: int = 0" "$GENERATED_LF"
grep -qF "state y: int = 0" "$GENERATED_LF"
grep -qF "x = 1;" "$GENERATED_LF"
grep -qF "y = 2;" "$GENERATED_LF"
grep -qF "y = x;" "$GENERATED_LF"
grep -qF "tick_action.schedule(1ms);" "$GENERATED_LF"

command -v lfc >/dev/null

cp \
  "$GENERATED_LF" \
  "$LFC_DIRECTORY/src/StoreProgram.lf"

(
  cd "$LFC_DIRECTORY"
  lfc src/StoreProgram.lf
)

GENERATED_EXECUTABLE="$LFC_DIRECTORY/bin/StoreProgram"

test -x "$GENERATED_EXECUTABLE"

python3 - \
  "$GENERATED_EXECUTABLE" <<'PY'
import subprocess
import sys

result = subprocess.run(
    [sys.argv[1]],
    timeout=10,
)

print(
    "Generated finite-store executable exit code:",
    result.returncode,
)

raise SystemExit(
    result.returncode
)
PY

echo "Real two-variable parser-to-LF/C++ check passed."
echo "Generated JSON: $GENERATED_JSON"
echo "Generated LF: $GENERATED_LF"
echo "Generated executable: $GENERATED_EXECUTABLE"
