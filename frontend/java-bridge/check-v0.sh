#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: check-v0.sh <artifact.zip>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"

REPOSITORY_ROOT="$(
  git rev-parse --show-toplevel
)"

GENERATED_DIRECTORY="$REPOSITORY_ROOT/.lake/frontend"
GENERATED_JSON="$GENERATED_DIRECTORY/v0-controller.parser.json"
GENERATED_LF="$GENERATED_DIRECTORY/V0Controller.lf"
LFC_DIRECTORY="$REPOSITORY_ROOT/.lake/lfc-check"

mkdir -p "$GENERATED_DIRECTORY"

"$REPOSITORY_ROOT/frontend/java-bridge/run-from-zip.sh" \
  "$ARTIFACT_ZIP" \
  "$REPOSITORY_ROOT/frontend/fixtures/v0-controller.rebeca" \
  "$GENERATED_JSON"

python3 - \
  "$REPOSITORY_ROOT/frontend/fixtures/v0-controller.json" \
  "$GENERATED_JSON" <<'PY'
import json
from pathlib import Path
import sys

expected_path = Path(sys.argv[1])
actual_path = Path(sys.argv[2])

expected = json.loads(expected_path.read_text())
actual = json.loads(actual_path.read_text())

if actual != expected:
    print("Parser-generated JSON differs from the checked fixture.")
    print()
    print("Expected:")
    print(json.dumps(expected, indent=2, sort_keys=True))
    print()
    print("Actual:")
    print(json.dumps(actual, indent=2, sort_keys=True))
    raise SystemExit(1)

print("Parser-generated JSON matches the checked v0 fixture.")
PY

lake build

lake env lean \
  --run \
  Relico/Frontend/BridgeCheck.lean \
  "$GENERATED_JSON" \
  "$GENERATED_LF"

grep -qF "target Cpp" "$GENERATED_LF"
grep -qF "reactor Controller" "$GENERATED_LF"
grep -qF "reaction(startup) -> tick_action" "$GENERATED_LF"
grep -qF "reaction(tick_action) -> tick_action" "$GENERATED_LF"
grep -qF "tick_action.schedule(1ms);" "$GENERATED_LF"
grep -qF "main reactor {" "$GENERATED_LF"

command -v lfc >/dev/null

rm -rf "$LFC_DIRECTORY"
mkdir -p "$LFC_DIRECTORY/src"

cp \
  "$GENERATED_LF" \
  "$LFC_DIRECTORY/src/V0Controller.lf"

(
  cd "$LFC_DIRECTORY"
  lfc src/V0Controller.lf
)

test -x "$LFC_DIRECTORY/bin/V0Controller"

echo "Real Timed Rebeca parser-to-LF/C++ check passed."
echo "Generated JSON: $GENERATED_JSON"
echo "Generated LF:   $GENERATED_LF"
echo "Generated C++ executable: $LFC_DIRECTORY/bin/V0Controller"
