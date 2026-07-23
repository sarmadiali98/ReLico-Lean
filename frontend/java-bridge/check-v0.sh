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
GENERATED_LF="$GENERATED_DIRECTORY/v0-controller.lf"

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
grep -qF "tick_action.schedule(1ms);" "$GENERATED_LF"

echo "Real Timed Rebeca parser-to-LF/C++ check passed."
echo "Generated JSON: $GENERATED_JSON"
echo "Generated LF:   $GENERATED_LF"
