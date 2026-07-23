#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: check-v0-runtime.sh <artifact.zip>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"
REPOSITORY_ROOT="$(git rev-parse --show-toplevel)"

cd "$REPOSITORY_ROOT"

GENERATED_DIRECTORY="$REPOSITORY_ROOT/.lake/frontend-runtime"
GENERATED_JSON="$GENERATED_DIRECTORY/v0-once.parser.json"
GENERATED_LF="$GENERATED_DIRECTORY/V0Once.lf"
LFC_DIRECTORY="$REPOSITORY_ROOT/.lake/lfc-runtime-check"
EXPECTED_JSON="$REPOSITORY_ROOT/frontend/fixtures/v0-once.json"
INPUT_REBECA="$REPOSITORY_ROOT/frontend/fixtures/v0-once.rebeca"

rm -rf "$GENERATED_DIRECTORY" "$LFC_DIRECTORY"
mkdir -p "$GENERATED_DIRECTORY" "$LFC_DIRECTORY/src"

"$REPOSITORY_ROOT/frontend/java-bridge/run-from-zip.sh" "$ARTIFACT_ZIP" "$INPUT_REBECA" "$GENERATED_JSON"

python3 -c 'import json,sys; from pathlib import Path; expected=json.loads(Path(sys.argv[1]).read_text()); actual=json.loads(Path(sys.argv[2]).read_text()); assert actual == expected, "Parser-generated JSON differs from the checked finite-runtime fixture."; print("Parser-generated JSON matches the finite-runtime fixture.")' "$EXPECTED_JSON" "$GENERATED_JSON"

lake build

lake env lean --run Relico/Frontend/BridgeCheck.lean "$GENERATED_JSON" "$GENERATED_LF"

grep -qF "target Cpp" "$GENERATED_LF"
grep -qF "reactor OnceController" "$GENERATED_LF"
grep -qF "reaction(startup) -> tick_action" "$GENERATED_LF"
grep -qF "reaction(tick_action) {=" "$GENERATED_LF"
grep -qF "x = 1;" "$GENERATED_LF"

if grep -qF "reaction(tick_action) -> tick_action" "$GENERATED_LF"; then
  echo "The terminating message reaction unexpectedly schedules another action."
  exit 1
fi

cp "$GENERATED_LF" "$LFC_DIRECTORY/src/V0Once.lf"

(
  cd "$LFC_DIRECTORY"
  lfc src/V0Once.lf
)

GENERATED_EXECUTABLE="$LFC_DIRECTORY/bin/V0Once"
test -x "$GENERATED_EXECUTABLE"

python3 -c 'import subprocess,sys; result=subprocess.run([sys.argv[1]], timeout=10); print("Generated executable exit code:", result.returncode); raise SystemExit(result.returncode)' "$GENERATED_EXECUTABLE"

echo "Finite generated LF/C++ executable ran and terminated successfully."
echo "Generated JSON: $GENERATED_JSON"
echo "Generated LF: $GENERATED_LF"
echo "Generated executable: $GENERATED_EXECUTABLE"
