#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: check-multistore.sh <artifact.zip>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"

REPOSITORY_ROOT="$(
  git rev-parse --show-toplevel
)"

cd "$REPOSITORY_ROOT"

GENERATED_DIRECTORY="$REPOSITORY_ROOT/.lake/frontend-multistore-check"
GENERATED_JSON="$GENERATED_DIRECTORY/multistore-priority.parser.json"
GENERATED_SUMMARY="$GENERATED_DIRECTORY/multistore-priority.summary.txt"

EXPECTED_JSON="$REPOSITORY_ROOT/frontend/fixtures/multistore-priority.json"
INPUT_REBECA="$REPOSITORY_ROOT/frontend/fixtures/multistore-priority.rebeca"

rm -rf "$GENERATED_DIRECTORY"
mkdir -p "$GENERATED_DIRECTORY"

"$REPOSITORY_ROOT/frontend/java-bridge/run-multistore-from-zip.sh" \
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
        "Parser-generated multi-server JSON differs from the checked fixture."
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
    "Parser-generated multi-server JSON matches the checked fixture."
)
PY

lake build Relico.Frontend.MultiStoreSchema
lake build Relico.Frontend.MultiStoreDecoder
lake build Relico.Tests.MultiStoreFrontendDecoder
lake build Relico.Frontend.MultiStoreBridgeCheck

lake env lean \
  --run \
  Relico/Frontend/MultiStoreBridgeCheck.lean \
  "$GENERATED_JSON" \
  "$GENERATED_SUMMARY"

grep -qF \
  "class=PriorityController" \
  "$GENERATED_SUMMARY"

grep -qF \
  "actor=controller" \
  "$GENERATED_SUMMARY"

grep -qF \
  "sourceMessageServers=low,high" \
  "$GENERATED_SUMMARY"

grep -qF \
  "sourcePriorities=4,1" \
  "$GENERATED_SUMMARY"

grep -qF \
  "logicalActions=high_action,low_action" \
  "$GENERATED_SUMMARY"

grep -qF \
  "messageReactionCount=2" \
  "$GENERATED_SUMMARY"

echo "Real multi-server priority parser-to-Lean check passed."
echo "Generated JSON: $GENERATED_JSON"
echo "Generated summary: $GENERATED_SUMMARY"
