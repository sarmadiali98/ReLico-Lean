#!/usr/bin/env bash
set -euo pipefail

REPO="$(
  cd "$(dirname "$0")/.." &&
  pwd
)"

ARTIFACT_ZIP="${1:?usage: check-multistore-payload-frontend.sh <artifact.zip>}"

MAVEN="${RELICO_MAVEN:-/usr/local/apache-maven/bin/mvn}"

FIXTURE_DIRECTORY="$REPO/frontend/fixtures/multi-store-payload"
RUNNER="$REPO/frontend/java-bridge/run-multistore-payload-from-zip.sh"
BRIDGE_MAIN="$REPO/frontend/lean-bridge/MultiStorePayloadBridgeMain.lean"
TEST_MAIN="$REPO/frontend/lean-bridge/MultiStorePayloadFrontendTestMain.lean"

TEMP_DIRECTORY="$(
  mktemp -d \
    "${TMPDIR:-/tmp}/relico-payload-frontend.XXXXXX"
)"

cleanup() {
  rm -rf "$TEMP_DIRECTORY"
}

trap cleanup EXIT

GENERATED_JSON="$TEMP_DIRECTORY/payload-single.parser.json"

cd "$REPO"

RELICO_MAVEN="$MAVEN" \
bash "$RUNNER" \
  "$ARTIFACT_ZIP" \
  "$FIXTURE_DIRECTORY/payload-single.rebeca" \
  "$GENERATED_JSON"

python3 - \
  "$GENERATED_JSON" \
  "$FIXTURE_DIRECTORY/payload-single.parser.json" <<'PY'
import json
from pathlib import Path
import sys

generated = json.loads(
    Path(sys.argv[1]).read_text(
        encoding="utf-8",
    )
)

expected = json.loads(
    Path(sys.argv[2]).read_text(
        encoding="utf-8",
    )
)

if generated != expected:
    raise SystemExit(
        "payload parser output differs from the expected contract"
    )

print(
    "PAYLOAD_PARSER_CONTRACT_OK"
)
PY

lake env lean \
  --run \
  "$BRIDGE_MAIN" \
  "$GENERATED_JSON"

lake env lean \
  --run \
  "$TEST_MAIN" \
  "$FIXTURE_DIRECTORY"

echo "MULTI_STORE_PAYLOAD_FRONTEND_GATE_OK"
