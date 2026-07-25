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
RUNTIME_DIRECTORY="$GENERATED_DIRECTORY/runtime"
GENERATED_LF="$RUNTIME_DIRECTORY/src/MultiStorePriority.lf"
GENERATED_EXECUTABLE="$RUNTIME_DIRECTORY/bin/MultiStorePriority"

EXPECTED_JSON="$REPOSITORY_ROOT/frontend/fixtures/multistore-priority.json"
INPUT_REBECA="$REPOSITORY_ROOT/frontend/fixtures/multistore-priority.rebeca"

rm -rf "$GENERATED_DIRECTORY"
mkdir -p "$RUNTIME_DIRECTORY/src"

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
lake build Relico.LF.MultiStoreCppPrinter
lake build Relico.Translation.MultiStoreCppBackend
lake build Relico.Tests.MultiStoreCppBackend
lake build Relico.Frontend.MultiStoreBridgeCheck

lake env lean \
  --run \
  Relico/Frontend/MultiStoreBridgeCheck.lean \
  "$GENERATED_JSON" \
  "$GENERATED_SUMMARY" \
  "$GENERATED_LF"

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

python3 - "$GENERATED_LF" <<'PY'
from pathlib import Path
import re
import sys

source = Path(sys.argv[1]).read_text()

required_fragments = [
    "logical action high_action: void",
    "logical action low_action: void",
    "reaction(high_action)",
    "reaction(low_action)",
]

for fragment in required_fragments:
    if fragment not in source:
        raise SystemExit(
            f"Generated LF source is missing: {fragment}"
        )

high_action = source.index(
    "logical action high_action: void"
)
low_action = source.index(
    "logical action low_action: void"
)

if high_action >= low_action:
    raise SystemExit(
        "High-priority logical action was not declared first."
    )

high_reaction = source.index(
    "reaction(high_action)"
)
low_reaction = source.index(
    "reaction(low_action)"
)

if high_reaction >= low_reaction:
    raise SystemExit(
        "High-priority reaction was not declared first."
    )

startup_begin = source.index(
    "reaction(startup)"
)
startup_end = source.index(
    "=}",
    startup_begin,
)
startup = source[
    startup_begin:startup_end
]

scheduled = dict(
    re.findall(
        r"(high_action|low_action)"
        r"\.schedule\(([^)]+)\);",
        startup,
    )
)

if set(scheduled) != {
    "high_action",
    "low_action",
}:
    raise SystemExit(
        "Startup does not schedule both priority actions."
    )

if scheduled["high_action"] != scheduled["low_action"]:
    raise SystemExit(
        "Priority actions are not scheduled at the same delay."
    )

print(
    "Concrete LF priority order is high-before-low."
)
print(
    "Both priority actions are scheduled at "
    + scheduled["high_action"]
    + "."
)
PY

command -v lfc >/dev/null

(
  cd "$RUNTIME_DIRECTORY"
  lfc src/MultiStorePriority.lf
)

test -x "$GENERATED_EXECUTABLE"

python3 - "$GENERATED_EXECUTABLE" <<'PY'
import subprocess
import sys

result = subprocess.run(
    [sys.argv[1]],
    timeout=10,
    check=False,
)

print(
    "Generated priority executable exit code:",
    result.returncode,
)

raise SystemExit(
    result.returncode
)
PY

echo "Real multi-server priority parser-to-native check passed."
echo "Generated JSON: $GENERATED_JSON"
echo "Generated summary: $GENERATED_SUMMARY"
echo "Generated LF: $GENERATED_LF"
echo "Generated executable: $GENERATED_EXECUTABLE"
