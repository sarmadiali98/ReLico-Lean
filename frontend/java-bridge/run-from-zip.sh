#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: run-from-zip.sh <artifact.zip> <input.rebeca> <output.json>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"
INPUT_FILE="$2"
OUTPUT_FILE="$3"

REPOSITORY_ROOT="$(
  git rev-parse --show-toplevel
)"

EXPORTER_SOURCE="$REPOSITORY_ROOT/frontend/java-bridge/RebecaV0JsonExporter.java"

test -f "$ARTIFACT_ZIP"
test -f "$INPUT_FILE"
test -f "$EXPORTER_SOURCE"
MAVEN_BIN="${RELICO_MAVEN:-mvn}"
"$MAVEN_BIN" -version 2>&1 | grep -q "Apache Maven"

WORK_DIRECTORY="$(
  mktemp -d /tmp/relico-parser-bridge.XXXXXX
)"

trap 'rm -rf "$WORK_DIRECTORY"' EXIT

UNPACKED_DIRECTORY="$WORK_DIRECTORY/unpacked"
mkdir -p "$UNPACKED_DIRECTORY"

python3 - "$ARTIFACT_ZIP" "$UNPACKED_DIRECTORY" <<'PY'
from pathlib import Path
import sys
import zipfile

archive = Path(sys.argv[1])
destination = Path(sys.argv[2])

with zipfile.ZipFile(archive) as source:
    for entry in source.infolist():
        parts = Path(entry.filename).parts

        if "examples" in parts:
            continue

        if "verifier-benchmarks" in parts:
            continue

        source.extract(entry, destination)
PY

PROJECT_POM="$(
  find "$UNPACKED_DIRECTORY" \
    -type f \
    -name pom.xml \
    -print \
    | head -n 1
)"

if [ -z "$PROJECT_POM" ]; then
  echo "No pom.xml was found in the artifact ZIP." >&2
  exit 1
fi

PROJECT_DIRECTORY="$(
  dirname "$PROJECT_POM"
)"

EXPORTER_DIRECTORY="$PROJECT_DIRECTORY/src/main/java/org/rebecalang/compiler/frontendbridge"

mkdir -p "$EXPORTER_DIRECTORY"

cp \
  "$EXPORTER_SOURCE" \
  "$EXPORTER_DIRECTORY/RebecaV0JsonExporter.java"

INPUT_COPY="$WORK_DIRECTORY/input.rebeca"
OUTPUT_COPY="$WORK_DIRECTORY/output.json"

cp "$INPUT_FILE" "$INPUT_COPY"

(
  cd "$PROJECT_DIRECTORY"

  "$MAVEN_BIN" \
    -q \
    -DskipTests \
    package

  "$MAVEN_BIN" \
    -q \
    org.codehaus.mojo:exec-maven-plugin:3.1.0:java \
    -Dexec.mainClass=org.rebecalang.compiler.frontendbridge.RebecaV0JsonExporter \
    -Dexec.args="$INPUT_COPY $OUTPUT_COPY"
)

test -f "$OUTPUT_COPY"

mkdir -p "$(
  dirname "$OUTPUT_FILE"
)"

cp "$OUTPUT_COPY" "$OUTPUT_FILE"

echo "Parser bridge output: $OUTPUT_FILE"
