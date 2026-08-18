#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: run-general-from-zip.sh <artifact.zip> <input.rebeca> <output.json>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"
INPUT_FILE="$2"
OUTPUT_FILE="$3"

EXPORTER_SOURCE="$(cd "$(dirname "$0")" && pwd)/RebecaGeneralJsonExporter.java"

test -f "$ARTIFACT_ZIP"
test -f "$INPUT_FILE"
test -f "$EXPORTER_SOURCE"

MAVEN_BIN="${RELICO_MAVEN:-}"

if [ -z "$MAVEN_BIN" ]; then
  for candidate in \
    /opt/homebrew/opt/maven/bin/mvn \
    /opt/homebrew/bin/mvn \
    /usr/local/bin/mvn \
    "$HOME/.sdkman/candidates/maven/current/bin/mvn"
  do
    if [ -x "$candidate" ] && \
       "$candidate" -version 2>&1 | grep -q "Apache Maven"
    then
      MAVEN_BIN="$candidate"
      break
    fi
  done
fi

if [ -z "$MAVEN_BIN" ]; then
  MAVEN_BIN="$(command -v mvn || true)"
fi

if [ -z "$MAVEN_BIN" ] || \
   ! "$MAVEN_BIN" -version 2>&1 | grep -q "Apache Maven"
then
  echo "Apache Maven was not found." >&2
  echo "Set RELICO_MAVEN to the full path of an Apache Maven executable." >&2
  exit 1
fi

# RELICO_GENERAL_BUILD_DIR is an opt-in cache. Unset, this script behaves
# exactly like its sibling runners: a fresh mktemp directory, unpacked and
# built from scratch, removed on exit. Set, the directory persists and a second
# invocation reuses the build, which is what lets check-general.sh run
# twenty-seven fixtures through one Maven build instead of twenty-seven.
#
# Each fixture still gets its own invocation of this script, so its exit code
# and its stderr remain separately observable. That is the whole point of the
# negative fixtures, and sharing a build directory must not cost it.
BUILD_DIRECTORY="${RELICO_GENERAL_BUILD_DIR:-}"

if [ -z "$BUILD_DIRECTORY" ]; then
  BUILD_DIRECTORY="$(
    mktemp -d /tmp/relico-general-parser-bridge.XXXXXX
  )"

  trap 'rm -rf "$BUILD_DIRECTORY"' EXIT
else
  mkdir -p "$BUILD_DIRECTORY"
fi

UNPACKED_DIRECTORY="$BUILD_DIRECTORY/unpacked"
SENTINEL_FILE="$BUILD_DIRECTORY/.relico-general-built"

# The sentinel records which exporter source the cached build was made from, so
# editing the exporter cannot be masked by a stale cache.
if command -v shasum >/dev/null 2>&1; then
  EXPORTER_FINGERPRINT="$(shasum -a 256 "$EXPORTER_SOURCE" | cut -d' ' -f1)"
elif command -v sha256sum >/dev/null 2>&1; then
  EXPORTER_FINGERPRINT="$(sha256sum "$EXPORTER_SOURCE" | cut -d' ' -f1)"
else
  echo "Neither shasum nor sha256sum was found." >&2
  exit 1
fi

CACHED_FINGERPRINT=""

if [ -f "$SENTINEL_FILE" ]; then
  CACHED_FINGERPRINT="$(cat "$SENTINEL_FILE")"
fi

if [ "$CACHED_FINGERPRINT" != "$EXPORTER_FINGERPRINT" ]; then
  rm -f "$SENTINEL_FILE"
  rm -rf "$UNPACKED_DIRECTORY"
fi

mkdir -p "$UNPACKED_DIRECTORY"

if [ ! -f "$SENTINEL_FILE" ]; then
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
fi

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
  "$EXPORTER_DIRECTORY/RebecaGeneralJsonExporter.java"

INPUT_COPY="$BUILD_DIRECTORY/input.rebeca"
OUTPUT_COPY="$BUILD_DIRECTORY/output.json"

cp "$INPUT_FILE" "$INPUT_COPY"

# Mandatory with a cached build directory: a leftover output from the previous
# fixture would make a rejected model look as though it had produced one.
rm -f "$OUTPUT_COPY"

if [ ! -f "$SENTINEL_FILE" ]; then
  (
    cd "$PROJECT_DIRECTORY"

    "$MAVEN_BIN" \
      -q \
      -DskipTests \
      package
  )

  printf '%s\n' "$EXPORTER_FINGERPRINT" > "$SENTINEL_FILE"
fi

(
  cd "$PROJECT_DIRECTORY"

  "$MAVEN_BIN" \
    -q \
    org.codehaus.mojo:exec-maven-plugin:3.1.0:java \
    -Dexec.mainClass=org.rebecalang.compiler.frontendbridge.RebecaGeneralJsonExporter \
    -Dexec.args="$INPUT_COPY $OUTPUT_COPY"
)

test -f "$OUTPUT_COPY"

mkdir -p "$(
  dirname "$OUTPUT_FILE"
)"

cp "$OUTPUT_COPY" "$OUTPUT_FILE"

echo "General parser bridge output: $OUTPUT_FILE"
