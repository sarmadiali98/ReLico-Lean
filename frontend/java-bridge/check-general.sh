#!/usr/bin/env bash
set -euo pipefail

# Stage A frontend gate. Runs every fixture in frontend/fixtures/general
# through the real Rebeca parser and RebecaGeneralJsonExporter, then checks
# each emitted document against the schema validator and its expected fixture.
# Nothing here touches Lean: this script is entirely about the Rebeca-to-JSON
# boundary.
#
# Three corpora, checked in three loops: the positives, the negatives this
# exporter rejects, and the negatives the Rebeca parser rejects before the
# exporter is handed an AST. The third corpus exists because eight restrictions
# turned out to be enforced a layer below us, and a fixture that cannot reach
# the code it claims to test is worse than no fixture -- it reads as coverage.
# Keeping them, in their own directory, records which layer enforces what, and
# that is exactly the list stage B has to re-enforce in Lean, where there is no
# Rebeca typechecker upstream of the decoder.

MODE=""

while [ "$#" -gt 0 ] && [ "${1#--}" != "$1" ]; do
  case "$1" in
    --record)
      MODE="--record"
      ;;
    --accept-lines)
      MODE="--accept-lines"
      ;;
    *)
      echo "unknown option $1" >&2
      exit 2
      ;;
  esac

  shift
done

if [ "$#" -ne 1 ]; then
  echo "usage: check-general.sh [--record|--accept-lines] <artifact.zip>" >&2
  exit 2
fi

ARTIFACT_ZIP="$1"

REPOSITORY_ROOT="$(
  git rev-parse --show-toplevel
)"

cd "$REPOSITORY_ROOT"

FIXTURE_DIRECTORY="$REPOSITORY_ROOT/frontend/fixtures/general"
REJECT_DIRECTORY="$FIXTURE_DIRECTORY/reject"
UPSTREAM_REJECT_DIRECTORY="$FIXTURE_DIRECTORY/upstream-reject"

GENERATED_DIRECTORY="$REPOSITORY_ROOT/.lake/frontend-general-check"

RUNNER="$REPOSITORY_ROOT/frontend/java-bridge/run-general-from-zip.sh"
VALIDATOR="$REPOSITORY_ROOT/frontend/validate_general_v1.py"
COMPARATOR="$REPOSITORY_ROOT/frontend/compare_general_v1.py"

# Which layer rejected a model is as much a part of a negative fixture's claim
# as the message is, and the two layers are distinguishable in the log. The
# upstream banner is printed by the Rebeca compiler's own driver when parsing or
# semantic checking fails; the marker is the prefix every diagnostic the
# exporter raises carries. Measured over a full run of both corpora: the banner
# appears in all eight upstream-caught logs and none of the exporter-caught
# ones, and the marker exactly the other way round. So requiring one and
# forbidding the other pins the layer in both directions, and a restriction that
# silently migrates from one layer to the other fails the gate instead of
# quietly changing meaning.
UPSTREAM_BANNER="Timed Rebeca parsing or semantic checking failed"
EXPORTER_MARKER="unsupported by the ReLico general parser bridge"

test -f "$ARTIFACT_ZIP"
test -d "$FIXTURE_DIRECTORY"
test -d "$REJECT_DIRECTORY"
test -d "$UPSTREAM_REJECT_DIRECTORY"
test -x "$RUNNER"
test -f "$VALIDATOR"
test -f "$COMPARATOR"

rm -rf "$GENERATED_DIRECTORY"
mkdir -p "$GENERATED_DIRECTORY/logs"

# One Maven build for the whole run. Each fixture still gets its own invocation
# of the runner, so its exit code and stderr stay separately observable; only
# the unpack-and-compile step is shared. Without this every fixture in all three
# loops would pay for its own build of the upstream compiler. Deliberately not
# written as a count: this comment said "twenty-seven fixtures" while the corpus
# held twenty-eight, and a number here has to be maintained by whoever adds a
# fixture anywhere, which is exactly the maintenance that keeps failing.
BUILD_DIRECTORY="$GENERATED_DIRECTORY/build"
mkdir -p "$BUILD_DIRECTORY"

export RELICO_GENERAL_BUILD_DIR="$BUILD_DIRECTORY"

echo "=== the checkers' own tests, before trusting anything they say"

# A recording run is the one run whose purpose is to create expected documents
# that do not exist yet, so the suite below must not demand them first. Without
# this the gate could not record a new positive at all: the preflight failed on
# the missing document, and the loop that would have written it never ran — while
# the failing test's own message said to "run the gate with --record". That is
# finding F55. The tight invariant is unchanged for every ordinary run, which is
# the run whose green result is the gate.
if [ "$MODE" = "--record" ]; then
  export RELICO_GENERAL_RECORDING=1
fi

python3 "$REPOSITORY_ROOT/frontend/test_validate_general_v1.py"
python3 "$REPOSITORY_ROOT/frontend/test_compare_general_v1.py"

FAILURES=0
FAILED_NAMES=""

note_failure() {
  FAILURES=$((FAILURES + 1))
  FAILED_NAMES="$FAILED_NAMES
  $1"
}

echo
echo "=== positives: must be accepted, must match their expected document"

POSITIVE_COUNT=0
RECORDED_COUNT=0

for SOURCE_PATH in "$FIXTURE_DIRECTORY"/*.rebeca; do
  NAME="$(basename "$SOURCE_PATH" .rebeca)"
  POSITIVE_COUNT=$((POSITIVE_COUNT + 1))

  EMITTED="$GENERATED_DIRECTORY/$NAME.parser.json"
  EXPECTED="$FIXTURE_DIRECTORY/$NAME.parser.json"
  LOG="$GENERATED_DIRECTORY/logs/$NAME.log"

  printf '%-24s ' "$NAME"

  set +e
  "$RUNNER" "$ARTIFACT_ZIP" "$SOURCE_PATH" "$EMITTED" > "$LOG" 2>&1
  RUNNER_STATUS=$?
  set -e

  if [ "$RUNNER_STATUS" -ne 0 ]; then
    echo "REJECTED (exit $RUNNER_STATUS) — see $LOG"
    note_failure "$NAME (exporter rejected a positive fixture)"
    continue
  fi

  if [ ! -f "$EMITTED" ]; then
    echo "NO OUTPUT despite exit 0"
    note_failure "$NAME (exit 0 but no output document)"
    continue
  fi

  set +e
  VALIDATOR_OUTPUT="$(python3 "$VALIDATOR" "$EMITTED" 2>&1)"
  VALIDATOR_STATUS=$?
  set -e

  if [ "$VALIDATOR_STATUS" -ne 0 ]; then
    echo "INVALID"
    printf '%s\n' "$VALIDATOR_OUTPUT" | sed 's/^/    /'
    note_failure "$NAME (emitted document violates general-v1)"
    continue
  fi

  set +e
  COMPARATOR_OUTPUT="$(
    if [ -n "$MODE" ]; then
      python3 "$COMPARATOR" "$MODE" "$EXPECTED" "$EMITTED" 2>&1
    else
      python3 "$COMPARATOR" "$EXPECTED" "$EMITTED" 2>&1
    fi
  )"
  COMPARATOR_STATUS=$?
  set -e

  case "$COMPARATOR_STATUS" in
    0)
      if printf '%s' "$COMPARATOR_OUTPUT" | grep -q "^recorded "; then
        echo "RECORDED — review before commit"
        RECORDED_COUNT=$((RECORDED_COUNT + 1))
      else
        echo "ok"
      fi
      ;;
    2)
      echo "LINE NUMBERS DIFFER"
      printf '%s\n' "$COMPARATOR_OUTPUT" | sed 's/^/    /'
      note_failure "$NAME (line numbers differ; rerun with --accept-lines)"
      ;;
    3)
      echo "NOT RECORDED — rerun with --record"
      note_failure "$NAME (no expected document)"
      ;;
    *)
      echo "DIFFERS"
      printf '%s\n' "$COMPARATOR_OUTPUT" | sed 's/^/    /'
      note_failure "$NAME (emitted document differs structurally)"
      ;;
  esac
done

echo
echo "=== negatives the exporter itself must reject, with the diagnostic they claim"

NEGATIVE_COUNT=0

for SOURCE_PATH in "$REJECT_DIRECTORY"/*.rebeca; do
  NAME="$(basename "$SOURCE_PATH" .rebeca)"
  NEGATIVE_COUNT=$((NEGATIVE_COUNT + 1))

  DIAGNOSTIC_PATH="$REJECT_DIRECTORY/$NAME.diagnostic"
  EMITTED="$GENERATED_DIRECTORY/reject-$NAME.parser.json"
  LOG="$GENERATED_DIRECTORY/logs/reject-$NAME.log"

  printf '%-26s ' "$NAME"

  if [ ! -f "$DIAGNOSTIC_PATH" ]; then
    echo "NO EXPECTED DIAGNOSTIC"
    note_failure "$NAME (missing .diagnostic)"
    continue
  fi

  EXPECTED_DIAGNOSTIC="$(cat "$DIAGNOSTIC_PATH")"

  set +e
  "$RUNNER" "$ARTIFACT_ZIP" "$SOURCE_PATH" "$EMITTED" > "$LOG" 2>&1
  RUNNER_STATUS=$?
  set -e

  if [ "$RUNNER_STATUS" -eq 0 ]; then
    echo "ACCEPTED — a negative fixture was not rejected"
    note_failure "$NAME (accepted a model that must be rejected)"
    continue
  fi

  if [ -f "$EMITTED" ]; then
    echo "WROTE OUTPUT while failing"
    note_failure "$NAME (rejected but still wrote an output document)"
    continue
  fi

  if grep -qF "$UPSTREAM_BANNER" "$LOG"; then
    # The model never reached the exporter, so whatever it proves, it does not
    # prove anything about this exporter. Relocating it is the fix; relabelling
    # its diagnostic would leave a test that passes for the wrong reason.
    echo "CAUGHT UPSTREAM — move to upstream-reject/"
    echo "    see $LOG"
    note_failure "$NAME (rejected by the Rebeca parser, not by the exporter)"
    continue
  fi

  if ! grep -qF "$EXPORTER_MARKER" "$LOG"; then
    echo "REJECTED BY NEITHER LAYER"
    echo "    no upstream banner and no exporter diagnostic; see $LOG"
    note_failure "$NAME (non-zero exit with no diagnostic from either layer)"
    continue
  fi

  if ! grep -qF "$EXPECTED_DIAGNOSTIC" "$LOG"; then
    echo "WRONG DIAGNOSTIC"
    echo "    expected to find: $EXPECTED_DIAGNOSTIC"
    echo "    see $LOG"
    note_failure "$NAME (the exporter rejected it for the wrong reason)"
    continue
  fi

  echo "ok"
done

echo
echo "=== negatives the Rebeca parser rejects before the exporter sees them"

UPSTREAM_NEGATIVE_COUNT=0

for SOURCE_PATH in "$UPSTREAM_REJECT_DIRECTORY"/*.rebeca; do
  NAME="$(basename "$SOURCE_PATH" .rebeca)"
  UPSTREAM_NEGATIVE_COUNT=$((UPSTREAM_NEGATIVE_COUNT + 1))

  DIAGNOSTIC_PATH="$UPSTREAM_REJECT_DIRECTORY/$NAME.diagnostic"
  EMITTED="$GENERATED_DIRECTORY/upstream-reject-$NAME.parser.json"
  LOG="$GENERATED_DIRECTORY/logs/upstream-reject-$NAME.log"

  printf '%-26s ' "$NAME"

  if [ ! -f "$DIAGNOSTIC_PATH" ]; then
    echo "NO EXPECTED DIAGNOSTIC"
    note_failure "$NAME (missing .diagnostic)"
    continue
  fi

  EXPECTED_DIAGNOSTIC="$(cat "$DIAGNOSTIC_PATH")"

  set +e
  "$RUNNER" "$ARTIFACT_ZIP" "$SOURCE_PATH" "$EMITTED" > "$LOG" 2>&1
  RUNNER_STATUS=$?
  set -e

  if [ "$RUNNER_STATUS" -eq 0 ]; then
    echo "ACCEPTED — a negative fixture was not rejected"
    note_failure "$NAME (accepted a model that must be rejected)"
    continue
  fi

  if [ -f "$EMITTED" ]; then
    echo "WROTE OUTPUT while failing"
    note_failure "$NAME (rejected but still wrote an output document)"
    continue
  fi

  if ! grep -qF "$UPSTREAM_BANNER" "$LOG"; then
    # Either the parser now accepts this model and the exporter caught it, or
    # nothing caught it at all. Both are real news: the restriction has changed
    # hands, and this directory is the record of who enforces what.
    echo "NOT CAUGHT UPSTREAM — reclassify"
    echo "    see $LOG"
    note_failure "$NAME (no longer rejected by the Rebeca parser)"
    continue
  fi

  if grep -qF "$EXPORTER_MARKER" "$LOG"; then
    echo "EXPORTER ALSO RAN"
    echo "    an exporter diagnostic appears in a parser-rejected run; see $LOG"
    note_failure "$NAME (both layers produced diagnostics)"
    continue
  fi

  if ! grep -qF "$EXPECTED_DIAGNOSTIC" "$LOG"; then
    echo "WRONG UPSTREAM DIAGNOSTIC"
    echo "    expected to find: $EXPECTED_DIAGNOSTIC"
    echo "    see $LOG"
    note_failure "$NAME (the parser rejected it for a different reason)"
    continue
  fi

  echo "ok"
done

echo
echo "positives:                    $POSITIVE_COUNT"
echo "negatives (exporter):         $NEGATIVE_COUNT"
echo "negatives (Rebeca parser):    $UPSTREAM_NEGATIVE_COUNT"

if [ "$RECORDED_COUNT" -gt 0 ]; then
  echo
  echo "$RECORDED_COUNT expected document(s) were recorded from this run."
  echo "They assert only that the exporter is deterministic until a human has"
  echo "read them. Review each against the source model before committing."
fi

if [ "$FAILURES" -ne 0 ]; then
  echo
  echo "$FAILURES fixture(s) failed:$FAILED_NAMES"
  echo
  echo "Logs: $GENERATED_DIRECTORY/logs"
  exit 1
fi

echo
echo "General frontend check passed."
echo "Emitted documents: $GENERATED_DIRECTORY"
