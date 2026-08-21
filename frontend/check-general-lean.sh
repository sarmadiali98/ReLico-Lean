#!/usr/bin/env bash
set -euo pipefail

# The Lean gate for the general family. Two runners, one build.
#
# Stage B's part checks that the Lean side agrees with the committed fixtures:
# every document decodes to the model it should, or is refused for the reason it
# should be. Stage C's part checks the generated-LF side, which has no fixtures at
# all -- it asserts the exact text the printer produces for a hand-built two-reactor
# program, and the exact accept-or-reject verdict well-formedness returns for nine
# variations on it.
#
# Both live here rather than in two scripts because they share the one expensive
# step, `lake build`, and neither can run against stale oleans.
#
# Deliberately does NOT run the Java exporter. frontend/java-bridge/check-general.sh
# already owns the Rebeca-to-JSON boundary -- it regenerates all nine positives
# from source and compares them against the committed documents, and runs the two
# negative corpora. Re-running it here would pay for a Maven build of the
# upstream compiler to re-establish a fact another gate already establishes.
# The division is: that script owns exporter-against-fixture, this one owns
# fixture-against-Lean, and the fixtures are the contract between them.
#
# The practical consequence is that this gate needs no artifact zip, no Maven and
# no network. It runs from a clean checkout plus a Lean toolchain, which is worth
# preserving: it means the Lean layer stays checkable when the upstream artifact
# is unavailable.

REPO="$(
  cd "$(dirname "$0")/.." &&
  pwd
)"

FIXTURE_DIRECTORY="$REPO/frontend/fixtures/general"
LEAN_REJECT_DIRECTORY="$FIXTURE_DIRECTORY/lean-reject"

BRIDGE_MAIN="$REPO/frontend/lean-bridge/GeneralBridgeMain.lean"
TEST_MAIN="$REPO/frontend/lean-bridge/GeneralFrontendTestMain.lean"
PRINTER_TEST_MAIN="$REPO/frontend/lean-bridge/GeneralLfPrinterTestMain.lean"

test -d "$FIXTURE_DIRECTORY"
test -d "$LEAN_REJECT_DIRECTORY"
test -f "$BRIDGE_MAIN"
test -f "$TEST_MAIN"
test -f "$PRINTER_TEST_MAIN"

cd "$REPO"

# Both mains are outside the build closure -- a module with an inline `def main`
# cannot be imported -- so `lake env lean --run` compiles them on demand. It does
# not build their imports, though; it only puts already-built ones on the path.
# Building first is therefore not belt-and-braces, it is what stops this gate
# from passing against stale oleans, which is the one failure a fixture gate must
# not have.
echo "=== building the Lean closure the bridge and the tests import"

lake build

echo
echo "=== the bridge check, over every positive fixture"

# One invocation per fixture, so that a failure names the fixture and so that the
# printed class and instance counts stay separately readable. control-flow is
# excluded here: the exporter emits it and this layer refuses it, which is the
# bridge check reporting a rejection rather than a bridge failure. The test
# runner is where that rejection is asserted, with the reason it must carry.
for DOCUMENT in "$FIXTURE_DIRECTORY"/*.parser.json; do
  NAME="$(basename "$DOCUMENT" .parser.json)"

  if [ "$NAME" = "control-flow" ]; then
    continue
  fi

  printf '%-24s ' "$NAME"

  lake env lean \
    --run \
    "$BRIDGE_MAIN" \
    "$DOCUMENT"
done

echo
echo "=== the fixture expectations, accepted and rejected"

# Captured rather than streamed, because the count below is taken from what the
# run actually printed. The status is taken separately instead of being left to
# `set -e`, which would abort at the capture and discard the output -- losing
# precisely the PASS_ lines that say how far the run got before it failed.
set +e
TEST_OUTPUT="$(
  lake env lean \
    --run \
    "$TEST_MAIN" \
    "$FIXTURE_DIRECTORY"
)"
TEST_STATUS=$?
set -e

# Streamed after the fact, so a failing run is still readable in the log. The
# runner's own diagnostic went to stderr and has already appeared above.
printf '%s\n' "$TEST_OUTPUT"

if [ "$TEST_STATUS" -ne 0 ]; then
  echo
  echo "the fixture expectations failed (exit $TEST_STATUS); see the diagnostic above"
  exit 1
fi

# A fixture that no assertion mentions is the failure mode this corpus is most
# exposed to: adding one is a two-file change, and forgetting the second file
# leaves a document that looks like coverage and is never decoded. Nothing in the
# Lean layer can notice that, because the runner names its fixtures literally --
# by design, so that adding one forces a decision about which layer should accept
# it.
#
# So the count is checked here instead, against what the run printed rather than
# against the runner's source: one PASS_ line per fixture, and every fixture on
# disk accounted for. Counting output rather than grepping for `expect` calls
# also means a commented-out or unreachable assertion fails this check.
POSITIVE_COUNT="$(
  ls -1 "$FIXTURE_DIRECTORY"/*.parser.json |
    wc -l |
    tr -d ' '
)"

LEAN_REJECT_COUNT="$(
  ls -1 "$LEAN_REJECT_DIRECTORY"/*.json |
    wc -l |
    tr -d ' '
)"

EXPECTED_ASSERTIONS=$((POSITIVE_COUNT + LEAN_REJECT_COUNT))

ACTUAL_ASSERTIONS="$(
  printf '%s\n' "$TEST_OUTPUT" |
    grep -c '^PASS_' ||
    true
)"

# `grep -c` exits 1 when it counts nothing, and under `pipefail` that would end
# the run here -- at the one moment this check has something to report. The `||
# true` above keeps the exit code out of it; this keeps the value usable, because
# a failed `grep -c` still prints its `0` but a killed pipeline prints nothing.
if [ -z "$ACTUAL_ASSERTIONS" ]; then
  ACTUAL_ASSERTIONS=0
fi

echo
echo "documents under fixtures/general:  $POSITIVE_COUNT"
echo "documents under lean-reject:       $LEAN_REJECT_COUNT"
echo "assertions the run reported:       $ACTUAL_ASSERTIONS"

if [ "$ACTUAL_ASSERTIONS" -ne "$EXPECTED_ASSERTIONS" ]; then
  echo
  echo "expected $EXPECTED_ASSERTIONS assertions, one per document, but the run"
  echo "reported $ACTUAL_ASSERTIONS."
  echo
  echo "Every document in both directories needs an expectAccept or expectReject"
  echo "in frontend/lean-bridge/GeneralFrontendTestMain.lean. A document with no"
  echo "assertion is never decoded by anything."
  exit 1
fi

if ! printf '%s\n' "$TEST_OUTPUT" | grep -q '^GENERAL_FRONTEND_TESTS_OK$'; then
  echo
  echo "the test runner did not print its completion marker"
  exit 1
fi

echo
echo "=== the general LF printer, well-formedness and translation assertions"

# Same capture-then-check shape as above, and for the same reason: the count is
# taken from what the run actually printed.
#
# Unlike the fixture expectations, the expected count here is a literal. There is
# nothing on disk to count -- this runner reads no fixtures, because the general LF
# family has no exporter and no decoder yet, so every value it asserts on is built
# in Lean. The literal is what lets the gate notice an assertion that stopped
# running: the completion marker alone cannot, since a `try` block that skipped
# twenty assertions still reaches its final `IO.println`.
#
# 34 printing, 10 well-formedness, 11 translation, 3 for the port-name collisions F34
# and F42, 5 for finding F32's counterexample, 7 for the routed model, 6 for the
# refusals routing reaches, 6 for finding F48's aliased endpoints. Eight blocks, 82,
# the same breakdown the runner's own docstring gives.
#
# That enumeration was itself stale until 2026-08-22, when it listed six blocks summing
# to 70 under a literal reading 82: F47's six and F48's six had been added to the
# paragraph below it and never to the list above it. Which is the same
# prose-instead-of-a-greppable-label failure as F44, F46 and F47, occurring in the file
# whose job is to catch exactly that, and recorded as its fifth instance in
# docs/STAGE_E_FINDINGS.md. Nothing executable reads this list, so only reading it
# against the literal finds a drift; do that whenever the literal moves.
#
# Stage C ran 25, in two blocks; the third block is the one that mentions
# `Relico.Translation`, so a translation that stopped being called would drop this
# count by eleven rather than pass quietly. The fourth is the only block that calls a
# naming function directly. The fifth asserts that the
# well-formedness preservation theorem is false; when the DTR-side clause lands it
# must be rewritten, and this literal is what forces that to be deliberate. The sixth
# is the only block that routes, so a stage E regression drops this by seven and says so.
#
# Stage E moved this literal four times. First down from 60: `generalModelSelfSendOnly` and
# its refusal text were asserted four times between them and the predicate no longer exists;
# three assertions took their place. Then up to 66 for the routed model. Then up to 67, when
# the F32 group moved off `compileGeneralModel` -- whose new guard refuses the counterexample
# instead of returning it -- and gained an assertion pinning that refusal, which is finding
# F43. Then up to 70 for three port-name collision witnesses that
# `Relico/Translation/NameGeneration.lean` had already claimed were asserted here while they
# did not exist, which is finding F44. A literal that is only ever raised is a literal being
# maintained by addition rather than by reading. Then up to 76 for the six translation
# refusals `Relico/Translation/GeneralBasic.lean` had credited to two `lean-reject` documents
# that cannot reach a translation function at all, which is finding F47 -- the same failure
# as F44 in a second module, and the reason both numbers are worth reading rather than
# bumping. Then up to 82 for finding F48's six: a well-formed source model whose routing
# collides two target endpoints, which refutes a docstring that had called the construction
# proof of `targetEndpointsUnique` deferred rather than false. The eighth block is the only
# one that asserts a named clause of `LF.GeneralProgram.wellFormed` to be false, so a drop of
# six here means the repository has stopped holding a witness for a property it claims.
EXPECTED_PRINTER_ASSERTIONS=82

set +e
PRINTER_OUTPUT="$(
  lake env lean \
    --run \
    "$PRINTER_TEST_MAIN"
)"
PRINTER_STATUS=$?
set -e

printf '%s\n' "$PRINTER_OUTPUT"

if [ "$PRINTER_STATUS" -ne 0 ]; then
  echo
  echo "the printer assertions failed (exit $PRINTER_STATUS); see the diagnostic above"
  exit 1
fi

ACTUAL_PRINTER_ASSERTIONS="$(
  printf '%s\n' "$PRINTER_OUTPUT" |
    grep -c '^PASS_' ||
    true
)"

if [ -z "$ACTUAL_PRINTER_ASSERTIONS" ]; then
  ACTUAL_PRINTER_ASSERTIONS=0
fi

echo
echo "printer assertions the run reported: $ACTUAL_PRINTER_ASSERTIONS"

if [ "$ACTUAL_PRINTER_ASSERTIONS" -ne "$EXPECTED_PRINTER_ASSERTIONS" ]; then
  echo
  echo "expected $EXPECTED_PRINTER_ASSERTIONS printer assertions, but the run"
  echo "reported $ACTUAL_PRINTER_ASSERTIONS."
  echo
  echo "The count is stated in the docstring of runGeneralLfPrinterTests in"
  echo "frontend/lean-bridge/GeneralLfPrinterTestMain.lean. Adding an assertion"
  echo "means changing both, on purpose."
  exit 1
fi

if ! printf '%s\n' "$PRINTER_OUTPUT" | grep -q '^GENERAL_LF_PRINTER_TESTS_OK$'; then
  echo
  echo "the printer test runner did not print its completion marker"
  exit 1
fi

echo
echo "GENERAL_LEAN_GATE_OK"
