#!/usr/bin/env bash
set -euo pipefail

# The TARGET gate for the general family: does a real `lfc` accept the LF text
# this repo's printer actually emits?
#
# This is a different question from the one frontend/check-general-lean.sh asks,
# and the difference is the whole reason this script exists. That gate asserts
# that the printer produces an exact string, which is a claim about the printer
# and a string sitting in the same repository. Both can agree and both can be
# wrong about LF. Only the compiler settles whether the emitted text is a legal
# program.
#
# The gap was not hypothetical. When this script was written, `*in.get()` --
# reading a value off an input port -- had ZERO occurrences across the 24
# committed `lfc`-accepted fixtures under tests/benchmarks/*/expected/lf-source,
# and `reaction(in) -> deliver`, a port-triggered reaction carrying a logical
# action as its effect, had no exact precedent either. The printer emits both.
# Every other construct in the emitted program did have precedent: `target Cpp`,
# `input`/`output` declarations, `state x: int = 0`, `logical action ...: int`,
# `out.set(1);`, `schedule(payload, delay)` and `... after 0 msec`.
#
# Kept OUT of check-general-lean.sh deliberately. That script's useful property
# is that it needs no Maven, no artifact zip and no network -- a clean checkout
# plus a Lean toolchain is enough, which is what keeps the Lean layer checkable
# when the upstream artifact is unavailable. `lfc` and a C++ toolchain are a
# heavier dependency than that, and folding them in would cost that property for
# every future run of the cheaper gate.
#
# The emitted text comes from the printer, not from a copy of it. The runner is
# asked for `emit-program`, which prints `renderGeneralProgram` applied to the
# same program the assertions pin, and nothing else -- so this gate cannot pass
# against a hand-transcribed variant that drifted from what the printer does.

REPO="$(
  cd "$(dirname "$0")/.." &&
  pwd
)"

# Overridable, because the path is a per-machine install location rather than a
# repository fact. The default is the one measured on 2026-08-19, and matches the
# path pinned by tools/paper-measurements/lf_semantics_probe.sh.
LFC="${LFC:-/Users/ali/.local/share/lingua-franca/cli/bin/lfc}"

PRINTER_TEST_MAIN="$REPO/frontend/lean-bridge/GeneralLfPrinterTestMain.lean"

# The file basename becomes the target name, because the emitted main reactor is
# anonymous -- `main reactor {`, with no name of its own. So this constant also
# names the binary that gets run below.
PROGRAM_NAME="GeneralPrinterProgram"

WORK="${TMPDIR:-/tmp}/relico_general_lf_target"

test -f "$PRINTER_TEST_MAIN"

if [ ! -x "$LFC" ]; then
  echo "no executable lfc at $LFC"
  echo
  echo "Set LFC to a Lingua Franca compiler, or install one. This gate cannot"
  echo "be satisfied by anything else: its whole content is what lfc accepts."
  exit 1
fi

cd "$REPO"

echo "=== lfc identity"

"$LFC" --version

echo
echo "=== building the Lean closure the printer lives in"

# `lake env lean --run` compiles the runner on demand but does NOT build its
# imports; it only puts already-built ones on the path. Without this the gate
# either fails on a missing olean or, worse, emits text from a stale printer.
lake build

echo
echo "=== emitting the program from the printer"

rm -rf "$WORK"
mkdir -p "$WORK/src"

EMITTED="$WORK/src/$PROGRAM_NAME.lf"

set +e
lake env lean \
  --run \
  "$PRINTER_TEST_MAIN" \
  emit-program \
  > "$EMITTED"
EMIT_STATUS=$?
set -e

if [ "$EMIT_STATUS" -ne 0 ]; then
  echo "the printer refused to emit (exit $EMIT_STATUS); see the diagnostic above"
  exit 1
fi

# An empty file would otherwise reach lfc and fail there, with a diagnostic
# about an empty program rather than about the emit step that actually broke.
if [ ! -s "$EMITTED" ]; then
  echo "the printer emitted nothing"
  exit 1
fi

# A cheap shape check before paying for a C++ build: if the first line is not the
# target declaration then something other than a program reached the file, and
# lfc's complaint would be about the stray text rather than about that.
if [ "$(head -1 "$EMITTED")" != "target Cpp" ]; then
  echo "the emitted text does not begin with a target declaration:"
  head -3 "$EMITTED"
  exit 1
fi

cat "$EMITTED"

echo
echo "=== compiling it with lfc"

# From the work directory with a src/-relative path, which is the layout lfc
# expects and the one the probe script uses.
set +e
(
  cd "$WORK" &&
  "$LFC" "src/$PROGRAM_NAME.lf"
) > "$WORK/lfc.log" 2>&1
LFC_STATUS=$?
set -e

if [ "$LFC_STATUS" -ne 0 ]; then
  echo "lfc rejected the emitted program (exit $LFC_STATUS)"
  echo
  tail -30 "$WORK/lfc.log"
  exit 1
fi

echo "lfc accepted it"

# Warnings are reported and not treated as failure. The generated C++ warns about
# an unused private field for any state variable a reaction never reads, and a
# DTR state variable is required to exist whether or not the model reads it -- so
# treating lfc log content as failure would reject correct output.
if grep -q 'warning' "$WORK/lfc.log"; then
  echo
  echo "compiler warnings, reported and not fatal:"
  grep 'warning' "$WORK/lfc.log" | head -10
fi

echo
echo "=== running the compiled binary"

# Compiling proves the text parses and the generated C++ builds. Running proves
# it links and that the reactions can actually fire, which is the part a
# code-generation check alone leaves open.
set +e
"$WORK/bin/$PROGRAM_NAME" > "$WORK/run.log" 2>&1
RUN_STATUS=$?
set -e

if [ "$RUN_STATUS" -ne 0 ]; then
  echo "the compiled program failed at run time (exit $RUN_STATUS)"
  echo
  tail -20 "$WORK/run.log"
  exit 1
fi

echo "it ran and exited cleanly"

echo
echo "GENERAL_LF_TARGET_OK"
