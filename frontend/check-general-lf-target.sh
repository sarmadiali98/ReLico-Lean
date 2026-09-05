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
#
# FIVE programs are emitted, compiled and run. `emit-program` prints a hand-built
# LF program and so asks only whether this printer's output is legal LF.
# `emit-widened` prints the translation of a single-actor Timed Rebeca model --
# `compileGeneralModel` then the printer -- and so asks the question stage D exists
# for: does what the translator produces compile and run. A gate that ran only the
# first would stay green against a translation that emitted nothing at all, because
# no hand-built program passes through it.
#
# `emit-routed` is stage E's, and it is the first program here with more than one
# reactor. Ports, connections and instances of two classes cannot appear in the
# other two: the widened model's every send is aimed at itself, so its `main
# reactor` body is nothing but instances. Three of its constructs reach a real
# compiler here for the first time in this repository, each having previously been
# argued for rather than measured:
#
#   * a connection with a NONZERO `after` delay. Every probe under
#     tools/paper-measurements/ writes `after 0 msec`; the routed program writes
#     `after 3 msec` and `after 7 msec` as well.
#   * a reactor with NO startup reaction, which is what an empty Rebeca constructor
#     body translates to. All 24 committed expected/lf-source/*.lf files have one
#     with a non-empty body.
#   * an instance whose input ports NO connection reaches. Input ports are a
#     projection of the receiving class rather than of the instance, because
#     lfc 0.11.0 rejects many-to-one connections, so a second instance of a
#     receiving class declares ports nothing feeds. §7.2 of the stage E design
#     needs that to be legal.
#
# The widened model terminates on its own: its constructor self-sends at
# `after(0)`, that message server self-sends at `after(5)`, and the last one sends
# nothing, so the event queue empties and the binary exits. The routed model
# terminates for the same kind of reason: its sender self-sends once from startup
# and the class it then sends to sends nothing. That is a requirement of this gate
# rather than a property of the models -- a model that kept scheduling would hang
# here instead of failing.
#
# `emit-repeated` is the F56 witness, and it is the first program here in which one
# message server owns more than one logical action. Its class self-sends `tick` twice
# from a single constructor body, with the same `after(1)` on both, which is the exact
# configuration lfc 0.11.0 mishandles when both sends share one action: it keeps only
# the last payload, silently, exiting 0. The three programs above would all still
# compile and run if the per-site repair were reverted, so this one is the only place
# in this gate where the repair is on trial. What lfc decides here is narrow but not
# nothing -- whether two logical actions on one reactor, two reactions distinguished
# only by their triggers, and one startup reaction declaring both actions as effects,
# are together legal LF.
#
# It terminates for the reason the two models above do: `tick` assigns to a state
# variable and sends nothing, so the queue empties once both deliveries have run.
#
# `emit-priority-witness` is G5's witness (STAGE_G_DESIGN §10), and the first program in
# this gate whose *run* is asserted on rather than only its exit code. Every ordering
# claim before it was gated as text; this one is gated as behaviour. The model carries
# two derangements, one per level: the hub declares its servers `early, late` and
# annotates only `late`, so the level-2 sort emits the hub's reaction blocks
# late-first; and the two senders are declared `early, late` with priorities `2` and
# `1`, so the level-1 sort emits `late`'s connection first. Both senders send from
# their constructors `after 0`, so both deliveries arrive at one complete tag on two
# port-triggered reactions of one reactor -- the exact shape stage F measured
# (STAGE_F_DESIGN §2.1: at one tag, declaration order decides). The assertion below
# therefore requires stdout to read `LATE` before `EARLY`, against a declaration order
# that says the opposite at both levels. A translator that emitted the right
# declaration order while running in the wrong one now fails here and nowhere else.
#
# The four cycles above keep their exit-code-only contract untouched; this is a new
# marker extending the gate, not a reinterpretation of the old ones. Stage E's "forced,
# not lazy" verdict on exit-code checking stands for them: they have no output to diff.
# This program does, because G5 added the `trace` statement whose only job is to put
# one there. The bytes on stdout are target-runtime evidence and stay outside the
# formal observable alphabet -- Option A made `.trace` a tau step on both sides
# precisely so the theorem boundary does not move.

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
# anonymous -- `main reactor {`, with no name of its own. So each name below also
# names the binary that gets run.
#
# Seven names, and each program gets its own work directory. Sharing one would let a
# binary left by an earlier run satisfy a later one even if its own compile step had
# quietly produced nothing. (This comment said "four" while five names stood below it;
# stage I0 added the sixth and corrected the count; stage I's S-I6 added the seventh.)
BASE_PROGRAM_NAME="GeneralPrinterProgram"
WIDENED_PROGRAM_NAME="GeneralTranslatedProgram"
ROUTED_PROGRAM_NAME="GeneralRoutedProgram"
REPEATED_PROGRAM_NAME="GeneralRepeatedSelfSendProgram"
PRIORITY_WITNESS_PROGRAM_NAME="GeneralPriorityWitnessProgram"
CONDITIONAL_PROGRAM_NAME="GeneralConditionalWitnessProgram"
LOCAL_DECL_PROGRAM_NAME="GeneralLocalDeclWitnessProgram"

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

# One emit-compile-run cycle, parameterised by the runner's selector and the
# program name.
#
# A function rather than the block it replaces, because stage D needed the cycle
# twice and stage E needs it three times; the copies would be identical except for
# two words. Written for bash 3.2, which is what /bin/bash is on this machine:
# positional parameters and `local`, no name references and no associative arrays.
check_program() {
  local selector="$1"
  local program_name="$2"
  local description="$3"

  local work="$WORK/$program_name"
  local emitted="$work/src/$program_name.lf"

  echo
  echo "=== emitting $description"

  mkdir -p "$work/src"

  set +e
  lake env lean \
    --run \
    "$PRINTER_TEST_MAIN" \
    "$selector" \
    > "$emitted"
  local emit_status=$?
  set -e

  if [ "$emit_status" -ne 0 ]; then
    echo "the runner refused to emit $description (exit $emit_status); see the diagnostic above"
    exit 1
  fi

  # An empty file would otherwise reach lfc and fail there, with a diagnostic
  # about an empty program rather than about the emit step that actually broke.
  if [ ! -s "$emitted" ]; then
    echo "the runner emitted nothing for $description"
    exit 1
  fi

  # A cheap shape check before paying for a C++ build: if the first line is not the
  # target declaration then something other than a program reached the file, and
  # lfc's complaint would be about the stray text rather than about that.
  if [ "$(head -1 "$emitted")" != "target Cpp" ]; then
    echo "the emitted text for $description does not begin with a target declaration:"
    head -3 "$emitted"
    exit 1
  fi

  cat "$emitted"

  echo
  echo "=== compiling $description with lfc"

  # From the work directory with a src/-relative path, which is the layout lfc
  # expects and the one the probe script uses.
  set +e
  (
    cd "$work" &&
    "$LFC" "src/$program_name.lf"
  ) > "$work/lfc.log" 2>&1
  local lfc_status=$?
  set -e

  if [ "$lfc_status" -ne 0 ]; then
    echo "lfc rejected $description (exit $lfc_status)"
    echo
    tail -30 "$work/lfc.log"
    exit 1
  fi

  echo "lfc accepted it"

  # Warnings are reported and not treated as failure. The generated C++ warns about
  # an unused private field for any state variable a reaction never reads, and a
  # DTR state variable is required to exist whether or not the model reads it -- so
  # treating lfc log content as failure would reject correct output.
  if grep -q 'warning' "$work/lfc.log"; then
    echo
    echo "compiler warnings, reported and not fatal:"
    grep 'warning' "$work/lfc.log" | head -10
  fi

  echo
  echo "=== running $description"

  # Compiling proves the text parses and the generated C++ builds. Running proves
  # it links and that the reactions can actually fire, which is the part a
  # code-generation check alone leaves open.
  set +e
  "$work/bin/$program_name" > "$work/run.log" 2>&1
  local run_status=$?
  set -e

  if [ "$run_status" -ne 0 ]; then
    echo "$description failed at run time (exit $run_status)"
    echo
    tail -20 "$work/run.log"
    exit 1
  fi

  echo "it ran and exited cleanly"
}

rm -rf "$WORK"

# The hand-built program first. It is the cheaper failure to read: if the printer
# emits something lfc rejects, that shows up here without the translation in the
# picture at all.
check_program \
  emit-program \
  "$BASE_PROGRAM_NAME" \
  "the hand-built program from the printer"

check_program \
  emit-widened \
  "$WIDENED_PROGRAM_NAME" \
  "the translated program from the widened Rebeca model"

# Third rather than last, by the same cost-of-reading rule: one reactor, one instance,
# no ports and no connections, so the only thing an lfc complaint here can be about is
# the construct this program exists to exercise -- two logical actions on one reactor,
# with two reactions that differ only in which one triggers them.
check_program \
  emit-repeated \
  "$REPEATED_PROGRAM_NAME" \
  "the translated program from the repeated-self-send Rebeca model"

# Fourth, by the same cost-of-reading rule and for the same shape: one reactor, one
# instance, no ports and no connections. Added by stage I0, and the only program in this
# gate whose emitted text contains a conditional. Every other one is branch-free, which is
# why a green gate said nothing about `if (…) { … } else { … }` until this line existed:
# `docs/STAGE_I_FINDINGS.md` F90 records the gap and the `grep -c 'if ('` measurement that
# established it. An lfc complaint here can only be about the conditional.
check_program \
  emit-conditional \
  "$CONDITIONAL_PROGRAM_NAME" \
  "the translated program from the conditional-witness Rebeca model"

# Fifth, the same single-actor shape once more. Added by stage I's S-I6, and the
# only program in this gate whose emitted text contains a C++ local declaration.
# Every other one is declaration-free, which is why a green gate said nothing
# about `int entry = 1;` inside a reaction body until this line existed — the
# LF-side analogue of the I0 conditional gap F90 records. The witness also reads
# the local and assigns to it, so the bare-name read and the widened assignment
# go through lfc too. An lfc complaint here can only be about the local.
check_program \
  emit-local-decl \
  "$LOCAL_DECL_PROGRAM_NAME" \
  "the translated program from the local-declaration-witness Rebeca model"

# Last, because it is the most expensive failure to read: two reactors, three
# instances and three connections, so an lfc complaint here has the most places to
# have come from. By the time it runs, the printer and the single-actor translation
# have both already been cleared.
check_program \
  emit-routed \
  "$ROUTED_PROGRAM_NAME" \
  "the translated program from the routed two-class Rebeca model"

# G5's witness cycle. The compile-and-run half reuses `check_program` unchanged, so the
# four programs above keep their exit-code-only contract; what is new starts after it:
# the assertion on the OBSERVED OUTPUT ORDER.
check_program \
  emit-priority-witness \
  "$PRIORITY_WITNESS_PROGRAM_NAME" \
  "the translated program from the priority-witness Rebeca model"

echo
echo "=== asserting the observed output order of the priority witness"

WITNESS_RUN_LOG="$WORK/$PRIORITY_WITNESS_PROGRAM_NAME/run.log"

if [ ! -f "$WITNESS_RUN_LOG" ]; then
  echo "no run log at $WITNESS_RUN_LOG; the witness binary never ran"
  exit 1
fi

# Command substitution strips the trailing newline, so both sides are compared without
# one: exactly two lines, LATE then EARLY, and nothing else.
WITNESS_OBSERVED="$(cat "$WITNESS_RUN_LOG")"
WITNESS_EXPECTED="LATE
EARLY"

echo "observed stdout:"
cat "$WITNESS_RUN_LOG"

if [ "$WITNESS_OBSERVED" != "$WITNESS_EXPECTED" ]; then
  echo
  echo "the witness ran in the wrong order."
  echo
  echo "expected stdout (priority order -- the hub's only annotated server is 'late'):"
  echo "$WITNESS_EXPECTED"
  echo
  echo "A translator that emits the right declaration order while running in the wrong"
  echo "one passes every other gate in this repository; this is the one it cannot pass."
  exit 1
fi

echo
echo "priority order beat declaration order: LATE ran before EARLY"
echo
echo "GENERAL_LF_PRIORITY_WITNESS_OK"

echo
echo "GENERAL_LF_TARGET_OK"
