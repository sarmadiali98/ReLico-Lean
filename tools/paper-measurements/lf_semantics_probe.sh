#!/bin/bash
# ============================================================================
# LF SEMANTICS PROBE -- READ-ONLY, TOUCHES NOTHING IN THE REPO.
#
# Everything in the paper's SS III-D rests on one empirical claim about real
# Lingua Franca that no one in this project has ever checked:
#
#     "reactions are ordered according to DTR actor priorities"
#
# i.e. that REACTION DECLARATION ORDER on a receiving reactor determines the
# execution order of two events that arrive at the SAME logical tag. If that is
# false, SS III-D does not work and the whole priority story needs a different
# mechanism. If it is true, SS III-D is not an arbitrary construction -- it is
# the only place LF gives us a deterministic order to attach priority to.
#
# This script settles that, plus the four syntax questions that decide the
# fan-in port shape (named ports vs multiports). It writes only under
# /tmp/relico_lf_probe and reads only $LFC.
#
# Run:  bash /Users/ali/Desktop/ReLico-Lean/tmp/lf_semantics_probe.sh 2>&1 | tee /tmp/relico_lf_probe.log
# ============================================================================
set -u

LFC=/Users/ali/.local/share/lingua-franca/cli/bin/lfc
ROOT=/tmp/relico_lf_probe

rm -rf "$ROOT"; mkdir -p "$ROOT"

printf '========== lfc identity ==========\n'
if [ ! -x "$LFC" ]; then
  printf '  FATAL  no executable lfc at %s\n' "$LFC"; exit 1
fi
"$LFC" --version 2>&1 | sed 's/^/  /'
printf '  (harness pins exactly "lfc 0.11.0" -- relico_bench_stage.py:473)\n'

# probe <name> <expectation>   ... LF source on stdin
# Mirrors the harness exactly: file staged as src/V0Controller.lf, compiled with
# `lfc src/V0Controller.lf` from the work dir, binary at bin/V0Controller, run
# with --timeout 5 msec --fast  (relico_bench_stage.py:457, :462, :494).
probe() {
  NAME=$1; EXPECT=$2
  W=$ROOT/$NAME
  mkdir -p "$W/src"
  cat > "$W/src/V0Controller.lf"

  printf '\n========== %s ==========\n' "$NAME"
  printf '  expectation: %s\n' "$EXPECT"

  ( cd "$W" && "$LFC" src/V0Controller.lf ) > "$W/lfc.log" 2>&1
  CRC=$?
  printf '  lfc exit: %s\n' "$CRC"
  if [ "$CRC" != 0 ]; then
    printf '  --- lfc diagnostics (last 15 lines) ---\n'
    tail -15 "$W/lfc.log" | sed 's/^/    /'
    printf '  RESULT: DID NOT COMPILE\n'
    return
  fi

  if [ ! -x "$W/bin/V0Controller" ]; then
    printf '  RESULT: compiled but no executable at bin/V0Controller\n'; return
  fi

  ( cd "$W" && ./bin/V0Controller --timeout "5 msec" --fast ) > "$W/run.log" 2>&1
  RRC=$?
  printf '  run exit: %s\n' "$RRC"
  printf '  --- observed RELICO_ output, IN ORDER ---\n'
  if grep -q 'RELICO_' "$W/run.log"; then
    grep 'RELICO_' "$W/run.log" | sed 's/^/    /'
  else
    printf '    (none -- full output follows)\n'
    tail -20 "$W/run.log" | sed 's/^/    /'
  fi
}

# ---------------------------------------------------------------------------
# 1 + 2. THE LOAD-BEARING PAIR.
# Identical models, identical connections, identical bodies. The ONLY
# difference is the order the two reactions are DECLARED in the receiver.
# Both messages arrive at the same tag (both senders fire at startup, both
# connections carry `after 0 msec`, so both land at the same logical time).
# If probe 1 prints A,B and probe 2 prints B,A then declaration order is
# semantically meaningful and SS III-D is implementable. If both print the
# same order, it is not, and the design must change.
# ---------------------------------------------------------------------------
probe order_decl_AB 'prints RELICO_A then RELICO_B' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor SenderB {
    output out: int
    reaction(startup) -> out {=
        out.set(2);
    =}
}

reactor Receiver {
    input inA: int
    input inB: int

    reaction(inA) {=
        std::printf("RELICO_A\n");
        std::fflush(stdout);
    =}

    reaction(inB) {=
        std::printf("RELICO_B\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderB()
    r = new Receiver()
    a.out -> r.inA after 0 msec
    b.out -> r.inB after 0 msec
}
LF

probe order_decl_BA 'prints RELICO_B then RELICO_A -- ONLY the declaration order changed' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor SenderB {
    output out: int
    reaction(startup) -> out {=
        out.set(2);
    =}
}

reactor Receiver {
    input inA: int
    input inB: int

    reaction(inB) {=
        std::printf("RELICO_B\n");
        std::fflush(stdout);
    =}

    reaction(inA) {=
        std::printf("RELICO_A\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderB()
    r = new Receiver()
    a.out -> r.inA after 0 msec
    b.out -> r.inB after 0 msec
}
LF

# ---------------------------------------------------------------------------
# 3. Does LF really prohibit many-to-one connections?
# SS III-D's entire construction exists to work around this. Worth
# establishing from the compiler rather than taking the paper's word, and
# worth capturing the exact diagnostic so our own error text can match it.
# EXPECTED TO FAIL. A failure here is the good outcome.
# ---------------------------------------------------------------------------
probe many_to_one_rejected 'lfc REJECTS this -- failure is the PASS condition' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor SenderB {
    output out: int
    reaction(startup) -> out {=
        out.set(2);
    =}
}

reactor Receiver {
    input inShared: int
    reaction(inShared) {=
        std::printf("RELICO_SHARED\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderB()
    r = new Receiver()
    a.out -> r.inShared after 0 msec
    b.out -> r.inShared after 0 msec
}
LF

# ---------------------------------------------------------------------------
# 4. Is an UNCONNECTED input port legal?
# The named-port fan-in design needs this: reactor A declares a port for every
# sender to ANY instance of A, so instances with fewer senders leave some
# unconnected. If lfc rejects or even warns, that design gets more expensive.
# ---------------------------------------------------------------------------
probe unconnected_input_ok 'compiles; prints RELICO_A only; inB never fires' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input inA: int
    input inB: int

    reaction(inA) {=
        std::printf("RELICO_A\n");
        std::fflush(stdout);
    =}

    reaction(inB) {=
        std::printf("RELICO_B_SHOULD_NOT_APPEAR\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    r = new Receiver()
    a.out -> r.inA after 0 msec
}
LF

# ---------------------------------------------------------------------------
# 5 + 6. MULTIPORT DECLARATION SYNTAX -- which spelling does 0.11.0 take?
# Fig. 5 of the paper writes `input inPort ([intLiteral])?`, which sanctions
# multiports, but LF has used width-before-name in some versions and
# width-after-name in others. Bodies deliberately touch no multiport API so
# that only the DECLARATION is under test.
# Exactly one of these two should compile.
# ---------------------------------------------------------------------------
probe multiport_decl_width_before 'input[2] in: int -- compiles?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input[2] in: int

    reaction(in) {=
        std::printf("RELICO_MP_ANY\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderA()
    r = new Receiver()
    a.out, b.out -> r.in after 0 msec
}
LF

probe multiport_decl_width_after 'input in[2]: int -- compiles?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input in[2]: int

    reaction(in) {=
        std::printf("RELICO_MP_ANY\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderA()
    r = new Receiver()
    a.out, b.out -> r.in after 0 msec
}
LF

# ---------------------------------------------------------------------------
# 7 + 8. THE DECIDING QUESTION for the fan-in port shape.
# Can a reaction be triggered by ONE CHANNEL of a multiport? If yes, the
# multiport design gives us k reactions ordered by channel index with a single
# port declaration, and -- crucially -- the index-to-sender mapping is chosen
# per INSTANCE at connection time, so `k` stays the per-instance sender count
# and matches SS III-F's O(kb). If no, we must use named ports and `k` becomes
# the union of senders across all instances of the receiving class.
# Run both spellings since probe 5/6 decides which declaration is legal.
# ---------------------------------------------------------------------------
probe multiport_indexed_trigger_width_before 'reaction(in[0]) legal? if so prints RELICO_I0 then RELICO_I1' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input[2] in: int

    reaction(in[0]) {=
        std::printf("RELICO_I0\n");
        std::fflush(stdout);
    =}

    reaction(in[1]) {=
        std::printf("RELICO_I1\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderA()
    r = new Receiver()
    a.out, b.out -> r.in after 0 msec
}
LF

probe multiport_indexed_trigger_width_after 'reaction(in[0]) legal with width-after decl?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor SenderA {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input in[2]: int

    reaction(in[0]) {=
        std::printf("RELICO_I0\n");
        std::fflush(stdout);
    =}

    reaction(in[1]) {=
        std::printf("RELICO_I1\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new SenderA()
    b = new SenderA()
    r = new Receiver()
    a.out, b.out -> r.in after 0 msec
}
LF

# ---------------------------------------------------------------------------
# 9. Two instances of ONE class, each with its own state -- the shape S1
# needs and the shape no exporter can currently produce. Confirms LF has no
# objection to it, independent of priority.
# ---------------------------------------------------------------------------
probe two_instances_one_class 'compiles; prints RELICO_INST twice' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Worker {
  state count: int = 0
  logical action tick: void

  reaction(startup) -> tick {=
    tick.schedule(1ms);
  =}

  reaction(tick) {=
    count = count + 1;
    std::printf("RELICO_INST\n");
    std::fflush(stdout);
  =}
}

main reactor {
  w0 = new Worker()
  w1 = new Worker()
}
LF

# ---------------------------------------------------------------------------
# 10. THE CONNECTION `after` CLAUSE: TIME UNIT SPELLING, AND SELF-CONNECTIONS.
#
# Added for stage C (LF ports and connections). Two independent questions.
#
# (a) WHICH TIME SPELLING DOES A CONNECTION ACCEPT? The repo's three committed
#     port-bearing fixtures write `after 0 msec`. The paper's Fig. 1b line 22
#     and Fig. 2b lines 41-42 write `after 2ms`. The existing `renderDelay`
#     produces `1ms`, but every one of its call sites is INSIDE a `{= ... =}`
#     block, where the text is C++ and `1ms` is a std::chrono literal -- which
#     says nothing about LF's own time syntax. Running the tight and spaced
#     forms separately is what separates "unknown unit" (both fail) from
#     "whitespace required" (only the tight form fails).
#
# (b) MAY AN INSTANCE CONNECT TO ITSELF? A DTR known rebec may be bound to the
#     sending actor, so the translation can produce `a.out -> a.in`. Split in
#     two, because they are different questions: self_acyclic asks only whether
#     the topology is legal, while self_cyclic builds a real causality loop
#     (reaction(in) -> out, connected back to in) that is broken only by the
#     `after` delay. SS III-E claims exactly that: "LF connections without
#     `after` are instantaneous ... and cycles cause compiler rejection".
#     self_cyclic is therefore a direct test of a paper claim, not just of a
#     syntax question.
# ---------------------------------------------------------------------------
probe unit_msec 'compiles and prints RELICO_RECEIVED -- the committed fixture spelling' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Sender {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input in: int
    reaction(in) {=
        std::printf("RELICO_RECEIVED\n");
        std::fflush(stdout);
    =}
}

main reactor {
    sender0 = new Sender()
    receiver0 = new Receiver()
    sender0.out -> receiver0.in after 0 msec
}
LF

probe unit_ms_tight 'the paper spelling, no space -- compiles?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Sender {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input in: int
    reaction(in) {=
        std::printf("RELICO_RECEIVED\n");
        std::fflush(stdout);
    =}
}

main reactor {
    sender0 = new Sender()
    receiver0 = new Receiver()
    sender0.out -> receiver0.in after 0ms
}
LF

probe unit_ms_spaced 'the `ms` alias with a space -- isolates unit from whitespace' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Sender {
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
}

reactor Receiver {
    input in: int
    reaction(in) {=
        std::printf("RELICO_RECEIVED\n");
        std::fflush(stdout);
    =}
}

main reactor {
    sender0 = new Sender()
    receiver0 = new Receiver()
    sender0.out -> receiver0.in after 0 ms
}
LF

probe self_acyclic 'one instance connected to itself, no cycle -- legal topology?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Node {
    input in: int
    output out: int
    reaction(startup) -> out {=
        out.set(1);
    =}
    reaction(in) {=
        std::printf("RELICO_SELF_ACYCLIC\n");
        std::fflush(stdout);
    =}
}

main reactor {
    a = new Node()
    a.out -> a.in after 0 msec
}
LF

probe self_cyclic 'a real causality loop broken only by `after 0 msec` -- prints 3 lines?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Node {
    input in: int
    output out: int
    state n: int = 0
    reaction(startup) -> out {=
        out.set(1);
    =}
    reaction(in) -> out {=
        n = n + 1;
        std::printf("RELICO_SELF_CYCLIC %d\n", n);
        std::fflush(stdout);
        if (n < 3) { out.set(n + 1); }
    =}
}

main reactor {
    a = new Node()
    a.out -> a.in after 0 msec
}
LF

printf '\n\n========== HOW TO READ THIS ==========\n'
cat <<'NOTE'
  The single most important line in this log is whether
  order_decl_AB and order_decl_BA printed DIFFERENT orders.

    different  -> reaction declaration order IS observable at a shared tag.
                  SS III-D is implementable and is the right mechanism.
    same       -> declaration order is NOT observable that way. SS III-D as
                  written does not work, and the fan-in design must change.

  Second: whichever of probes 5-8 compiled decides named ports vs multiports.
  Multiports win only if an INDEXED TRIGGER (probe 7 or 8) is legal AND the
  two indexed reactions fired in index order.

  Third: many_to_one_rejected SHOULD have failed to compile. Paste its
  diagnostic -- our own fan-in error message should echo lfc's wording.

  Fourth, from section 10, measured 2026-08-19 against lfc 0.11.0: all three
  of `after 0 msec`, `after 0ms` and `after 0 ms` compile and run, so the unit
  spelling is free and the paper's `2ms` in Fig. 1b is NOT a compile error. The
  printer keeps ` msec` only to stay byte-identical with the committed
  fixtures. Both self-connection cases also compile, and self_cyclic printing
  three lines confirms SS III-E's claim that an `after` delay breaks a
  causality loop -- a paper claim measured TRUE, which is worth as much as the
  corrections.

  Nothing in the repo was read or written. Scratch tree: /tmp/relico_lf_probe
NOTE
