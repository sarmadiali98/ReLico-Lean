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
# Run:  bash tools/paper-measurements/lf_semantics_probe.sh 2>&1 | tee /tmp/relico_lf_probe.log
#
# That is the TRACKED copy. This line used to name `tmp/lf_semantics_probe.sh`,
# which is gitignored, so a fresh clone following the instruction found no file.
#
# Every probe runs by default. To re-measure one section without paying for all
# of them -- each probe is a full lfc compile AND a C++ build -- set PROBE_FILTER
# to a substring of the probe names:
#
#     PROBE_FILTER=action bash tools/paper-measurements/lf_semantics_probe.sh
#
# Skipped probes announce themselves in the log, so a filtered run cannot be
# mistaken for a full one when the log is read later.
# ============================================================================
set -u

PROBE_FILTER=${PROBE_FILTER:-}

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

  # With PROBE_FILTER unset the pattern is `**`, which matches every name, so the
  # default remains a full run and no existing invocation changes behaviour.
  case "$NAME" in
    *$PROBE_FILTER*) ;;
    *)
      printf '\n========== %s ==========\n' "$NAME"
      printf '  SKIPPED by PROBE_FILTER=%s -- this log is NOT a full run\n' "$PROBE_FILTER"
      cat > /dev/null
      return ;;
  esac

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

# ---------------------------------------------------------------------------
# 11. STAGE E PREREQUISITES, added 2026-08-20 after stage D landed at 3290ad4.
# Three questions, each of which changes what a later document may claim.
#
# 11a decides F30. Stage D's printer refuses a reaction that declares two or
# more parameters for an INPUT PORT, on the true ground that a port carries one
# value of one type. The candidate fix for stage E is to give the port the
# payload struct as its type, which makes the refusal unreachable rather than
# merely unreached. Route A measured struct payloads on ACTIONS only, and an
# action type and a port type are different positions in the grammar.
#
# 11b bears on F32. `LF.GeneralReactor.declaredNames` puts parameters into the
# same uniqueness union as state variables, and the file admits at :81 that
# whether lfc actually rejects the collision was never measured -- including
# them was the conservative side of an unmeasured question. If lfc REJECTS,
# the conservatism is a measured requirement and the DTR side owes the mirror
# clause. If lfc ACCEPTS, this repository is deliberately stricter than its
# target and must say so in those words. The reaction body deliberately does
# not mention `x`, so only the DECLARATION is under test.
#
# 11b ANSWERED, and the two sentences above are kept as the question that was
# asked rather than rewritten into the answer. lfc ACCEPTS at the validator and
# the generated C++ then fails to compile, so both branches fire at different
# layers; stage E acts on it in docs/STAGE_E_DESIGN.md section 9. The `:81`
# citation above is also stale -- that docstring was rewritten in stage E to
# carry this result, and it moved down the file when it grew.
#
# 11c pays a debt. The named-argument and parameter-default forms were measured
# ad hoc in stage D and only prose recorded it; a fresh clone could not re-run
# it. Cross-reactor print order has no guarantee in the Cpp target, so the
# expectation is stated as a SET of lines, not a sequence.
# ---------------------------------------------------------------------------

probe struct_as_port_type 'a preamble struct as a PORT type -- compiles and prints RELICO_STRUCT_PORT 9 1?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
struct Receiver_m_Args { int left; int right; bool flag; };
=}

reactor Sender {
    output out: Receiver_m_Args
    reaction(startup) -> out {=
        out.set(Receiver_m_Args{7, 2, true});
    =}
}

reactor Receiver {
    input in: Receiver_m_Args
    reaction(in) {=
        auto p = *in.get();
        std::printf("RELICO_STRUCT_PORT %d %d\n", p.left + p.right, p.flag ? 1 : 0);
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Sender()
    r = new Receiver()
    s.out -> r.in after 0 msec
}
LF

probe param_state_name_collision 'parameter and state variable SHARING a name -- does lfc reject it? either answer is informative' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor R(x: int = 3) {
    state x: int = 0
    reaction(startup) {=
        std::printf("RELICO_COLLIDE\n");
        std::fflush(stdout);
    =}
}

main reactor {
    r = new R(x=7)
}
LF

probe parameter_defaults_named_args 'reactor parameters with defaults and per-instance named arguments -- both RELICO_PARAM 0 0 and RELICO_PARAM 7 1, in either order?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Configured(bound: int = 0, active: bool = false) {
    state limit: int = 0
    reaction(startup) {=
        limit = bound;
        std::printf("RELICO_PARAM %d %d\n", limit, active ? 1 : 0);
        std::fflush(stdout);
    =}
}

main reactor {
    off = new Configured()
    on = new Configured(bound=7, active=true)
}
LF

# ============================================================================
# Section 12 -- two schedules of one action at one tag (task #39).
#
# This section measures the design alternative stage E REJECTED, which is the
# only reason it is worth running. STAGE_E_DESIGN.md SS6 keys an output port on
# the SEND SITE rather than on the (message, target) pair, and the stated
# reason is that one Rebeca message server may send the same message twice to
# the same target at the same tag. If a logical action can carry both of those
# sends, the per-send-site key is a convenience. If it cannot, the key is
# FORCED, and that is a much stronger claim -- one the paper should make in
# those words rather than presenting per-send-site ports as a preference.
#
# No probe in this file has ever used `action` or `schedule`, so the API itself
# is unmeasured here. That is why there are two probes and not one: the second
# is a CONTROL that schedules at two DISTINCT tags. Without it a single output
# line is ambiguous between "the two schedules collided" and "the schedule call
# was written wrong", and reading the first as the second would be a false
# negative in the direction of believing a collision.
#
#   experiment prints ONE line  + control prints TWO  -> collision is real, the
#                                                        send-site key is forced
#   experiment prints TWO lines + control prints TWO  -> one action carries both
#                                                        sends; SS6 needs revisiting
#   BOTH fail to compile                              -> the API call is wrong and
#                                                        neither probe means anything
# ============================================================================

probe action_two_schedules_same_tag 'ONE line or TWO? schedules 1 then 2 at the SAME tag -- read only together with the control below' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slot: int
    reaction(startup) -> slot {=
        slot.schedule(1, 0ms);
        slot.schedule(2, 0ms);
        std::printf("RELICO_SCHEDULED_TWICE\n");
        std::fflush(stdout);
    =}
    reaction(slot) {=
        std::printf("RELICO_ACTION %d\n", *slot.get());
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

probe action_two_schedules_distinct_tags 'CONTROL -- same code, delays 0ms and 1ms, so two DISTINCT tags. Expect RELICO_ACTION 1 then RELICO_ACTION 2' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slot: int
    reaction(startup) -> slot {=
        slot.schedule(1, 0ms);
        slot.schedule(2, 1ms);
        std::printf("RELICO_SCHEDULED_TWICE\n");
        std::fflush(stdout);
    =}
    reaction(slot) {=
        std::printf("RELICO_ACTION %d\n", *slot.get());
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

# ============================================================================
# Section 13 -- can `policy: defer` recover the dropped send? (task #39, part 2)
#
# Section 12 established that two schedules at one tag keep only the last value.
# STAGE_E_DESIGN.md SS11.2 item 7 asked for this second probe in the same breath,
# and it is the one with a repair attached: LF actions take (min_delay,
# min_spacing, policy), and `defer` is documented to push a schedule that would
# violate min_spacing to the next permitted tag instead of discarding it.
#
# The rule stated before the run, kept because the prediction is evidence: if defer
# fires the reaction TWICE, a faithful encoding of Rebeca's queue exists and the
# repair to stage D's self-send path is a declaration change; if it fires ONCE, the
# loss is not a policy choice and the repair has to be structural -- distinct
# actions per send site, mirroring what SS6.2 already does for ports.
#
# MEASURED 2026-08-22, lfc 0.11.0: neither. The declaration is REJECTED, because
# reactor-cpp implements no spacing policy for logical actions at all, so there was
# a third branch the rule did not enumerate and it is the structural one -- see the
# "Seventh" paragraph in HOW TO READ THIS for the diagnostic and what follows.
#
# min_spacing is 1ms against a 5 msec timeout, so a deferred second event has room
# to arrive well inside the run.
# ============================================================================

probe action_defer_policy_same_tag 'TWICE, ONCE, or REJECTED? two schedules at one tag with min_spacing 1ms and policy defer -- only TWICE means a declaration-level repair exists' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slot(0ms, 1ms, "defer"): int
    reaction(startup) -> slot {=
        slot.schedule(1, 0ms);
        slot.schedule(2, 0ms);
        std::printf("RELICO_SCHEDULED_TWICE\n");
        std::fflush(stdout);
    =}
    reaction(slot) {=
        std::printf("RELICO_ACTION %d\n", *slot.get());
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

# ============================================================================
# SECTION 14 (2026-08-23) -- WHICH SHAPE the forced repair takes
#
# Section 12 measured that one action cannot carry two sends at one tag, and
# section 13 that no declaration-level policy repairs it in this target. So the
# repair is structural: one action per send SITE, mirroring what SS6.2 does for
# ports. That leaves one open question, and it decides the shape of the generated
# reactor. With k actions all feeding ONE message server, does that server get one
# reaction with k triggers, or k reactions?
#
# 14a asks whether a multi-trigger reaction fires ONCE or TWICE when both of its
# triggers are present at one tag. Its body prints a fixed marker and reads no
# payload at all, deliberately: counting markers answers the question with no
# dependence on an is_present() API this harness has never exercised, so the probe
# cannot fail for a reason unrelated to what it asks.
#
# If 14a fires ONCE, shape (A) is lossy for section 12's reason and the only rescue
# is branching over presence inside the body -- which is the multiport fallback this
# project already rejected, because it moves the ordering guarantee into generated
# C++ statement order, where the Lean development cannot see it.
#
# 14b is the shape the repair uses if (A) falls: k actions, k reactions. Two
# reactions in one reactor firing at one tag in declaration order is already
# measured (section 1); what is NOT measured is whether that holds when the
# triggers are ACTIONS rather than ports. This probe checks that, and is not a
# re-measurement of the ordering result.
# ============================================================================

probe action_two_actions_one_reaction 'ONCE or TWICE? two actions scheduled at one tag, ONE reaction triggered by both -- count the RELICO_MULTI_FIRED lines' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slotA: int
    logical action slotB: int
    reaction(startup) -> slotA, slotB {=
        slotA.schedule(1, 0ms);
        slotB.schedule(2, 0ms);
    =}
    reaction(slotA, slotB) {=
        std::printf("RELICO_MULTI_FIRED\n");
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

probe action_two_actions_two_reactions 'TWO lines, A then B? two actions at one tag with ONE REACTION EACH -- the shape the repair takes if the probe above fires once' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slotA: int
    logical action slotB: int
    reaction(startup) -> slotA, slotB {=
        slotA.schedule(1, 0ms);
        slotB.schedule(2, 0ms);
    =}
    reaction(slotA) {=
        std::printf("RELICO_TWO A %d\n", *slotA.get());
        std::fflush(stdout);
    =}
    reaction(slotB) {=
        std::printf("RELICO_TWO B %d\n", *slotB.get());
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

# ---------------------------------------------------------------------------
# SECTION 15 (2026-08-23) -- WHICH ORDER decides at one tag, DECLARATION or
# SCHEDULE, in the two trigger shapes a generated receiver actually produces.
# Six probes, three pairs, one filter: PROBE_FILTER=stageF
#
# Every pair differs ONLY in the order two reactions are DECLARED.  Everything
# else -- schedules, set() calls, connections, payloads, bodies -- is byte
# identical between the members of a pair.  A pair must be read together; a
# single member proves nothing.
#
# Why these are needed even though order_decl_AB/BA already measured that
# declaration order is observable: generated receivers produce two trigger
# shapes that order_decl_* does not, and the action pair below isolates a
# variable that `action_two_actions_two_reactions` (above) leaves confounded.
#
# MEASURED 2026-08-23 against lfc 0.11.0, all six compiled and ran clean:
#
#   stageF_action_declsame_AB     RELICO_DECL A 1 ; RELICO_DECL B 2
#   stageF_action_declswap_BA     RELICO_DECL B 2 ; RELICO_DECL A 1
#   stageF_onesender_twoports_AB  RELICO_PORT A 1 ; RELICO_PORT B 2
#   stageF_onesender_twoports_BA  RELICO_PORT B 2 ; RELICO_PORT A 1
#   stageF_action_port_mixed_AB   RELICO_MIX ACT 1 ; RELICO_MIX PORT 2
#   stageF_action_port_mixed_BA   RELICO_MIX PORT 2 ; RELICO_MIX ACT 1
#
# DECLARATION ORDER DECIDES, in all three shapes.  Every pair swapped, so no
# member's result is explicable by anything the pair holds fixed.  Cite THIS
# section, not 14b, for the action-triggered ordering claim -- see F58.
#
# Pair 3 also proves a fact no pair was designed to test: `act.schedule(1, 0ms)`
# and a connection's `after 0 msec` deliver at the SAME microstep.  Had they
# differed, complete-tag order would have fixed the outcome and swapping the
# declarations could not have moved it.  It moved.
# ---------------------------------------------------------------------------

# --- PAIR 1.  THE LOAD-BEARING ONE: declaration order vs SCHEDULE order.
# `action_two_actions_two_reactions` schedules slotA first AND declares it
# first, so its observed "A then B" is consistent with either cause.  Stage F
# is the first place the two diverge: a priority sort reorders reaction
# DECLARATIONS while the schedule() calls stay in the sender body's order.
# Here the schedules are A-then-B in BOTH members and only the declarations
# move.  BA printing "B A" means declaration order decides and Lemma 2's
# same-actor case is implementable for self-sends.  BA printing "A B" means
# schedule order decides and stage F's design must change.
# The payload identifies the action independently of the label: slotA always
# carries 1, slotB always carries 2.

probe stageF_action_declsame_AB 'CONTROL -- schedules A,B and declarations A,B: expect RELICO_DECL A 1 then RELICO_DECL B 2' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slotA: int
    logical action slotB: int
    reaction(startup) -> slotA, slotB {=
        slotA.schedule(1, 0ms);
        slotB.schedule(2, 0ms);
    =}
    reaction(slotA) {=
        std::printf("RELICO_DECL A %d\n", *slotA.get());
        std::fflush(stdout);
    =}
    reaction(slotB) {=
        std::printf("RELICO_DECL B %d\n", *slotB.get());
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

probe stageF_action_declswap_BA 'schedules STILL A,B but declarations B,A: "B 2" then "A 1" means DECLARATION order wins; "A 1" then "B 2" means SCHEDULE order wins' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Queue {
    logical action slotA: int
    logical action slotB: int
    reaction(startup) -> slotA, slotB {=
        slotA.schedule(1, 0ms);
        slotB.schedule(2, 0ms);
    =}
    reaction(slotB) {=
        std::printf("RELICO_DECL B %d\n", *slotB.get());
        std::fflush(stdout);
    =}
    reaction(slotA) {=
        std::printf("RELICO_DECL A %d\n", *slotA.get());
        std::fflush(stdout);
    =}
}

main reactor {
    q = new Queue()
}
LF

# --- PAIR 2.  ONE sender, TWO output ports, one tag.
# order_decl_AB/BA use TWO senders, so their two edges enter the receiver from
# two different upstream reactions.  The routed model the tool actually emits
# has ONE sender writing two ports in ONE reaction body (Probe sets
# reportToHub1 and reportToHub2 in a single reaction), which is a different
# precedence-graph shape.  Both connections carry `after 0 msec`, so both
# inputs are present at the same tag.  Payloads identify the port: inA=1, inB=2.

probe stageF_onesender_twoports_AB 'one sender, two ports, declarations A,B: expect RELICO_PORT A 1 then RELICO_PORT B 2' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink {
    input inA: int
    input inB: int
    reaction(inA) {=
        std::printf("RELICO_PORT A %d\n", *inA.get());
        std::fflush(stdout);
    =}
    reaction(inB) {=
        std::printf("RELICO_PORT B %d\n", *inB.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k = new Sink()
    s.outA -> k.inA after 0 msec
    s.outB -> k.inB after 0 msec
}
LF

probe stageF_onesender_twoports_BA 'identical model, ONLY the two Sink reactions swapped: expect RELICO_PORT B 2 then RELICO_PORT A 1' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink {
    input inA: int
    input inB: int
    reaction(inB) {=
        std::printf("RELICO_PORT B %d\n", *inB.get());
        std::fflush(stdout);
    =}
    reaction(inA) {=
        std::printf("RELICO_PORT A %d\n", *inA.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k = new Sink()
    s.outA -> k.inA after 0 msec
    s.outB -> k.inB after 0 msec
}
LF

# --- PAIR 3.  An ACTION-triggered and a PORT-triggered reaction at one tag.
# A generated receiver's reaction list interleaves both kinds: Gateway emits
# reaction(report_action), then one reaction per incoming send site, then the
# next message server's block.  A priority sort reorders whole blocks, so it
# reorders across the action/port boundary -- and no probe has ever put an
# action and a port at the same tag in one reactor.
# act.schedule(1, 0ms) from a reaction at (0,0) lands at (0,1); the connection's
# `after 0 msec` also lands at (0,1).  The startup reaction stays FIRST in both
# members so that only the two reactions under test move.

probe stageF_action_port_mixed_AB 'action and port at ONE tag, declarations ACT,PORT: expect RELICO_MIX ACT 1 then RELICO_MIX PORT 2' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output out: int
    reaction(startup) -> out {=
        out.set(2);
    =}
}

reactor Mix {
    input inp: int
    logical action act: int
    reaction(startup) -> act {=
        act.schedule(1, 0ms);
    =}
    reaction(act) {=
        std::printf("RELICO_MIX ACT %d\n", *act.get());
        std::fflush(stdout);
    =}
    reaction(inp) {=
        std::printf("RELICO_MIX PORT %d\n", *inp.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    m = new Mix()
    s.out -> m.inp after 0 msec
}
LF

probe stageF_action_port_mixed_BA 'identical model, ONLY act and inp reactions swapped: expect RELICO_MIX PORT 2 then RELICO_MIX ACT 1' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output out: int
    reaction(startup) -> out {=
        out.set(2);
    =}
}

reactor Mix {
    input inp: int
    logical action act: int
    reaction(startup) -> act {=
        act.schedule(1, 0ms);
    =}
    reaction(inp) {=
        std::printf("RELICO_MIX PORT %d\n", *inp.get());
        std::fflush(stdout);
    =}
    reaction(act) {=
        std::printf("RELICO_MIX ACT %d\n", *act.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    m = new Mix()
    s.out -> m.inp after 0 msec
}
LF

# ---------------------------------------------------------------------------
# SECTION 16 (2026-08-25) -- IS THERE ANY CROSS-REACTOR ORDER AT ONE TAG?
# Seven probes, one filter: PROBE_FILTER=stageG
#
# This section exists because of F76 (docs/STAGE_G_FINDINGS.md). At run level the
# source selector `DTR.GeneralActorSelection.selectedActor` keys on (arrival,
# PRIORITY) while the target selector `LF.GeneralRuntimeState.earliestPendingEvent?`
# keys on (tag.time, tag.microstep) and is priority-BLIND. So for two events at one
# tag targeting DIFFERENT actors the two sides can select differently, and the
# `.consume` case of Definition 1's transfer conditions is false as specified.
#
# Every ordering result this file already holds is WITHIN one reactor. Section 1
# and section 15 measured reaction DECLARATION order, in three trigger shapes, and
# all six section-15 probes swapped -- but a declaration list belongs to a reactor
# CLASS, and F76's divergence is between two INSTANCES. Nothing here has ever put
# two reactions in two DIFFERENT reactors at one tag and asked which runs first.
#
# The load-bearing question is therefore not "does a priority attribute exist" but:
#
#     DOES ANY MECHANISM ORDER REACTIONS ACROSS REACTORS AT ONE TAG?
#
# and it has three possible answers, each of which forces a different repair:
#
#   ORDERED BY SOMETHING THE PRINTER CONTROLS (instantiation order, an attribute,
#     a dependency edge) -> the target CAN implement actor priority, and F76's
#     repair is to teach the printer to emit in priority order. The theorem is
#     then provable without a guard, and no fragment need be refused.
#   ORDERED, BUT ONLY BY SENDER STATEMENT ORDER -> the order is real yet lives in
#     generated C++ where the Lean development cannot see it. That is the multiport
#     fallback this project already rejected twice (sections 12 and 14a); it would
#     be rejected a third time for the same reason.
#   NOT ORDERED AT ALL -> `earliestPendingEvent?`'s total order OVER-SPECIFIES real
#     LF, our target model is stricter than its target, and by the standing
#     doctrine the answer is to REFUSE such models rather than narrow the theorem.
#
# The third answer is the one no pair of probes can establish, because a pair only
# shows that an order MOVED. Absence of order is a claim about repeated runs, which
# is why this section adds a second runner instead of reusing `probe`.
#
# ---------------------------------------------------------------------------
# MEASURED VERDICT, 2026-08-25, lfc 0.11.0 -- READ THIS BEFORE CITING SECTION 16
# ---------------------------------------------------------------------------
# The trichotomy above is WRONG, and its first branch is the dangerous one. It
# treats "the printer controls it" as sufficient for "the target CAN implement
# actor priority". It is not sufficient, because the printer controlling an order
# says nothing about whether LF ASSIGNS that order any meaning.
#
# What the nine probes measured:
#
#   * an order exists and is stable -- 16d, seven runs, --workers 1 and 4 agreeing
#   * sender statement order does NOT produce it (16b unmoved)
#   * instance declaration order DOES influence it (16c moved), but by no rule two
#     instances revealed: at three instances the order is sink3, sink1, sink2, so
#     reverse instantiation is refuted (16h)
#   * `@priority` does not exist -- "Unknown attribute: priority", and the `@label`
#     control (16e) compiled, so this is a MEASURED ABSENCE not a syntax accident
#   * a zero-delay `uses` edge overrides the default and forces the order (16i)
#
# And the limitation that governs all of it: every probe here observes order
# through `std::printf`, an UNMODELLED side effect. LF's determinism guarantee
# fixes port values and reactor state, not the interleaving of raw C++ statements.
# Two independent reactors reacting at one tag hand identical values downstream
# whichever body ran first. So 16a-16h measured this RUNTIME being incidentally
# stable on a channel the LANGUAGE leaves free, and cannot license a theorem.
#
# 16i is the one probe that escapes this, and escapes it by construction rather
# than by luck. A zero-delay connection into a `uses` clause creates a genuine LF
# DEPENDENCY, and dependencies are precisely what LF's semantics DO order. Its
# result is a language-level guarantee; every other result in this section is an
# implementation observation.
#
# So the branch that actually fired is the THIRD one, and F76's over-specification
# paragraph is CONFIRMED, not refuted: `earliestPendingEvent?`'s total order is
# stronger than LF supports. The surviving repairs are therefore (i) inject
# dependency edges to MAKE the order real, per 16i, at the cost of ports and
# connections the source model does not have and of serialising reactors the source
# leaves concurrent; or (ii) stop claiming an order the target does not have, i.e.
# state the correspondence up to within-tag permutation. Instantiation order (16c,
# 16h) and a refused fragment are weaker fallbacks. That decision is the user's.
#
# Read 16a/16b as a pair and 16a/16c as a pair; 16a is the shared control for both.
# In 16a every candidate order agrees on sink1-before-sink2 (it is declared first,
# instantiated first, and sent to first), which is exactly why 16a alone proves
# nothing and each partner moves exactly one of those three.
# ---------------------------------------------------------------------------

# probe_repeat <name> <expectation>   ... LF source on stdin
# Stages and compiles exactly as `probe` does, then runs the binary FIVE times at
# the default worker count and once each at --workers 1 and --workers 4. A single
# run cannot distinguish "the order is fixed" from "the order came out this way
# once", and every earlier question in this file was about what compiles or about
# an order a PAIR isolates, so no runner here needed repetition before now.
# An unrecognised --workers flag must be VISIBLE rather than fatal: the exit code
# is printed per run and a non-zero one does not stop the loop, so a flag that does
# not exist cannot be misread as an absence of output.
probe_repeat() {
  NAME=$1; EXPECT=$2

  case "$NAME" in
    *$PROBE_FILTER*) ;;
    *)
      printf '\n========== %s ==========\n' "$NAME"
      printf '  SKIPPED by PROBE_FILTER=%s -- this log is NOT a full run\n' "$PROBE_FILTER"
      cat > /dev/null
      return ;;
  esac

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

  for ATTEMPT in 1 2 3 4 5; do
    ( cd "$W" && ./bin/V0Controller --timeout "5 msec" --fast ) > "$W/run.$ATTEMPT.log" 2>&1
    RRC=$?
    printf '  default-workers run %s (exit %s): %s\n' "$ATTEMPT" "$RRC" \
      "$(grep 'RELICO_' "$W/run.$ATTEMPT.log" | tr '\n' ' ')"
  done

  for WK in 1 4; do
    ( cd "$W" && ./bin/V0Controller --timeout "5 msec" --fast --workers "$WK" ) > "$W/run.w$WK.log" 2>&1
    RRC=$?
    printf '  --workers %s (exit %s): %s\n' "$WK" "$RRC" \
      "$(grep 'RELICO_' "$W/run.w$WK.log" | tr '\n' ' ')"
    if [ "$RRC" != 0 ]; then
      printf '    --- last 6 lines, in case the flag is unrecognised ---\n'
      tail -6 "$W/run.w$WK.log" | sed 's/^/      /'
    fi
  done
}

# --- 16a. THE SHARED CONTROL. One sender writes two ports in ONE reaction body,
# both connections carry `after 0 msec`, and the two receivers are two INSTANCES
# OF ONE CLASS -- so the class's reaction declaration order, the only ordering
# mechanism this file has ever measured, is held constant and cannot explain
# anything observed here. This is F76's counterexample shape: one body, two sends,
# two different target actors, one tag.
# In this member sink1 is declared first, instantiated first, and sent to first,
# so all three of those candidate orders predict "sink1 payload1" then "sink2
# payload2". That agreement is why 16a alone proves nothing, and why 16b and 16c
# each move exactly one of the three.
#
# MEASURED 2026-08-25, lfc 0.11.0: the control prints sink2 FIRST. None of the
# three candidate orders enumerated above predicts that, so the enumeration was
# INCOMPLETE -- the missing candidate is REVERSE instantiation order, which 16c
# then confirmed by swapping. This comment originally concluded "so EVERY candidate
# order predicts sink1 first"; that inference was wrong and is corrected here
# rather than deleted, because missing a candidate while believing the list was
# exhaustive is the same error F75 and F76 record one level up.

probe stageG_xr_control 'CONTROL -- expect RELICO_XR sink1 payload1 then RELICO_XR sink2 payload2; every candidate order agrees here' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    reaction(in) {=
        std::printf("RELICO_XR sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
}
LF

# --- 16b. ONLY the two set() statements in the sender body are swapped. Nothing
# else moves: same classes, same instantiation order, same connection order.
# If the output swaps, cross-reactor order is decided by generated C++ STATEMENT
# order. That would make the order real but invisible to the Lean development,
# which is the multiport fallback rejected in sections 12 and 14a for the same
# reason -- and it would also mean the order is NOT a function of the LF text the
# printer is proved to emit.
# If the output does NOT swap, send order is ruled out, which is the answer that
# lets 16c be read cleanly.

probe stageG_xr_sendorder_swap 'ONLY the sender body statements swapped -- does RELICO_XR sink2 now print FIRST?' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outB.set(2);
        outA.set(1);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    reaction(in) {=
        std::printf("RELICO_XR sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
}
LF

# --- 16c. ONLY the two instantiation lines are swapped. The sender body stays
# outA-then-outB and the two connection lines stay in their original textual
# order, so the single moved thing is the order the two Sink instances are
# DECLARED in the main reactor.
# This is the probe with a cheap repair attached. If the output swaps,
# instantiation order orders reactions across reactors, the printer already
# controls that order, and F76's repair is to emit instances in actor-priority
# order -- no guard, no refused fragment, and the `.consume` case becomes
# provable. If it does not swap, that repair does not exist.

probe stageG_xr_instorder_swap 'ONLY the two new Sink lines swapped -- does RELICO_XR sink2 now print FIRST? a swap means the printer can implement actor priority' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    reaction(in) {=
        std::printf("RELICO_XR sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k2 = new Sink(id=2)
    k1 = new Sink(id=1)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
}
LF

# --- 16d. DOES AN ORDER EXIST AT ALL? Byte-identical to 16a, run seven times
# instead of once: five at the default worker count, then once each at --workers 1
# and --workers 4. No pair of probes can establish the ABSENCE of an order, because
# a pair only shows that an order moved; this is the only probe in the file whose
# result is a property of repeated runs.
# If the marker order varies between any two of the seven lines, real LF leaves
# same-tag reactions in independent reactors UNORDERED, our `earliestPendingEvent?`
# total order over-specifies the target, and by the standing doctrine the answer to
# F76 is to REFUSE such models rather than narrow the theorem.
# If all seven agree, an order exists and 16b/16c/16f/16g are about which mechanism
# produces it. Note that agreement at --workers 1 with disagreement at --workers 4
# is the most informative outcome of all: it would mean the order is an artefact of
# the scheduler's thread count and not a language guarantee, which no amount of
# printer discipline can fix.

probe_repeat stageG_xr_determinism 'byte-identical to 16a -- do all SEVEN runs print the same order? any disagreement means real LF does not order these at all' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    reaction(in) {=
        std::printf("RELICO_XR sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
}
LF

# --- 16e. ATTRIBUTE CONTROL. Nothing in this repository has ever emitted or probed
# an LF attribute -- there is no `@` in any committed fixture and no printer site
# produces one -- so "does a priority attribute exist" is not yet a well-posed
# question. This probe asks the prior one: is ANY attribute accepted in front of a
# reaction declaration? `@label` is used because it is documented for diagram
# rendering and so should be semantically inert, which is what makes it a control.
# Without this, a rejection in 16f cannot be read: it would be ambiguous between
# "no priority attribute" and "no attributes in this position at all".

probe stageG_attr_label_control 'CONTROL -- is ANY attribute accepted before a reaction? @label should compile and change nothing' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    @label("relico probe")
    reaction(in) {=
        std::printf("RELICO_XR sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
}
LF

# --- 16f. THE ATTRIBUTE ITSELF, on TWO DIFFERENT CLASSES. Two classes rather than
# two instances, deliberately: an attribute sits on a reaction, a reaction belongs
# to a CLASS, and so no attribute can ever distinguish two instances of one class.
# That is a structural limit worth stating whatever this probe returns -- it means
# even a working priority attribute could not order two instances of one Rebeca
# reactive class, which `phils` is made of.
# SinkA is declared first and instantiated first but annotated with the LARGER
# number, so the attribute and the default order disagree. Which polarity counts as
# "better" is unknown, so the reading is not "does sinkB come first" but "does the
# order DIFFER from 16a's":
#   does not compile   -> no such attribute; combined with 16e passing, that is a
#                         measured absence rather than a syntax accident
#   compiles, same order as 16a -> accepted but INERT, which is worse than a
#                         rejection: a printer could emit it and prove nothing
#   compiles, order differs     -> a real cross-reactor mechanism exists

probe stageG_attr_priority 'does @priority exist? SinkA is declared first but annotated 2 vs SinkB 1 -- read as "does the order DIFFER from 16a", not as a polarity' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor SinkA {
    input in: int
    @priority(2)
    reaction(in) {=
        std::printf("RELICO_PRIO sinkA payload%d\n", *in.get());
        std::fflush(stdout);
    =}
}

reactor SinkB {
    input in: int
    @priority(1)
    reaction(in) {=
        std::printf("RELICO_PRIO sinkB payload%d\n", *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    a = new SinkA()
    b = new SinkB()
    s.outA -> a.in after 0 msec
    s.outB -> b.in after 0 msec
}
LF

# --- 16g. THE ONE MECHANISM THAT CERTAINLY ORDERS ACROSS REACTORS, and the
# question is what it costs. A zero-delay connection into a reaction's USES clause
# makes that reaction depend on the upstream one without making it a trigger, so
# the dependency graph must order them at a shared tag.
# The chain is deliberately REVERSED -- k2.done feeds k1.gate -- so the expected
# order is sink2 BEFORE sink1, which is the opposite of what declaration order,
# instantiation order and send order all predict. One probe therefore suffices:
# nothing except the uses edge can explain sink2 printing first.
#
# MEASURED 2026-08-25: it compiled and printed sink2 before sink1 -- and the probe
# is therefore CONFOUNDED and proves nothing. The sentence above rests on 16a's
# default being sink1-first, which 16a refuted in the same run: sink2-first IS the
# default, so this result is equally consistent with the uses edge deciding
# everything and with it deciding nothing. DO NOT CITE THIS PROBE. 16i is the
# un-confounded version, chaining FORWARD so that the expected order opposes the
# measured default instead of agreeing with it.
# If this compiles and reverses the order, F76 gains a SIXTH repair candidate that
# is expressible in real LF: realise actor priority as a causal chain among the
# receivers. It is not free -- it injects ports and connections the source model
# does not have, and it serialises reactors the source leaves concurrent -- so it
# is a candidate to put to the user, not a decision to take here.
# If it does NOT compile, the `reaction(trigger) uses -> effect` spelling is what
# failed, not the mechanism; the follow-up is the heavier pipeline shape, where k1
# forwards the payload to k2 as a real trigger.

probe stageG_uses_reverse_chain 'a REVERSED zero-delay uses edge -- expect RELICO_USES sink2 BEFORE sink1, which no default order predicts' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    input gate: int
    output done: int
    reaction(in) gate -> done {=
        std::printf("RELICO_USES sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
        done.set(1);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
    k2.done -> k1.gate
}
LF

# ---------------------------------------------------------------------------
# 16h + 16i (2026-08-25, added AFTER the first seven ran) -- two follow-ups the
# first run made necessary. Filter: PROBE_FILTER=stageG2
#
# 16a/16b/16c measured that cross-reactor same-tag order IS decided, deterministically
# and stably across worker counts, by INSTANTIATION order -- in REVERSE: the
# last-declared instance fired first, in both members of the 16a/16c pair. That is
# the answer F76 needed, and it means the printer controls the order. But it was
# measured at n = 2, where "reverse" is indistinguishable from any other
# non-identity permutation, and a printer repair would rely on the rule holding
# generally. 16h is the cheapest thing that separates them.
#
# 16i repairs 16g, which came out confounded: 16g chained k2 -> k1 expecting
# sink2-first as the tell, and sink2-first turned out to be the DEFAULT.
# ---------------------------------------------------------------------------

# --- 16h. THREE instances, declared k1, k2, k3, all sent to at one tag.
# If the rule is reverse instantiation order the output is sink3, sink2, sink1.
# Any other permutation means the n = 2 result was not the rule it looked like, and
# the printer cannot implement actor priority by ordering its instance declarations
# -- which would move F76's repair back to a refused fragment.
# Worth stating plainly: even a confirmed rule here is a reactor-cpp 0.11.0
# property, not a documented LF guarantee. LF specifies reactions in INDEPENDENT
# reactors at one tag as logically concurrent, i.e. unordered. So a theorem resting
# on this would be true of this runtime rather than of the language, and that is a
# fidelity cost to record however 16h comes out.
#
# MEASURED 2026-08-25, lfc 0.11.0: sink3, sink1, sink2. NOT sink3, sink2, sink1.
# So REVERSE instantiation order is REFUTED, and with it the correction written on
# 16a above, which named reverse order as the missing candidate the n = 2 result
# implied. Both are left standing rather than deleted: the n = 2 datum is genuinely
# consistent with reversal, and the point of this comment is that being consistent
# with a rule is not evidence FOR it when the alternatives were never enumerated.
# The function that fits BOTH data points is "the LAST-declared instance fires
# first, then the remaining instances in declaration order", which at n = 2 is
# indistinguishable from reversal. That is a two-point fit to an undocumented
# scheduler and n >= 4 is unmeasured, so it is recorded as a shape, NOT as a rule.
#
# The caveat four lines above is the load-bearing part of this probe, and it grew
# TEETH once all nine probes were read together. Every probe in this section
# observes order through `std::printf`, which is an UNMODELLED side effect: LF's
# determinism guarantee fixes port values and reactor state, not the execution
# interleaving of raw C++ statements. Had the sinks written to output ports instead
# of stdout, a downstream reactor would read identical values at that tag whichever
# body ran first. So this section did not measure "the order LF gives"; it measured
# reactor-cpp 0.11.0 being incidentally stable on a channel LF leaves free. 16c and
# 16h therefore CANNOT license a printer that orders by instantiation, and F76's
# over-specification paragraph is CONFIRMED rather than refuted. 16i is the sole
# exception, and deliberately so -- see its own comment.

probe stageG2_xr_three_instances 'THREE instances declared k1,k2,k3 -- reverse instantiation order predicts sink3, sink2, sink1; any other permutation refutes the rule' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    output outC: int
    reaction(startup) -> outA, outB, outC {=
        outA.set(1);
        outB.set(2);
        outC.set(3);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    reaction(in) {=
        std::printf("RELICO_XR3 sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    k3 = new Sink(id=3)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
    s.outC -> k3.in after 0 msec
}
LF

# --- 16i. THE UNCONFOUNDED USES EDGE. Identical to 16g except the chain runs
# FORWARD: k1.done feeds k2.gate, so the uses edge demands sink1 before sink2 while
# the measured default (16a, 16b, 16e all agree) is sink2 first. The two now
# disagree, which is what 16g needed and did not have.
#   prints sink1 first -> the uses edge OVERRIDES instantiation order, and there are
#     two independent printer-controlled mechanisms rather than one. Useful as a
#     fallback if 16h refutes the instantiation rule.
#   prints sink2 first -> the uses edge does NOT order these reactions, and 16g's
#     apparent success was entirely the default order.
#   does not compile -> the `reaction(trigger) uses -> effect` spelling is what
#     failed, not the mechanism; the follow-up is the heavier pipeline shape where
#     k1 forwards the payload to k2 as a real trigger.

probe stageG2_uses_forward_chain 'k1.done feeds k2.gate, so the uses edge demands sink1 FIRST while the measured default is sink2 first -- the two disagree, which is what 16g lacked' <<'LF'
target Cpp

public preamble {=
#include <cstdio>
=}

reactor Src {
    output outA: int
    output outB: int
    reaction(startup) -> outA, outB {=
        outA.set(1);
        outB.set(2);
    =}
}

reactor Sink(id: int = 0) {
    input in: int
    input gate: int
    output done: int
    reaction(in) gate -> done {=
        std::printf("RELICO_USES sink%d payload%d\n", id, *in.get());
        std::fflush(stdout);
        done.set(1);
    =}
}

main reactor {
    s = new Src()
    k1 = new Sink(id=1)
    k2 = new Sink(id=2)
    s.outA -> k1.in after 0 msec
    s.outB -> k2.in after 0 msec
    k1.done -> k2.gate
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

  Fifth, section 11 exists to unblock stage E, and its three probes are read
  differently from the rest. struct_as_port_type compiling means F30's refusal
  can be made unreachable by giving a port the payload struct as its type;
  failing means the payload-arity limit becomes a stated restriction on the
  accepted fragment and must be documented as such rather than as a printer
  detail. param_state_name_collision is informative EITHER way: rejection makes
  our name-uniqueness union a measured requirement and obliges the DTR side to
  mirror it, while acceptance means this repository is deliberately stricter
  than its target and must say so in those words -- see F32.
  parameter_defaults_named_args simply repays a debt: that form was measured ad
  hoc in stage D with no committed script, and a fresh clone can now re-run it.

  Sixth, sections 12, 13 and 14a are the only ones here that measure a road NOT
  taken, and the only ones whose result moved a claim from "chosen" to "forced".
  14b is the exception within its own section: it measures the road that IS taken,
  which is why section 14 is split across this sentence and the Eighth paragraph
  below. Measured 2026-08-22 against lfc 0.11.0, section 12's two probes compiling
  and running cleanly:

    action_two_schedules_same_tag       lfc 0, run 0 -> ONE line,  RELICO_ACTION 2
    action_two_schedules_distinct_tags  lfc 0, run 0 -> TWO lines, 1 then 2

  Read them together, which is why the control exists. The control printed both
  values, so the two-argument `schedule(value, delay)` call and the `0ms` literal
  are right, and the single line in the experiment is therefore a real collision
  rather than a mistyped API call. Two schedules of one logical action at one tag
  keep only the LAST value; the first is dropped with exit 0 and no diagnostic of
  any kind.

  That silence is the whole result. A rejection would have been a restriction to
  write down. A SILENT drop means an action-based encoding of a Rebeca send is not
  merely wrong but undetectably wrong -- the program compiles, runs, exits 0, and
  loses a message. SS6's per-send-site port key is therefore FORCED, and both the
  design document and the paper should say forced rather than presenting it as a
  preference among workable options.

  Seventh, section 13 asked whether that loss is a policy choice, and the answer
  is that in this target the policy cannot be expressed at all. Measured the same
  day, same lfc:

    action_defer_policy_same_tag        lfc 1 -> DID NOT COMPILE

  and the diagnostic is worth keeping verbatim, typo included, because it names
  its own scope:

    lfc: error: minSpacing and spacing violation policies are not yet supported
         for logical actions in reactor-ccp!
      --> src/V0Controller.lf:8:5
       8 |     logical action slot(0ms, 1ms, "defer"): int

  So `defer` neither fires the reaction twice nor once: the declaration is
  rejected before code generation, by the C++ runtime rather than by the language.
  The consequence is the one that costs more work. There is no declaration-level
  repair available in the target this translator emits, so a faithful encoding of
  Rebeca's queue must be STRUCTURAL -- a distinct action per send site, exactly
  what SS6.2 already does for ports. That makes the port decision and the
  self-send decision the same decision, reached twice.

  Read section 12 and section 13 together and there is a sharper observation than
  either alone. The target refuses to *discuss* spacing -- naming a policy is a
  hard error -- while silently *implementing* the worst available spacing
  behaviour when you say nothing. The safe-looking declaration is the lossy one
  and the explicit one is unavailable, which is close to the opposite of
  fail-closed. Both facts are version-scoped: the error says "not yet", so a later
  reactor-cpp may support the policy, and a re-run of section 13 is the cheapest
  way to find out. Do not carry either result forward across an lfc upgrade
  without re-measuring.

  Eighth, section 14 asked which SHAPE the forced structural repair takes. Given k
  actions all feeding one message server, does that server get one reaction with k
  triggers, or k reactions? Measured 2026-08-23, same lfc:

    action_two_actions_one_reaction     lfc 0, run 0 -> ONE  RELICO_MULTI_FIRED
    action_two_actions_two_reactions    lfc 0, run 0 -> TWO  lines, A 1 then B 2

  The one-reaction shape fires ONCE. A reaction's trigger list is a disjunction,
  not a queue: the reaction is enabled if ANY trigger is present, so two triggers
  present at one tag is one firing and k-1 message executions are lost. Note this
  is a DIFFERENT loss from section 12 -- there the payload was overwritten on a
  single action, here the firings themselves are merged across two distinct
  actions -- so it is independent confirmation rather than a restatement, and the
  two results close the space from opposite directions. The only rescue for the
  multi-trigger shape would be branching over presence inside the reaction body,
  which relocates the ordering guarantee into generated C++ statement order where
  the Lean development cannot see it; that is the multiport fallback this project
  has already rejected once, and the reason has not changed.

  The k-reactions shape works, and it also settles something that had never been
  measured: section 1 established that two reactions in one reactor both fire at
  one tag in DECLARATION order, but only for reactions triggered by ports.

  CORRECTED 2026-08-23 (finding F58). This paragraph used to read "Section 14b
  shows the same holds when the triggers are logical ACTIONS." The claim is TRUE,
  but 14b does not show it and never could: 14b schedules slotA first AND declares
  reaction(slotA) first, so its observed "A then B" is exactly what SCHEDULE order
  would also produce. The two candidate causes are not separable from that probe.
  SECTION 15 separates them -- same schedules in both members, only the two
  declarations swapped, and the output swaps -- so the action-triggered ordering
  claim is now earned. Cite section 15 for it. That is a load
  on the printer, not a free gift -- if declaration order is what orders the
  firings, the generated reactor must emit one reaction per send site in the order
  the sends appear in the body, and that emission order becomes semantically
  significant rather than cosmetic.

  So the repair is one action AND one reaction per self-send SITE, and the "reached
  twice" above becomes reached three times. The value of three roads is that every
  alternative to site-keying is now measured dead rather than merely disfavoured:
  one action for k sends drops values (12), no policy can restore them (13), and
  one reaction for k actions drops firings (14a). The design document and the paper
  should make that claim in exactly that form, because it is stronger than an
  argument from preference and it is the form the evidence actually supports.


  Ninth, section 16 (2026-08-25) is the only section here whose question is still
  OPEN at the time it was written, and it is written that way on purpose: the rule
  for reading it is recorded before the run, as sections 12 and 13 did, so that the
  result cannot be reverse-fitted to a preference. F76 measured that our two
  run-level selectors disagree -- the source keys on (arrival, PRIORITY), the target
  on (tag.time, tag.microstep) and is priority-blind -- and every ordering fact this
  file already holds is WITHIN one reactor, because a reaction declaration list
  belongs to a reactor CLASS while F76's divergence is between two INSTANCES.

  The load-bearing question is not whether a priority attribute exists. It is
  whether ANY mechanism orders reactions across reactors at one tag, and the three
  answers force three different repairs:

    ordered by something the printer controls (16c instantiation order, 16f an
      attribute, 16g a uses edge) -> the target CAN implement actor priority, F76 is
      repaired by emitting in priority order, and the `.consume` case of Definition
      1 becomes provable with no guard and no refused fragment.
    ordered only by sender STATEMENT order (16b) -> the order is real but lives in
      generated C++ where the Lean development cannot see it. That is the multiport
      fallback rejected in sections 12 and 14a, and the reason has not changed.
    not ordered at all (16d) -> `earliestPendingEvent?`'s total order OVER-SPECIFIES
      real LF. Our target model would then be stricter than its own target, and the
      standing doctrine says refuse such models rather than quietly narrow the
      theorem.

  16d is the reason this section adds a second runner. Every other probe in this
  file answers "what compiles" or "did a pair swap", and neither shape can establish
  an ABSENCE of order -- that is a claim about repeated runs. Its most informative
  outcome is agreement at --workers 1 with disagreement at --workers 4, which would
  mean the order is an artefact of the scheduler's thread count rather than a
  language guarantee, and no printer discipline could fix it.

  Two things section 16 settles regardless of how it comes out. First, an attribute
  annotates a reaction, a reaction belongs to a class, and so no attribute can ever
  distinguish two INSTANCES of one class -- which is what `phils` is made of. Second,
  16f compiling but leaving the order unchanged would be worse than 16f being
  rejected, because an inert annotation is one a printer could emit while proving
  nothing, and this project has already been burned once by an assertion that was
  invariant under the sort it was credited with pinning (F60).

  Nothing in the repo was read or written. Scratch tree: /tmp/relico_lf_probe
NOTE
