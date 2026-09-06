# Stage K findings: F92 onward

**Why this file exists.**
Stage K is the benchmark phase: it registers the general family, pilots benchmarks through the
nine-stage pipeline, and grows the corpus. Its findings start at **F92**, continuing the single `F`
series that [`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened at F1–F20,
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md) carried to F21–F33,
[`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) carried to F34–F58,
[`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) carried from F59,
[`STAGE_G_FINDINGS.md`](STAGE_G_FINDINGS.md) carried to F88,
[`STAGE_H_FINDINGS.md`](STAGE_H_FINDINGS.md) opened at F89, and
[`STAGE_I_FINDINGS.md`](STAGE_I_FINDINGS.md) carried to **F91**.

Nothing before F92 is restated, renumbered or amended here.

The three findings below share a shape, and it is the shape of the whole stage: **a fixture that
satisfies the gate it was written for says nothing about the gate it was not written for.** Every
defect in this file is an instrument measuring the wrong boundary and being believed anyway.

---

## F92: the general fixtures satisfy the model checker exactly when they do nothing

**Grade: measured**, every sub-claim by a named run.

Every benchmark source must clear two mandatory gates: the ReLico frontend, and the official Rebeca
model checker at `Deadlock-Freedom and No Deadline Missed`. The thirteen accepted general fixtures
under `frontend/fixtures/general/` were authored for the first gate. Until stage K's pilot wave, none
had ever been put through the second. Eight of the thirteen fail it.

The split is exact on a single predicate — **whether the fixture sends any message at all**:

| behaviour | fixtures | verdict |
|---|---|---|
| sends nothing | `constructor-arguments`, `control-flow`, `expressions`, `local-declaration`, `minimal-class` | **satisfied**, and the report contains zero states |
| sends, then stops | `branching`, `fan-in`, `locals`, `send-sites`, `two-classes`, `two-instances` | **deadlock** |
| sends two into a one-deep queue | `priorities` | **queue overflow** |
| sends forever, counter unbounded | `keep-alive` | **no report**, the checker times out at 60 s |

Five of five zero-send fixtures pass; eight of eight sending fixtures fail. The mechanism is not
subtle once the counter-example is read rather than the exit code: `branching`'s trace ends in state
`6_0` with both queues empty and `now = 2147483647`. **RMC calls a terminating Timed Rebeca model a
deadlock.** A model that never sends never reaches such a state, so it passes by being inert;
`keep-alive` recurs unconditionally but does `beats = beats + 1` forever, so its state space is
infinite and the checker does not finish. `branching` looks recurrent and is not: its `self.sample()`
reschedule sits behind `level > 4`, which the increment in the sibling branch makes unreachable.

So the rule an RMC-clean source must satisfy is four-part, and the thirty-two pre-existing benchmark
sources already satisfy all four: **send**, recur **unconditionally**, keep every state variable in a
**finite** range, and size the queue for the messages in flight.

The consequence for the registry was concrete. Selecting the pilot wave by construct coverage alone
named `locals` (+12 constructs), `expressions` (+1) and `priorities` (+1). Two of those three fail
RMC. Restricted to models that clear both gates, the eligible construct universe is **8, not 14**:
`known-rebecs`, `delayed-send`, `conditional`, `else-branch`, `priority-annotation` and `self-send`
occur *only* in fixtures that deadlock or overflow. Two registry rows —
`general--conditional--positive` and `general--priority-selection--positive` — therefore had no
fixture source at all, and were filled from the upstream corpus instead, where models were authored
as models rather than as gate inputs.

### The transferable check

When a corpus of inputs exists to exercise one boundary, do not assume it clears any other boundary,
and do not infer that it does from the fact that it was reviewed. Run the second gate over the whole
corpus before selecting from it, and expect the eligible set to be smaller than the union of the two
acceptance criteria suggests. The cheap version of this check is one predicate: ask what the inputs
were *written to provoke*, and whether the other gate cares about that at all.

---

## F93: a static construct screen is sound against the fragment, and not complete

**Grade: measured** against the real frontend over all 49 upstream corpus models.

`general-corpus-selection.tsv` first carried a *static screen*: a construct census over the corpus,
scored against the exclusion list in
[`supported-fragment-general.md`](supported-fragment-general.md). The file said so, and named its
column `static-screen` rather than a verdict, precisely because a construct census is not a frontend.
Stage K then ran the real frontend — the Java exporter, then the Lean decoder and
`DTR.GeneralModel.wellFormed` — over all 49.

| instrument | inside the fragment |
|---|---|
| static screen | 28 of 49 |
| **real frontend, measured** | **27 of 49** |

The two agree on 27 models. The screen has **zero false blocks** and **exactly one false clear**:
`benchmarks/pingpong`, which the exporter accepts and the Lean layer then refuses with

> `general-v1: an assignment to a name that is not a state variable: msg in Node.sendMsg at line 19`

an assignment to a *message-server parameter*. The fragment's `assign` admits a state variable or a
live local; a parameter is neither. No construct pattern can see that, because nothing about the
model's construct inventory is wrong — `int`, assignment and message servers are all admitted. The
defect is in a name's *binding class*, which is a property of the elaborated model rather than of the
source text.

That asymmetry is the finding, and it is the useful direction: a construct screen can be trusted to
say *no* and cannot be trusted to say *yes*. Blocking constructs are visible in the text; acceptance
depends on resolution rules that only the elaborator applies.

The registry now carries `frontend-verdict` for all 49 upstream rows, with values naming the layer
that refused, and the measured diagnostic in `refusal_reason`. `blocking_constructs` survives as a
census, no longer load-bearing for the verdict.

### The transferable check

Before a screen's output is written into a registry as fact, ask which direction of its answer is
sound. A screen built from a documented exclusion list inherits exactly the completeness of that
list, and exclusion lists enumerate *syntax*, so any refusal that depends on binding, typing or
resolution is invisible to it. Where the real gate is runnable, run it and keep the screen only as the
cheap pre-filter it is.

---

## F94: the corpus-coverage figure was an estimate quoted as a measurement

**Grade: measured.** Supersedes the figure in
[`0047-local-declarations-in-the-fragment.md`](decisions/0047-local-declarations-in-the-fragment.md).

Decision record 0047 states twice that I0's acceptance of conditionals "took the fragment from 8 to
31 of 49 models", and uses the second of those numerals in its rationale for treating locals as
lower-value than conditionals. That figure came from the I0 census, a static construct analysis of
the same kind F93 describes.

Measured against the real frontend on the current tree, the figure is **27 of 49**. The comparison is
sound rather than confounded: 0047 itself records that locals moved coverage by zero, and stage I only
ever widened the fragment, so the tree measured today implements the same acceptance the 31 was
claimed for. The estimate was four models high.

The decision 0047 records does not change — conditionals moved coverage by an order of magnitude and
locals moved it by nothing, on either figure. What changes is the standing of the number. It was
carried in prose as a measurement, cited in a rationale, and repeated into a handoff, and no
instrument had ever produced it.

0047's two numerals are corrected in place with a pointer here, rather than left standing with a
footnote, because a decision record is read for its numbers as often as for its decision, and a
reader who takes 31 from it and 27 from the registry has no way to tell which is stale.

### The transferable check

A count that no committed instrument can reproduce is an estimate, whatever the sentence around it
claims. When one appears in a decision record or a paper draft, either name the instrument in the same
sentence or re-measure before quoting it — and when the real gate becomes runnable, re-measure every
figure that predates it rather than only the one currently in dispute.
