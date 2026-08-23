# Stage G findings — F63 onward

**Why this file exists.**
Stage G makes designer-specified priority *preserved and observable* rather than merely emitted in a
defined order, which is what stage F delivered. Its findings start at **F63**, continuing the single
`F` series that [`STAGE_B_FINDINGS.md`](STAGE_B_FINDINGS.md) opened at F1–F20,
[`STAGE_D_FINDINGS.md`](STAGE_D_FINDINGS.md) carried to F21–F33,
[`STAGE_E_FINDINGS.md`](STAGE_E_FINDINGS.md) carried to F34–F58, and
[`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) carried from F59.

This file exists rather than an extra section of [`STAGE_F_FINDINGS.md`](STAGE_F_FINDINGS.md) because
that file states its own scope in one sentence — *"This file owns only what stage F found wrong"* — and
F63 was not found by stage F. It was found while deriving stage G's scope from the repository, which is
also the reason it went unnoticed: it is a defect that accumulated across stages B through F without
being any single stage's output. Filing it under a heading that says "Stage F" would reproduce **F54**,
whose whole content is that an entry which exists but is invisible from where a reader looks costs a
duplicate investigation.

**The provenance rule, unchanged since stage D.** Every entry carries one of four grades, and where a
single entry mixes them the sub-claims are graded separately rather than the whole taking the weakest
label: **measured** (a named run produced the result, identified well enough to repeat), **read** (a
reading of source at a cited `path:line`, including absence established by a described search),
**decided** (a choice between recorded alternatives, with the alternative stated), and **inferred**
(argued, not run — and either it names the experiment that would settle it or it does not belong here).

`docs/STAGE_G_DESIGN.md` owns what stage G *does* and why. This file owns only what stage G *found
wrong*.

---

## F63 — the repository's headline claim is quantified over a fragment five stages out of date, and nothing declares the fragment it actually accepts

*Read.* Two parts, both repaired in the same commit that files this entry. They are one finding because
they share a single cause and a single repair site: there is no tracked statement of what the general
family accepts, so both the outer claim and the inner carve-out are unstatable.

### Part 1 — "the declared supported fragment" resolves to vertical slice v0

The project's top-level claim is quantified over a named fragment in three places:

- `README.md:3` — *"an executable Lean 4 translation from a supported fragment of Deterministic Timed
  Rebeca to a generated subset of Lingua Franca"*.
- `docs/trusted-boundary.md:28` — *"For every well-formed source model in the supported fragment, the
  project aims to prove that:"*, followed by the nine numbered obligations.
- `docs/trusted-boundary.md:62`, the *Intended claim* — *"The executable DTR-AST-to-LF-AST translation
  core implemented in ReLico-Lean is formally verified for the **declared** supported fragment."*

The only document that declares one is `docs/supported-fragment.md`, and it declares **vertical slice
v0**: one reactive class, one actor instance, one integer state variable, one constructor, one message
server, no message parameters, no payload values, `selfSend` as the only send form, and integer literals
plus one state-variable reference as the entire expression language (`:9-26`, `:41-49`).

Its *Initially excluded* list (`:82-97`) has sixteen entries, and the split is exactly even. **Eight have
since been delivered** — multiple classes and multiple actor instances (stage B), known rebecs and
external sends and ports and inter-reactor connections (stages C and E), message parameters and payloads
(stages D and E), actor priorities and message-server priorities (stage F, levels 1 and 2). **Eight
remain genuinely excluded** — conditionals, loops, arrays, inheritance, physical actions, environmental
inputs, broadcast, arbitrary LF programs — and reading the list as written, nothing else.

Half the list is stale, which is the strongest single argument that the document cannot be left as the
resolution of "the declared supported fragment": a reader has no way to tell which half they are in.

Grading this correctly matters, because the obvious verdict is wrong twice over. The document is **not
false about v0**; it is an accurate historical record of the first milestone, and its forward-looking
sentences were overtaken by the 2026-08-17 generalization pivot rather than being mistaken when
written. What is false is the *resolution*: a reader following "the declared supported fragment" from
the intended claim arrives at a declaration that excludes the priority work the claim is now largely
about. The defect is therefore in the pointer and the absence, not in the prose it points at — which is
why the repair is a dated scope marker plus a per-item delivery status, and **not** a rewrite of the v0
body.

The consequence is asymmetric and worth stating plainly, because it decides how urgent this is: the
outer claim is *understated* for what the tool accepts, and *misdescribed* for what is verified. No
proof is weaker than advertised. But the paper's scope section is the single most likely thing to be
drafted from a file named `supported-fragment.md`, and drafting it from this one would exclude stages
B through F from the paper's own statement of its subject.

### Part 2 — a binding decision to make theorem-eligibility legible was never carried out

`docs/STAGE_B_DESIGN.md:593-611` records the decision of 2026-08-18 — option **D**, guards as
theorem-level hypotheses — under the heading *"Consequences, which are now binding on stage B and on
every later stage"*. Two of those consequences are load-bearing for every stage since:

> *"Every stage-F/G correctness theorem carries them as explicit hypotheses. A theorem that needs
> determinism and does not name them is a bug in that theorem."*

> *"The three actor-tie and two message-server-tie fixtures identified in §7's table are therefore
> elaborable but not theorem-eligible. That distinction has to be legible, so §7's table graduates into
> the tracked docs alongside this file rather than living only here."*

The first was honoured: stage F's guard-relative theorems carry `ActorPrioritiesDistinct` and
`MessageServerPrioritiesDistinct` as explicit hypotheses, and `GeneralModel.wellFormed` still does not
mention priority. The second was not. Absence established by search: `grep -rniI
"theorem-eligible\|theorem eligible"` across `docs/`, `Relico/` and `frontend/` returns exactly one
line — `docs/STAGE_B_DESIGN.md:610`, the sentence that says the distinction has to be legible. The
table never graduated.

So five fixtures in the tracked corpus elaborate successfully and are excluded from every correctness
theorem, and no tracked document says which five. That is the same shape as **F47** (docstrings
crediting coverage to fixtures that cannot reach the code) and **F59** (ordering evidence credited to an
instrument that cannot produce it): a coverage boundary that is real, load-bearing, and invisible from
where a reader checks.

### Why this is one finding and not two

Part 1 is a missing *outer* boundary — what the tool accepts. Part 2 is a missing *inner* boundary —
which accepted models the theorems actually speak about. A reader needs both to interpret
`docs/trusted-boundary.md:28`'s "every well-formed source model in the supported fragment", and neither
exists in tracked form. The repair is one document, so the finding is one entry.

### Repair, and what is deliberately not repaired

Repaired here: a dated scope marker at the head of `docs/supported-fragment.md` recording that it
declares v0 and is retained as the historical declaration; a per-item delivery status on the
*Initially excluded* list separating the eight delivered from the nine still excluded; and the
namespace qualification at `docs/STAGE_C_DESIGN.md:794` (see below).

Deliberately **not** repaired here, and filed as stage G design work instead: writing the tracked
declaration of the general family's accepted fragment, and the theorem-eligibility table Part 2 owes.
Both are substantial documents whose content is partly decided by stage G's own scope — in particular
by which of `docs/trusted-boundary.md`'s nine obligations the general family can currently claim — and
writing them before that scope is approved would produce a third document that needs a marker later.
`docs/STAGE_G_DESIGN.md` states them as deliverables with the evidence already gathered here.

### A near-miss recorded because it nearly produced a false repair

While enumerating stage-G mentions, `docs/STAGE_C_DESIGN.md:794` — *"`GeneralStmt` has three
constructors"* — read as a direct contradiction of `docs/STAGE_F_DESIGN.md` §2.4, which says
*"`DTR.GeneralStmt` has exactly two constructors, `assign` and `send`"*. Measured: **both are true.**
`Relico/LF/GeneralSyntax.lean:349` defines an `LF.GeneralStmt` with exactly three constructors
(`assign`, `schedule`, `setPort`), and stage C is the stage that built the LF side, so `:794`'s
unqualified name means the LF type. `MultiStorePayloadStmt`'s "two" is also correct
(`assign`, `selfSend`).

The transferable point is the mirror image of `docs/STAGE_F_DESIGN.md` §7.4's triage lesson, and worth
separating from it. §7.4 failed by grading six lines without re-reading their paragraphs, so it called
two false claims cosmetic. This nearly failed the other way: a *true* claim looked false because it was
graded against the wrong referent, and the only thing that distinguishes the two cases is resolving the
namespace from the surrounding stage rather than from the name. Two types share the short name
`GeneralStmt` across `DTR` and `LF`, and the same is true of `GeneralSyntax.lean`, `GeneralExpr`,
`GeneralBody` and `GeneralWellFormed`. In tracked prose the namespace is not optional, and `:794` now
carries it along with both constructor lists.
