# The paper's DTR fragment, as restrictions a frontend can enforce

This document exists because the translator generalization needs a written-down specification to
reject against. Before it existed, the phrase "R1-R19" was used in planning documents while the
enumerated list lived nowhere, which made every rejection diagnostic unauditable.

## Provenance, and why it matters here

Everything below is taken from `DTR_LF__After_FMCAD_.pdf` directly: Fig. 4 and Fig. 5 from
Appendix A on page 13, and prose from the sections cited per entry. Nothing is derived from this
repository's own summaries of the paper, and nothing is derived from
`docs/actor-priority/phase2/*.tsv`. That rule is not pedantry. Two claims recorded in this project
from secondary sources turned out to be wrong, one of them a grammar production quoted with the
wrong delimiters, so the paper is read directly or not cited.

Where a restriction is not actually stated in the paper, it says so. "Inferred from absence" means
the construct has no production and no prose forbidding it either, so excluding it is our decision
and not a citation.

## Figure 4 verbatim

Transcribed with superscripts inline. Terminals are bold or typewriter in the original, nonterminals
italic; that distinction is lost here but no production is ambiguous without it. Thirteen
productions.

~~~text
       Model  ::=  ClassDecl+ Main
        Main  ::=  main { InstanceDecl* }
InstanceDecl  ::=  Priority?C rebecName
                     (rebecName*) : (IntLit*) ;
   ClassDecl  ::=  reactiveclass C(IntLit) {KnownRebecs
                     Vars Constructor? MsgSrv*}
 KnownRebecs  ::=  knownrebecs { Type id+ ;}
        Vars  ::=  statevars { VarDecl* }
     VarDecl  ::=  Type v+ ;
 Constructor  ::=  C (<Type v>*) { Stmt* }
      MsgSrv  ::=  Priority? msgsrv msgsrvName
                     (<Type v>*) { Stmt* }
    Priority  ::=  @priority (IntLit)
        Stmt  ::=  if (Expr) {Stmt*} (else {Stmt*})? |
                   for (Expr? ; Expr? ; Expr?) {Stmt*} |
                   v = Expr | SendMsg
     SendMsg  ::=  RebecExpr . msgsrvName (Expr*)
                     (after(Expr))? ;
   RebecExpr  ::=  self | rebecName
~~~

`<Type v>` is `⟨Type v⟩`, angle brackets, in `Constructor` and `MsgSrv` only.

**A correction to an earlier transcription in this project.** `InstanceDecl`'s known-rebec binding
list is delimited by **parentheses**, `(rebecName*)`, not angle brackets. This was verified down to
the font and character code on page 13: the two delimiters are `OUPIJB+CMEX7` charcodes 0 and 1, the
large parenthesis glyphs, and no `⟨`/`⟩` character occurs on that line at all. Angle brackets do
appear in Fig. 4, but only around `Type v` in the two parameter lists. Any earlier note in this
repository writing `⟨rebecName*⟩` is wrong.

## Figure 5 verbatim

Recorded here because stage C implements it and because two restrictions below cite it as
contrastive evidence. `e` is the empty string.

~~~text
  LFProgram  ::=  target Cpp; Reactor+ MainReactor
    Reactor  ::=  reactor R (ParamList?) {PortDecl*
                    StateDecl* ActionDecl* ReactionDecl*}
  ParamList  ::=  ParamDecl(, ParamDecl)* | e
  ParamDecl  ::=  par : Type = Expr
   PortDecl  ::=  input inPort ([intLiteral])? : Type ; |
                  output outPort ([intLiteral])? : Type ;
  StateDecl  ::=  state var : Type (= Expr)? ;
 ActionDecl  ::=  logical action act(: Type)? ;
ReactionDecl ::=  reaction(TriggerList) (-> OutputList)?
                    {= LFStmt* =}
TriggerList  ::=  Trigger (, Trigger)*
    Trigger  ::=  startup | inPort ([Expr])? | act
  OutTarget  ::=  outPort ([Expr])? | act
 OutputList  ::=  OutTarget(, OutTarget)*
     LFStmt  ::=  outPort ([Expr])?.set(Expr) ; |
                  act.schedule(delay) ; |
                  if(Expr){LFStmt*}else{LFStmt*} |
                  for(Stmt; Expr; Stmt){LFStmt*} |
                  var = Expr ; | Expr ; | skip
MainReactor  ::=  main reactor {
                    InstDecl+
                    Connection* }
   InstDecl  ::=  ins = new R(ArgList?) ;
    ArgList  ::=  Expr (, Expr)*
 Connection  ::=  ins.outPort ([Expr])? ->
                    ins.inPort ([Expr])?(after delay)? ;
~~~

## The restrictions

### Program structure

**R1 — exactly one `main`, mandatory, after all classes.** `Model ::= ClassDecl+ Main` carries no
quantifier on `Main`, and `ClassDecl+` requires at least one class. *Fig. 4, `Model`.*

**R2 — nothing at top level but classes and `main`.** No properties, assertions, environment
variables, or imports. *Inferred from absence; `Model` derives nothing else.* Worth noting that §V
evaluates safety properties, so property syntax exists in the tool but is outside the figure.

**R3 — `main` holds instance declarations only.** `Main ::= main { InstanceDecl* }`. The `*` means an
empty `main` is derivable by the grammar. *Fig. 4, `Main`.*

**R4 — instance constructor arguments must be integer literals.** `: (IntLit*)`, not `(Expr*)`, so
`:(1+2)` and `:(x)` are out. *Fig. 4, `InstanceDecl`.*

**R5 — known-rebec bindings are a positional list of bare instance names.** `(rebecName*)`: no
expressions, no named or keyword bindings, no indexing. *Fig. 4, `InstanceDecl`.*

**R6 — `@priority` takes one integer literal and is syntactically optional in both positions.**
`Priority ::= @priority (IntLit)`, used as `Priority?` in `InstanceDecl` and `MsgSrv`. Lower means
earlier. *Fig. 4, `Priority`; Lemma 2 §IV p. 8 compares with strict `<`; §II-A p. 3 describes
`@priority(1)` as higher priority than `@priority(2)`.*

### Class body

**R7 — the queue-size argument is mandatory and a bare integer literal.** `reactiveclass C(IntLit)`,
no `?`. *Fig. 4, `ClassDecl`.* See R23 for the fact that it is given no meaning.

**R8 — fixed class-body order, and `knownrebecs`/`statevars` are not optional.**
`{KnownRebecs Vars Constructor? MsgSrv*}` — only the constructor carries `?`. *Fig. 4, `ClassDecl`.*
See D1 and D2: we do not enforce this, because the paper's own figures violate it.

**R9 — `knownrebecs` is one type group with at least one name.** `knownrebecs { Type id+ ;}` has a
single `Type`, a single `;`, and `id+`. So neither an empty block nor two known rebecs of different
types is derivable. *Fig. 4, `KnownRebecs`.* See D1.

**R10 — at most one constructor, named for its class.** `Constructor?` and
`Constructor ::= C (⟨Type v⟩*) {Stmt*}`. No overloading. *Fig. 4.*

**R11 — message servers only; no methods, return types, or modifiers.** *Fig. 4, `MsgSrv` and
`ClassDecl`. Corroborated: "synchronized" appears zero times in the paper, and "method" appears only
as a synonym for message server (§II-A p. 2).*

**R12 — no inheritance, interfaces, records, generics, or nested classes.** *Inferred from absence in
`ClassDecl`. Corroborated: none of those words occurs as a language construct anywhere in the paper.*

**R13 — no global variables.** Variables come only from `KnownRebecs`, `Vars`, and the two parameter
lists, all class-scoped. *Inferred from absence.*

### Statements

**R14 — `Stmt` has exactly four alternatives: `if`, `for`, assignment, send.** No `while`, `do`,
`switch`, `break`, `continue`, `return`, bare block, or bare expression statement. *Fig. 4, `Stmt`.
`while` as a keyword occurs zero times in the paper; all seven occurrences of the string are English
prose. The asymmetry looks deliberate rather than accidental, since Fig. 5's `LFStmt` does admit
`Expr ;` and `skip`.*

**R15 — no local variable declarations in bodies.** `Stmt` has no `VarDecl` alternative, and
`VarDecl` is reachable only through `statevars`. So `int x = 5;` inside a message server is not
derivable. *Fig. 4, `Stmt`, `Vars`, `VarDecl`.*

**R16 — assignment targets a bare variable name.** `v = Expr`: no array element, no qualified target,
no compound assignment, no increment. *Fig. 4, `Stmt`. Corroborated: "array" occurs zero times.*

**R17 — `for` header slots are expressions, not statements.** `for (Expr? ; Expr? ; Expr?)`. Because
assignment is a `Stmt` and not an `Expr`, and because `Expr` has no production at all, the ordinary
loop `for (i = 0; i < n; i = i + 1)` is **not derivable from Fig. 4**. Fig. 5's LF counterpart uses
`for(Stmt; Expr; Stmt)`, so the two figures disagree about loop headers. *Fig. 4, `Stmt`; Fig. 5,
`LFStmt`.* That Fig. 4's `for` is unusable as written is an inference, but §V p. 9 claims the
benchmark suite covers control flow, so something has to give. See D4.

### Send and timing

**R18 — a send target is `self` or a single bare name.** `RebecExpr ::= self | rebecName`: no
expression-valued target, no cast, no index, no broadcast, no reply value. Note that **Fig. 4 never
requires the target to be a declared known rebec** — `KnownRebecs` binds `id`, `RebecExpr` uses
`rebecName`, and no production connects the two. The requirement is prose only. *Fig. 4,
`RebecExpr`; §III-A p. 5: "In DTR, an actor sends messages only to its known rebecs."*

**R19 — `after(Expr)` is optional, and omitting it means delay zero.** *Fig. 4, `SendMsg`; §III-E
p. 6: "An external send in DTR with no explicit after is treated as delay 0. Our tool translates it
to an LF connection with after 0ms, scheduling at the next microstep within the same logical tag."*

**R20 — no `delay(...)`, no `deadline(...)`, no nondeterministic `?(a,b)`.** `after` is the only
timing primitive. *Fig. 4, `Stmt` and `SendMsg`, by absence, plus whole-document token counts:
"deadline" occurs zero times; a DTR `delay(` statement occurs zero times, every `delay` token in the
paper being LF-side; and the string `?(` occurs exactly once, as Fig. 5 metasyntax.* This matters
because the upstream example corpus uses all three constructs freely — 9 models use `delay(`, 5 use
`deadline(`, 9 use `?(...)` — so those models are outside the paper's fragment, not merely outside
our implementation.

**R21 — no dynamic actor creation or destruction; the topology is fixed by `main`.** *Inferred from
absence: `Stmt` has no `new`. Fig. 5 does have `InstDecl ::= ins = new R(ArgList?) ;` but only inside
`MainReactor`, never inside `LFStmt`.*

### Semantic side conditions, which no grammar check can enforce

**R22 — priorities must resolve every observable same-time choice.** This is the restriction the
contention rule implements, and the paper states it in prose while its own grammar contradicts it by
making `@priority` optional. *§II-A p. 3: "Full Timed Rebeca models with unresolved observable
choices require priorities before translation." §III-G p. 6: "Full Timed Rebeca models with
unresolved observable choices are outside the supported fragment."* The paper gives **no
tie-breaking rule**: Lemma 2 compares priorities with strict `<` only, and "tie", "distinct", "equal
priority", "same priority" and "unique priority" occur zero times.

**R23 — the single-port assumption: at most one identical message from one sender to one receiver at
one logical time.** *§III-G pp. 6-7: "Also, ReLico excludes multiple identical messages from one
sender to one receiver at the same logical time. DTR stores them separately, whereas LF retains only
the last same-time port write, losing multiplicity. Fig. 2a, lines 12-13, illustrates this case."
Restated twice in §IV p. 9.*

**R24 — the source model must be overflow-free.** *§IV p. 8, in full: "Now we prove that the DTR
model M_dtr is weakly bisimilar to its LF translation M_lf, assuming M_dtr is overflow-free (no
dropped messages)."* This is the only occurrence of "overflow" in the paper, it is a hypothesis on
the source model, and it is never related to the queue bound of R7 nor discharged anywhere. The DTR
semantics makes the bag unbounded — §II-A p. 3, "modeled as a multi-set of time-tagged messages" —
and no rule in Table I can drop a message, so within the paper the class-header integer is
decoration.

## Symbols Fig. 4 uses and never defines

There are eight. Fig. 4 has thirteen left-hand sides; every other symbol on a right-hand side is
undefined.

| symbol | uses | consequence |
|---|---|---|
| `Expr` | 7 | no expression language exists in the paper at all |
| `Type` | 4 | the type universe is unspecified, so whether rebec references are values is undecided |
| `IntLit` | 3 | lexical, undefined but harmless |
| `C` | 3 | class name |
| `rebecName` | 3 | never tied to `id`, which is why R18 has no grammatical force |
| `msgsrvName` | 2 | never tied to a declaring `MsgSrv` |
| `v` | 4 | variable name |
| `id` | 1 | distinct from `rebecName` for no stated reason |

`Expr` is the consequential one. The paper says nothing whatsoever about what an expression is: no
operators, no literals, no precedence. Its only handles are semantic and opaque — §II-A p. 3,
"The function eval(expr, e) computes the result of an expression expr under the current valuation
e", and §IV p. 9, "expression translation preserves evaluation". **So no expression restriction below
can cite the paper.** The admissible operator set is our choice, and D5 states it as such. The only
type appearing in any example in the paper is `int`; `boolean`, `byte`, `short`, `long`, `double`,
`float`, `char` and `string` occur zero times.

`Type` is the one that threatens the translation rather than merely the prose, because on the reading
where it ranges over class names the fragment admits rebec-typed state variables and rebec-typed
payloads, and then the sender set of a message server is not statically computable. Five upstream
models exercise that reading.

## Where ReLico deliberately does not enforce Figure 4

Enforcing Fig. 4 literally would reject the paper's own figures. These are the deviations, each with
the reason, so that a reader can tell a considered divergence from an unimplemented restriction.

**D1 — `knownrebecs` may be empty and may contain several type groups.** R9 as written forbids both.
But Fig. 1a line 14 is `knownrebecs { }` and Fig. 2a line 30 is `knownrebecs { }`, so the empty block
is required to accept the paper's own examples; and a single `Type id+ ;` group cannot declare two
known rebecs of different types, which real models need constantly. We accept a list of groups,
matching the actual parser, whose field is `List<FieldDeclaration> knownRebecs`.

**D2 — `statevars` may be absent.** R8 makes `Vars` mandatory, but Fig. 2a's `Controller`, lines
29-34, has no `statevars` block and no constructor. Enforcing R8 rejects it.

**D3 — a class may have no message servers.** `MsgSrv*` already permits this, so it is not a
divergence; recorded only because the previous exporters required at least one.

**D4 — `for` init and update slots accept assignment.** Under R17 no useful loop is derivable. We
follow Fig. 5's `for(Stmt; Expr; Stmt)` shape instead, restricted to assignment in the two statement
slots, which is the reading under which the paper's own control-flow benchmarks make sense.

**D5 — the expression language is ours, not the paper's.** Since `Expr` is undefined, we fix it:
integer literals, boolean literals, references to state variables and to message-server or
constructor parameters, the binary operators `+ - * / %` and `== != < <= > >=` and `&& ||`, and the
unary operators `!` and `-`. Ternary conditionals, casts, `instanceof`, nondeterministic choice, and
function calls are rejected. None of this is a paper citation and none of it should be presented as
one.

**D6 — sends must target `self` or a declared known rebec.** R18 gives this no grammatical force
because `rebecName` and `id` are never connected, so we enforce §III-A's prose instead. This is the
restriction that makes the sender set of a message server computable, so it is load-bearing rather
than cosmetic.

**D7 — the `for` initializer may declare its own counter.** R15 forbids local declarations, and neither
Fig. 4 nor Fig. 5 admits `for (int i = 0; ...)`, so under the figures a loop counter would have to be a
state variable. We reject that reading, because it is not semantics-preserving in the direction that
matters here: a counter promoted to `statevars` becomes part of the actor's persistent valuation, so it
enlarges the reachable state space the model checker explores and changes the state-matching behaviour
of the very verification the tool exists to support. A counter that lives and dies inside one message
server has no business in the state vector. The declaration is accepted in the initializer slot only,
one name, of a value type, with an initial expression, and the name leaves scope at the end of the
loop.

**D8 — instance arguments may be boolean literals, not only integer literals.** R4 says `IntLit`. But
`Type` is undefined (see P11), our own value set contains `boolean` by D5, and the combination would
make a constructor with a boolean parameter impossible to instantiate — an inconsistency internal to
our frontend rather than to the paper. So `IntLit` is read as "literal", and the literal is required to
match the declared type of the corresponding constructor parameter. This is a consequence of the
undefined `Type`, and it is cross-referenced from ledger entries P6 and P11.

**D9 — `after` must be a non-negative integer literal, not an arbitrary expression.** Fig. 4 writes
`(after(Expr))?`, so the delay is an expression. The tool requires a literal. The reason is the target
side: §III-E p. 6 states that an external send becomes an LF connection carrying the delay — "Our tool
translates it to an LF connection with after 0ms" — and a connection delay is fixed at elaboration
time, so a delay computed from a state variable at run time has nothing to translate into. Absence is
carried through as null rather than rewritten to zero, because R19's default is a fact about the
translation and this schema is an abstract syntax tree; the Lean side applies the default.

**A caveat on D9, and a measurement that is still owed.** The first half of that argument is quoted;
the second half is not. That an LF connection's `after` delay must be static is a claim about Lingua
Franca that this project has not measured. The `lfc 0.11.0` probe established three other things —
`reaction(in[0])` is rejected, reaction declaration order decides same-tag order, and unconnected
input ports are legal — but it never tested a non-constant connection delay. Until it does, D9 stands
as an implementation restriction and **must not** be filed against the paper, because the finding it
would support depends on the unmeasured half.

Every divergence here except D9 is also filed against the paper in `docs/PAPER_CORRECTIONS.md`, since
the project's standing position is that a divergence found by building the tool is a result to write up
rather than a problem to route around. D9 is held back deliberately: filing it would mean asserting a
Lingua Franca property from memory, and this document's own provenance rule exists because exactly that
kind of shortcut has already produced two wrong claims in this project.

## Which layer enforces each restriction, and why stage B cannot inherit any of it

Measured on the first full run of `frontend/java-bridge/check-general.sh`: of the nineteen negative
fixtures written against the restrictions above, the Java exporter is what rejects eleven, and the
Rebeca parser and typechecker reject the other eight before the exporter is handed an AST at all. The
eight are kept, in `frontend/fixtures/general/upstream-reject/`, with the upstream compiler's own
message recorded; the gate holds each corpus to its own layer so that a restriction cannot migrate
between them unnoticed.

The eight enforced upstream are: a `knownrebecs` binding whose arity disagrees with the declaration; an
instance argument whose literal type disagrees with the constructor parameter (the D8 check); an
initialized state variable; a known rebec used as a value (A1); a read of the implicit `sender` (A4); a
send to the implicit `sender` (A4); a send to a name that is not a known rebec (D6); and a send naming a
message server the receiving class does not declare.

**This matters for stage B, and the direction is easy to get backwards.** Being enforced upstream makes
these restrictions *less* covered downstream, not more. The Lean side decodes a `general-v1` JSON
document; there is no Rebeca parser and no typechecker anywhere upstream of that decoder. So every one
of the eight has to be re-established in Lean as an explicit well-formedness condition, and they are
exactly the ones for which no Java code in this repository can be pointed at as prior art — the checks
exist in the exporter's source, but they have never executed, because nothing reaches them. Treating
"the exporter checks it" as coverage would leave the Lean fragment admitting eight classes of model the
Java pipeline could never have produced.

Two further notes from the same run, both about reachability rather than about the paper:

- `TimedRebecaCompleteCompilerFacade` injects four reserved `int` variables into every message server's
  scope: `now`, `currentMessageArrival`, `currentMessageDeadline`, `currentMessageWaitingTime`. All four
  typecheck upstream and therefore reach the exporter. Only `now` has a named rejection site; the other
  three are rejected by the general undeclared-name check, which is safe but describes a reserved word
  as undeclared. The Lean well-formedness layer has no equivalent of these names at all, so nothing is
  owed there — this is recorded so that the diagnostic is not mistaken for a missing check.
- A negative fixture that fails to *parse* satisfies any test that merely asks whether something
  rejected it. One fixture in this corpus did exactly that for its whole first life, because it used a
  reserved token as an identifier. The lesson generalizes past the frontend: a negative test needs to
  assert which layer rejected the input, not only that the input was rejected.
