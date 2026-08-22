import Relico.DTR.GeneralSyntax
import Relico.LF.GeneralSyntax
import Relico.Translation.NameGeneration

set_option autoImplicit false

namespace Relico
namespace Translation

/-!
# Stage E: send sites, ports, routes

Where an external send becomes a place in the target. Nothing here compiles a body, an
expression or a reaction — `Relico/Translation/GeneralBasic.lean` does that, and it
imports this file — and nothing here prints anything. What this file owns is the answer
to one question: given a model, *which ports exist, on which reactors, carrying what, and
which connections join them*.

The answer is a **routing table**. `routesOf` builds one row per (sender instance, send
site), and the output ports, the input ports and the connections are three projections of
that one list. That is the design's §7.2 shape and the reason for it is worth restating:
the two ends of a connection are built from **one** string. `GeneralRoute.outputPort` is
carried rather than recomputed, and the input port is `inputPortNameFor` applied to that
same carried string, so the endpoints of a connection cannot drift apart under a later
change to the naming rule. A version that recomputed each end from the underlying
(message, known rebec, site) triple would be one edit away from a program whose
connections name ports no reactor declares, and `lfc` — not Lean — would be the thing
that noticed.

A **send site** is an address, not a counter: `SendSite` is a body key together with the
statement's position in that body's statement list. Two sends to one (known rebec,
message) pair therefore have distinct sites without any traversal having to thread a
running total, and — the point of the whole revision — they get distinct ports. Two `set`
calls on one port at one tag, which `lfc` accepts and then silently drops one of, becomes
structurally impossible rather than a refusal.

## Two functions moved here from `GeneralBasic`

`compileGeneralType` and `compileGeneralTypedParameter` are defined in this file and no
longer in `Relico/Translation/GeneralBasic.lean`. The namespace is the same one, so no
call site changes and the simp lemmas about them stay where they were.

The move is forced rather than tidy. A port's payload is built from a message server's
declared formals, so the routing layer needs the type map; `GeneralBasic` imports this
file, so it cannot be the one to supply it; and a second copy of a two-arm type map is
exactly the kind of duplicate that stays correct for one stage and then diverges. The
sharpest reason is F41: a payload struct is named by the message server's logical action
*and* by every port that carries it, the printer's preamble deduplicates those
declarations on the name alone, and nothing anywhere compares the action's parameter list
against the port payload's field list. Two builders that disagreed on a type would
produce two declarations of one struct name, of which the preamble would keep the first,
and half the generated program would be compiled against fields the other half never
declared. One builder is what makes that unsayable. (F37 is a different guarantee: it
compares the two *ends of a connection*, payload and all, which catches a sender and a
receiver disagreeing but says nothing about an action and a port on the same reactor.)

## Three places this file departs from `docs/STAGE_E_DESIGN.md`

**§4.1 loses to §7.1 on what `SendSite.index` counts.** §4.1 says the index *"counts
external sends only"*; §7.1 says it is *"the position within that body's statement list"*.
Those disagree on any body with an assignment before a send, and only the second one is
an address: counting external sends means threading a total through the traversal, which
§7.1 rejects in the same breath. The position in the statement list wins. The visible
consequence is that indices are not contiguous — a body whose only external send is its
third statement yields index `2` — and that is a feature, because it makes the site
recoverable by looking at the source rather than by re-running the filter.

**§4.3's second injectivity lemma is false and is not stated.** The gap is filed as F42
and the witnesses are recorded on `outputPortNameFor` in
`Relico/Translation/NameGeneration.lean`, which is where a reader looking for the naming
rule will be.

**§4.2's prose loses to §4.2's own table on when a suffix appears.** The prose says digits
run *"from `2` upward"*, leaving the first site unsuffixed; the code block beside it says
`n = 1, 2, 3, …` and the table under it spells `reportToHub1` and `reportToHub2`. The
table wins: when a class has more than one send to a pair, **every** one of those sites
carries its 1-based ordinal, and when it has exactly one the suffix is empty. Leaving the
first site bare in a group of three would make `reportToHub` mean *"the first of several"*
in one class and *"the only one"* in another, and the two would be indistinguishable in
generated code.

## What the refusals in this file are for

Every refusal in this file but one refuses something `DTR.GeneralModel.wellFormed` already
forbids, and each of those names the conjunct that makes it unreachable. That is deliberate
and it is not dead code: this file's functions are total on their own types, so a
hand-built model — or a well-formedness predicate that loses a conjunct in a later stage —
reaches them, and a diagnostic is a better outcome than a `default` port name. The
refusals are ordered so that the *first* thing to fail is the thing furthest from the
generated code, so a diagnostic names a cause and not a symptom.

One refusal is not defensive: arity zero. A message server with no parameters has no port
payload to declare, because whether `lfc 0.11.0` accepts a port with no type at all is
**unmeasured** — §5.3 and §11.2 both record the probe as owed. Until it is measured the
translation refuses, and the refusal is reachable from a perfectly well-formed model,
which is why its diagnostic says what is missing rather than what is wrong.
-/

/-!
## The type map, shared by actions and ports
-/

/--
Translate a declared type.

Total and injective in the only sense that matters here: the two DTR constructors map
to the two LF constructors of the same name, and neither side has a type the other
cannot express. The emitted spellings differ — LF writes `bool` where this writes
`boolean` — and the single place that knows this is `renderGeneralType` in the printer.

Stage D defined this in `Relico/Translation/GeneralBasic.lean`. It lives here now for the
reason the module note gives, and the namespace is unchanged, so nothing that called it
had to move with it.
-/
def compileGeneralType :
    DTR.GeneralType →
    LF.GeneralType

  | .int =>
      .int

  | .boolean =>
      .boolean

/--
Translate a typed parameter.

One function for both uses, because one structure serves both on each side: a message
server's formals and a constructor's formals are the same shape in DTR, and stage D made
them the same shape in LF. Stage E adds a third use — the fields of a port's payload
struct — and that third use is the reason this definition moved out of `GeneralBasic`.
-/
def compileGeneralTypedParameter
    (parameter : DTR.GeneralTypedParameter) :
    LF.GeneralTypedParameter where

  name :=
    parameter.name

  declaredType :=
    compileGeneralType parameter.declaredType

/-!
## Send sites

Three types and one traversal. Everything downstream — port names, payloads, connections,
and the theorem that two sets on one port at one tag are unsayable — is a function of the
list this traversal returns.
-/

/--
Which body a send site lives in.

A class has one constructor and any number of message servers, and a send can occur in any
of them, so a body is identified either as *the* constructor or by the message name of the
server. Message names are unique within a class — `namesUniqueAndValid` — so this really
does name a body and not merely a kind of body.

The constructor arm carries nothing, which is worth one sentence because it is the reason
this is an inductive type and not a `MsgName`: there is no message name that means "the
constructor", and inventing one (`"initial"`, say) would collide with a message server a
model is entitled to declare.
-/
inductive GeneralBodyKey where
  | constructor

  | messageServer :
      MsgName →
      GeneralBodyKey

deriving Repr, DecidableEq, BEq, Inhabited

/--
The address of one statement inside one class.

`index` is the statement's **position in its body's statement list**, counted from zero
over *all* statements and not only over the sends. §4.1 of the design says the opposite
and loses; the module note above says why at length. The short version is that a position
is an address — it can be checked against the source by counting statements — whereas a
count of preceding sends is a number that only the traversal that produced it can explain.

Indices are therefore sparse: a body whose sole external send is its third statement
yields `2`, and nothing anywhere depends on the set of indices being an initial segment.
The two things that do depend on this type are decidable equality, which is what lets a
statement compiler look its own site up in the environment, and the fact that distinct
statements have distinct sites, which is what makes two sends to one (known rebec,
message) pair get two ports.
-/
structure SendSite where
  body :
    GeneralBodyKey

  index :
    Nat

deriving Repr, DecidableEq, BEq, Inhabited

/--
One external send, addressed.

The message arguments are deliberately absent. A send's arguments are expressions, they
are compiled where every other expression is compiled, and carrying them here would put
the routing layer in the business of deciding what a payload *value* is when its only
business is deciding what a payload's *type* is. What is kept is exactly what names a port
and joins a connection: where the send is, whom it names, what it says, and how late it
arrives.

The delay is kept because it lands on the **connection** rather than in the reaction body,
which is the one place stage E's shape differs from stage D's: a self-send's `after`
becomes the delay argument of a `schedule` call, an external send's `after` becomes
`after N msec` on the connection that carries it. Two sends to one pair with different
delays therefore need two connections, hence two ports — the case that made per-send-site
ports necessary rather than merely tidy.
-/
structure GeneralExternalSend where
  site :
    SendSite

  knownRebec :
    KnownRebecName

  message :
    MsgName

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

/--
The external sends of one body, from a given starting index.

Explicit recursion with the index in the *matched* position rather than as a leading
parameter, which is the shape `DTR.findKnownRebec?` and its three siblings use. Self-sends
and assignments advance the index and contribute nothing, which is what makes the index a
statement position rather than a send count.

§7.1 suggests `List.zipIdx` for the index, and it would compute the same list. It is not used
for the reason `String.capitalize` is not used in `NameGeneration.lean`: this development
depends on no library function whose name has churned across Lean releases, and that one was
`List.enum` until recently. A four-line recursion cannot be renamed underneath a build.

There is no wildcard on the send arm's target: `.selfTarget` is matched explicitly, so the
stage that adds a third send target gets a build error here rather than a silently dropped
send.
-/
def externalSendsFromIndex
    (bodyKey : GeneralBodyKey) :
    Nat →
    DTR.GeneralBody →
    List GeneralExternalSend

  | _, [] =>
      []

  | index, .assign _ _ :: remaining =>
      externalSendsFromIndex
        bodyKey
        (index + 1)
        remaining

  | index, .send .selfTarget _ _ _ :: remaining =>
      externalSendsFromIndex
        bodyKey
        (index + 1)
        remaining

  | index, .send (.knownRebec knownRebec) message _ delay :: remaining =>
      {
        site :=
          {
            body :=
              bodyKey

            index :=
              index
          }

        knownRebec :=
          knownRebec

        message :=
          message

        delay :=
          delay
      } ::
        externalSendsFromIndex
          bodyKey
          (index + 1)
          remaining

/--
The external sends of one body.
-/
def externalSendsOfBody
    (bodyKey : GeneralBodyKey)
    (body : DTR.GeneralBody) :
    List GeneralExternalSend :=
  externalSendsFromIndex
    bodyKey
    0
    body

/--
The external sends of a list of message servers, in declaration order.
-/
def externalSendsOfMessageServers :
    List DTR.GeneralMessageServer →
    List GeneralExternalSend

  | [] =>
      []

  | server :: remaining =>
      externalSendsOfBody
          (.messageServer server.name)
          server.body ++
        externalSendsOfMessageServers
          remaining

/--
Every external send of one class, in canonical order.

Canonical means the constructor first and then the message servers in declaration order,
and it is fixed here once because the site *ordinals* that decide port names are positions
in this list. Any other order would rename ports without changing a program, which is the
kind of instability that makes a generated artifact unreviewable.

Declaration order is also the order the frontend emits and the order the printer emits
reactions in, so a reader comparing a `.rebeca` source against a `.lf` output walks both
in the same direction.
-/
def externalSendsOfClass
    (reactiveClass : DTR.GeneralReactiveClass) :
    List GeneralExternalSend :=
  externalSendsOfBody
      .constructor
      reactiveClass.constructor.body ++
    externalSendsOfMessageServers
      reactiveClass.messageServers

/-!
## Numbering the sites of one (known rebec, message) pair

The suffix that distinguishes `reportToHub1` from `reportToHub2` is computed here, and it
is computed from the class's whole send list rather than threaded through the traversal.
Two facts have to come out of this section: each site of a pair gets a distinct ordinal,
and a pair with one site gets no suffix at all, so every fixture inherited from stage D
keeps the port name it would have had before send sites existed.
-/

/--
How many of these sends name the same known rebec and the same message.

Decidable equality on a pair rather than two nested tests or a `&&` of `BEq`, for the
reason `DTR.findKnownRebec?` gives at length: `DecidableEq` and `BEq` are derived
independently and nothing bridges them, so a development that mixes the two cannot prove
anything about either. `Prod.mk.injEq` is a simp lemma, so a proof about this function can
still split the pair.
-/
def countSendsTo
    (knownRebec : KnownRebecName)
    (message : MsgName) :
    List GeneralExternalSend →
    Nat

  | [] =>
      0

  | send :: remaining =>
      if
        (
          send.knownRebec,
          send.message
        ) =
          (
            knownRebec,
            message
          )
      then
        1 +
          countSendsTo
            knownRebec
            message
            remaining
      else
        countSendsTo
          knownRebec
          message
          remaining

/--
Pair every send with its 1-based ordinal among the sends to its own pair.

The ordinal of a send is one more than the number of *earlier* sends to the same pair,
which is why the first argument accumulates the sends already numbered. The arithmetic
alternative — total sends to the pair, minus the sends after this one, plus one — computes
the same number and is not obviously correct at a glance, which for a function that decides
generated identifiers is the whole of the argument against it.

The accumulator grows by prepending, so it holds the earlier sends in reverse order.
Nothing here depends on its order, only on how many of its elements match, and that is
worth stating because a later stage tempted to read the accumulator as a history would be
reading it backwards.
-/
def numberExternalSends :
    List GeneralExternalSend →
    List GeneralExternalSend →
    List (GeneralExternalSend × Nat)

  | _, [] =>
      []

  | numbered, send :: remaining =>
      (
        send,
        1 +
          countSendsTo
            send.knownRebec
            send.message
            numbered
      ) ::
        numberExternalSends
          (send :: numbered)
          remaining

/--
Every send of one class, paired with its ordinal.
-/
def numberedExternalSendsOfClass
    (reactiveClass : DTR.GeneralReactiveClass) :
    List (GeneralExternalSend × Nat) :=
  numberExternalSends
    []
    (externalSendsOfClass
      reactiveClass)

/--
The suffix that distinguishes one send site's port from its pair's other sites.

Empty when the class sends to this pair exactly once, and the site's 1-based ordinal
otherwise. §4.2's table is what this implements; §4.2's prose says the first of several
sites is also unsuffixed, and it loses, because `reportToHub` would then mean "the first of
several" in one class and "the only one" in another with nothing in the generated code able
to tell them apart.

`allSends` is the class's whole send list and `send` is expected to be one of its elements,
in which case the count is at least one. A send from somewhere else counts zero, takes the
`else` branch and is suffixed — which is the safe direction, and is not relied on anywhere:
the only caller passes a send it drew from the list it passes.
-/
def generalSiteSuffixFor
    (allSends : List GeneralExternalSend)
    (send : GeneralExternalSend)
    (ordinal : Nat) :
    String :=
  if
    countSendsTo
        send.knownRebec
        send.message
        allSends =
      1
  then
    ""
  else
    toString ordinal

/-!
## The same numbering, for self-sends

Everything above numbers *external* send sites so that two sends to one (known rebec,
message) pair get two ports. This section does the same for *self*-sends, so that two sends
to one message server get two logical actions, and it exists because of a measurement rather
than for symmetry.

Probe sections 12 to 14 of `tools/paper-measurements/lf_semantics_probe.sh`, against `lfc`
0.11.0: two `schedule` calls on one logical action at one tag keep only the **last** value,
with `lfc` exit 0, a clean C++ build, run exit 0 and no diagnostic anywhere (section 12); the
spacing policy that would repair it, `logical action slot(0ms, 1ms, "defer")`, is rejected
before code generation because reactor-cpp implements no spacing policy for logical actions
(section 13); and one reaction triggered by *two* actions both scheduled at one tag fires
**once**, because a reaction's trigger list is a disjunction rather than a queue (section
14a). So neither one action for k sends nor one reaction for k actions is faithful, and the
only shape left standing is one action **and** one reaction per site (section 14b). Recorded
as finding F56 in `docs/STAGE_E_FINDINGS.md` and in §6.3 of the design.

Two consequences are worth stating where the code is rather than only in the design. The
first is that this is not a tidiness argument: `self.tick(); self.tick();` in one body
compiled, ran, exited 0 and executed `tick` once, so the defect this repairs was silent. The
second is that `selfSendsOfClass` fixes the site ordinals, and section 14b measured that
reaction *declaration* order decides same-tag firing order for action-triggered reactions as
it already did for port-triggered ones — so the order of this list is a correctness property
of the generated program and not a presentation choice.
-/

/--
One self-send, addressed.

The same shape as `GeneralExternalSend` with the known rebec dropped, because a self-send
names no other actor. The delay is kept and, unlike the external case, it stays *in* the
reaction body: a self-send's `after` becomes the delay argument of the `schedule` call, which
is the asymmetry §6.3 turns on.
-/
structure GeneralSelfSend where
  site :
    SendSite

  message :
    MsgName

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

/--
The self-sends of one body, from a given starting index.

The mirror of `externalSendsFromIndex`, and the indices agree with it by construction because
both advance on **every** statement rather than only on the ones they collect. That is what
lets one site identify one statement whichever list it was drawn from, and it is why the
`.assign` arm is not a wildcard here either: a stage that adds a statement form gets a build
error rather than a site numbering that has silently shifted.
-/
def selfSendsFromIndex
    (bodyKey : GeneralBodyKey) :
    Nat →
    DTR.GeneralBody →
    List GeneralSelfSend

  | _, [] =>
      []

  | index, .assign _ _ :: remaining =>
      selfSendsFromIndex
        bodyKey
        (index + 1)
        remaining

  | index, .send (.knownRebec _) _ _ _ :: remaining =>
      selfSendsFromIndex
        bodyKey
        (index + 1)
        remaining

  | index, .send .selfTarget message _ delay :: remaining =>
      {
        site :=
          {
            body :=
              bodyKey

            index :=
              index
          }

        message :=
          message

        delay :=
          delay
      } ::
        selfSendsFromIndex
          bodyKey
          (index + 1)
          remaining

/--
The self-sends of one body.
-/
def selfSendsOfBody
    (bodyKey : GeneralBodyKey)
    (body : DTR.GeneralBody) :
    List GeneralSelfSend :=
  selfSendsFromIndex
    bodyKey
    0
    body

/--
The self-sends of a list of message servers, in declaration order.
-/
def selfSendsOfMessageServers :
    List DTR.GeneralMessageServer →
    List GeneralSelfSend

  | [] =>
      []

  | server :: remaining =>
      selfSendsOfBody
          (.messageServer server.name)
          server.body ++
        selfSendsOfMessageServers
          remaining

/--
Every self-send of one class, in canonical order.

Constructor first, then message servers in declaration order — the same canonical order
`externalSendsOfClass` fixes, for the same reason it fixes it, and now with a second reason
that the external case did not have. Ordinals drawn from this list decide action *names*, as
they decide port names there; but they also decide the order the site reactions are declared
in, and probe section 14b measured that declaration order is what orders two action-triggered
reactions firing at one tag. Reordering this list would therefore change the observable
behaviour of the emitted program, not merely its identifiers.
-/
def selfSendsOfClass
    (reactiveClass : DTR.GeneralReactiveClass) :
    List GeneralSelfSend :=
  selfSendsOfBody
      .constructor
      reactiveClass.constructor.body ++
    selfSendsOfMessageServers
      reactiveClass.messageServers

/--
How many of these self-sends name the same message.

One field rather than the pair `countSendsTo` tests, so this is a plain `DecidableEq` test
and needs no `Prod.mk.injEq` to split. The reason its sibling uses a pair — that `DecidableEq`
and `BEq` are derived independently and nothing bridges them — applies here too and is the
reason this is `=` rather than `==`.
-/
def countSelfSendsTo
    (message : MsgName) :
    List GeneralSelfSend →
    Nat

  | [] =>
      0

  | send :: remaining =>
      if
        send.message =
          message
      then
        1 +
          countSelfSendsTo
            message
            remaining
      else
        countSelfSendsTo
          message
          remaining

/--
The 1-based ordinal of one self-send site among its class's sends of the same message.

Counts the sends of `message` lying before `site` and adds one, rather than searching a
pre-numbered list, and the difference is the whole reason this is written as a count: a count
is **total**. A site drawn from outside `allSelfSends` counts every matching send and lands one
past the last real ordinal, so the fallback cannot collide with a site that is really there.
The alternative — a lookup returning `Option` — would add a refusal cause to a function that
cannot fail, and would owe a totality induction like the one task #47 needed for ports.

That fallback is unreachable from frontend output anyway, and for a reason already proved
elsewhere: `DTR.GeneralModel.sendsResolveToMessageServers` sends `.selfTarget` to
`receivingClass? = some` on the sending class itself, so every self-send's message names a
message server of its own class and every site in a compiled body is a site this list contains.

`allSelfSends` is the **class's** list, not the body's, so this depends on
`selfSendsOfClass`'s traversal order: the constructor first, then the message servers in
declaration order, ascending index within a body. That order is therefore a correctness
property of the translation rather than a formatting choice, and it is the same order the
per-site reactions are emitted in — which, measured against `lfc` 0.11.0, is what decides
which of two same-tag firings runs first.
-/
def selfSendOrdinalAt
    (site : SendSite)
    (message : MsgName) :
    List GeneralSelfSend →
    Nat

  | [] =>
      1

  | send :: remaining =>
      if
        send.site =
          site
      then
        1
      else
        if
          send.message =
            message
        then
          1 +
            selfSendOrdinalAt
              site
              message
              remaining
        else
          selfSendOrdinalAt
            site
            message
            remaining

/--
The self-send sites of one class that target one message, in the class's traversal order.

Selection, not lookup: the result is a **list**, so nothing here can fail, no `Option` is
introduced and no refusal cause is added. A well-formed model declares one message server per
name, so applied to a message server's own name this yields that server's sites and nothing
else — the guard is what makes that true, and it is stated where it is used rather than assumed
here.

The order is `selfSendsOfClass`'s: constructor first, then message servers in declaration
order, ascending statement index within a body. That order is a **correctness property** and
not a formatting one, because F56 section 14b measured that two reactions triggered at one tag
fire in reaction *declaration* order. The reactions this list drives are emitted in its order,
so a body's two sends to one message are delivered in the order the body wrote them.

Recursive rather than `List.filter` for the reason `NameGeneration.lean` gives for avoiding
`String.capitalize`: this development depends on no library function whose name has churned
across Lean releases, and it also gets usable `nil`/`cons` equations for free.
-/
def generalSelfSendSitesOf
    (message : MsgName) :
    List GeneralSelfSend →
    List GeneralSelfSend

  | [] =>
      []

  | send :: remaining =>
      if
        send.message =
          message
      then
        send ::
          generalSelfSendSitesOf
            message
            remaining
      else
        generalSelfSendSitesOf
          message
          remaining

/--
The suffix that distinguishes one self-send site's action from its message's other sites.

Empty when the class sends to this message **at most** once, and the site's 1-based ordinal
otherwise — the same rule `generalSiteSuffixFor` applies to ports.

**Why `at most` and not `exactly`.** A message server nothing self-sends has zero sites, and
the zero case has to land in the empty-suffix branch: it keeps `actionNameFor`'s spelling, so
the action list stays at minimum one action per message server, and every fixture whose
message servers are reached only from outside is byte-identical after this repair. An `= 1`
test sends the zero case to `toString ordinal` instead, numbering a site that does not exist.

**MEASURED 2026-08-23, correcting what this docstring claimed yesterday.** It said that
"every committed positive fixture sends to each of its message servers at most once per class,
so ... this repair changes no expected LF text that was already green". The second half is
false. Ten committed positive fixtures, five self-send at all, and of those `fan-in`,
`send-sites`, `two-classes`, `two-instances` and `priorities` all send *distinct* messages once
each, so they are unchanged. `keep-alive.rebeca` is not: it sends `self.keepAlive()` at its
constructor's line 7 and again at line 11 inside `msgsrv keepAlive`, which is two sites on one
message, so its single `keepAlive_action` becomes two suffixed actions with two reactions and
its expected LF does change. That fixture is the near-miss F56 was found through — both
schedules are `after(1)` from bodies that run at different times, so they never share a tag and
no message is actually lost — and this is the second time a claim about it has been written
from memory instead of from the file.

Takes the message rather than the send it belongs to, because the *declaration* side and the
*schedule* side reach this function from different data — a message server and a statement —
and only the message is common to both.
-/
def generalActionSiteSuffixFor
    (allSelfSends : List GeneralSelfSend)
    (message : MsgName)
    (ordinal : Nat) :
    String :=
  if
    countSelfSendsTo
        message
        allSelfSends ≤
      1
  then
    ""
  else
    toString ordinal

/--
The name of the logical action that carries one self-send site's message.

**The single place a site's action name is computed.** Both the `schedule` statement that
sends the message and the action declaration that receives it call this, on the same site, so
they agree by construction. Numbering the sites once and deriving the two names separately —
the first shape this took — would have left two computations to keep in step, and F56 is a
finding about exactly that class of silent divergence.
-/
def generalActionNameAtSite
    (allSelfSends : List GeneralSelfSend)
    (site : SendSite)
    (message : MsgName) :
    ActionName :=
  generalActionNameFor
    message
    (generalActionSiteSuffixFor
      allSelfSends
      message
      (selfSendOrdinalAt
        site
        message
        allSelfSends))

/--
The data a statement is compiled against, beyond the statement itself.

Two facts about *where* a statement sits, carried as one record so that `compileGeneralStmt`
and `compileGeneralBody` keep a fixed arity. That is not only economy: adding a field costs
nothing at the three dozen call sites that merely pass this argument along, and stage H will
need to add one, because a loop body is a body whose statement index is no longer a position
in a flat list.

* `bodyKey` is the body the statement occurs in. With the statement's index it makes the
  `SendSite` that both the output-port environment and the action names are keyed by.
* `selfSends` is every self-send of the **enclosing class**, not of this body, because the
  action-name suffix is the site's ordinal among that class's sends of the same message.
  Per-body numbering would be a weaker repair that looks like this one: two bodies of one
  class each sending `m` once would both take the empty suffix and share a single action,
  which loses a message whenever those two bodies run at the **same tag**.

  `keep-alive.rebeca` has the sharing shape but *not* the tag collision — its two schedules
  are `after(1)` from bodies that run at different times — so even per-body numbering would
  lose nothing there. An action shared between two bodies is not sufficient for F56's loss; a
  shared tag is the other half of it. So that fixture is a near-miss rather than the witness
  this repair is tested with, which is a weaker reason than the one this paragraph gave until
  2026-08-23, when it claimed the fixture would "reproduce exactly the loss F56 records".

  That claim was false, and it is the third about this fixture in this repository written from
  memory instead of from the file — the second being the one the paragraph above
  `generalActionSiteSuffixFor` records, sixty lines above this one and in the same task. Which
  is the point worth keeping: writing that correction did not stop the next false claim about
  the same fixture from being written immediately below it.
-/
structure GeneralBodyContext where
  bodyKey :
    GeneralBodyKey

  selfSends :
    List GeneralSelfSend

deriving Repr, DecidableEq, BEq, Inhabited

/-!
## What a port carries
-/

/--
The payload of the port that carries one message.

Three arms, and the arity decides which. Arity one is a bare scalar, so `int` and `bool`
ports look exactly like the ones stage C emitted and the parameter *name* is dropped —
which is safe because the name a reaction body reads comes from the message server's own
formal list, carried on the reaction, and never from the port. Arity two and above is a
struct, and the struct is named `<Reactor>_<Action>_Args` after the **receiving** reactor
and the receiving message server's logical action, which is the load-bearing agreement of
this whole stage: the same struct declaration serves the receiver's logical action, the
sender's output port and the receiver's input port, so a payload crosses a connection and
lands in a `schedule` call without a conversion anywhere. `lfc 0.11.0` was measured to
accept one `public preamble` struct in exactly those three positions — probe
`struct_as_port_type` — and this is the function that depends on that measurement.

Arity zero is refused, and it is the one refusal in this file a well-formed model reaches.
A parameterless message server is legal Rebeca and stage D translated it perfectly well,
because a logical action can carry nothing; a *port* carrying nothing has no measured
spelling. §5.3 records the choice and §11.2 records the probe as owed. The diagnostic
therefore names the missing measurement rather than blaming the model, because the model is
not at fault.

The receiver's class is taken as a `ClassName` and turned into a `ReactorName` here rather
than being passed as one, so that `reactorNameFor` is applied at one place in this file and
a reader can see that the struct name and the reactor declaration cannot disagree.
-/
def generalPortPayloadFor
    (receiverClass : ClassName)
    (message : MsgName)
    (parameters : List DTR.GeneralTypedParameter) :
    Except String LF.GeneralPortPayload :=
  match parameters with

  | [] =>
      .error
        ("message server `" ++
          receiverClass.value ++
          "`.`" ++
          message.value ++
          "` takes no parameters, so the port that would carry it has no payload; " ++
          "whether the target accepts a port with no value type is unmeasured, " ++
          "so this translation refuses rather than guesses")

  | [parameter] =>
      .ok
        (.scalar
          (compileGeneralType
            parameter.declaredType))

  | first :: second :: remaining =>
      .ok
        (.struct
          (reactorNameFor
            receiverClass)
          (actionNameFor
            message)
          ((first ::
              second ::
              remaining).map
            compileGeneralTypedParameter))

/-!
## A class's output-port environment

The context §7.1 adopted in place of passing a whole model down to statement level. It is
built once per class, it is a function of the class and the class table alone, and every
interesting refusal of this stage happens while building it — which is what leaves
`compileGeneralStmt`'s external-send arm as a lookup with a defensive failure rather than
the stage boundary it is today.
-/

/--
One output port of one class, with everything the rest of the stage needs about it.

A named structure where §7.1 writes a six-component tuple, and the fields are one more than
six. The extra field is `receiverClass`, and it earns its place: the payload is built from
the message server of the class the *known rebec declaration* names, while the connection
lands on the class of the instance the *binding* names. Those two agree in any well-formed
model — `DTR.GeneralModel.bindingsMatchClass` checks exactly that, second half — but nothing
in this file checks well-formedness, so carrying the declared class lets `routesOf` compare
the two and refuse. Without it, a model whose binding disagreed with its declaration would
produce an input port whose payload struct is named after a different reactor, and the first
thing to notice would be a C++ compiler.

The names are the other half of the reason for a structure. Six positional components of
which two are `PortName`-shaped and two are name-shaped is a tuple whose components can be
swapped without a type error, and this is the record that decides generated identifiers.
-/
structure GeneralOutputPortEntry where
  site :
    SendSite

  knownRebec :
    KnownRebecName

  message :
    MsgName

  receiverClass :
    ClassName

  outputPort :
    PortName

  payload :
    LF.GeneralPortPayload

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

/--
Everything one class sends outward, in canonical site order.

An `abbrev` over a list rather than a structure wrapping one, because there is nothing to
carry beside the entries: the class this belongs to is always in the hand of whoever asked
for it. Nothing is merged, so the length of this list is exactly the number of external send
sites in the class, and that is the count the port declarations, the connections and §III-F's
cost bound all range over.
-/
abbrev GeneralOutputPortEnv :=
  List GeneralOutputPortEntry

/--
The entry at one send site, if there is one.

Explicit recursion over decidable equality of sites, for the same reason the four DTR
lookups are written that way. This is the function `compileGeneralStmt` will call, and its
`none` means *the class sends on a rebec it does not declare* — which D6 already forbids, so
the caller's refusal is defensive.
-/
def generalEntryAtSite? :
    GeneralOutputPortEnv →
    SendSite →
    Option GeneralOutputPortEntry

  | [], _ =>
      none

  | entry :: remaining, site =>
      if entry.site = site then
        some entry
      else
        generalEntryAtSite?
          remaining
          site

/--
Render a body key for a diagnostic.
-/
def renderGeneralBodyKey :
    GeneralBodyKey →
    String

  | .constructor =>
      "the constructor"

  | .messageServer message =>
      "message server `" ++
        message.value ++
        "`"

/--
Render a send site for a diagnostic.

The index is the statement's position in its body, counted from zero, and the diagnostic
says so, because a reader who has to count statements to find the offending send should not
also have to guess where counting starts.
-/
def renderGeneralSendSite
    (site : SendSite) :
    String :=
  renderGeneralBodyKey
      site.body ++
    ", statement at index " ++
    toString site.index ++
    " counting from zero"

/--
Resolve one external send into an output port.

§7.1's five steps in order, and the order is the point: the first thing to fail is the thing
furthest from the generated code, so a diagnostic names a cause rather than a symptom.

1. the known rebec, through this class's declarations;
2. the declared class of that rebec, through the class table;
3. the message server of that name on that class;
4. the payload, from that server's parameters;
5. the port name, from the message, the rebec and the site's suffix.

Steps 1 to 3 are refusals a well-formed model never reaches, and it is worth being exact
about which conjunct closes each one, because the obvious answer is wrong for two of them.
`sendTargetsDeclared` — D6 — closes step 1. Steps 2 *and* 3 are both closed by
`sendsResolveToMessageServers`, whose `statementResolves` goes through
`DTR.GeneralModel.receivingClass?`, and that function returns `none` exactly when the rebec's
declared class is missing from the class table; `bindingsMatchDeclarations` does not close
step 2, because a class that is never instantiated has no bindings to check and may declare a
known rebec of a class the model never declares — it just may not *send* to it. Each check is
kept because this function is total on its own argument types and a hand-built class reaches
it. Step 4's refusal is *not* defensive — see `generalPortPayloadFor`.

The delay is copied out of the send and never compared with anything, which is §6's whole
content: two sites are two ports and two connections, so two different delays are not a
conflict and two equal ones are not a collision.
-/
def generalOutputPortEntryFor
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass)
    (allSends : List GeneralExternalSend)
    (send : GeneralExternalSend)
    (ordinal : Nat) :
    Except String GeneralOutputPortEntry :=
  match sendingClass.knownRebec? send.knownRebec with

  | none =>
      .error
        ("class `" ++
          sendingClass.name.value ++
          "` sends to `" ++
          send.knownRebec.value ++
          "` at " ++
          renderGeneralSendSite send.site ++
          ", but declares no known rebec of that name")

  | some declaration =>
      match DTR.findClass? classes declaration.className with

      | none =>
          .error
            ("known rebec `" ++
              send.knownRebec.value ++
              "` of class `" ++
              sendingClass.name.value ++
              "` is declared to have class `" ++
              declaration.className.value ++
              "`, which the model does not declare")

      | some receivingClass =>
          match receivingClass.messageServer? send.message with

          | none =>
              .error
                ("class `" ++
                  sendingClass.name.value ++
                  "` sends `" ++
                  send.message.value ++
                  "` to `" ++
                  send.knownRebec.value ++
                  "` at " ++
                  renderGeneralSendSite send.site ++
                  ", but class `" ++
                  receivingClass.name.value ++
                  "` declares no message server of that name")

          | some receivingServer =>
              match
                  generalPortPayloadFor
                    receivingClass.name
                    send.message
                    receivingServer.parameters with

              | .error diagnostic =>
                  .error diagnostic

              | .ok portPayload =>
                  .ok
                    {
                      site :=
                        send.site

                      knownRebec :=
                        send.knownRebec

                      message :=
                        send.message

                      receiverClass :=
                        receivingClass.name

                      outputPort :=
                        outputPortNameFor
                          send.message
                          send.knownRebec
                          (generalSiteSuffixFor
                            allSends
                            send
                            ordinal)

                      payload :=
                        portPayload

                      delay :=
                        send.delay
                    }

/--
Resolve a numbered send list, stopping at the first refusal.

Explicit recursion rather than `mapM`, matching `compileGeneralBody`: the `nil` equation
holds by `rfl` and order preservation is provable by an induction of the same shape.
-/
def generalOutputPortEntriesOf
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass)
    (allSends : List GeneralExternalSend) :
    List (GeneralExternalSend × Nat) →
    Except String GeneralOutputPortEnv

  | [] =>
      .ok []

  | (send, ordinal) :: remaining =>
      match
          generalOutputPortEntryFor
            classes
            sendingClass
            allSends
            send
            ordinal with

      | .error diagnostic =>
          .error diagnostic

      | .ok entry =>
          match
              generalOutputPortEntriesOf
                classes
                sendingClass
                allSends
                remaining with

          | .error diagnostic =>
              .error diagnostic

          | .ok entries =>
              .ok
                (entry ::
                  entries)

/--
One class's output-port environment.

A function of the class and the class table, and of nothing else — no instance, no model.
§7.2 gives the reason this asymmetry is forced rather than chosen: a class with **no
instances** still compiles to a reactor whose bodies still contain `set()` calls, so if
output ports came from the model's instances they would be empty for such a class and
`stmtWellFormed` would fail on the translator's own output.

Being a function of the class alone is also what makes it safe for `routesOf` to call this
once per *instance* rather than caching one result per class. Two instances of one class get
equal environments because the argument is equal, which is a fact a proof can use directly;
a memo table would need a lemma saying the table agrees with this function. The cost is
linear in instances times send sites, and if a model ever arrives where that matters, the
table is a local change behind this signature.
-/
def outputPortEnvOf
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass) :
    Except String GeneralOutputPortEnv :=
  generalOutputPortEntriesOf
    classes
    sendingClass
    (externalSendsOfClass
      sendingClass)
    (numberedExternalSendsOfClass
      sendingClass)

/-!
## The routing table

One row per (sender instance, send site). Everything the target's topology consists of is a
projection of this list, and the reason to build the list first and project afterwards is
that the two ends of a connection then come from one row and cannot disagree.
-/

/--
One arrow of the target, fully resolved.

Ten fields, four of which could be recomputed from the others and are carried anyway. That
is the design's choice and it is the load-bearing one: `outputPort` is a *string* that a
naming rule produced, and the input port's name is that same string with a suffix, so the
only way the two ends of a connection can drift is if two call sites recompute the name
independently. Carrying it makes that impossible rather than unlikely.

`site` is carried because it is what makes two rows distinguishable — and because stage F,
which owes §III-D's same-tag ordering, will need to say which statement an arrow came from.
`senderClass` and `receiverClass` are carried because the port declarations are projected
per *reactor*, and a reactor is a class.
-/
structure GeneralRoute where
  senderInstance :
    ActorName

  senderClass :
    ClassName

  site :
    SendSite

  knownRebec :
    KnownRebecName

  message :
    MsgName

  receiverInstance :
    ActorName

  receiverClass :
    ClassName

  outputPort :
    PortName

  payload :
    LF.GeneralPortPayload

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

/--
The input port an arrow lands on.

Derived and never stored, unlike the output port, and the asymmetry is deliberate: the
output port's name is *chosen* by a rule with a site suffix in it, so it has to be carried
from the place that chose it; the input port's name is a function of the output port's, so
carrying it would be carrying the same information twice. This is the single site that knows
the rule, and both the port declaration and the connection's target endpoint go through it.
-/
def generalInputPortOfRoute
    (route : GeneralRoute) :
    PortName :=
  inputPortNameFor
    route.senderInstance
    route.outputPort

/--
Resolve one of a sender instance's output ports into a route.

Three refusals, all three of which a well-formed model reaches never:
`bindingsMatchClass` requires the bound name sequence to equal the declared one, so a
declared rebec is bound; it requires every bound actor to exist; and it requires that actor's
class to be the one the declaration names.

The third check is the one worth having anyway. The payload on the entry was built from the
message server of the class the *declaration* names, and the arrow lands on the class of the
instance the *binding* names. If those differ, the receiving reactor gets an input port whose
payload struct belongs to another reactor, and every layer between here and a C++ compiler
would carry it without complaint.
-/
def generalRouteFor
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance)
    (entry : GeneralOutputPortEntry) :
    Except String GeneralRoute :=
  match Store.lookup actor.bindings entry.knownRebec with

  | none =>
      .error
        ("instance `" ++
          actor.name.value ++
          "` binds no known rebec named `" ++
          entry.knownRebec.value ++
          "`, which its class `" ++
          actor.className.value ++
          "` declares and sends to")

  | some receiverInstance =>
      match model.actor? receiverInstance with

      | none =>
          .error
            ("instance `" ++
              actor.name.value ++
              "` binds `" ++
              entry.knownRebec.value ++
              "` to `" ++
              receiverInstance.value ++
              "`, which the model does not instantiate")

      | some receiver =>
          if receiver.className = entry.receiverClass then
            .ok
              {
                senderInstance :=
                  actor.name

                senderClass :=
                  actor.className

                site :=
                  entry.site

                knownRebec :=
                  entry.knownRebec

                message :=
                  entry.message

                receiverInstance :=
                  receiver.name

                receiverClass :=
                  receiver.className

                outputPort :=
                  entry.outputPort

                payload :=
                  entry.payload

                delay :=
                  entry.delay
              }
          else
            .error
              ("instance `" ++
                actor.name.value ++
                "` binds `" ++
                entry.knownRebec.value ++
                "` to `" ++
                receiver.name.value ++
                "` of class `" ++
                receiver.className.value ++
                "`, but its own class declares that rebec to have class `" ++
                entry.receiverClass.value ++
                "`, so the payload of port `" ++
                entry.outputPort.value ++
                "` was built from the wrong message server")

/--
One sender instance's routes, in canonical site order.
-/
def routesOfEntries
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance) :
    GeneralOutputPortEnv →
    Except String (List GeneralRoute)

  | [] =>
      .ok []

  | entry :: remaining =>
      match
          generalRouteFor
            model
            actor
            entry with

      | .error diagnostic =>
          .error diagnostic

      | .ok route =>
          match
              routesOfEntries
                model
                actor
                remaining with

          | .error diagnostic =>
              .error diagnostic

          | .ok routes =>
              .ok
                (route ::
                  routes)

/--
The routes of a list of instances, in the order the instances arrive.
-/
def routesOfInstances
    (model : DTR.GeneralModel) :
    List DTR.GeneralActorInstance →
    Except String (List GeneralRoute)

  | [] =>
      .ok []

  | actor :: remaining =>
      match model.class? actor.className with

      | none =>
          .error
            ("instance `" ++
              actor.name.value ++
              "` instantiates class `" ++
              actor.className.value ++
              "`, which the model does not declare")

      | some sendingClass =>
          match
              outputPortEnvOf
                model.classes
                sendingClass with

          | .error diagnostic =>
              .error diagnostic

          | .ok env =>
              match
                  routesOfEntries
                    model
                    actor
                    env with

              | .error diagnostic =>
                  .error diagnostic

              | .ok routes =>
                  match
                      routesOfInstances
                        model
                        remaining with

                  | .error diagnostic =>
                      .error diagnostic

                  | .ok remainingRoutes =>
                      .ok
                        (routes ++
                          remainingRoutes)

/--
The model's routing table, in main-block declaration order.

Instance order is the order of `model.instances`, which is main-block declaration order,
and within one instance the order is canonical site order. Nothing sorts, here or anywhere
below: connection order is observable in the emitted program, so a translation that sorted
would be making a semantic choice in a projection.

`Store.lookup actor.bindings` is the resolution used, and `DTR.GeneralModel`'s own
`resolve_topology_of_actor` proves it agrees with resolution through the derived topology —
which is what lets a later correctness argument talk about either one.
-/
def routesOf
    (model : DTR.GeneralModel) :
    Except String (List GeneralRoute) :=
  routesOfInstances
    model
    model.instances

/-!
## The three projections

Output ports from a class's environment, input ports and connections from the model's
routes. Nothing here deduplicates, and that is a decision rather than an omission: two
declarations of one port name is a defect this stage's `Nodup` guard on
`LF.GeneralReactor.declaredNames` reports with the offending name in the diagnostic, whereas
a `dedup` here would collapse two ports that carry *different payloads* into whichever one
came first and emit a program that compiles and drops messages. The printer's preamble
already had to make this choice for structs and made the other one, deliberately and under
protest — that is F41 — and the difference is that a struct declaration is not a name a
`set()` call can miss.
-/

/--
One output port declaration.
-/
def generalOutputPortDeclOf
    (entry : GeneralOutputPortEntry) :
    LF.GeneralPortDecl where

  name :=
    entry.outputPort

  payload :=
    entry.payload

/--
A class's output ports, in canonical site order.

From the class's environment and never from the routes, which is §7.2's forced asymmetry: a
class with no instances still compiles to a reactor whose bodies still call `set()`.
-/
def generalOutputPortsOf
    (env : GeneralOutputPortEnv) :
    List LF.GeneralPortDecl :=
  env.map
    generalOutputPortDeclOf

/--
One input port declaration, named after the arrow that lands on it.
-/
def generalInputPortDeclOf
    (route : GeneralRoute) :
    LF.GeneralPortDecl where

  name :=
    generalInputPortOfRoute
      route

  payload :=
    route.payload

/--
The routes that land on one class, in route order.

Two things about this filter are load-bearing, and both are reasons it is a named function
rather than an `if` inside each of the two places that need it. The input port declarations
and the port-triggered reactions of §7.3 must range over **the same** routes — a reaction
triggered by a port the reactor does not declare fails `triggerWellFormed`, and a port nothing
reads is a silent message sink — so the two projections are written as maps over one filter
and the agreement is definitional rather than a coincidence between two conditions. And the
filter is what a proof about either projection inducts over.
-/
def generalRoutesIntoClass
    (className : ClassName) :
    List GeneralRoute →
    List GeneralRoute

  | [] =>
      []

  | route :: remaining =>
      if route.receiverClass = className then
        route ::
          generalRoutesIntoClass
            className
            remaining
      else
        generalRoutesIntoClass
          className
          remaining

/--
The routes that land on one message server of one class, in route order.

The unit §7.3 groups reactions by. Written as its own recursion rather than as
`generalRoutesIntoClass` followed by a second filter, because the two are used at different
levels and a composition would make every statement about this one unfold the other; the pair
comparison is the same `Prod` decidable equality `countSendsTo` uses, for the same reason.

Route order is main-block instance-declaration order, and that is all it is. §7.3 says so in
as many words and it is worth repeating at the definition: for a fixture whose instances are
declared in priority order the two orders coincide, and that coincidence is **not** a result.
Stage F owns the claim that reaction order realizes priority.
-/
def generalRoutesIntoMessageServer
    (className : ClassName)
    (message : MsgName) :
    List GeneralRoute →
    List GeneralRoute

  | [] =>
      []

  | route :: remaining =>
      if
          (
            route.receiverClass,
            route.message
          ) =
          (
            className,
            message
          ) then
        route ::
          generalRoutesIntoMessageServer
            className
            message
            remaining
      else
        generalRoutesIntoMessageServer
          className
          message
          remaining

/--
The input ports of one class, in route order.

The union over the class's instances, which is what makes this a projection of the *model*
rather than of the class: `lfc 0.11.0` rejects many-to-one connections, so each sender
instance needs its own input port on the receiver, and a reactor with two instances receiving
from two different senders declares both ports. Every instance then has an input port that
nothing connects to, and that is legal — measured, not assumed, in the probe that also
measured a struct as a port type.

No deduplication. The argument that none is needed used to be written out here as an argument
rather than left as a silence, which is what made it checkable — and it did not survive the
check. It ran: an input port's name is built from the sender instance and the sender's output
port name; a sender instance's output port names are distinct within its class by step 4 of the
environment; and one instance binds one known rebec to one instance, so one (sender instance,
output port) pair contributes exactly one arrow. Two rows with equal input port names on one
class would therefore have to be one row.

**Both of those premises are false, and finding F48 measured them.** `outputPortNameFor` is not
injective — `Relico/Translation/NameGeneration.lean` says so on the function itself, listing two
independent collision channels — so two send sites of one class can carry one output port name,
and F48's model produced exactly that: an output port environment whose two entries are both
`reportToToHub`. And `bindingsMatchClass` permits aliasing, two different known rebecs bound to
one actor, so a (sender instance, output port) pair does not determine the arrow either. Two rows
with equal input port names on one class are therefore possible, and F48 exhibits them.

The conclusion the argument was aimed at is still the right one, reached by the other route the
argument already gave: the `Nodup` guard says so by name at the point of failure, so rely on the
guard and not on a claim about names. Deduplicating here would not even be a fix — it would merge
the two colliding declarations while `generalConnectionsOf` went on mapping over the same routes,
so the program would carry two arrows onto one input port with nothing on this side left to
notice, which is the many-to-one connection `lfc 0.11.0` rejects. A collision has to be refused,
not absorbed.
-/
def generalInputPortsOf
    (className : ClassName)
    (routes : List GeneralRoute) :
    List LF.GeneralPortDecl :=
  (generalRoutesIntoClass
    className
    routes).map
      generalInputPortDeclOf

/--
One connection.

The delay lands here and nowhere else. A self-send's `after` becomes the delay argument of a
`schedule` call inside a reaction; an external send's `after` becomes `after N msec` on the
arrow, because the message leaves the sender at the tag the reaction runs and has to arrive
later at the *receiver*. Two sends to one pair with different delays are two rows, hence two
ports and two arrows, which is the case that made a port a per-site thing.
-/
def generalConnectionOf
    (route : GeneralRoute) :
    LF.GeneralConnection where

  sourceInstance :=
    route.senderInstance

  sourcePort :=
    route.outputPort

  targetInstance :=
    route.receiverInstance

  targetPort :=
    generalInputPortOfRoute
      route

  delay :=
    route.delay

/--
The model's connections, one per route, in route order.

`targetEndpointsUnique` does **not** hold by construction, and this docstring said it did until
finding F49. The claim was that a target endpoint is a receiver instance together with an input
port name, that the input port name determines the sender instance and that sender's output port
name, and that `inputPortNameFor_outputPort_injective` is the cancellation turning "determines"
into a theorem for the second of those.

That theorem is true and does not carry the weight asked of it. It says one sender's two
*different* output ports cannot yield one input port name. It says nothing about two routes that
share one output port *name*, which is exactly what `outputPortNameFor`'s non-injectivity permits
and what F48 measured on translation output. So two rows can share a target endpoint,
`compileGeneralModel` can assemble a program with a many-to-one connection in it, and
`guardGeneralProgram` is what refuses it — checked, not earned, which is how
`Relico/Translation/GeneralBasic.lean` states it in both of the places that state it correctly.

The clause cannot be dropped as redundant either. F49 exhibits a program satisfying the other
eight clauses of `LF.GeneralProgram.wellFormed` and failing this one, so it is independent of
them, and independence is a stronger reason to keep a clause than the absence of a construction
proof is. What is true is *relative*: for connections and input ports built from the **same**
routes, two connections sharing a target endpoint are two distinct rows, both survive
`generalRoutesIntoClass`, and `generalInputPortsOf` does not deduplicate, so the shared name
duplicates in the receiver's `declaredNames` and `reactorsWellFormed` fails first. That is a
statement about `compileGeneralModel` rather than about this function, and it is where the
by-construction intuition actually belongs.
-/
def generalConnectionsOf
    (routes : List GeneralRoute) :
    List LF.GeneralConnection :=
  routes.map
    generalConnectionOf

/-!
## The equations the next stage rewrites with

Five `rfl` facts and one induction. The `rfl` facts are the empty cases of everything above,
stated because `Relico/Translation/GeneralBasic.lean`'s boundary theorems — the ones that say
in arithmetic what a stage has and has not done — are proved by rewriting with them. The
induction is the one property of `generalEntryAtSite?` a caller needs: a lookup that succeeds
returns the entry *at the site asked for*, which is what lets a statement compiler use the
entry's port name and know it belongs to the statement it is compiling.
-/

@[simp]
theorem externalSendsOfBody_nil
    (bodyKey : GeneralBodyKey) :
    externalSendsOfBody
        bodyKey
        [] =
      [] := by
  rfl

@[simp]
theorem generalOutputPortEntriesOf_nil
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass)
    (allSends : List GeneralExternalSend) :
    generalOutputPortEntriesOf
        classes
        sendingClass
        allSends
        [] =
      .ok [] := by
  rfl

@[simp]
theorem routesOfInstances_nil
    (model : DTR.GeneralModel) :
    routesOfInstances
        model
        [] =
      .ok [] := by
  rfl

@[simp]
theorem generalOutputPortsOf_nil :
    generalOutputPortsOf [] =
      [] := by
  rfl

@[simp]
theorem generalInputPortsOf_nil
    (className : ClassName) :
    generalInputPortsOf
        className
        [] =
      [] := by
  rfl

@[simp]
theorem generalConnectionsOf_nil :
    generalConnectionsOf [] =
      [] := by
  rfl

/--
A successful site lookup returns the entry at that site.

The whole content of the lemma is that `generalEntryAtSite?` does not return a neighbour, and
the reason to prove it rather than read it off the definition is that the statement compiler
uses the returned entry's *port name* while the site is what it has in hand. Without this, the
step from "the lookup succeeded" to "this port belongs to this statement" is an appeal to the
code.
-/
theorem generalEntryAtSite?_site
    (env : GeneralOutputPortEnv)
    (site : SendSite)
    (entry : GeneralOutputPortEntry) :
    generalEntryAtSite?
          env
          site =
        some entry →
      entry.site = site := by

  induction env with

  | nil =>
      intro hFound

      simp [
        generalEntryAtSite?
      ] at hFound

  | cons candidate remaining inductionHypothesis =>
      intro hFound

      by_cases hMatch :
          candidate.site = site

      · simp [
          generalEntryAtSite?,
          hMatch
        ] at hFound

        subst hFound

        exact hMatch

      · simp [
          generalEntryAtSite?,
          hMatch
        ] at hFound

        exact
          inductionHypothesis
            hFound

/-!
## Site totality

Task #47, and the reason `compileGeneralStmt`'s `none` arm carries a message addressed to a
translator author rather than to a user: an external send whose site is missing from its own
class's environment is a defect here, not something anybody can write. The arm was left
reachable-in-principle when it landed because proving a two-hundred-line induction against a
module that had never elaborated would have made a build failure undiagnosable.

The chain has four links and each is separately usable. A successful lookup returns an
element of the environment; an environment built from a numbered send list has exactly that
list's sites; numbering preserves the sends; so every send of a class is looked up
successfully in that class's environment. `Relico/Translation/GeneralBasic.lean` then walks a
body once more and turns that into totality of the body compiler.

The order matters for reading: everything here is about `outputPortEnvOf` and says nothing
about *ports*. Two sites can share a port name — the naming rule is not injective, finding
F34 — and no lemma in this section pretends otherwise. Port-name distinctness is a property
of accepted *programs* and it is established where the guard is, not here.
-/

/--
The `cons` equation when the head is the site asked for.

Split into two directed equations rather than proved inline at each use, for the reason
`compileGeneralBody`'s three `cons` lemmas give: a `match` written inside a theorem
statement elaborates to a fresh matcher constant, and every proof that then rewrites with
the equation depends on that constant agreeing definitionally with the one in the
definition. Two `rw`-able equations carry the same content and depend on nothing.
-/
theorem generalEntryAtSite?_cons_self
    (entry : GeneralOutputPortEntry)
    (remaining : GeneralOutputPortEnv)
    (site : SendSite)
    (hMatch :
      entry.site = site) :
    generalEntryAtSite?
        (entry :: remaining)
        site =
      some entry := by
  simp [
    generalEntryAtSite?,
    hMatch
  ]

/--
The `cons` equation when the head is some other site.
-/
theorem generalEntryAtSite?_cons_of_ne
    (entry : GeneralOutputPortEntry)
    (remaining : GeneralOutputPortEnv)
    (site : SendSite)
    (hMatch :
      ¬ entry.site = site) :
    generalEntryAtSite?
        (entry :: remaining)
        site =
      generalEntryAtSite?
        remaining
        site := by
  simp [
    generalEntryAtSite?,
    hMatch
  ]

/--
A successful lookup returns an entry the environment actually holds.

Together with `generalEntryAtSite?_site` this is everything a caller can want from the
lookup: the entry is *in* the environment, so any property established for the whole
environment holds of it, and its site is the site asked for, so the port name it carries
belongs to the statement in hand. The pair is what lets a later theorem about port names
quantify over the environment instead of over the lookup.
-/
theorem generalEntryAtSite?_mem
    (env : GeneralOutputPortEnv)
    (site : SendSite)
    (entry : GeneralOutputPortEntry) :
    generalEntryAtSite?
          env
          site =
        some entry →
      entry ∈ env := by

  induction env with

  | nil =>
      intro hFound

      simp [
        generalEntryAtSite?
      ] at hFound

  | cons candidate remaining inductionHypothesis =>
      intro hFound

      by_cases hMatch :
          candidate.site = site

      · rw [
          generalEntryAtSite?_cons_self
            candidate
            remaining
            site
            hMatch
        ] at hFound

        injection hFound with hEntry

        subst hEntry

        simp

      · rw [
          generalEntryAtSite?_cons_of_ne
            candidate
            remaining
            site
            hMatch
        ] at hFound

        rw [
          List.mem_cons
        ]

        exact
          Or.inr
            (inductionHypothesis
              hFound)

/--
A site the environment lists is a site the lookup finds.

Stated as an existential rather than with `Option.isSome`, because every consumer wants the
entry: the statement compiler needs its port name and the totality proof needs to hand it to
`compileGeneralStmt`. `isSome` would force each of them to re-destruct an option that this
proof has already destructed.

The entry produced is not necessarily the one whose membership supplied the site — the lookup
returns the *first* match. That is why the conclusion names no particular entry, and it is
also why nothing here needs the environment's sites to be distinct.
-/
theorem exists_generalEntryAtSite?_of_mem_sites
    (env : GeneralOutputPortEnv)
    (site : SendSite) :
    site ∈
        env.map
          (fun entry =>
            entry.site) →
      ∃ entry,
        generalEntryAtSite?
            env
            site =
          some entry := by

  induction env with

  | nil =>
      intro hMember

      simp at hMember

  | cons candidate remaining inductionHypothesis =>
      intro hMember

      by_cases hMatch :
          candidate.site = site

      · exact
          ⟨
            candidate,
            generalEntryAtSite?_cons_self
              candidate
              remaining
              site
              hMatch
          ⟩

      · rw [
          generalEntryAtSite?_cons_of_ne
            candidate
            remaining
            site
            hMatch
        ]

        rw [
          List.map_cons,
          List.mem_cons
        ] at hMember

        cases hMember with

        | inl hHead =>
            exact
              absurd
                hHead.symm
                hMatch

        | inr hTail =>
            exact
              inductionHypothesis
                hTail

/-!
### Inverting one entry

`generalOutputPortEntryFor` is four nested matches deep and the site-map lemma below needs one
fact out of it: a resolved entry sits at the site of the send it was resolved from. Getting
that fact requires ruling out the four refusals, and the four are ruled out the way this
repository rules out every other one — with a forward equation per outcome, rewritten into the
hypothesis. `docs/STAGE_D_DESIGN.md` §9.1's argument applies unchanged: no `match` appears in
any statement here, so no proof below depends on a matcher constant elaborated inside a
theorem.

The four refusals are stated as `¬ … = .ok entry` rather than as `∃ diagnostic, … = .error
diagnostic`. Both are true; the negative form is what an inversion consumes, and it avoids
writing four long diagnostic strings into four theorem statements where a later edit to a
message would break a proof that has nothing to do with messages.
-/

/--
A send naming a rebec its class does not declare resolves to no entry.
-/
private theorem generalOutputPortEntryFor_ne_ok_of_knownRebec_none
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    (hKnown :
      sendingClass.knownRebec?
          send.knownRebec =
        none)
    (entry : GeneralOutputPortEntry) :
    ¬ generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry := by
  simp [
    generalOutputPortEntryFor,
    hKnown
  ]

/--
A known rebec whose declared class the model does not declare resolves to no entry.
-/
private theorem generalOutputPortEntryFor_ne_ok_of_class_none
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {declaration : DTR.GeneralKnownRebecDecl}
    (hKnown :
      sendingClass.knownRebec?
          send.knownRebec =
        some declaration)
    (hClass :
      DTR.findClass?
          classes
          declaration.className =
        none)
    (entry : GeneralOutputPortEntry) :
    ¬ generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry := by
  simp [
    generalOutputPortEntryFor,
    hKnown,
    hClass
  ]

/--
A message the receiving class does not declare resolves to no entry.
-/
private theorem generalOutputPortEntryFor_ne_ok_of_messageServer_none
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {declaration : DTR.GeneralKnownRebecDecl}
    {receivingClass : DTR.GeneralReactiveClass}
    (hKnown :
      sendingClass.knownRebec?
          send.knownRebec =
        some declaration)
    (hClass :
      DTR.findClass?
          classes
          declaration.className =
        some receivingClass)
    (hServer :
      receivingClass.messageServer?
          send.message =
        none)
    (entry : GeneralOutputPortEntry) :
    ¬ generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry := by
  simp [
    generalOutputPortEntryFor,
    hKnown,
    hClass,
    hServer
  ]

/--
A message server whose parameters admit no port payload resolves to no entry.

This is the one of the four that is a *translation* limit rather than a document defect: an
arity-zero external send has no measured port declaration to compile to, which is finding F36's
open residue.
-/
private theorem generalOutputPortEntryFor_ne_ok_of_payload_error
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {declaration : DTR.GeneralKnownRebecDecl}
    {receivingClass : DTR.GeneralReactiveClass}
    {receivingServer : DTR.GeneralMessageServer}
    {diagnostic : String}
    (hKnown :
      sendingClass.knownRebec?
          send.knownRebec =
        some declaration)
    (hClass :
      DTR.findClass?
          classes
          declaration.className =
        some receivingClass)
    (hServer :
      receivingClass.messageServer?
          send.message =
        some receivingServer)
    (hPayload :
      generalPortPayloadFor
          receivingClass.name
          send.message
          receivingServer.parameters =
        .error diagnostic)
    (entry : GeneralOutputPortEntry) :
    ¬ generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry := by
  simp [
    generalOutputPortEntryFor,
    hKnown,
    hClass,
    hServer,
    hPayload
  ]

/--
The one success equation, with every field spelled out.

Long, and deliberately so: the entry this function builds is the record that decides a
generated identifier, and a forward equation that names all seven fields is what lets a later
theorem about *any* of them be proved by rewriting rather than by unfolding four matches
again. The site-map lemma below uses only the first field; §10.2's port-name theorem will use
the fifth.
-/
private theorem generalOutputPortEntryFor_ok
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {declaration : DTR.GeneralKnownRebecDecl}
    {receivingClass : DTR.GeneralReactiveClass}
    {receivingServer : DTR.GeneralMessageServer}
    {portPayload : LF.GeneralPortPayload}
    (hKnown :
      sendingClass.knownRebec?
          send.knownRebec =
        some declaration)
    (hClass :
      DTR.findClass?
          classes
          declaration.className =
        some receivingClass)
    (hServer :
      receivingClass.messageServer?
          send.message =
        some receivingServer)
    (hPayload :
      generalPortPayloadFor
          receivingClass.name
          send.message
          receivingServer.parameters =
        .ok portPayload) :
    generalOutputPortEntryFor
        classes
        sendingClass
        allSends
        send
        ordinal =
      .ok
        {
          site :=
            send.site

          knownRebec :=
            send.knownRebec

          message :=
            send.message

          receiverClass :=
            receivingClass.name

          outputPort :=
            outputPortNameFor
              send.message
              send.knownRebec
              (generalSiteSuffixFor
                allSends
                send
                ordinal)

          payload :=
            portPayload

          delay :=
            send.delay
        } := by
  simp [
    generalOutputPortEntryFor,
    hKnown,
    hClass,
    hServer,
    hPayload
  ]

/--
A resolved entry sits at the site of the send it was resolved from.

The whole of the site-map lemma rests on this, and the reason it needs a proof rather than a
glance is that `site` is the field the statement compiler matches on while `outputPort` is the
field it uses. If the two could come from different sends, every port in the emitted program
would still be a port the reactor declares and the messages would go to the wrong places.
-/
theorem generalOutputPortEntryFor_site
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {entry : GeneralOutputPortEntry}
    (hResolved :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry) :
    entry.site = send.site := by

  cases hKnown :
      sendingClass.knownRebec?
        send.knownRebec with

  | none =>
      exact
        absurd
          hResolved
          (generalOutputPortEntryFor_ne_ok_of_knownRebec_none
            hKnown
            entry)

  | some declaration =>

      cases hClass :
          DTR.findClass?
            classes
            declaration.className with

      | none =>
          exact
            absurd
              hResolved
              (generalOutputPortEntryFor_ne_ok_of_class_none
                hKnown
                hClass
                entry)

      | some receivingClass =>

          cases hServer :
              receivingClass.messageServer?
                send.message with

          | none =>
              exact
                absurd
                  hResolved
                  (generalOutputPortEntryFor_ne_ok_of_messageServer_none
                    hKnown
                    hClass
                    hServer
                    entry)

          | some receivingServer =>

              cases hPayload :
                  generalPortPayloadFor
                    receivingClass.name
                    send.message
                    receivingServer.parameters with

              | error diagnostic =>
                  exact
                    absurd
                      hResolved
                      (generalOutputPortEntryFor_ne_ok_of_payload_error
                        hKnown
                        hClass
                        hServer
                        hPayload
                        entry)

              | ok portPayload =>
                  rw [
                    generalOutputPortEntryFor_ok
                      hKnown
                      hClass
                      hServer
                      hPayload
                  ] at hResolved

                  injection hResolved with hEntry

                  subst hEntry

                  rfl

/-!
### Inverting the whole environment

Three forward equations and one induction. The equations are the same shape
`compileGeneralBody`'s are (`_cons_ok`, `_cons_error_head`, `_cons_error_tail`), which is not a
coincidence: `generalOutputPortEntriesOf` was written as explicit recursion rather than as
`mapM` precisely so that this shape would be available, and the note on the definition says so.

The induction proves the fact the statement compiler needs: **a resolved environment has one
entry per numbered send, at that send's site, in order.** Order is stated as an equality of the
two site lists rather than as a length equality plus an index-wise claim, because the length
equality alone would not rule out a permutation and a permutation would silently reassign every
port name whose pair has more than one site.
-/

/-!
The nil equation is **not** restated here. `generalOutputPortEntriesOf_nil` already exists above,
as a public `@[simp]` lemma with exactly this statement and argument order, and re-declaring it
privately here was a build error until it was removed. The induction below rewrites with that
lemma directly.
-/

/--
Both halves succeeding is the only way a cons succeeds, and this is that way.
-/
private theorem generalOutputPortEntriesOf_cons_ok
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {remaining : List (GeneralExternalSend × Nat)}
    {entry : GeneralOutputPortEntry}
    {entries : GeneralOutputPortEnv}
    (hEntry :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry)
    (hRemaining :
      generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          remaining =
        .ok entries) :
    generalOutputPortEntriesOf
        classes
        sendingClass
        allSends
        (
          (
            send,
            ordinal
          ) ::
            remaining
        ) =
      .ok
        (entry ::
          entries) := by
  simp [
    generalOutputPortEntriesOf,
    hEntry,
    hRemaining
  ]

/--
A refusal on the head is a refusal for the whole list.
-/
private theorem generalOutputPortEntriesOf_cons_ne_ok_of_head_error
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {remaining : List (GeneralExternalSend × Nat)}
    {diagnostic : String}
    (hEntry :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .error diagnostic)
    (env : GeneralOutputPortEnv) :
    ¬ generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          (
            (
              send,
              ordinal
            ) ::
              remaining
          ) =
        .ok env := by
  simp [
    generalOutputPortEntriesOf,
    hEntry
  ]

/--
A refusal anywhere in the tail is a refusal for the whole list.
-/
private theorem generalOutputPortEntriesOf_cons_ne_ok_of_tail_error
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {remaining : List (GeneralExternalSend × Nat)}
    {entry : GeneralOutputPortEntry}
    {diagnostic : String}
    (hEntry :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry)
    (hRemaining :
      generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          remaining =
        .error diagnostic)
    (env : GeneralOutputPortEnv) :
    ¬ generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          (
            (
              send,
              ordinal
            ) ::
              remaining
          ) =
        .ok env := by
  simp [
    generalOutputPortEntriesOf,
    hEntry,
    hRemaining
  ]

/--
A resolved environment carries exactly the sites of the sends it was resolved from, in order.
-/
theorem generalOutputPortEntriesOf_sites
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass)
    (allSends : List GeneralExternalSend)
    (numbered : List (GeneralExternalSend × Nat)) :
    ∀ env : GeneralOutputPortEnv,
      generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          numbered =
        .ok env →
      env.map
          (fun entry =>
            entry.site) =
        numbered.map
          (fun pair =>
            pair.1.site) := by

  induction numbered with

  | nil =>
      intro env hResolved

      rw [
        generalOutputPortEntriesOf_nil
      ] at hResolved

      injection hResolved with hEnv

      subst hEnv

      simp

  | cons pair remaining inductionHypothesis =>
      intro env hResolved

      cases pair with
      | mk send ordinal =>

          cases hEntry :
              generalOutputPortEntryFor
                classes
                sendingClass
                allSends
                send
                ordinal with

          | error diagnostic =>
              exact
                absurd
                  hResolved
                  (generalOutputPortEntriesOf_cons_ne_ok_of_head_error
                    hEntry
                    env)

          | ok entry =>

              cases hRemaining :
                  generalOutputPortEntriesOf
                    classes
                    sendingClass
                    allSends
                    remaining with

              | error diagnostic =>
                  exact
                    absurd
                      hResolved
                      (generalOutputPortEntriesOf_cons_ne_ok_of_tail_error
                        hEntry
                        hRemaining
                        env)

              | ok entries =>
                  rw [
                    generalOutputPortEntriesOf_cons_ok
                      hEntry
                      hRemaining
                  ] at hResolved

                  injection hResolved with hEnv

                  subst hEnv

                  have hHead :
                      entry.site =
                        send.site :=
                    generalOutputPortEntryFor_site
                      hEntry

                  have hTail :
                      entries.map
                          (fun entry =>
                            entry.site) =
                        remaining.map
                          (fun pair =>
                            pair.1.site) :=
                    inductionHypothesis
                      entries
                      hRemaining

                  simp [
                    hHead,
                    hTail
                  ]

/-!
### From a class's sends to its environment

Three links remain between "this statement is an external send" and "the environment has an
entry for it": numbering has to preserve the send list, `outputPortEnvOf` has to be the
numbered list resolved, and a body's sends have to be among its class's sends.

The numbering lemma is proved by its own four-line induction rather than by composing an
order-preservation lemma with `List.map_map`. The composition is one line shorter and it makes
the proof depend on the *shape* of a library lemma stated with `∘`, which is the kind of
dependency the note on `externalSendsFromIndex` already refused once for `List.enum`.
-/

/--
Numbering preserves the send list.

Stated even though nothing below consumes it: it is the fact that makes the ordinal a property
*of a send in a list* rather than of a traversal, and §10.2's port-name theorem needs the sends
themselves, not their sites.
-/
theorem numberExternalSends_sends
    (sends : List GeneralExternalSend) :
    ∀ numbered : List GeneralExternalSend,
      (numberExternalSends
            numbered
            sends).map
          (fun pair =>
            pair.1) =
        sends := by

  induction sends with

  | nil =>
      intro numbered

      simp [
        numberExternalSends
      ]

  | cons send remaining inductionHypothesis =>
      intro numbered

      simp [
        numberExternalSends,
        inductionHypothesis
      ]

/--
Numbering preserves the site list.
-/
theorem numberExternalSends_sites
    (sends : List GeneralExternalSend) :
    ∀ numbered : List GeneralExternalSend,
      (numberExternalSends
            numbered
            sends).map
          (fun pair =>
            pair.1.site) =
        sends.map
          (fun send =>
            send.site) := by

  induction sends with

  | nil =>
      intro numbered

      simp [
        numberExternalSends
      ]

  | cons send remaining inductionHypothesis =>
      intro numbered

      simp [
        numberExternalSends,
        inductionHypothesis
      ]

/--
A class's resolved environment carries exactly the sites of that class's sends, in order.
-/
theorem outputPortEnvOf_sites
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    (hResolved :
      outputPortEnvOf
          classes
          sendingClass =
        .ok env) :
    env.map
        (fun entry =>
          entry.site) =
      (externalSendsOfClass
          sendingClass).map
        (fun send =>
          send.site) := by

  unfold outputPortEnvOf at hResolved

  rw [
    generalOutputPortEntriesOf_sites
      classes
      sendingClass
      (externalSendsOfClass
        sendingClass)
      (numberedExternalSendsOfClass
        sendingClass)
      env
      hResolved
  ]

  unfold numberedExternalSendsOfClass

  exact
    numberExternalSends_sites
      (externalSendsOfClass
        sendingClass)
      []

/--
Every send of a class has an entry in that class's resolved environment.

This is the root of the site-totality chain and the only theorem in this section a reader has
to hold in mind: **if `outputPortEnvOf` succeeded, the lookup `compileGeneralStmt` performs
cannot fail.** Everything above it is inversion and everything below it, in
`Relico/Translation/GeneralBasic.lean`, is the induction that carries this from one statement to
a whole class.
-/
theorem exists_generalEntryAtSite?_of_mem_sends
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    {send : GeneralExternalSend}
    (hResolved :
      outputPortEnvOf
          classes
          sendingClass =
        .ok env)
    (hMember :
      send ∈
        externalSendsOfClass
          sendingClass) :
    ∃ entry,
      generalEntryAtSite?
          env
          send.site =
        some entry := by

  apply
    exists_generalEntryAtSite?_of_mem_sites

  rw [
    outputPortEnvOf_sites
      hResolved
  ]

  exact
    List.mem_map.mpr
      ⟨send,
       hMember,
       rfl⟩

/-!
### A body's sends are its class's sends

The last link, and the one that is pure list bookkeeping. It is stated in the direction the
induction consumes — from a body to the class — rather than as a characterisation of
`externalSendsOfClass`, because a characterisation would have to say something about the
*order* of the append and nothing needs that.
-/

/--
The empty body sends nothing.
-/
theorem externalSendsFromIndex_nil
    (bodyKey : GeneralBodyKey)
    (index : Nat) :
    externalSendsFromIndex
        bodyKey
        index
        [] =
      [] := by
  simp [
    externalSendsFromIndex
  ]

/--
An assignment contributes nothing and advances the index.
-/
theorem externalSendsFromIndex_assign
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (variableName : VarName)
    (expression : DTR.GeneralExpr)
    (remaining : DTR.GeneralBody) :
    externalSendsFromIndex
        bodyKey
        index
        (
          .assign
              variableName
              expression ::
            remaining
        ) =
      externalSendsFromIndex
        bodyKey
        (index + 1)
        remaining := by
  simp [
    externalSendsFromIndex
  ]

/--
A self-send contributes nothing and advances the index.
-/
theorem externalSendsFromIndex_send_selfTarget
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay)
    (remaining : DTR.GeneralBody) :
    externalSendsFromIndex
        bodyKey
        index
        (
          .send
              .selfTarget
              message
              arguments
              delay ::
            remaining
        ) =
      externalSendsFromIndex
        bodyKey
        (index + 1)
        remaining := by
  simp [
    externalSendsFromIndex
  ]

/--
An external send contributes one send, at this statement's address.
-/
theorem externalSendsFromIndex_send_knownRebec
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (knownRebec : KnownRebecName)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay)
    (remaining : DTR.GeneralBody) :
    externalSendsFromIndex
        bodyKey
        index
        (
          .send
              (.knownRebec
                knownRebec)
              message
              arguments
              delay ::
            remaining
        ) =
      {
        site :=
          {
            body :=
              bodyKey

            index :=
              index
          }

        knownRebec :=
          knownRebec

        message :=
          message

        delay :=
          delay
      } ::
        externalSendsFromIndex
          bodyKey
          (index + 1)
          remaining := by
  simp [
    externalSendsFromIndex
  ]

/--
A constructor's sends are among its class's sends.
-/
theorem mem_externalSendsOfClass_of_mem_constructor
    {sendingClass : DTR.GeneralReactiveClass}
    {send : GeneralExternalSend}
    (hMember :
      send ∈
        externalSendsOfBody
          .constructor
          sendingClass.constructor.body) :
    send ∈
      externalSendsOfClass
        sendingClass := by

  unfold externalSendsOfClass

  rw [
    List.mem_append
  ]

  exact
    Or.inl
      hMember

/--
One message server's sends are among the whole list's sends.
-/
theorem mem_externalSendsOfMessageServers_of_mem
    (servers : List DTR.GeneralMessageServer)
    {server : DTR.GeneralMessageServer}
    {send : GeneralExternalSend} :
    server ∈ servers →
    send ∈
      externalSendsOfBody
        (.messageServer
          server.name)
        server.body →
    send ∈
      externalSendsOfMessageServers
        servers := by

  induction servers with

  | nil =>
      intro hServer _

      simp at hServer

  | cons candidate remaining inductionHypothesis =>
      intro hServer hSend

      unfold externalSendsOfMessageServers

      rw [
        List.mem_append
      ]

      rw [
        List.mem_cons
      ] at hServer

      cases hServer with

      | inl hHead =>
          subst hHead

          exact
            Or.inl
              hSend

      | inr hTail =>
          exact
            Or.inr
              (inductionHypothesis
                hTail
                hSend)

/--
A message server's sends are among its class's sends.
-/
theorem mem_externalSendsOfClass_of_mem_messageServer
    {sendingClass : DTR.GeneralReactiveClass}
    {server : DTR.GeneralMessageServer}
    {send : GeneralExternalSend}
    (hServer :
      server ∈
        sendingClass.messageServers)
    (hMember :
      send ∈
        externalSendsOfBody
          (.messageServer
            server.name)
          server.body) :
    send ∈
      externalSendsOfClass
        sendingClass := by

  unfold externalSendsOfClass

  rw [
    List.mem_append
  ]

  exact
    Or.inr
      (mem_externalSendsOfMessageServers_of_mem
        sendingClass.messageServers
        hServer
        hMember)

/-!
## Endpoint uniqueness, indexed by the routing table

Finding F49 measured that `LF.GeneralProgram.targetEndpointsUnique` is **independent** of the
other eight clauses of `LF.GeneralProgram.wellFormed`: a hand-built program satisfies all eight
and fails the ninth. No theorem can therefore derive that clause from them, and the guard cannot
retire it.

What this section proves is the statement that survives F49. It is relative to the routing
table: for connections built by `generalConnectionsOf routes` and input ports built by
`generalInputPortsOf className routes` out of the **same** `routes`, a repeated target endpoint
forces a repeated input port name on the receiving reactor — which
`LF.GeneralReactor.declaredNames` already refuses. Scope is exactly what F49 corrected. The
earlier statement quantified over an arbitrary `LF.GeneralProgram`, where it is false, because
*two connections sharing a target endpoint come from two distinct routes* is a fact about
programs this translation assembles and not a fact about programs.

Everything here is about routes and names, so it stays in this module. `GeneralRouting.lean`
imports LF *syntax* and not `Relico.LF.GeneralWellFormed`, and widening an import to place a
theorem would be the wrong trade; the bridge from `reactorsWellFormed` and `declaredNames` to
the hypothesis these lemmas take lives in `Relico/Translation/GeneralBasic.lean`, which already
imports both sides.
-/

/--
The `cons` equation of the class filter when the head lands on the class asked for.

Two directed equations rather than a `match` inside a statement, for the reason
`generalEntryAtSite?_cons_self` gives: a `match` written in a theorem statement elaborates to a
fresh matcher constant, and every rewrite then depends on that constant agreeing definitionally
with the one in the definition.
-/
theorem generalRoutesIntoClass_cons_self
    (className : ClassName)
    (route : GeneralRoute)
    (remaining : List GeneralRoute)
    (hClass :
      route.receiverClass = className) :
    generalRoutesIntoClass
        className
        (route :: remaining) =
      route ::
        generalRoutesIntoClass
          className
          remaining := by
  simp [
    generalRoutesIntoClass,
    hClass
  ]

/--
The `cons` equation when the head lands on some other class.
-/
theorem generalRoutesIntoClass_cons_of_ne
    (className : ClassName)
    (route : GeneralRoute)
    (remaining : List GeneralRoute)
    (hClass :
      ¬ route.receiverClass = className) :
    generalRoutesIntoClass
        className
        (route :: remaining) =
      generalRoutesIntoClass
        className
        remaining := by
  simp [
    generalRoutesIntoClass,
    hClass
  ]

/--
A route whose receiver class is the one asked for survives the filter.

The direction that matters for endpoint uniqueness: the induction below has a route in the tail
and needs it among the input ports the receiving reactor declares, which is this statement
composed with the fact that `generalInputPortsOf` maps over exactly this filter.
-/
theorem mem_generalRoutesIntoClass
    (className : ClassName)
    (route : GeneralRoute) :
    ∀ (routes : List GeneralRoute),
      route ∈ routes →
      route.receiverClass = className →
        route ∈
          generalRoutesIntoClass
            className
            routes := by

  intro routes
  induction routes with

  | nil =>
      intro hMember _
      cases hMember

  | cons head remaining inductionHypothesis =>
      intro hMember hClass

      by_cases hHead :
          head.receiverClass = className

      · rw [
          generalRoutesIntoClass_cons_self
            className
            head
            remaining
            hHead,
          List.mem_cons
        ]

        cases List.mem_cons.mp hMember with

        | inl hEqual =>
            exact Or.inl hEqual

        | inr hTail =>
            exact
              Or.inr
                (inductionHypothesis
                  hTail
                  hClass)

      · rw [
          generalRoutesIntoClass_cons_of_ne
            className
            head
            remaining
            hHead
        ]

        cases List.mem_cons.mp hMember with

        | inl hEqual =>
            rw [hEqual] at hClass
            exact absurd hClass hHead

        | inr hTail =>
            exact
              inductionHypothesis
                hTail
                hClass

/--
The target endpoints of the emitted connections, read off the routes instead.

`LF.GeneralProgram.targetEndpointsUnique` asks for `Nodup` of the list on the left. This
equation is what lets the induction below work on the list on the right, where a route's
receiver class is available and the filter of the previous lemmas applies. One connection per
route and both projections are fields of `generalConnectionOf`, so the content is a `map`
composition and nothing else.
-/
theorem generalConnectionsOf_targetEndpoints :
    ∀ (routes : List GeneralRoute),
      (generalConnectionsOf
          routes).map
          (fun connection =>
            (
              connection.targetInstance,
              connection.targetPort
            )) =
        routes.map
          (fun route =>
            (
              route.receiverInstance,
              generalInputPortOfRoute route
            )) := by

  intro routes
  induction routes with

  | nil =>
      simp [
        generalConnectionsOf
      ]

  | cons route remaining inductionHypothesis =>
      simp only [
        generalConnectionsOf
      ] at inductionHypothesis ⊢

      simp [
        generalConnectionOf,
        inductionHypothesis
      ]

/--
Distinct input port names give distinct target endpoints — the theorem F49 left standing.

Two hypotheses, and naming what each one does is most of the content.

`hReceiverClass` says the routes agree about what class an instance has. It is not decoration:
a target endpoint is an instance and a port name, while input ports are declared on a *class*,
so without it two routes could share a receiver instance and be filtered into two different
reactors, where neither reactor's `declaredNames` can see the collision. Routing built by
`routesOf` satisfies it because a route's receiver class comes from resolving its receiver
instance, and this is where that fact has to be supplied rather than assumed.

`hInputPortNames` is the guard clause, one class at a time: the input port names the receiving
reactor declares are distinct. `LF.GeneralReactor.declaredNames` is what supplies it, which is
why the bridge lives in the other module.

Given both, the emitted endpoints are distinct. The induction is on the routes, and the head
step is the whole argument: a later route with the head's endpoint has the head's receiver
instance, so by `hReceiverClass` it has the head's receiver class, so it survives the same
filter, so `generalInputPortsOf` declares its name too — and the two names are equal, which
`hInputPortNames` forbids. Nothing here holds by construction; the conclusion is inherited from
a decided property of the receiver, exactly as F49 says it must be.
-/
theorem generalRouteEndpoints_nodup :
    ∀ (routes : List GeneralRoute),
      (∀ (first : GeneralRoute),
        first ∈ routes →
        ∀ (second : GeneralRoute),
          second ∈ routes →
          first.receiverInstance = second.receiverInstance →
            first.receiverClass = second.receiverClass) →
      (∀ (route : GeneralRoute),
        route ∈ routes →
          ((generalInputPortsOf
            route.receiverClass
            routes).map
            (fun port =>
              port.name.value)).Nodup) →
        (routes.map
          (fun route =>
            (
              route.receiverInstance,
              generalInputPortOfRoute route
            ))).Nodup := by

  intro routes
  induction routes with

  | nil =>
      intro _ _
      simp

  | cons head remaining inductionHypothesis =>
      intro hReceiverClass hInputPortNames

      have hHeadMember :
          head ∈ head :: remaining := by
        rw [List.mem_cons]
        exact Or.inl rfl

      have hTailMember :
          ∀ (route : GeneralRoute),
            route ∈ remaining →
              route ∈ head :: remaining := by
        intro route hMember
        rw [List.mem_cons]
        exact Or.inr hMember

      have hConsistentTail :
          ∀ (first : GeneralRoute),
            first ∈ remaining →
            ∀ (second : GeneralRoute),
              second ∈ remaining →
              first.receiverInstance = second.receiverInstance →
                first.receiverClass = second.receiverClass := by
        intro first hFirst second hSecond hInstance
        exact
          hReceiverClass
            first
            (hTailMember first hFirst)
            second
            (hTailMember second hSecond)
            hInstance

      have hNamesTail :
          ∀ (route : GeneralRoute),
            route ∈ remaining →
              ((generalInputPortsOf
                route.receiverClass
                remaining).map
                (fun port =>
                  port.name.value)).Nodup := by

        intro route hRoute

        have hFull :=
          hInputPortNames
            route
            (hTailMember route hRoute)

        unfold generalInputPortsOf at hFull ⊢

        by_cases hClass :
            head.receiverClass = route.receiverClass

        · rw [
            generalRoutesIntoClass_cons_self
              route.receiverClass
              head
              remaining
              hClass,
            List.map_cons,
            List.map_cons
          ] at hFull

          cases hFull with

          | cons _ hTail =>
              exact hTail

        · rw [
            generalRoutesIntoClass_cons_of_ne
              route.receiverClass
              head
              remaining
              hClass
          ] at hFull

          exact hFull

      have hHeadNames :=
        hInputPortNames
          head
          hHeadMember

      unfold generalInputPortsOf at hHeadNames

      rw [
        generalRoutesIntoClass_cons_self
          head.receiverClass
          head
          remaining
          rfl,
        List.map_cons,
        List.map_cons
      ] at hHeadNames

      cases hHeadNames with

      | cons hHeadFresh _ =>

          constructor

          · intro mapped hMapped hEqual

            rcases
                List.mem_map.mp
                  hMapped
              with
                ⟨route,
                 hRoute,
                 hMappedRoute⟩

            have hPair :
                (
                  head.receiverInstance,
                  generalInputPortOfRoute head
                ) =
                  (
                    route.receiverInstance,
                    generalInputPortOfRoute route
                  ) :=
              hEqual.trans
                hMappedRoute.symm

            simp only [
              Prod.mk.injEq
            ] at hPair

            have hClass :
                head.receiverClass =
                  route.receiverClass :=
              hReceiverClass
                head
                hHeadMember
                route
                (hTailMember route hRoute)
                hPair.left

            have hFiltered :
                route ∈
                  generalRoutesIntoClass
                    head.receiverClass
                    remaining :=
              mem_generalRoutesIntoClass
                head.receiverClass
                route
                remaining
                hRoute
                hClass.symm

            exact
              hHeadFresh
                ((generalInputPortDeclOf route).name.value)
                (List.mem_map.mpr
                  ⟨generalInputPortDeclOf route,
                   List.mem_map.mpr
                     ⟨route,
                      hFiltered,
                      rfl⟩,
                   rfl⟩)
                (by
                  simp only [
                    generalInputPortDeclOf,
                    hPair.right
                  ])

          · exact
              inductionHypothesis
                hConsistentTail
                hNamesTail

/--
`generalRouteEndpoints_nodup` restated on the connection list the assembler actually emits.

The two hypotheses are unchanged and unweakened; only the shape of the conclusion moves, through
`generalConnectionsOf_targetEndpoints`. This is the form `LF.GeneralProgram.targetEndpointsUnique`
wants once `assembleGeneralProgram_connections` has fired, so it is the last route-level step before
the statement becomes a claim about a well-formedness clause — and that step needs
`LF.GeneralWellFormed`, which this module does not import.
-/
theorem generalConnectionsOf_targetEndpoints_nodup
    (routes : List GeneralRoute)
    (hReceiverClass :
      ∀ (first : GeneralRoute),
        first ∈ routes →
        ∀ (second : GeneralRoute),
          second ∈ routes →
          first.receiverInstance = second.receiverInstance →
            first.receiverClass = second.receiverClass)
    (hInputPortNames :
      ∀ (route : GeneralRoute),
        route ∈ routes →
          ((generalInputPortsOf
            route.receiverClass
            routes).map
            (fun port =>
              port.name.value)).Nodup) :
    ((generalConnectionsOf
        routes).map
        (fun connection =>
          (
            connection.targetInstance,
            connection.targetPort
          ))).Nodup := by

  rw [
    generalConnectionsOf_targetEndpoints
      routes
  ]

  exact
    generalRouteEndpoints_nodup
      routes
      hReceiverClass
      hInputPortNames

/-!
## Instance-declaration order

`docs/STAGE_E_DESIGN.md` §10.2's fourth owed item: an explicit statement that a receiver's port
reactions for one message server appear in main-block instance-declaration order. The *docstring*
half of that item already sits on `generalRoutesIntoMessageServer` above, and says in as many words
that route order is instance-declaration order and that reaction order realizing priority is stage
F's claim rather than this stage's. What follows is the statement half. The composite lives in
`Relico/Translation/GeneralBasic.lean`, because that is where the reaction assembly is and this
module deliberately does not import it.

Everything here is phrased with `++` over an arbitrary split of the instance list, rather than with
a list-order predicate. `List.Sublist` is used by no statement and no proof in this development —
the identifier occurs only in prose like this paragraph — and introducing a core order API to say
"in order" would put one more trusted name between the claim and its proof for no gain. The split
says the same thing, and says it at every cut point rather than only at the head: if the instances
are `earlier ++ later`, every route owed to an instance declared in `earlier` precedes every route
owed to one declared in `later`.

Appended at file end deliberately, so that no line number cited from `docs/STAGE_E_FINDINGS.md` or
from another module moves.
-/

/--
The `cons` equation of the instance recursion, in the direction that builds a table.

Four hypotheses because the definition has four gates, and each is a real refusal rather than a
defensive one: an instance of a class the model does not declare, an output-port environment that
does not resolve, a send site the environment cannot place, and a failure further down the instance
list. The conclusion is the `++` that makes instance order observable — the head instance's routes
are a *prefix* of the table, never interleaved with a later instance's.
-/
theorem routesOfInstances_cons_ok
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance)
    (remaining : List DTR.GeneralActorInstance)
    (sendingClass : DTR.GeneralReactiveClass)
    (env : GeneralOutputPortEnv)
    (headRoutes tailRoutes : List GeneralRoute)
    (hClass :
      model.class? actor.className =
        some sendingClass)
    (hEnv :
      outputPortEnvOf
          model.classes
          sendingClass =
        .ok env)
    (hHead :
      routesOfEntries
          model
          actor
          env =
        .ok headRoutes)
    (hTail :
      routesOfInstances
          model
          remaining =
        .ok tailRoutes) :
    routesOfInstances
        model
        (actor :: remaining) =
      .ok
        (headRoutes ++
          tailRoutes) := by

  simp [
    routesOfInstances,
    hClass,
    hEnv,
    hHead,
    hTail
  ]

/--
The same equation read backwards: a successful table on a `cons` exhibits its four successes.

Stated as one existential rather than as four projections because the four are produced together by
a single unfolding, and a caller that needs one needs the rest. `routesOfInstances_append` below is
that caller: its induction step holds a successful table for `actor :: remaining` and has to rebuild
one for `actor :: (remaining ++ later)`, which needs the head's routes, the tail's table **and** the
two lookups, since `routesOfInstances_cons_ok` takes all four.

Each error branch is closed by the hypothesis becoming `.error … = .ok …`, which is the only way an
unfolding of this definition can contradict a success.
-/
theorem routesOfInstances_cons_inv
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance)
    (remaining : List DTR.GeneralActorInstance)
    (routes : List GeneralRoute)
    (hRoutes :
      routesOfInstances
          model
          (actor :: remaining) =
        .ok routes) :
    ∃ (sendingClass : DTR.GeneralReactiveClass)
      (env : GeneralOutputPortEnv)
      (headRoutes tailRoutes : List GeneralRoute),
      model.class? actor.className =
          some sendingClass ∧
        outputPortEnvOf
            model.classes
            sendingClass =
          .ok env ∧
        routesOfEntries
            model
            actor
            env =
          .ok headRoutes ∧
        routesOfInstances
            model
            remaining =
          .ok tailRoutes ∧
        routes =
          headRoutes ++
            tailRoutes := by

  cases hClass :
      model.class? actor.className with

  | none =>
      simp [
        routesOfInstances,
        hClass
      ] at hRoutes

  | some sendingClass =>
      cases hEnv :
          outputPortEnvOf
            model.classes
            sendingClass with

      | error diagnostic =>
          simp [
            routesOfInstances,
            hClass,
            hEnv
          ] at hRoutes

      | ok env =>
          cases hHead :
              routesOfEntries
                model
                actor
                env with

          | error diagnostic =>
              simp [
                routesOfInstances,
                hClass,
                hEnv,
                hHead
              ] at hRoutes

          | ok headRoutes =>
              cases hTail :
                  routesOfInstances
                    model
                    remaining with

              | error diagnostic =>
                  simp [
                    routesOfInstances,
                    hClass,
                    hEnv,
                    hHead,
                    hTail
                  ] at hRoutes

              | ok tailRoutes =>
                  refine
                    ⟨sendingClass,
                      env,
                      headRoutes,
                      tailRoutes,
                      ?_,
                      ?_,
                      ?_,
                      ?_,
                      ?_⟩

                  · simp [hClass]

                  · simp [hEnv]

                  · simp [hHead]

                  · simp [hTail]

                  · simpa [
                      routesOfInstances,
                      hClass,
                      hEnv,
                      hHead,
                      hTail
                    ] using hRoutes.symm

/--
The instance list splits, and so does the table it produces.

Stated with the two quantifiers *inside* the conclusion rather than as hypotheses of the theorem,
which is the shape `exists_compileGeneralReactiveClasses` uses and for the same reason: the
induction is on `earlier`, `earlierRoutes` has to vary with it, and putting both under a `∀` in the
goal avoids `induction … generalizing` and leaves the induction hypothesis in an unambiguous shape.
`later` and `laterRoutes` are fixed throughout and stay as parameters.
-/
private theorem routesOfInstances_append_aux
    (model : DTR.GeneralModel)
    (later : List DTR.GeneralActorInstance)
    (laterRoutes : List GeneralRoute)
    (hLater :
      routesOfInstances
          model
          later =
        .ok laterRoutes) :
    ∀ (earlier : List DTR.GeneralActorInstance)
      (earlierRoutes : List GeneralRoute),
      routesOfInstances
            model
            earlier =
          .ok earlierRoutes →
        routesOfInstances
            model
            (earlier ++ later) =
          .ok
            (earlierRoutes ++
              laterRoutes) := by

  intro earlier

  induction earlier with

  | nil =>
      intro earlierRoutes hEarlier

      have hEmpty :
          earlierRoutes = [] := by
        simpa [
          routesOfInstances
        ] using hEarlier.symm

      subst hEmpty

      simpa using hLater

  | cons actor remaining inductionHypothesis =>
      intro earlierRoutes hEarlier

      obtain
          ⟨sendingClass,
            env,
            headRoutes,
            tailRoutes,
            hClass,
            hEnv,
            hHead,
            hTail,
            hSplit⟩ :=
        routesOfInstances_cons_inv
          model
          actor
          remaining
          earlierRoutes
          hEarlier

      subst hSplit

      rw [
        List.cons_append,
        List.append_assoc
      ]

      exact
        routesOfInstances_cons_ok
          model
          actor
          (remaining ++ later)
          sendingClass
          env
          headRoutes
          (tailRoutes ++ laterRoutes)
          hClass
          hEnv
          hHead
          (inductionHypothesis
            tailRoutes
            hTail)

/--
The table of a split instance list is the concatenation of the two tables, in order.

This is the order claim at the level of the routing table: no interleaving, no sorting, and the cut
point is arbitrary, so it holds between *any* earlier instance and *any* later one rather than only
at the head of the list.
-/
theorem routesOfInstances_append
    (model : DTR.GeneralModel)
    (earlier later : List DTR.GeneralActorInstance)
    (earlierRoutes laterRoutes : List GeneralRoute)
    (hEarlier :
      routesOfInstances
          model
          earlier =
        .ok earlierRoutes)
    (hLater :
      routesOfInstances
          model
          later =
        .ok laterRoutes) :
    routesOfInstances
        model
        (earlier ++ later) =
      .ok
        (earlierRoutes ++
          laterRoutes) :=
  routesOfInstances_append_aux
    model
    later
    laterRoutes
    hLater
    earlier
    earlierRoutes
    hEarlier

/--
The same statement about the model's own table, split at a cut in the main block.

`routesOf` is `routesOfInstances` at `model.instances`, and `model.instances` *is* main-block
declaration order — `DTR.GeneralElaborator` preserves it and nothing between here and there sorts.
So a hypothesis that the declared instances split as `earlier ++ later` is exactly a hypothesis
about where the cut falls in the main block, which is what §10.2's item asks the statement to be
about.
-/
theorem routesOf_split
    (model : DTR.GeneralModel)
    (earlier later : List DTR.GeneralActorInstance)
    (earlierRoutes laterRoutes : List GeneralRoute)
    (hInstances :
      model.instances =
        earlier ++ later)
    (hEarlier :
      routesOfInstances
          model
          earlier =
        .ok earlierRoutes)
    (hLater :
      routesOfInstances
          model
          later =
        .ok laterRoutes) :
    routesOf model =
      .ok
        (earlierRoutes ++
          laterRoutes) := by

  show
    routesOfInstances
        model
        model.instances =
      .ok
        (earlierRoutes ++
          laterRoutes)

  rw [hInstances]

  exact
    routesOfInstances_append
      model
      earlier
      later
      earlierRoutes
      laterRoutes
      hEarlier
      hLater

/--
The `cons` equation of the message-server filter when the head lands on the server asked for.

Mirrors `generalRoutesIntoClass_cons_self` above, and exists for the reason given there: two
directed equations rather than a `match` inside a statement. The hypothesis is the `Prod` equality
the definition actually tests, rather than its two components, so that nothing has to decompose a
pair in the middle of a rewrite — and because `by_cases` at the one call site below produces exactly
this shape.
-/
theorem generalRoutesIntoMessageServer_cons_self
    (className : ClassName)
    (message : MsgName)
    (route : GeneralRoute)
    (remaining : List GeneralRoute)
    (hMatch :
      (route.receiverClass,
        route.message) =
        (className, message)) :
    generalRoutesIntoMessageServer
        className
        message
        (route :: remaining) =
      route ::
        generalRoutesIntoMessageServer
          className
          message
          remaining := by

  simp [
    generalRoutesIntoMessageServer,
    hMatch
  ]

/--
The `cons` equation when the head lands on some other class, or on the same class but a different
message server.

Both misses go through one equation because the definition tests one pair, which is also why §7.3's
grouping is by the pair rather than by class followed by a second filter.
-/
theorem generalRoutesIntoMessageServer_cons_of_ne
    (className : ClassName)
    (message : MsgName)
    (route : GeneralRoute)
    (remaining : List GeneralRoute)
    (hMatch :
      ¬ ((route.receiverClass,
        route.message) =
        (className, message))) :
    generalRoutesIntoMessageServer
        className
        message
        (route :: remaining) =
      generalRoutesIntoMessageServer
        className
        message
        remaining := by

  simp [
    generalRoutesIntoMessageServer,
    hMatch
  ]

/--
The filter distributes over concatenation.

The bridge from the routing table's split to the reaction group's split: `routesOf_split` says the
table is `earlierRoutes ++ laterRoutes`, this says the group of routes landing on one message server
splits at the same point, and `assembleGeneralPortReactions` is a `map`, so the reactions do too.
Proved by induction on the left list with a case split on the head, because the filter is not
structurally a `List.filter` — it is its own recursion, for the reason its docstring gives.
-/
theorem generalRoutesIntoMessageServer_append
    (className : ClassName)
    (message : MsgName)
    (earlier later : List GeneralRoute) :
    generalRoutesIntoMessageServer
        className
        message
        (earlier ++ later) =
      generalRoutesIntoMessageServer
          className
          message
          earlier ++
        generalRoutesIntoMessageServer
          className
          message
          later := by

  induction earlier with

  | nil =>
      simp [
        generalRoutesIntoMessageServer
      ]

  | cons route remaining inductionHypothesis =>
      by_cases hMatch :
          (route.receiverClass,
            route.message) =
            (className, message)

      · rw [
          List.cons_append,
          generalRoutesIntoMessageServer_cons_self
            className
            message
            route
            (remaining ++ later)
            hMatch,
          generalRoutesIntoMessageServer_cons_self
            className
            message
            route
            remaining
            hMatch,
          inductionHypothesis,
          List.cons_append
        ]

      · rw [
          List.cons_append,
          generalRoutesIntoMessageServer_cons_of_ne
            className
            message
            route
            (remaining ++ later)
            hMatch,
          generalRoutesIntoMessageServer_cons_of_ne
            className
            message
            route
            remaining
            hMatch,
          inductionHypothesis
        ]

end Translation
end Relico
