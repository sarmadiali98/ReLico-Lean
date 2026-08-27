import Relico.Common.ActorTopology
import Relico.Common.Name

set_option autoImplicit false

namespace Relico
namespace Translation

def reactorNameFor
    (className : ClassName) :
    ReactorName :=
  ⟨className.value⟩

def actionNameFor
    (messageName : MsgName) :
    ActionName :=
  ⟨messageName.value ++ "_action"⟩

/--
Everything that follows the message name in a general translator's action name.

Split out for the reason `outputPortInfixFor` is: it puts the varying component at one end of
a **single** `++` against one opaque string, which is what keeps
`generalActionNameFor_message_injective` a suffix cancellation instead of a reassociation
argument about three appends.
-/
def generalActionInfixFor
    (siteSuffix : String) :
    String :=
  "_action" ++
    siteSuffix

/--
The name of the logical action that carries one self-send **site's** message.

`<message>_action<siteSuffix>`, declared on the sending class, which is also the receiving
class because the send is a self-send.

**Why this exists rather than a second parameter on `actionNameFor`.** `actionNameFor` is
shared with the six pre-general translation families, and `actionNameFor_injective` is used in
roughly twenty proofs under `Relico/Correctness/`. Giving it a site parameter would edit all of
them without changing anything any of them claims. The general translator therefore carries its
own action-name rule, exactly as it carries its own syntax, well-formedness, printer and
assembly; the older families keep a name function whose one action per message server is
correct *for them*, because none of them admits two sends to one message server in one body.

**Why sites at all.** Measured against `lfc` 0.11.0 and recorded as finding F56: two
`schedule` calls on one logical action at one tag keep only the last value, silently, with
every exit code 0; the spacing policy that would repair it does not compile in reactor-cpp;
and one reaction triggered by two actions at one tag fires once, because a trigger list is a
disjunction. One action and one reaction per site is the only shape left standing. See
`Translation.generalActionSiteSuffixFor` in `Relico/Translation/GeneralRouting.lean` for the
suffix, which is empty when the class sends to a message **at most** once — so every fixture
that predates send sites keeps the action name it already had.

**The zero case is the reason that reads "at most" rather than "exactly", and it was a
correction to what this docstring first said.** A message server nothing self-sends has no
sites at all, and under an "exactly once" rule it fell to the numeric branch and was handed a
suffix for a site that does not exist — renaming the actions of every message server in the
corpus that is only ever reached from outside. That is most of them, so the rule as first
written would have churned ten fixtures to repair a defect that shows up in one.

**No injectivity in both components is claimed, and none is proved.** The separator `_action`
is not escaped, so this function is in the same category as `outputPortNameFor`: uniqueness of
generated identifiers is decided on the assembled program, by requiring
`LF.GeneralReactor.declaredNames` to be `Nodup` and refusing with a diagnostic otherwise, which
is strictly stronger than injectivity here because it also covers collisions against state
variable, reaction and parameter names. What *is* proved below is the one direction that
carries weight: with the site suffix fixed, the name determines the message.
-/
def generalActionNameFor
    (messageName : MsgName)
    (siteSuffix : String) :
    ActionName :=
  ⟨messageName.value ++
    generalActionInfixFor
      siteSuffix⟩

def startupReactionName :
    ReactionName :=
  ⟨"startup"⟩

def messageReactionNameFor
    (messageName : MsgName) :
    ReactionName :=
  ⟨messageName.value ++ "_reaction"⟩

/--
The name of the reaction that runs one message server's body on one incoming arrow.

`docs/STAGE_E_DESIGN.md` §7.3: a receiving class gets one reaction per route that lands on
it, named after the input port that triggers it. The action reaction keeps
`messageReactionNameFor`, so a message server reached both by self-sends and from outside has
one reaction per delivery mechanism and their names say which is which.

**This name can collide, with `messageReactionNameFor` and with a sibling, and none of that is
a defect.** `messageReactionNameFor ⟨"reportToHubFromWorkerAlpha"⟩` and the port reaction for
the input port `reportToHubFromWorkerAlpha` are the same string, and `reportToHubFromWorkerAlpha`
is a legal Rebeca message name. Reaction names are not checked for uniqueness anywhere and must
not be: `Relico/LF/GeneralWellFormed.lean:37` records that *"LF reactions are anonymous in
concrete syntax, so uniqueness would constrain an identifier the target language never sees"*,
and `renderGeneralReaction` bears that out by printing `reaction(<trigger>)` and dropping the
name. The name exists for this development's own theorems — it is what
`assembleGeneralPortReaction_names` states route order in terms of — and for nothing else.

That also means reaction names are **not** in `LF.GeneralReactor.declaredNames`, so the §9
guard does not cover them. The guard covering them would be wrong, not merely absent.
-/
def portReactionNameFor
    (inputPort : PortName) :
    ReactionName :=
  ⟨inputPort.value ++ "_reaction"⟩

/--
Capitalize an identifier's first character and leave the rest of it alone.

Stage E's port names read as English in the direction the arrow points — `reportToHub`,
`reportToHubFromWorkerAlpha` — and that reading depends on each embedded source identifier
starting with a capital. `String.capitalize` is deliberately not called: this development
depends on no library function whose name or availability has churned across Lean releases,
and `String.isEmpty`, `String.front`, `Char.toUpper` and `String.drop` have not.

**This function is not injective, and that is a fact about the names rather than an accident
of the definition.** `hub` and `Hub` are both legal Rebeca identifiers and both give `Hub`.
The consequence is recorded on `outputPortNameFor`, where it matters.
-/
def capitalizeName
    (identifier : String) :
    String :=
  if identifier.isEmpty then
    identifier
  else
    String.singleton
        identifier.front.toUpper ++
      identifier.drop 1

/--
Everything that follows the message name in an output port's name.

Split out from `outputPortNameFor` rather than inlined, so that the varying component of
that name sits at one end of a **single** `++` against one opaque string. That is what makes
`outputPortNameFor_message_injective` below a proof of the same shape as
`actionNameFor_injective` instead of a reassociation argument about three appends, and it is
the only reason this function exists.
-/
def outputPortInfixFor
    (knownRebec : KnownRebecName)
    (siteSuffix : String) :
    String :=
  "To" ++
    capitalizeName knownRebec.value ++
    siteSuffix

/--
The name of the output port that carries one send site's message.

`<message>To<KnownRebec><siteSuffix>`, declared on the **sending** class. Fig. 2b's idiom
(`readingFromTemp`) extended to the sending side, which the paper names nowhere at all —
recorded as this project's own rule under ledger correction P20, in the same category as the
`<Reactor>_<Action>_Args` struct name (F25).

The suffix is empty when the sending class has exactly one send to this (known rebec,
message) pair, and the site's 1-based ordinal among that pair's sites otherwise, so every
class that sends once per pair — which is all three fixtures inherited from stage D, and
every example in the paper — keeps the name it would have had before send sites existed.

**This function is not injective and no theorem below claims that it is.** Two independent
collision channels are known:

* the separator is not escaped, so `reportTo`/`hub` and `report`/`toHub` both give
  `reportToToHub`, and `report`/`hub` at site 2 collides with `report`/`hub2` at a class's
  only site — finding F34;
* `capitalizeName` folds case, so `hub` and `Hub` give one name no matter what the separator
  does — finding F42, which is *not* F34: escaping the separator, the standard fix for the
  first channel, does nothing about this one.

Uniqueness of generated names is therefore **decided on the program the translation builds**
— `LF.GeneralReactor.declaredNames` must be `Nodup` — and refused with a diagnostic when it
fails. That is strictly stronger than injectivity of this function would be, because it also
covers collisions against state-variable, action, reaction and parameter names, which no
port-naming rule can rule out from its own side.
-/
def outputPortNameFor
    (message : MsgName)
    (knownRebec : KnownRebecName)
    (siteSuffix : String) :
    PortName :=
  ⟨message.value ++
    outputPortInfixFor
      knownRebec
      siteSuffix⟩

/--
Everything that follows the output port name in an input port's name.

Named for the same reason `outputPortInfixFor` is, and the symmetry is worth keeping even
though this one is shorter.
-/
def inputPortInfixFor
    (senderInstance : ActorName) :
    String :=
  "From" ++
    capitalizeName senderInstance.value

/--
The name of the input port on which one sender instance's arrows on one output port land.

`<outputPort>From<SenderInstance>`, declared on the **receiving** class. This is Fig. 2b's
rule verbatim, and it wraps whatever the sender's port is called, so the send-site suffix
propagates for free and both ends of a connection are derivable from the same two pieces of
data.

The sender instance has to appear here because `lfc 0.11.0` rejects many-to-one connections,
so two senders reaching one receiver need two ports. The known rebec and the message appear
transitively, through the output port's own name, which is why this rule needs no further
components: it inherits every distinction the sender's side already made.
-/
def inputPortNameFor
    (senderInstance : ActorName)
    (outputPort : PortName) :
    PortName :=
  ⟨outputPort.value ++
    inputPortInfixFor
      senderInstance⟩


theorem actionNameFor_injective :
    Function.Injective actionNameFor := by

  intro left right hEqual

  cases left
  cases right

  simpa [
    actionNameFor
  ] using
    hEqual

/--
A class's name determines its reactor's name.

The identity on underlying strings, so injectivity is one constructor injection. Stated
because the initial correspondence needs the converse of `assembleGeneralReactor_name`: to
recover a class from a compiled program's reactor it must be known that two classes cannot
share one reactor name, and without this lemma that recovery is an unstated assumption.

The proof is the same shape as `actionNameFor_injective`, which is the pattern this file
establishes for a name function that wraps its input in one structure constructor.
-/
theorem reactorNameFor_injective :
    Function.Injective reactorNameFor := by

  intro left right hEqual

  cases left
  cases right

  simpa [
    reactorNameFor
  ] using
    hEqual

/--
With the site suffix fixed, a general action's name determines the message.

Suffix cancellation, the same one-line proof as `actionNameFor_injective` and the same shape as
`outputPortNameFor_message_injective`, which is the whole reason `generalActionInfixFor` was
factored out instead of the suffix being appended inline.

The converse direction is not stated, and the omission is deliberate rather than pending: with
the message fixed, the name determines `generalActionInfixFor siteSuffix`, and since that
function is `"_action" ++ siteSuffix` the suffix *is* recoverable — but nothing in this
development needs it, and a lemma that exists only to be complete is a lemma a later reader has
to check the relevance of. If a stage needs it, prefix cancellation gives it in the same three
lines `outputPortInfixFor_eq_of_outputPortNameFor_eq` uses.
-/
theorem generalActionNameFor_message_injective
    (siteSuffix : String) :
    Function.Injective
      (fun message =>
        generalActionNameFor
          message
          siteSuffix) := by

  intro left right hEqual

  cases left
  cases right

  simpa [
    generalActionNameFor
  ] using
    hEqual

theorem messageReactionNameFor_injective :
    Function.Injective messageReactionNameFor := by

  intro left right hEqual

  cases left
  cases right

  simpa [
    messageReactionNameFor
  ] using
    hEqual

/-!
### What can be proved about the port names, and what cannot

`docs/STAGE_E_DESIGN.md` §4.3 asks for *"two one-sided injectivity lemmas … with the message
fixed the name determines the rebec, and with the rebec fixed the name determines the
message"*, on the stated ground that *"both reduce to suffix or prefix cancellation"*.

**Only one of the two is true, and the design's own material refutes the other.** With the
known rebec and the site suffix fixed, the name does determine the message: that is suffix
cancellation and it is proved below. With the message fixed, the name determines the *infix*
and no more — and the infix does not determine the rebec, for two reasons the design states
in the same section without noticing that they close this direction off. `capitalizeName`
folds case, so `hub` and `Hub` give one infix; and the boundary between the capitalized rebec
and the site suffix is not marked, so `hub` at site 2 and `hub2` at a sole site give one
infix. §4.3's first lemma is therefore stated here in the strongest form that holds, which is
cancellation down to the infix, and the gap is filed as F42.

No Lean *refutation* of the stronger reading is attempted, and the reason is worth recording
rather than leaving as an omission. A concrete witness needs `capitalizeName "hub"` to reduce
in the kernel, which means reducing `String.front` and `String.drop` through the UTF-8 model,
and a parametric witness needs idempotence of `Char.toUpper`, which core does not supply. The
right instrument for a concrete string witness is
`frontend/lean-bridge/GeneralLfPrinterTestMain.lean`, which evaluates these functions at run
time and compares the results, so the collisions are asserted there rather than argued here:
`PORT_NAME_CASE_FOLDING_COLLIDES` for the case-folding channel,
`PORT_NAME_SITE_SUFFIX_BOUNDARY_COLLIDES` for the unmarked boundary, and
`PORT_NAME_UNESCAPED_SEPARATOR_COLLIDES` for F34's separator.

**Those three labels are named here because the earlier version of this paragraph promised
them and they did not exist**, in this docstring and two others, for a day — recorded as
finding F44 in `docs/STAGE_E_FINDINGS.md`. A docstring that describes a test is a claim about
the suite and has to be checkable by grepping for the label, which is why the labels appear
here rather than a sentence saying the matter is covered.
-/

/--
With the known rebec and the site suffix fixed, an output port's name determines the message.

Suffix cancellation, the same one-line proof as `actionNameFor_injective`, which is what
`outputPortInfixFor` was factored out to make possible.
-/
theorem outputPortNameFor_message_injective
    (knownRebec : KnownRebecName)
    (siteSuffix : String) :
    Function.Injective
      (fun message =>
        outputPortNameFor
          message
          knownRebec
          siteSuffix) := by

  intro left right hEqual

  cases left
  cases right

  simpa [
    outputPortNameFor
  ] using
    hEqual

/--
With the message fixed, an output port's name determines the infix — and stops there.

Prefix cancellation. This is the honest form of the second lemma §4.3 asks for: it does *not*
follow that the known rebec or the site suffix are determined, and the section note above
gives the two witnesses that show they are not.
-/
theorem outputPortInfixFor_eq_of_outputPortNameFor_eq
    (message : MsgName)
    (leftRebec rightRebec : KnownRebecName)
    (leftSuffix rightSuffix : String)
    (hEqual :
      outputPortNameFor
          message
          leftRebec
          leftSuffix =
        outputPortNameFor
          message
          rightRebec
          rightSuffix) :
    outputPortInfixFor
        leftRebec
        leftSuffix =
      outputPortInfixFor
        rightRebec
        rightSuffix := by

  simpa [
    outputPortNameFor
  ] using
    hEqual

/--
With the sender instance fixed, an input port's name determines the sender's output port.

Suffix cancellation again, and this is the direction that carries weight: it says an input
port name cannot be produced by two different output ports of one sender.

**It does not say the sender side of `targetEndpointsUnique` holds by construction, and an
earlier version of this paragraph did say that.** The claim is injectivity in the *output port
name*, and finding F48 measured that the step before this one is where uniqueness is actually
lost: `outputPortNameFor` concatenates message, `To`, capitalized known rebec and site suffix
without escaping the separator, so `report` with `toHub` and `reportTo` with `hub` both spell
`reportToToHub`. Two distinct send sites therefore arrive at this function as the *same*
argument, and injectivity is satisfied without excluding anything. The composite a
construction argument would need — `(message, known rebec, site)` to input port name — is the
non-injective one.

So the clause is earned by a check, not by naming. See F48 and F49 in
`docs/STAGE_E_FINDINGS.md`, and `Translation.assembleGeneralProgram_targetEndpointsUnique` in
`Relico/Translation/GeneralBasic.lean` for the theorem that does establish it, whose
hypotheses include the well-formedness guard precisely because this lemma cannot replace it.
-/
theorem inputPortNameFor_outputPort_injective
    (senderInstance : ActorName) :
    Function.Injective
      (fun outputPort =>
        inputPortNameFor
          senderInstance
          outputPort) := by

  intro left right hEqual

  cases left
  cases right

  simpa [
    inputPortNameFor
  ] using
    hEqual

end Translation
end Relico
