import Relico.LF.GeneralWellFormed
import Relico.LF.GeneralCppPrinter
import Relico.Translation.GeneralBasic
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Relico
namespace GeneralLfPrinterTests

/-!
# Executable assertions for the general generated-LF family

Every value here is built by hand in Lean, with one deliberate exception that is
the point of stage D: the *widened* program is not built at all, it is
`Translation.compileGeneralModel` applied to a hand-built DTR model. A printer
assertion over a hand-built LF program checks the printer; the same assertion
over a translated one checks the printer, the translation and their agreement,
and only the second can fail when the two drift apart.

This runner reads no fixtures. There is no exporter and no decoder for this
family yet, so there is nothing on disk to read, and what is being pinned is the
exact text `renderGeneralProgram` produces and the exact accept or reject verdict
`wellFormed` returns.

Two departures from the stage design are recorded rather than buried.

**This one file covers printing, well-formedness and translation**, though §4 of
the stage C design names it a printer test. All three are pure total functions
over hand-built values, all three need the same handful of reactors to exercise,
and a second main would double the gate's cost to assert nothing the first could
not. The alternative — leaving `GeneralWellFormed.lean` with no executable
assertion at all while its two theorems only ever range over an arbitrary
program — is worse.

**It lives in `frontend/lean-bridge/`, not `Relico/Tests/`.** Every one of
`obligations.tsv`'s 2129 rows carries a `test_file` under `Relico/Tests/`, so a
module there would owe the registry new rows and an `EXPECTED_OBLIGATIONS` bump
for a family that has no benchmark yet. Being outside the import closure of
`Relico.lean` also costs the build nothing: this module is compiled on demand by
`lake env lean --run` and never becomes a Lake target.

The accept cases matter as much as the reject cases. Three of them exist purely to
hold open a door that a tightening of `wellFormed` would quietly shut: an
unconnected port, a self-connection, and one output feeding two inputs are each
legal for a measured reason, and each would be easy to forbid by accident while
strengthening something else.
-/

/-!
## Names of the base family

The base program is stage C's, unchanged in what it prints. Its values are
retyped for stage D's widened syntax — a port is a declaration rather than a
name, a state variable carries a type instead of an initial value — and the
pinned text below is byte-for-byte the text stage C pinned. That is the whole
claim of §8.2: existing output does not move.
-/

private def senderReactorName :
    ReactorName :=
  ⟨"Sender"⟩

private def receiverReactorName :
    ReactorName :=
  ⟨"Receiver"⟩

private def senderInstanceName :
    ActorName :=
  ⟨"sender0"⟩

private def receiverInstanceName :
    ActorName :=
  ⟨"receiver0"⟩

private def secondReceiverInstanceName :
    ActorName :=
  ⟨"receiver1"⟩

private def outPort :
    PortName :=
  ⟨"out"⟩

private def inPort :
    PortName :=
  ⟨"in"⟩

private def backPort :
    PortName :=
  ⟨"back"⟩

private def senderStateName :
    VarName :=
  ⟨"x"⟩

private def receiverStateName :
    VarName :=
  ⟨"y"⟩

private def deliverAction :
    ActionName :=
  ⟨"deliver"⟩

private def arrivedParameter :
    VarName :=
  ⟨"v"⟩

private def payloadParameter :
    VarName :=
  ⟨"w"⟩

private def senderStartupReactionName :
    ReactionName :=
  ⟨"sender_startup"⟩

private def receiverStartupReactionName :
    ReactionName :=
  ⟨"receiver_startup"⟩

private def receiveReactionName :
    ReactionName :=
  ⟨"receive_reaction"⟩

private def deliverReactionName :
    ReactionName :=
  ⟨"deliver_reaction"⟩

/--
An integer input port.
-/
private def inPortDecl :
    LF.GeneralPortDecl where

  name :=
    inPort

  payload :=
    .scalar
      .int

/--
An integer output port.
-/
private def outPortDecl :
    LF.GeneralPortDecl where

  name :=
    outPort

  payload :=
    .scalar
      .int

/--
The sender's own input port, used by the unconnected-port and self-connection cases.
-/
private def backPortDecl :
    LF.GeneralPortDecl where

  name :=
    backPort

  payload :=
    .scalar
      .int

/--
A boolean input port.

Kept, and its reason for existing has changed. Stage D emitted no ports at all, so a
boolean port could not reach the `lfc` gate through the translation and asserting it on
the renderer directly was the only option. Stage E's routed model *does* carry one — a
message server of arity one taking a `boolean` compiles to a `.scalar .boolean` payload —
so the claim now holds at two layers.

Both are worth keeping because they fail for different reasons. This one fails if
`renderGeneralType`'s boolean arm is wrong in the port position. The routed model's fails
if the *translation* picks the wrong payload arm, which it can do while the renderer is
perfect. Deleting this one on the grounds that the translation covers it would leave the
renderer's boolean port position asserted only through a path that has to be right about
arity, receiving class and payload selection first.
-/
private def flagInPortDecl :
    LF.GeneralPortDecl where

  name :=
    ⟨"flagIn"⟩

  payload :=
    .scalar
      .boolean

/--
A port declaration colliding with the receiver's state variable.

Spelled out here rather than reusing `receiverStateName`, because the two are
different *types* — `PortName` and `VarName` — and it is exactly that type-level
separation which makes the collision invisible to anything but the union check.
-/
private def collidingPortDecl :
    LF.GeneralPortDecl where

  name :=
    ⟨"y"⟩

  payload :=
    .scalar
      .int

/--
A reactor parameter colliding with the receiver's state variable.

The stage D half of the same check: `GeneralReactor.declaredNames` gained the
parameter list, and a predicate that gained a case nobody exercises is the defect
stage B found in `PrioritiesDistinct` one step earlier.
-/
private def collidingParameter :
    LF.GeneralTypedParameter where

  name :=
    ⟨"y"⟩

  declaredType :=
    .int

/-!
## Assertion helpers
-/

/--
Fail the run, and fail it loudly.

The runner catches this once and returns a nonzero status, so the first failing
assertion is the one reported. A later assertion cannot mask an earlier one.
-/
private def testFailure
    {α : Type}
    (message : String) :
    IO α :=
  throw
    (IO.userError
      message)

/--
Assert an exact string.

Compared whole rather than by substring search. A printer's output is the artifact
under test, so a check that passes on any text merely *containing* the expected
lines would accept a stray blank line, a duplicated block, or a reordered one —
which are precisely the mistakes an intercalation bug makes.
-/
private def expectString
    (label expected actual : String) :
    IO Unit :=
  if actual == expected then
    IO.println
      ("PASS_" ++ label)
  else
    testFailure
      (label ++
        ": expected\n" ++
        expected ++
        "\nbut got\n" ++
        actual)

/--
Assert a `Bool` predicate's exact verdict.

Takes the expected verdict as an argument rather than coming in accept and reject
flavours, because the two assertions this exists for — one instance argument list
that matches its parameters and one that does not — differ in nothing else, and a
pair of helpers would let the negative one be quietly pointed at the positive
value.
-/
private def expectBool
    (label : String)
    (expected actual : Bool) :
    IO Unit :=
  if actual == expected then
    IO.println
      ("PASS_" ++ label)
  else
    testFailure
      (label ++
        ": expected " ++
        toString expected ++
        " but got " ++
        toString actual)

/--
Assert that a rendering succeeds, with exactly the expected text.
-/
private def expectRendered
    (label expected : String)
    (actual : Except String String) :
    IO Unit :=
  match actual with

  | .error diagnostic =>
      testFailure
        (label ++
          ": expected a rendering, but it was refused: " ++
          diagnostic)

  | .ok text =>
      expectString
        label
        expected
        text

/--
Assert that a rendering is refused, with exactly the expected message.

The message is compared in full, unlike the frontend runner which compares a
structured reason. There is no reason value here to compare: a printer refusal is
a `String`, and the point of these assertions is that the refusals are worded in
the same vocabulary the sibling printers use, so that a reader of the
generated-artifact log sees one vocabulary rather than four.
-/
private def expectRefused
    (label expected : String)
    (actual : Except String String) :
    IO Unit :=
  match actual with

  | .ok text =>
      testFailure
        (label ++
          ": expected a refusal, but it rendered:\n" ++
          text)

  | .error diagnostic =>
      expectString
        label
        expected
        diagnostic

/--
Assert that a computation over some other type is refused, with exactly the
expected message.

Separate from `expectRefused` rather than replacing it: the translation refuses
with `Except String LF.GeneralStmt` and `Except String LF.GeneralProgram`, and
folding all three into one polymorphic helper would cost the `String` case its
readable failure output, which is the case a printer author reads most often.
-/
private def expectRefusedTerm
    {α : Type}
    [Repr α]
    (label expected : String)
    (actual : Except String α) :
    IO Unit :=
  match actual with

  | .ok value =>
      testFailure
        (label ++
          ": expected a refusal, but it produced\n" ++
          toString (repr value))

  | .error diagnostic =>
      expectString
        label
        expected
        diagnostic

/--
Assert that a program is well-formed.
-/
private def expectWellFormed
    (label : String)
    (program : LF.GeneralProgram) :
    IO Unit :=
  if program.wellFormed then
    IO.println
      ("PASS_" ++ label)
  else
    testFailure
      (label ++
        ": expected this program to be well-formed, but it was rejected")

/--
Assert that a program is not well-formed.
-/
private def expectIllFormed
    (label : String)
    (program : LF.GeneralProgram) :
    IO Unit :=
  if program.wellFormed then
    testFailure
      (label ++
        ": expected this program to be rejected, but it was accepted")
  else
    IO.println
      ("PASS_" ++ label)

/-!
## The base family

Stage C's program, retyped. Every reactor here has an empty parameter list and no
action of arity two or more, which is what makes it the witness for "no preamble,
no argument list, no bytes moved".
-/

/--
The sender's startup reaction: it sets its output port.
-/
private def senderStartupReaction :
    LF.GeneralReaction where

  name :=
    senderStartupReactionName

  trigger :=
    .startup

  parameters :=
    []

  body :=
    [
      .setPort
        outPort
        [.intLiteral 1]
    ]

/--
The sender, parameterised by its input ports.

Parameterised rather than copied, so that the unconnected-port case and the
self-connection case are the same reactor with one field changed. A second
hand-written copy could drift from this one and the assertions would still pass.
-/
private def senderReactorWith
    (inputPortList :
      List LF.GeneralPortDecl) :
    LF.GeneralReactor where

  name :=
    senderReactorName

  parameters :=
    []

  inputPorts :=
    inputPortList

  outputPorts :=
    [outPortDecl]

  stateVariables :=
    [
      {
        name :=
          senderStateName

        declaredType :=
          .int
      }
    ]

  logicalActions :=
    []

  startupReaction :=
    senderStartupReaction

  messageReactions :=
    []

/--
The receiver's startup reaction, with an empty body.

Empty on purpose: a DTR class whose constructor neither assigns nor sends produces
exactly this, and the printer must omit the reaction rather than emit
`reaction(startup) {= =}`.
-/
private def receiverStartupReaction :
    LF.GeneralReaction where

  name :=
    receiverStartupReactionName

  trigger :=
    .startup

  parameters :=
    []

  body :=
    []

/--
A startup reaction that declares parameters.

This shape is what `assembleGeneralStartupReaction` produces for a constructor with
formals, and stage C's printer refused it. See finding F33: the names in that list
are the *reactor's* parameters, readable with no binder, so the correct emission is
nothing at all.
-/
private def parameterisedStartupReaction :
    LF.GeneralReaction where

  name :=
    senderStartupReactionName

  trigger :=
    .startup

  parameters :=
    [arrivedParameter]

  body :=
    []

/--
The receiving reaction: triggered by an input port, forwarding to a logical action.

This is the shape the whole family exists to make expressible — no earlier LF
family in this development can write a port-triggered reaction at all.
-/
private def receiveReaction :
    LF.GeneralReaction where

  name :=
    receiveReactionName

  trigger :=
    .inputPort inPort

  parameters :=
    [arrivedParameter]

  body :=
    [
      .schedule
        deliverAction
        [.parameterVar arrivedParameter]
        ⟨0⟩
    ]

/--
A port-triggered reaction declaring two parameters.

Stage D's one remaining refusal in the parameter reader, and stage E's newest total arm.
The refusal rested on a sentence with two halves — a `GeneralPortDecl` carries a single
declared type and so delivers one value, and unlike a logical action a port has no
parameter list to destructure — and stage E falsified the first and exposed the second as
never having been the obstacle. A port now carries a payload, and the parameter list being
destructured was always the *reaction's*, which a port-triggered reaction gets from its
message server exactly as an action-triggered one does.

Kept under its old name because the shape it names has not changed, only the verdict on it.
The assertion that consumes it is the evidence for F30's retraction.
-/
private def twoParameterPortReaction :
    LF.GeneralReaction where

  name :=
    receiveReactionName

  trigger :=
    .inputPort inPort

  parameters :=
    [
      arrivedParameter,
      payloadParameter
    ]

  body :=
    []

/--
The action-triggered reaction, storing its payload.
-/
private def deliverReaction :
    LF.GeneralReaction where

  name :=
    deliverReactionName

  trigger :=
    .logicalAction deliverAction

  parameters :=
    [payloadParameter]

  body :=
    [
      .assign
        receiverStateName
        (.parameterVar payloadParameter)
    ]

/--
A reaction that writes to an **input** port.

Representable in the syntax and refused by well-formedness. Direction is not
carried in `PortName`, so the only thing standing between a translation bug and a
program `lfc` rejects is the `outputPorts` check this pins.
-/
private def setInputPortReaction :
    LF.GeneralReaction where

  name :=
    deliverReactionName

  trigger :=
    .logicalAction deliverAction

  parameters :=
    [payloadParameter]

  body :=
    [
      .setPort
        inPort
        [.parameterVar payloadParameter]
    ]

/--
The receiver, parameterised by its input ports and its message reactions.
-/
private def receiverReactorWith
    (inputPortList :
      List LF.GeneralPortDecl)
    (messageReactionList :
      List LF.GeneralReaction) :
    LF.GeneralReactor where

  name :=
    receiverReactorName

  parameters :=
    []

  inputPorts :=
    inputPortList

  outputPorts :=
    []

  stateVariables :=
    [
      {
        name :=
          receiverStateName

        declaredType :=
          .int
      }
    ]

  logicalActions :=
    [
      {
        name :=
          deliverAction

        parameters :=
          [
            {
              name :=
                arrivedParameter

              declaredType :=
                .int
            }
          ]
      }
    ]

  startupReaction :=
    receiverStartupReaction

  messageReactions :=
    messageReactionList

private def senderReactor :
    LF.GeneralReactor :=
  senderReactorWith
    []

private def senderReactorWithInputPort :
    LF.GeneralReactor :=
  senderReactorWith
    [backPortDecl]

private def receiverReactor :
    LF.GeneralReactor :=
  receiverReactorWith
    [inPortDecl]
    [
      receiveReaction,
      deliverReaction
    ]

/--
A two-parameter logical action, used for the struct assertions.

Declared on no reactor. The struct spellings it pins are reached by the widened
program through the translation; this value is what lets each of the three sites
that must agree — declaration, `schedule`, destructuring — be asserted on its own
rather than only inside a whole program, where one wrong site is a diff in a
33-line string.
-/
private def twoParameterDeliverAction :
    LF.GeneralAction where

  name :=
    deliverAction

  parameters :=
    [
      {
        name :=
          arrivedParameter

        declaredType :=
          .int
      },

      {
        name :=
          payloadParameter

        declaredType :=
          .boolean
      }
    ]

/--
A single-parameter boolean logical action.
-/
private def booleanDeliverAction :
    LF.GeneralAction where

  name :=
    deliverAction

  parameters :=
    [
      {
        name :=
          arrivedParameter

        declaredType :=
          .boolean
      }
    ]

/--
A reaction destructuring a two-value payload.
-/
private def twoParameterDeliverReaction :
    LF.GeneralReaction where

  name :=
    deliverReactionName

  trigger :=
    .logicalAction deliverAction

  parameters :=
    [
      arrivedParameter,
      payloadParameter
    ]

  body :=
    []

private def senderInstance :
    LF.GeneralReactorInstance where

  name :=
    senderInstanceName

  reactorName :=
    senderReactorName

  arguments :=
    []

private def receiverInstance :
    LF.GeneralReactorInstance where

  name :=
    receiverInstanceName

  reactorName :=
    receiverReactorName

  arguments :=
    []

/--
A second instance of the *same* receiver reactor.

Two instances sharing one reactor declaration is the structural point of the
family: Table III maps a reactive class to a reactor, so a per-instance reactor
would make the paper's own mapping unrepresentable.
-/
private def secondReceiverInstance :
    LF.GeneralReactorInstance where

  name :=
    secondReceiverInstanceName

  reactorName :=
    receiverReactorName

  arguments :=
    []

/--
An instance of a reactor nobody declares.
-/
private def ghostInstance :
    LF.GeneralReactorInstance where

  name :=
    ⟨"ghost"⟩

  reactorName :=
    ⟨"Missing"⟩

  arguments :=
    []

private def senderToReceiver :
    LF.GeneralConnection where

  sourceInstance :=
    senderInstanceName

  sourcePort :=
    outPort

  targetInstance :=
    receiverInstanceName

  targetPort :=
    inPort

  delay :=
    ⟨0⟩

private def senderToSecondReceiver :
    LF.GeneralConnection where

  sourceInstance :=
    senderInstanceName

  sourcePort :=
    outPort

  targetInstance :=
    secondReceiverInstanceName

  targetPort :=
    inPort

  delay :=
    ⟨0⟩

/--
A connection whose target port is not declared on the target reactor.
-/
private def senderToUnknownPort :
    LF.GeneralConnection where

  sourceInstance :=
    senderInstanceName

  sourcePort :=
    outPort

  targetInstance :=
    receiverInstanceName

  targetPort :=
    ⟨"missing"⟩

  delay :=
    ⟨0⟩

/--
A connection from an instance back to itself.
-/
private def senderToSelf :
    LF.GeneralConnection where

  sourceInstance :=
    senderInstanceName

  sourcePort :=
    outPort

  targetInstance :=
    senderInstanceName

  targetPort :=
    backPort

  delay :=
    ⟨0⟩

private def programWith
    (reactorList :
      List LF.GeneralReactor)
    (instanceList :
      List LF.GeneralReactorInstance)
    (connectionList :
      List LF.GeneralConnection) :
    LF.GeneralProgram where

  reactors :=
    reactorList

  instances :=
    instanceList

  connections :=
    connectionList

private def baseInstances :
    List LF.GeneralReactorInstance :=
  [
    senderInstance,
    receiverInstance
  ]

/--
The program every base printer assertion renders and the accept assertion accepts.
-/
private def baseProgram :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactor
    ]
    baseInstances
    [senderToReceiver]

/--
A declared port that nothing connects to. Legal, and load-bearing.
-/
private def programWithUnconnectedPort :
    LF.GeneralProgram :=
  programWith
    [
      senderReactorWithInputPort,
      receiverReactor
    ]
    baseInstances
    [senderToReceiver]

/--
An instance connected to itself. Legal, because the `after` delay breaks the cycle.
-/
private def programWithSelfConnection :
    LF.GeneralProgram :=
  programWith
    [
      senderReactorWithInputPort,
      receiverReactor
    ]
    baseInstances
    [
      senderToReceiver,
      senderToSelf
    ]

/--
One output feeding two inputs. Legal: source endpoints are deliberately
unconstrained, and this is the case that shows the asymmetry is real rather than an
oversight in `targetEndpointsUnique`.
-/
private def programWithBroadcast :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactor
    ]
    [
      senderInstance,
      receiverInstance,
      secondReceiverInstance
    ]
    [
      senderToReceiver,
      senderToSecondReceiver
    ]

private def programSettingInputPort :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactorWith
        [inPortDecl]
        [
          receiveReaction,
          setInputPortReaction
        ]
    ]
    baseInstances
    [senderToReceiver]

private def programWithUnknownTargetPort :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactor
    ]
    baseInstances
    [senderToUnknownPort]

/--
Two connections into one input port. The one topology `wellFormed` forbids.
-/
private def programWithDuplicateTargetEndpoint :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactor
    ]
    baseInstances
    [
      senderToReceiver,
      senderToReceiver
    ]

private def programWithPortStateCollision :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactorWith
        [
          inPortDecl,
          collidingPortDecl
        ]
        [
          receiveReaction,
          deliverReaction
        ]
    ]
    baseInstances
    [senderToReceiver]

/--
A reactor parameter colliding with a state variable of the same reactor.

The instance is given a matching argument on purpose. Adding a parameter to a
reactor whose instance supplies none would fail `instanceArgumentsMatch` as well,
and a reject assertion that holds for two reasons pins neither.
-/
private def programWithParameterStateCollision :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      {
        receiverReactor with

        parameters :=
          [collidingParameter]
      }
    ]
    [
      senderInstance,
      {
        receiverInstance with

        arguments :=
          [.int 0]
      }
    ]
    [senderToReceiver]

private def programWithDanglingInstance :
    LF.GeneralProgram :=
  programWith
    [
      senderReactor,
      receiverReactor
    ]
    [
      senderInstance,
      receiverInstance,
      ghostInstance
    ]
    [senderToReceiver]

/--
The exact text `baseProgram` must print.

Written as a list of lines joined with `"\n"` rather than as one escaped literal, so
that the expectation is auditable line by line and a blank line is visibly a blank
line. The trailing newline is added separately because it is the file's final
newline, not a separator.

Read top to bottom this is the whole claim of stage C: a port declaration block
before state, two reactors in one file, a port-triggered reaction, and a main
reactor whose connections carry `after`. **Not one byte of it changed in stage D**,
which is the assertion form of §8.2 — no parameter list on either reactor, no
preamble, and `new Sender()` still empty-handed.
-/
private def expectedProgramText :
    String :=
  String.intercalate
    "\n"
    [
      "target Cpp",
      "",
      "reactor Sender {",
      "  output out: int",
      "  state x: int = 0",
      "",
      "  reaction(startup) -> out {=",
      "    out.set(1);",
      "  =}",
      "}",
      "",
      "reactor Receiver {",
      "  input in: int",
      "  state y: int = 0",
      "  logical action deliver: int",
      "",
      "  reaction(in) -> deliver {=",
      "    auto v = *in.get();",
      "    deliver.schedule(v, 0ms);",
      "  =}",
      "",
      "  reaction(deliver) {=",
      "    auto w = *deliver.get();",
      "    y = w;",
      "  =}",
      "}",
      "",
      "main reactor {",
      "  sender0 = new Sender()",
      "  receiver0 = new Receiver()",
      "  sender0.out -> receiver0.in after 0 msec",
      "}"
    ] ++
    "\n"

/-!
## The widened family, as the output of the translation

Everything below is stage D's actual claim. The LF program is never written down:
it is `Translation.compileGeneralModel` applied to `widenedModel`, and the text
pinned below is what the printer makes of *that*. A hand-built LF program would
pin the printer alone, and the printer has already been pinned by the base
program.

One class covers every widening at once — boolean state, a boolean constructor
parameter, a three-value mixed-type payload, nested fully-parenthesized
arithmetic, comparison and boolean operators, an arity-zero action, and two
instances of one parameterised reactor with different arguments.

It also terminates. The constructor self-sends `adjust` at `after(0)`, `adjust`
self-sends `settle` at `after(5)`, and `settle` sends nothing, so the event queue
empties and the generated binary exits on its own. That is not a stylistic point:
`frontend/check-general-lf-target.sh` *runs* the binary, and a model that kept
scheduling would hang the gate rather than fail it.
-/

private def configuredClassName :
    ClassName :=
  ⟨"Configured"⟩

private def limitStateName :
    VarName :=
  ⟨"limit"⟩

private def enabledStateName :
    VarName :=
  ⟨"enabled"⟩

private def boundParameter :
    VarName :=
  ⟨"bound"⟩

private def activeParameter :
    VarName :=
  ⟨"active"⟩

private def adjustMessageName :
    MsgName :=
  ⟨"adjust"⟩

private def settleMessageName :
    MsgName :=
  ⟨"settle"⟩

private def leftParameter :
    VarName :=
  ⟨"left"⟩

private def rightParameter :
    VarName :=
  ⟨"right"⟩

private def flagParameter :
    VarName :=
  ⟨"flag"⟩

private def configuredOnInstanceName :
    ActorName :=
  ⟨"configuredOn"⟩

private def configuredOffInstanceName :
    ActorName :=
  ⟨"configuredOff"⟩

private def peerKnownRebecName :
    KnownRebecName :=
  ⟨"peer"⟩

private def pingMessageName :
    MsgName :=
  ⟨"ping"⟩

/-!
### The LF names the translation derives

Taken from `Translation`'s own name generators rather than written as string
literals. The literals appear once, in the pinned program text, and an assertion
that spelled them a second time here would agree with itself while disagreeing
with the translator.
-/

private def configuredReactorName :
    ReactorName :=
  Translation.reactorNameFor
    configuredClassName

private def adjustActionName :
    ActionName :=
  Translation.actionNameFor
    adjustMessageName

private def settleActionName :
    ActionName :=
  Translation.actionNameFor
    settleMessageName

/--
The constructor: it initialises both state variables from its formals, then
self-sends the three-value message.

The payload mixes a parameter read, a literal and a boolean parameter read, which
is what makes the emitted `Args{bound, 2, active}` an aggregate initialisation of a
mixed struct rather than of three integers.
-/
private def configuredConstructor :
    DTR.GeneralConstructor where

  parameters :=
    [
      {
        name :=
          boundParameter

        declaredType :=
          .int
      },

      {
        name :=
          activeParameter

        declaredType :=
          .boolean
      }
    ]

  body :=
    [
      .assign
        limitStateName
        (.parameterVar boundParameter),

      .assign
        enabledStateName
        (.parameterVar activeParameter),

      .send
        .selfTarget
        adjustMessageName
        [
          .parameterVar boundParameter,
          .intLiteral 2,
          .parameterVar activeParameter
        ]
        ⟨0⟩
    ]

/--
The three-parameter message server.

Its first statement is `left + right * 2 - 1`, the expression
`frontend/fixtures/general/expressions.rebeca` uses, written here with the
precedence the elaborator would give it. Fully parenthesized output is what the
printer owes, and this is the assertion that says so end to end rather than on one
expression in isolation.
-/
private def adjustMessageServer :
    DTR.GeneralMessageServer where

  name :=
    adjustMessageName

  parameters :=
    [
      {
        name :=
          leftParameter

        declaredType :=
          .int
      },

      {
        name :=
          rightParameter

        declaredType :=
          .int
      },

      {
        name :=
          flagParameter

        declaredType :=
          .boolean
      }
    ]

  body :=
    [
      .assign
        limitStateName
        (.binary
          .sub
          (.binary
            .add
            (.parameterVar leftParameter)
            (.binary
              .mul
              (.parameterVar rightParameter)
              (.intLiteral 2)))
          (.intLiteral 1)),

      .assign
        enabledStateName
        (.binary
          .logicalAnd
          (.parameterVar flagParameter)
          (.binary
            .gt
            (.stateVar limitStateName)
            (.intLiteral 0))),

      .send
        .selfTarget
        settleMessageName
        []
        ⟨5⟩
    ]

/--
The arity-zero message server, which is also what stops the program.
-/
private def settleMessageServer :
    DTR.GeneralMessageServer where

  name :=
    settleMessageName

  parameters :=
    []

  body :=
    [
      .assign
        enabledStateName
        (.boolLiteral false)
    ]

private def configuredClass :
    DTR.GeneralReactiveClass where

  name :=
    configuredClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name :=
          limitStateName

        declaredType :=
          .int
      },

      {
        name :=
          enabledStateName

        declaredType :=
          .boolean
      }
    ]

  constructor :=
    configuredConstructor

  messageServers :=
    [
      adjustMessageServer,
      settleMessageServer
    ]

private def configuredOnActor :
    DTR.GeneralActorInstance where

  name :=
    configuredOnInstanceName

  className :=
    configuredClassName

  bindings :=
    []

  arguments :=
    [
      .int 7,
      .bool true
    ]

private def configuredOffActor :
    DTR.GeneralActorInstance where

  name :=
    configuredOffInstanceName

  className :=
    configuredClassName

  bindings :=
    []

  arguments :=
    [
      .int 0,
      .bool false
    ]

private def widenedModel :
    DTR.GeneralModel where

  classes :=
    [configuredClass]

  instances :=
    [
      configuredOnActor,
      configuredOffActor
    ]

/--
The same model with one message server's body replaced by an external send that
routing refuses.

Written as a structure update so that the only difference from `widenedModel` is
the construct under test. A second hand-written class could differ in some other
way and the refusal would still be reported, which would make this assertion pass
for the wrong reason.

The send targets `settle`, and `settle` is where it is written. That is not a
self-send: the target is `.knownRebec peer`, so it leaves the reactor and needs a
port, and the coincidence of names is because `settle` is the only message server
`configuredClass` declares that takes no parameters — which is the whole point.
Steps 1 to 3 of `generalOutputPortEntryFor` all succeed here, and step 4 refuses,
so this model reaches stage E's one refusal that a *well-formed* model can reach
rather than one of routing's defensive arms.

Both instances still carry `bindings := []` while the class now declares `peer`.
That is deliberate and it is also a limit on what this model witnesses: it is a
refusal witness only. Were the arity-zero arm ever to start accepting, this model
would not begin to translate — it would fail one layer later in
`generalRouteFor`, on the missing binding, and an assertion that merely demanded
*some* refusal would not notice the difference. Hence the exact text.
-/
private def externalSendModel :
    DTR.GeneralModel where

  classes :=
    [
      {
        configuredClass with

        knownRebecs :=
          [
            {
              name :=
                peerKnownRebecName

              className :=
                configuredClassName
            }
          ]

        messageServers :=
          [
            {
              settleMessageServer with

              body :=
                [
                  .send
                    (.knownRebec peerKnownRebecName)
                    settleMessageName
                    []
                    ⟨0⟩
                ]
            }
          ]
      }
    ]

  instances :=
    [
      configuredOnActor,
      configuredOffActor
    ]

/--
The same shape again, with the send aimed at a message server no class declares.

`ping` is not a message server of `configuredClass`, so this one stops at step 3
of `generalOutputPortEntryFor` instead of step 4. Kept as a second model rather
than folded into `externalSendModel` because the two refusals are answers to
different questions. Stage E's boundary is *"a port with no payload has no
measured spelling"*, and that is a statement about the target language. Step 3's
refusal is *"you sent a message that does not exist"*, and that is a statement
about a hand-built model — a document could never carry it, because
`sendsResolveToMessageServers` rejects it at the frontend
(`Relico/DTR/GeneralWellFormed.lean`), which is exactly why the only place it can
be exercised is here.

`GeneralRouting.lean:664–673` claims steps 1 to 3 are unreachable from a
well-formed model and names the conjunct closing each. This asserts that the arm
so justified still produces the text it says it does. An unreachable arm whose
message has rotted is worse than no message: it is read only by whoever has
already lost an afternoon.
-/
private def undeclaredServerSendModel :
    DTR.GeneralModel where

  classes :=
    [
      {
        configuredClass with

        knownRebecs :=
          [
            {
              name :=
                peerKnownRebecName

              className :=
                configuredClassName
            }
          ]

        messageServers :=
          [
            {
              settleMessageServer with

              body :=
                [
                  .send
                    (.knownRebec peerKnownRebecName)
                    pingMessageName
                    []
                    ⟨0⟩
                ]
            }
          ]
      }
    ]

  instances :=
    [
      configuredOnActor,
      configuredOffActor
    ]

/--
The constructor of `configuredClass` with its first formal renamed to `limit`,
which is already one of that class's state variables.

`limitStateName` is reused rather than a fresh `"limit"` written out, so the
collision holds by construction instead of by two spellings happening to agree.
The body and the self-send are renamed with it: a `.parameterVar` naming a formal
that no longer exists would be a *different* defect, and `sendsResolveToMessageServers`
does not look inside expressions, so it would pass unnoticed and the assertion
below would be measuring the wrong thing.
-/
private def collisionConstructor :
    DTR.GeneralConstructor where

  parameters :=
    [
      {
        name :=
          limitStateName

        declaredType :=
          .int
      },

      {
        name :=
          activeParameter

        declaredType :=
          .boolean
      }
    ]

  body :=
    [
      .assign
        limitStateName
        (.parameterVar limitStateName),

      .assign
        enabledStateName
        (.parameterVar activeParameter),

      .send
        .selfTarget
        adjustMessageName
        [
          .parameterVar limitStateName,
          .intLiteral 2,
          .parameterVar activeParameter
        ]
        ⟨0⟩
    ]

/--
Finding F32's counterexample, as a model rather than as a paragraph.

A structure update on `widenedModel`, so the constructor is the only difference and
the three assertions cannot be explained by anything else. `widenedModel` itself is
asserted well-formed, translating and LF-well-formed above, which is what makes this
model's third outcome a divergence rather than an isolated fact.

`DTR.GeneralModel.wellFormed` accepts it: none of its five clauses mentions state
variables, and `namesUniqueAndValid` says so deliberately at
`Relico/DTR/GeneralWellFormed.lean:319-321`, on the ground that scope uniqueness is
"the elaborator's concern". `LF.GeneralReactor.wellFormed` rejects the result, because
`declaredNames` puts parameters and state variables in one union and requires it
`Nodup`.

**This model cannot come from a `.rebeca` file, and that is the point.**
`Relico/Frontend/GeneralElaborator.lean:793-796` rejects a constructor formal that
shadows a state variable, with its own `.parameterShadowsStateVariable` diagnostic, so
the delegation quoted above is honoured and the *tool* is protected one layer above
`wellFormed`. What is not protected is the *theorem*: its hypothesis is `m.wellFormed`,
which does not imply what the LF side checks, and a hand-built model is enough to
refute it. The gap is therefore a missing proof that the elaborator's guarantee and
the LF predicate agree -- not a missing clause in `wellFormed`, which would duplicate
the elaborator's check and collapse a layering three docstrings agree on.

If such a model ever did reach `lfc`, the outcome is measured rather than assumed:
`tools/paper-measurements/lf_semantics_probe.sh` probe `param_state_name_collision`
shows the LF validator accepting the collision and the generated C++ then failing on a
reference member bound to a temporary. That is why the LF-side `Nodup` requirement is
worth keeping, and it is the whole of what the probe licenses.
-/
private def collisionModel :
    DTR.GeneralModel where

  classes :=
    [
      {
        configuredClass with

        constructor :=
          collisionConstructor
      }
    ]

  instances :=
    [
      configuredOnActor,
      configuredOffActor
    ]

/--
The refusal a send to a parameterless message server earns in stage E.

Asserted on its exact text, not merely on being an error. Stage D's version of this
def pinned the refusal of *every* external send and said so; stage E deletes that
refusal, and what is left is narrower and more interesting. The message names a
missing measurement rather than a defect in the model, because the model is fine:
`msgsrv settle() {}` is ordinary Rebeca and stage D translated it into a logical
action without complaint. It is the *port* that has no measured spelling, and
§11.2 records the probe that would remove this refusal as owed.

A diagnostic that decays into a bare `.error` later would still be an error, and
would no longer tell a reader that the obstacle is a measurement nobody has taken.
-/
private def parameterlessPortDiagnostic :
    String :=
  "message server `Configured`.`settle` takes no parameters, " ++
    "so the port that would carry it has no payload; " ++
    "whether the target accepts a port with no value type is unmeasured, " ++
    "so this translation refuses rather than guesses"

/--
The refusal a send to an undeclared message server earns.

Step 3 of `generalOutputPortEntryFor`, one of the three arms that file argues a
well-formed model never reaches. The text carries the send's address, and the
address is rendered by `renderGeneralSendSite`, so the two halves of this literal
that look like prose — *"message server `settle`"* and *"statement at index 0
counting from zero"* — are the two halves of that function's output and will move
if it moves.

Both class names in the text are `Configured`, and that is not a copy-paste slip:
`peer` is declared to have the sending class's own class, so the class that sends
and the class that fails to declare `ping` are the same one. A reader who sees one
name twice should be able to check that against the model rather than against this
comment, which is why `undeclaredServerSendModel` binds `peer` to
`configuredClassName`.
-/
private def undeclaredMessageServerDiagnostic :
    String :=
  "class `Configured` sends `ping` to `peer` at message server `settle`, " ++
    "statement at index 0 counting from zero, " ++
    "but class `Configured` declares no message server of that name"

/--
The refusal a send site with no resolved port earns.

The only failure `compileGeneralStmt` can still produce, and by design it is a
statement about this translator rather than about any model: `outputPortEnvOf`
walks the very sites `externalSendsOf` produces, so a site missing from its own
class's environment is a defect. #47 will discharge the arm by induction, at which
point this assertion becomes the last executable trace of a diagnostic no run can
reach.

That is a reason to keep it, not to drop it. It is pinned here by handing
`compileGeneralStmt` an empty environment, which no caller inside the translator
ever does and which is the whole trick: the arm is unreachable *through
`compileGeneralModel`*, not unreachable through its own interface.
-/
private def unresolvedSendSiteDiagnostic :
    String :=
  "no output port was resolved for the send `peer`.`ping` " ++
    "in message server `settle`, statement at index 0 counting from zero; " ++
    "every external send site is resolved by outputPortEnvOf, " ++
    "so this is a defect in the translator and not in the model"

/--
The exact text the translation of `widenedModel` must print.

Every line here is derived, not chosen: the reactor name from `reactorNameFor`, the
action names from `actionNameFor`, the struct name and the payload binder from the
printer's two naming functions, the initial values from `GeneralType.initialValue`,
and the two argument lists from the actors' own values.

Two lines are worth reading twice. `limit = ((left + (right * 2)) - 1);` is full
parenthesization, so the target's precedence never has to agree with Rebeca's. And
`adjust_action.schedule(Configured_adjust_action_Args{bound, 2, active}, 0ms);`
reads a reactor parameter inside a payload with no binder, which is the measured
fact §5.5 rests on and finding F33's whole subject.
-/
private def expectedWidenedProgramText :
    String :=
  String.intercalate
    "\n"
    [
      "target Cpp",
      "",
      "public preamble {=",
      "  struct Configured_adjust_action_Args { int left; int right; bool flag; };",
      "=}",
      "",
      "reactor Configured(bound: int = 0, active: bool = false) {",
      "  state limit: int = 0",
      "  state enabled: bool = false",
      "  logical action adjust_action: Configured_adjust_action_Args",
      "  logical action settle_action: void",
      "",
      "  reaction(startup) -> adjust_action {=",
      "    limit = bound;",
      "    enabled = active;",
      "    adjust_action.schedule(Configured_adjust_action_Args{bound, 2, active}, 0ms);",
      "  =}",
      "",
      "  reaction(adjust_action) -> settle_action {=",
      "    auto adjust_action_payload = *adjust_action.get();",
      "    auto left = adjust_action_payload.left;",
      "    auto right = adjust_action_payload.right;",
      "    auto flag = adjust_action_payload.flag;",
      "    limit = ((left + (right * 2)) - 1);",
      "    enabled = (flag && (limit > 0));",
      "    settle_action.schedule(5ms);",
      "  =}",
      "",
      "  reaction(settle_action) {=",
      "    enabled = false;",
      "  =}",
      "}",
      "",
      "main reactor {",
      "  configuredOn = new Configured(bound=7, active=true)",
      "  configuredOff = new Configured(bound=0, active=false)",
      "}"
    ] ++
    "\n"

/--
Translate the widened model and print it, in one `Except`.

The emitter and the assertion call this same function, so the bytes `lfc` compiles
are the bytes the assertion pinned. Two paths that each recompute the program would
be two chances to compile something no assertion ever checked.
-/
private def widenedProgramText :
    Except String String := do

  let program ←
    Translation.compileGeneralModel
      widenedModel

  LF.CppPrinter.renderGeneralProgram
    program

/--
An instance of the translated reactor, written out rather than taken from the
translation's own output.

Hand-built on purpose, and only for the three assertions that need an instance the
translation would never produce. The named-argument *form* is a printer question — finding
F31, a divergence from Fig. 5's positional `ArgList` — and pinning it on a value this file
controls keeps it separable from the translation, which is pinned whole by
`expectedWidenedProgramText`. The arguments match `configuredOn`'s so that the positive
rendering is the same text that appears there.
-/
private def widenedInstanceWithNamedArguments :
    LF.GeneralReactorInstance where

  name :=
    configuredOnInstanceName

  reactorName :=
    configuredReactorName

  arguments :=
    [
      .int 7,
      .bool true
    ]

/--
The same instance with one argument too few.

A structure update, so arity is the only difference from the positive case.
-/
private def widenedInstanceWithWrongArity :
    LF.GeneralReactorInstance :=
  {
    widenedInstanceWithNamedArguments with

    arguments :=
      [.int 7]
  }

/--
The same instance with its two arguments transposed.

Right count, wrong types, which is the half of `argumentsMatchParameters` that an arity
test alone would leave unexercised: `bool` for `bound: int` and `int` for `active: bool`.
-/
private def widenedInstanceWithWrongTypes :
    LF.GeneralReactorInstance :=
  {
    widenedInstanceWithNamedArguments with

    arguments :=
      [
        .bool true,
        .int 7
      ]
  }

/-!
## The routed family

Stage E's own model, and the first one in this file whose translation has ports,
connections and two reactors. `widenedModel` above is one class with two instances and
every send aimed at itself, so it exercises the whole of stages C and D and none of
stage E: no known rebec resolves, `routesOf` returns the empty list, and the printed
`main reactor` body is nothing but instances.

Two classes, three instances, three send sites, three connections. Every one of those
numbers is load-bearing, and each is a claim §7 of the stage E design argues for:

**Two sends to one message server** of one receiver, so `generalSiteSuffixFor` has to
suffix both — `reportToHub1` and `reportToHub2` — while a third send to a *different*
server of the same receiver stays bare. That is §4.2's table; §4.2's prose says
something else, and this model is where the disagreement becomes a byte.

**A leading assignment in the sending body**, so the three sends sit at statement
indices 1, 2 and 3 rather than 0, 1 and 2. `SendSite.index` is a statement position
(§7.1) and not a send ordinal (§4.1). Without a non-send statement in front of them the
two readings compute the same list and nothing here could say which one is implemented.

**A receiver whose constructor body is empty**, so its reactor has no startup reaction at
all. All **24** committed `expected/lf-source/*.lf` files have a startup reaction with a
non-empty body, so `renderGeneralStartupReaction`'s empty arm has never reached a real
`lfc` — stage C's design says so at `docs/STAGE_C_DESIGN.md:750` and leaves it owed.

**A second instance of the receiving class that nothing sends to**, so its three input
ports are declared and unconnected. Input ports are a projection of the *class*
(`generalInputPortsOf`) rather than of the instance, because `lfc 0.11.0` rejects
many-to-one connections; the price of that asymmetry is exactly this instance, and §7.2
rests on unconnected input ports being legal. The probe measured that on hand-written
LF. This is what measures it on generated LF.

**Payload arities one and two**, so both `setPort` arms and both parameter-read arms run:
an aggregate `Args{...}` beside a bare `false`, a destructured struct beside a bare
`*get()`.

The model terminates, and that is a requirement rather than a remark.
`frontend/check-general-lf-target.sh` *runs* the compiled binary, so a model whose
reactions re-armed themselves would hang the gate rather than fail it. `poll` fires once
from startup and schedules nothing further; the sends it makes reach a class that sends
nothing.
-/

private def sensorClassName :
    ClassName :=
  ⟨"Sensor"⟩

private def gatewayClassName :
    ClassName :=
  ⟨"Gateway"⟩

private def hubKnownRebecName :
    KnownRebecName :=
  ⟨"hub"⟩

private def readingStateName :
    VarName :=
  ⟨"reading"⟩

private def lastLevelStateName :
    VarName :=
  ⟨"lastLevel"⟩

private def alarmStateName :
    VarName :=
  ⟨"alarm"⟩

private def startParameter :
    VarName :=
  ⟨"start"⟩

private def levelParameter :
    VarName :=
  ⟨"level"⟩

private def urgentParameter :
    VarName :=
  ⟨"urgent"⟩

private def fullParameter :
    VarName :=
  ⟨"full"⟩

private def pollMessageName :
    MsgName :=
  ⟨"poll"⟩

private def reportMessageName :
    MsgName :=
  ⟨"report"⟩

private def resetMessageName :
    MsgName :=
  ⟨"reset"⟩

private def probeInstanceName :
    ActorName :=
  ⟨"probe"⟩

private def stationInstanceName :
    ActorName :=
  ⟨"station"⟩

private def spareInstanceName :
    ActorName :=
  ⟨"spare"⟩

/--
The sensor's constructor: it seeds its one state variable from its one formal and
self-sends `poll`.

The self-send is what makes the model run at all. `poll` is where every external send
lives, and a reaction triggered by a logical action nothing schedules is dead code that
`lfc` compiles and never executes — which would leave the three `set()` calls asserted
in this file and unexecuted by the target gate.
-/
private def sensorConstructor :
    DTR.GeneralConstructor where

  parameters :=
    [
      {
        name :=
          startParameter

        declaredType :=
          .int
      }
    ]

  body :=
    [
      .assign
        readingStateName
        (.parameterVar startParameter),

      .send
        .selfTarget
        pollMessageName
        []
        ⟨0⟩
    ]

/--
The one message server that sends: an assignment and then three external sends.

The assignment is first on purpose — see the family note above on §7.1 against §4.1.
It also reads and writes the state variable the next send's payload reads, so the
emitted order of the two statements is observable in the generated C++ rather than only
in the `.lf` file.

The three delays are all different and two of them are nonzero. No probe under
`tools/paper-measurements/` has ever compiled a *connection* with a nonzero `after` —
`after 0 msec` is measured many times over and `after 3 msec` is not measured at all —
so `after 3 msec` and `after 7 msec` are first established by the target gate this
model feeds. That is the right place for them: they are a claim about `lfc`, and a
probe asserting them would be a second, weaker copy of a gate that compiles and runs
the real thing.
-/
private def pollMessageServer :
    DTR.GeneralMessageServer where

  name :=
    pollMessageName

  parameters :=
    []

  body :=
    [
      .assign
        readingStateName
        (.binary
          .add
          (.stateVar readingStateName)
          (.intLiteral 1)),

      .send
        (.knownRebec hubKnownRebecName)
        reportMessageName
        [
          .stateVar readingStateName,
          .boolLiteral true
        ]
        ⟨0⟩,

      .send
        (.knownRebec hubKnownRebecName)
        reportMessageName
        [
          .binary
            .mul
            (.stateVar readingStateName)
            (.intLiteral 2),
          .boolLiteral false
        ]
        ⟨3⟩,

      .send
        (.knownRebec hubKnownRebecName)
        resetMessageName
        [.boolLiteral false]
        ⟨7⟩
    ]

/--
The sending class. One known rebec, one state variable, one message server.
-/
private def sensorClass :
    DTR.GeneralReactiveClass where

  name :=
    sensorClassName

  knownRebecs :=
    [
      {
        name :=
          hubKnownRebecName

        className :=
          gatewayClassName
      }
    ]

  stateVariables :=
    [
      {
        name :=
          readingStateName

        declaredType :=
          .int
      }
    ]

  constructor :=
    sensorConstructor

  messageServers :=
    [pollMessageServer]

/--
The receiver's two-parameter message server, and the reason a struct payload exists in
this model at all.

Its two formals have different types, so the emitted struct is mixed and the two
destructuring reads are of different types too. Its body assigns both formals to state
variables, which is what stops the reactor's generated C++ from having two unread
locals — `-Wunused-variable` is not fatal, but the target gate greps for
`-Wunused-private-field` and a body that read nothing would be a poor witness for the
parameter-read arms.
-/
private def reportMessageServer :
    DTR.GeneralMessageServer where

  name :=
    reportMessageName

  parameters :=
    [
      {
        name :=
          levelParameter

        declaredType :=
          .int
      },

      {
        name :=
          urgentParameter

        declaredType :=
          .boolean
      }
    ]

  body :=
    [
      .assign
        lastLevelStateName
        (.parameterVar levelParameter),

      .assign
        alarmStateName
        (.parameterVar urgentParameter)
    ]

/--
The receiver's one-parameter message server: the arity-one, `boolean` case.

Arity one is what makes `generalPortPayloadFor` emit `.scalar` rather than a
one-field struct, so this server is the whole of the difference between
`resetToHub: bool` and `resetToHub: Gateway_reset_action_Args`. It is also the second
layer at which the boolean port type is now pinned; the note on `flagInPortDecl` above
says why both are kept.
-/
private def resetMessageServer :
    DTR.GeneralMessageServer where

  name :=
    resetMessageName

  parameters :=
    [
      {
        name :=
          fullParameter

        declaredType :=
          .boolean
      }
    ]

  body :=
    [
      .assign
        alarmStateName
        (.parameterVar fullParameter)
    ]

/--
The receiving class, whose constructor is empty.

The empty constructor is written as an inline literal rather than as a named def
because there is nothing in it to name. It is also the one field of this class that an
edit could change without breaking anything visible, so: an empty body is what makes
`renderGeneralStartupReaction` return `""` and `renderGeneralReactor` filter the
reaction away, and the pinned text below has `reactor Gateway {` with no
`reaction(startup)` under it. Giving this constructor a statement would silently
retire that coverage.

It declares no known rebecs and sends nothing. A receiver that also sent would make
route order and reaction order harder to read off the expected text, and fan-in is
stage F's subject, not this one's.
-/
private def gatewayClass :
    DTR.GeneralReactiveClass where

  name :=
    gatewayClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name :=
          lastLevelStateName

        declaredType :=
          .int
      },

      {
        name :=
          alarmStateName

        declaredType :=
          .boolean
      }
    ]

  constructor :=
    {
      parameters :=
        []

      body :=
        []
    }

  messageServers :=
    [
      reportMessageServer,
      resetMessageServer
    ]

/--
The sending instance, and the first non-empty `bindings` store in this file.

`bindings` is a `Store KnownRebecName ActorName`, so this is a list of pairs rather
than a record. Every model above it carries `bindings := []`, which is why every model
above it routes nothing.

Its one argument is what `Sensor`'s one constructor formal is checked against, and it is
nonzero so that `start=4` in the pinned text cannot be confused with
`GeneralType.initialValue`'s `int` default.
-/
private def probeActor :
    DTR.GeneralActorInstance where

  name :=
    probeInstanceName

  className :=
    sensorClassName

  bindings :=
    [(hubKnownRebecName, stationInstanceName)]

  arguments :=
    [.int 4]

/--
The bound receiver.

No arguments, because `Gateway`'s constructor has no formals — which also means the
reactor is printed without a parameter list, so `new Gateway()` in the pinned text is
`instanceArgumentsMatch` holding vacuously rather than by agreement.
-/
private def stationActor :
    DTR.GeneralActorInstance where

  name :=
    stationInstanceName

  className :=
    gatewayClassName

  bindings :=
    []

  arguments :=
    []

/--
A second `Gateway` nobody sends to.

A structure update on `stationActor`, so the name is the only difference and the three
unconnected input ports it declares cannot be explained by anything else. This is the
instance §7.2's asymmetry costs: input ports come from `generalInputPortsOf className`,
a projection of the class, so every instance of `Gateway` declares all three whether or
not a connection reaches it.
-/
private def spareActor :
    DTR.GeneralActorInstance :=
  {
    stationActor with

    name :=
      spareInstanceName
  }

/--
The routed model.

Class order fixes reactor order, and instance order fixes both instance order and route
order, so this is where the expected text's ordering comes from. `routesOf` walks
instances in declaration order and, within an instance, sites in canonical order:
`probe` contributes all three routes, `station` and `spare` contribute none.
-/
private def routedModel :
    DTR.GeneralModel where

  classes :=
    [
      sensorClass,
      gatewayClass
    ]

  instances :=
    [
      probeActor,
      stationActor,
      spareActor
    ]

/-!
### The six refusals routing can reach and no document can produce

`Relico/Translation/GeneralRouting.lean` has exactly eight causes that reach `routesOf`,
and all eight share one `Except String`. Two are pinned in `translationAssertions` above,
against `compileGeneralModel`: the arity-zero payload and the undeclared message server.
The other six are pinned here. The inventory, and the line that *decides* each cause as
distinct from the line that raises it, is finding F47 in `docs/STAGE_E_FINDINGS.md`. That
finding exists because two docstrings in `Relico/Translation/GeneralBasic.lean` credited
this coverage to `lean-reject` fixtures — documents the *frontend* refuses, which
therefore never reach a translation function at all.

Each of the six is a structure update on `routedModel` changing one field, so a refusal
cannot be explained by anything but the construct under test, the discipline
`externalSendModel` follows against `widenedModel`. `routedModel` is the base rather than
`widenedModel` because four of the six are arms a model only gets close enough to raise
once it actually routes.

None of the six can be written as a document, and the conjunct that stops each one is
worth naming rather than gesturing at, since "well-formedness rules it out" is the kind of
sentence F47 was made of. Measured against `wellFormed`'s five conjuncts in
`Relico/DTR/GeneralWellFormed.lean:359`: `sendTargetsDeclared` closes the undeclared known
rebec; `sendsResolveToMessageServers` closes the undeclared *class* of a declared known
rebec, and `bindingsMatchDeclarations` does **not**, because a class that is never
instantiated has no bindings to check; and `bindingsMatchDeclarations` closes the remaining
four — three through `bindingsMatchClass`, whose `none` arms are at `:162` and `:168` and
whose class comparison is at `:172`, and the fourth through its own `none` arm at `:189`.

The assertions call `Translation.routesOf` rather than `compileGeneralModel`, one layer in,
because `routesOf` is the function all eight causes reach. Going through the outer function
would additionally assert that no arm of *its* own fires first, which is a different claim,
and one that would quietly absorb these six if it ever stopped holding.
-/

private def relayClassName :
    ClassName :=
  ⟨"Relay"⟩

private def absentHubInstanceName :
    ActorName :=
  ⟨"absentHub"⟩

/--
`Sensor` with its one known-rebec declaration removed.

`poll` still sends three times to `hub`, so every send now names a rebec the class does
not declare, and `generalOutputPortEntryFor` refuses at step 1. The refusal reported is
the *first* send's, because `generalOutputPortEntriesOf` recurses left to right and
returns the first `.error` it meets; that is why the expected text names statement index
1 and not 2.
-/
private def undeclaredKnownRebecModel :
    DTR.GeneralModel :=
  {
    routedModel with

    classes :=
      [
        {
          sensorClass with

          knownRebecs :=
            []
        },

        gatewayClass
      ]
  }

/--
`Sensor` declaring `hub` to be a `Relay`, which this model does not declare.

Step 2, and the cause the earlier docstring in `GeneralBasic.lean` omitted entirely.
`Relay` is declared nowhere in this file but here, so the class table genuinely lacks it
rather than having it under another name.
-/
private def undeclaredRebecClassModel :
    DTR.GeneralModel :=
  {
    routedModel with

    classes :=
      [
        {
          sensorClass with

          knownRebecs :=
            [
              {
                name :=
                  hubKnownRebecName

                className :=
                  relayClassName
              }
            ]
        },

        gatewayClass
      ]
  }

/--
`probe` binding nothing at all, while its class still declares and sends to `hub`.

The first of the four `generalRouteFor` reaches, and the one the note on
`externalSendModel` above predicts in passing: *"it would fail one layer later in
`generalRouteFor`, on the missing binding"*. That prediction is asserted here rather than
left as prose — which is the whole of what finding F47 asks for.

Only the sending instance changes. `stationActor` and `spareActor` are repeated verbatim
because the update is on the list, not on an element of it, and a list literal is the only
way Lean lets one element differ.
-/
private def unboundKnownRebecModel :
    DTR.GeneralModel :=
  {
    routedModel with

    instances :=
      [
        {
          probeActor with

          bindings :=
            []
        },

        stationActor,
        spareActor
      ]
  }

/--
`probe` binding `hub` to an instance name the model never instantiates.

`absentHub` is not a typo of `station`: it is spelled to be obviously absent, so a reader
who meets this diagnostic in the wild is not left wondering whether two similar names were
confused.
-/
private def bindingNotInstantiatedModel :
    DTR.GeneralModel :=
  {
    routedModel with

    instances :=
      [
        {
          probeActor with

          bindings :=
            [(hubKnownRebecName, absentHubInstanceName)]
        },

        stationActor,
        spareActor
      ]
  }

/--
`probe` binding `hub` to itself, so the bound instance is a `Sensor` where `Sensor`
declares a `Gateway`.

A self-binding rather than a third class, because it makes the mismatch out of what the
model already has: no new class means nothing else about the model moved, and the
diagnostic's two class names come from the two places that genuinely disagree.

This is the cause whose message names a port, and the port it names is `reportToHub1` —
the first entry in canonical site order, carrying the site suffix `routedSiteSuffixes`
pins independently. So this assertion is also the only place the naming rule and a refusal
are checked against each other.
-/
private def bindingClassMismatchModel :
    DTR.GeneralModel :=
  {
    routedModel with

    instances :=
      [
        {
          probeActor with

          bindings :=
            [(hubKnownRebecName, probeInstanceName)]
        },

        stationActor,
        spareActor
      ]
  }

/--
`probe` instantiating `Relay`, a class the model does not declare.

The only one of the eight raised by `routesOfInstances` itself rather than by a callee, and
the only one that fails before any send is looked at.
-/
private def instanceClassUndeclaredModel :
    DTR.GeneralModel :=
  {
    routedModel with

    instances :=
      [
        {
          probeActor with

          className :=
            relayClassName
        },

        stationActor,
        spareActor
      ]
  }

/--
The six expected refusals, one per cause, written out rather than derived.

Derived expectations are the failure this whole section exists to avoid: a text built by
calling the same concatenation the translator calls would agree with any edit to it,
including one that dropped a name. These are literals, and the class, rebec, message,
instance and port names in them are the ones the models above carry.
-/
private def undeclaredKnownRebecDiagnostic :
    String :=
  "class `Sensor` sends to `hub` at " ++
    "message server `poll`, statement at index 1 counting from zero, " ++
    "but declares no known rebec of that name"

private def undeclaredRebecClassDiagnostic :
    String :=
  "known rebec `hub` of class `Sensor` is declared to have class `Relay`, " ++
    "which the model does not declare"

private def unboundKnownRebecDiagnostic :
    String :=
  "instance `probe` binds no known rebec named `hub`, " ++
    "which its class `Sensor` declares and sends to"

private def bindingNotInstantiatedDiagnostic :
    String :=
  "instance `probe` binds `hub` to `absentHub`, " ++
    "which the model does not instantiate"

private def bindingClassMismatchDiagnostic :
    String :=
  "instance `probe` binds `hub` to `probe` of class `Sensor`, " ++
    "but its own class declares that rebec to have class `Gateway`, " ++
    "so the payload of port `reportToHub1` was built from the wrong message server"

private def instanceClassUndeclaredDiagnostic :
    String :=
  "instance `probe` instantiates class `Relay`, " ++
    "which the model does not declare"

/--
The site suffixes routing computes for `Sensor`, as one auditable string.

`"1|2|"` and not `"|2|"`. §4.2's *table* suffixes every site of a pair that has more than
one, and §4.2's *prose* leaves the first of several bare; the table wins, because
`reportToHub` would otherwise mean "the first of several" in one class and "the only one"
in another, with nothing in the generated code able to tell them apart. The empty third
entry is the other half of the rule: `reset` is sent once, so its port is unsuffixed.

Computed from `numberedExternalSendsOfClass` rather than from the port names, so this
assertion fails if the *rule* changes even when the names happen to survive.
-/
private def routedSiteSuffixes :
    String :=
  String.intercalate
    "|"
    ((Translation.numberedExternalSendsOfClass
      sensorClass).map
      (fun numbered =>
        Translation.generalSiteSuffixFor
          (Translation.externalSendsOfClass
            sensorClass)
          numbered.fst
          numbered.snd))

/--
The statement indices of `Sensor`'s three external sends.

`"1|2|3"`, because `poll`'s first statement is the assignment. §4.1 of the design reads
the index as a send ordinal and would compute `"0|1|2"`; §7.1 reads it as a position over
*all* statements and is what `externalSendsFromIndex` implements. The two readings are
distinguishable only in a body that mixes sends with something else, which is why this
model has one.

The consequence is that `SendSite.index` is sparse — no site here has index 0 — and any
future code that treats it as a dense counter over sends will disagree with this string.

**Rendered by `Translation.renderGeneralSitePath`, not by `toString`, as of stage H.** The
index became `List Nat` under decision `0046`, and `toString ([1] : List Nat)` is `"[1]"`, so
`toString` here would have silently moved this assertion's value to `"[1]|[2]|[3]"`. Every send
in this model is at the top level of its body, so each path has one component and the expected
string is unchanged. That is the point of routing both this digest and every diagnostic through
one path renderer: the level-0 spelling survives the type change, and a nested send would show
its path here as `1.0` rather than as an unreadable list.
-/
private def routedSendSiteIndices :
    String :=
  String.intercalate
    "|"
    ((Translation.externalSendsOfClass
      sensorClass).map
      (fun send =>
        Translation.renderGeneralSitePath
          send.site.index))

/--
The reaction order the *specification* function assigns, one class per group.

`generalReactionNamesOf` is the function §7.3's two replacement theorems are stated
against, and `compileGeneralMessageServerReactionGroup` is what actually builds the
reactions. They are separate pieces of code that must agree, and the assertion below
compares this against the reaction names of the program the translation produced.

Nothing here is spelled as a literal, so a rename in `NameGeneration.lean` moves both
sides at once and this assertion stays silent. That is a real limit and not the intended
economy it was once described as: the sentence here used to end *"correctly, because it is
about order"*, and finding **F60** records why that is backwards. Both sides consume
`routesOf`, which is where level 1's sort is applied, so **order** is precisely what this
comparison cannot see — every permutation the sort can produce moves the two sides
together. What it can see, and what it is for, is the two pieces of code **drifting apart**.
The names themselves are pinned once, in the program text, and the order is pinned against
a literal in the priority fan-in block below.

The routes come from `routesOf`, and a failure to route surfaces as a refusal rather than
as an empty list: an empty list would drop every port reaction from the specified order
and the comparison would fail loudly anyway, but a refusal names the reason.
-/
private def routedSpecifiedReactionOrder :
    Except String String := do

  let routes ←
    Translation.routesOf
      routedModel

  pure
    (String.intercalate
      "|"
      (routedModel.classes.map
        (fun reactiveClass =>
          String.intercalate
            ","
            ((Translation.generalReactionNamesOf
              (Translation.selfSendsOfClass
                reactiveClass)
              routes
              reactiveClass.name
              reactiveClass.messageServers).map
              (fun reactionName =>
                reactionName.value)))))

/--
The exact text the translation of `routedModel` must print.

Read against the widened program above, everything new in stage E is on this page: a
preamble struct reached from a *port* rather than from an action, an output-port block, an
input-port block, a `set()` whose argument is an aggregate initialisation, a `set()` whose
argument is a bare literal, five reactions in one reactor, a reactor with no startup
reaction, three instances of two reactors, and a `main reactor` body with connections in
it.

Six lines repay a second reading.

`  struct Gateway_report_action_Args { int level; bool urgent; };` appears **once**,
though five declarations claim it: `Gateway`'s own `report_action` and both of `Sensor`'s
`reportTo…` output ports and both of `Gateway`'s matching input ports. They agree because
`generalPortPayloadFor` names the struct after the *receiving* reactor and the receiving
action, which is the same pair `renderGeneralActionDecl` uses. The dedup that collapses
them keeps the first and does not compare the rest — finding F41 — and here the survivor
comes from `Sensor`'s first output port rather than from `Gateway`'s action.

`  reaction(poll_action) -> reportToHub1, reportToHub2, resetToHub {=` is the effect
clause derived from the body, so a send this file forgot could not be smuggled into the
clause and a clause this printer forgot could not be smuggled past `lfc`.

`    reportToHub2.set(Gateway_report_action_Args{(reading * 2), false});` is the
arity-two `setPort` arm: full parenthesization inside an aggregate initialiser, and a
mixed struct built from an expression and a literal.

`    resetToHub.set(false);` is the arity-one arm — no struct name, because the payload
is a `.scalar` and not a one-field struct.

`reactor Gateway {` carries no `reaction(startup)`, because its constructor body is
empty. That is `renderGeneralStartupReaction`'s empty arm, reaching a real `lfc` for the
first time.

`  spare = new Gateway()` declares three input ports that no connection reaches, which
§7.2 needs to be legal and which the probe measured only on hand-written LF.
-/
private def expectedRoutedProgramText :
    String :=
  String.intercalate
    "\n"
    [
      "target Cpp",
      "",
      "public preamble {=",
      "  struct Gateway_report_action_Args { int level; bool urgent; };",
      "=}",
      "",
      "reactor Sensor(start: int = 0) {",
      "  output reportToHub1: Gateway_report_action_Args",
      "  output reportToHub2: Gateway_report_action_Args",
      "  output resetToHub: bool",
      "  state reading: int = 0",
      "  logical action poll_action: void",
      "",
      "  reaction(startup) -> poll_action {=",
      "    reading = start;",
      "    poll_action.schedule(0ms);",
      "  =}",
      "",
      "  reaction(poll_action) -> reportToHub1, reportToHub2, resetToHub {=",
      "    reading = (reading + 1);",
      "    reportToHub1.set(Gateway_report_action_Args{reading, true});",
      "    reportToHub2.set(Gateway_report_action_Args{(reading * 2), false});",
      "    resetToHub.set(false);",
      "  =}",
      "}",
      "",
      "reactor Gateway {",
      "  input reportToHub1FromProbe: Gateway_report_action_Args",
      "  input reportToHub2FromProbe: Gateway_report_action_Args",
      "  input resetToHubFromProbe: bool",
      "  state lastLevel: int = 0",
      "  state alarm: bool = false",
      "  logical action report_action: Gateway_report_action_Args",
      "  logical action reset_action: bool",
      "",
      "  reaction(report_action) {=",
      "    auto report_action_payload = *report_action.get();",
      "    auto level = report_action_payload.level;",
      "    auto urgent = report_action_payload.urgent;",
      "    lastLevel = level;",
      "    alarm = urgent;",
      "  =}",
      "",
      "  reaction(reportToHub1FromProbe) {=",
      "    auto reportToHub1FromProbe_payload = *reportToHub1FromProbe.get();",
      "    auto level = reportToHub1FromProbe_payload.level;",
      "    auto urgent = reportToHub1FromProbe_payload.urgent;",
      "    lastLevel = level;",
      "    alarm = urgent;",
      "  =}",
      "",
      "  reaction(reportToHub2FromProbe) {=",
      "    auto reportToHub2FromProbe_payload = *reportToHub2FromProbe.get();",
      "    auto level = reportToHub2FromProbe_payload.level;",
      "    auto urgent = reportToHub2FromProbe_payload.urgent;",
      "    lastLevel = level;",
      "    alarm = urgent;",
      "  =}",
      "",
      "  reaction(reset_action) {=",
      "    auto full = *reset_action.get();",
      "    alarm = full;",
      "  =}",
      "",
      "  reaction(resetToHubFromProbe) {=",
      "    auto full = *resetToHubFromProbe.get();",
      "    alarm = full;",
      "  =}",
      "}",
      "",
      "main reactor {",
      "  probe = new Sensor(start=4)",
      "  station = new Gateway()",
      "  spare = new Gateway()",
      "  probe.reportToHub1 -> station.reportToHub1FromProbe after 0 msec",
      "  probe.reportToHub2 -> station.reportToHub2FromProbe after 3 msec",
      "  probe.resetToHub -> station.resetToHubFromProbe after 7 msec",
      "}"
    ] ++
    "\n"

/--
Translate the routed model and print it, in one `Except`.

Shared between the emitter and the assertion, for the reason `widenedProgramText` is:
the bytes `lfc` compiles have to be the bytes an assertion pinned, and two paths that
each recompute the program would be two chances to compile something unchecked.
-/
private def routedProgramText :
    Except String String := do

  let program ←
    Translation.compileGeneralModel
      routedModel

  LF.CppPrinter.renderGeneralProgram
    program

/-!
### The F56 witness: two sends to one message server, from one body, at one tag

Every other model in this file self-sends a given message **at most once**, and that is
precisely why none of them can detect whether the per-site repair is right. Under the
`≤ 1` suffix rule a one-site message keeps the name it had before send sites existed, so
`baseProgram`, `widenedModel` and `routedModel` render byte-identically before and after
the repair. They are regression witnesses, not repair witnesses.

This model is the repair witness. `Pulse`'s constructor sends `tick` twice, with different
payloads and the **same** delay, so both messages land at one tag. That combination is what
finding F56 measured as a silent loss against `lfc` 0.11.0: two `schedule` calls on one
logical action at one tag keep only the last value, and every exit code stays 0. Before the
repair this model emits one action and one reaction and drops the payload `1`; after it,
one action and one reaction **per site**.

`keep-alive.rebeca` is deliberately not the witness even though it has two sends of one
message. Its sends sit in two different bodies — the constructor and `keepAlive` itself —
which run at different times, so it is a near miss rather than a live loss. Reusing it
would have produced a test that passes either way.

The payloads differ (`1` and `2`) rather than being two copies of one value, so that the
two emitted `schedule` calls are distinguishable in the expected text. Two identical
schedules would render as two identical lines, and an assertion over those cannot tell one
action from two.
-/

private def pulseClassName :
    ClassName :=
  ⟨"Pulse"⟩

private def countStateName :
    VarName :=
  ⟨"count"⟩

private def tickMessageName :
    MsgName :=
  ⟨"tick"⟩

private def amountParameter :
    VarName :=
  ⟨"amount"⟩

private def pulseInstanceName :
    ActorName :=
  ⟨"pulse"⟩

/--
The body that carries both sites.

The two sends are the last two statements rather than being separated by an assignment,
because site order is a correctness property of the repair and adjacent sends are the
arrangement in which a reversal is visible as a payload swap rather than as a reordering
of unrelated statements.
-/
private def pulseConstructor :
    DTR.GeneralConstructor where

  parameters :=
    []

  body :=
    [
      .assign
        countStateName
        (.intLiteral 0),

      .send
        .selfTarget
        tickMessageName
        [.intLiteral 1]
        ⟨1⟩,

      .send
        .selfTarget
        tickMessageName
        [.intLiteral 2]
        ⟨1⟩
    ]

/--
The message server both sites reach.

It accumulates rather than overwriting, so that the two deliveries are not
observationally equivalent: with both payloads delivered `count` ends at 3, and with one
lost it ends at whichever payload survived. Nothing in this file asserts the runtime
value, but the target gate runs the compiled binary, so a model whose two deliveries
cancelled out would be a weaker program to hand `lfc`.
-/
private def tickMessageServer :
    DTR.GeneralMessageServer where

  name :=
    tickMessageName

  parameters :=
    [
      {
        name :=
          amountParameter

        declaredType :=
          .int
      }
    ]

  body :=
    [
      .assign
        countStateName
        (.binary
          .add
          (.stateVar countStateName)
          (.parameterVar amountParameter))
    ]

private def pulseClass :
    DTR.GeneralReactiveClass where

  name :=
    pulseClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name :=
          countStateName

        declaredType :=
          .int
      }
    ]

  constructor :=
    pulseConstructor

  messageServers :=
    [tickMessageServer]

private def pulseActor :
    DTR.GeneralActorInstance where

  name :=
    pulseInstanceName

  className :=
    pulseClassName

  bindings :=
    []

  arguments :=
    []

/--
One class, one instance, no known rebecs and no routing.

Kept minimal on purpose: this model exists to vary exactly one thing against the rest of
the file, and a known rebec or a second instance would let a failure here have a cause
that has nothing to do with send sites.
-/
private def repeatedSelfSendModel :
    DTR.GeneralModel where

  classes :=
    [pulseClass]

  instances :=
    [pulseActor]

/--
Translate the repeated-self-send model and print it, in one `Except`.

Shared between the emitter and the assertion, for the reason `widenedProgramText` and
`routedProgramText` are: the bytes `lfc` compiles have to be the bytes an assertion
pinned.
-/
private def repeatedSelfSendProgramText :
    Except String String := do

  let program ←
    Translation.compileGeneralModel
      repeatedSelfSendModel

  LF.CppPrinter.renderGeneralProgram
    program

/--
The exact text the repaired translation produces for `repeatedSelfSendModel`.

**Transcribed from a measured emission, not composed by hand.** Two earlier descriptions of a
two-send model in this project were written from memory and both were wrong, so this block was
produced by running `emit-repeated` and copying the bytes.

Three lines carry the whole point of finding F56. Lines four and five declare **two** logical
actions with distinct names, where the pre-repair translation declared one. The two
`schedule` calls then land on *different* actions at the *same* tag — both `1ms`, from one
constructor body — which is exactly the configuration that silently discarded a payload when
both calls targeted one action. And the two `reaction(tick_action…)` blocks are
distinguished by their triggers alone.

The two message reactions share the name `tick_reaction` in the AST and the printer drops it,
which is why nothing in this text says `tick_reaction` anywhere. That asymmetry against the
action names is deliberate and is asserted structurally below rather than being left to this
text, precisely because the text cannot show it.

`state count: int = 0` on the second line of the reactor is the printer's default initializer
for an `int` state variable, and `count = 0;` inside the startup reaction is the constructor
body. The redundancy predates send sites and is shared with every other fixture; it is not
part of this witness.
-/
private def expectedRepeatedSelfSendProgramText :
    String :=
  String.intercalate
    "\n"
    [
      "target Cpp",
      "",
      "reactor Pulse {",
      "  state count: int = 0",
      "  logical action tick_action1: int",
      "  logical action tick_action2: int",
      "",
      "  reaction(startup) -> tick_action1, tick_action2 {=",
      "    count = 0;",
      "    tick_action1.schedule(1, 1ms);",
      "    tick_action2.schedule(2, 1ms);",
      "  =}",
      "",
      "  reaction(tick_action1) {=",
      "    auto amount = *tick_action1.get();",
      "    count = (count + amount);",
      "  =}",
      "",
      "  reaction(tick_action2) {=",
      "    auto amount = *tick_action2.get();",
      "    count = (count + amount);",
      "  =}",
      "}",
      "",
      "main reactor {",
      "  pulse = new Pulse()",
      "}"
    ] ++
    "\n"

/-!
## Assertions

Three blocks, and the split is not cosmetic. The first pins the printer on values written
in this file, the second pins well-formedness on programs written in this file, and the
third pins the translation on a *model*, taking whatever LF program it produces. Only the
third can fail because `Relico/Translation/GeneralBasic.lean` changed, so a failure in the
first two localises without reading the label.
-/

private def printerAssertions :
    IO Unit := do

  expectString
    "LF_TIME_MSEC"
    "0 msec"
    (LF.CppPrinter.renderLfTime
      ⟨0⟩)

  -- The two time renderers must stay distinct. Folding them together is the single
  -- most plausible refactor to attempt here, and it would produce `after 5ms`
  -- outside a `{= … =}` block, where `5ms` is a C++ literal rather than LF time.
  expectString
    "LF_TIME_AND_CPP_DELAY_DIFFER"
    "5 msec|5ms"
    (LF.CppPrinter.renderLfTime
        ⟨5⟩ ++
      "|" ++
      LF.CppPrinter.renderDelay
        ⟨5⟩)

  expectString
    "INPUT_PORT_DECL"
    "  input in: int"
    (LF.CppPrinter.renderInputPortDecl
      inPortDecl)

  expectString
    "OUTPUT_PORT_DECL"
    "  output out: int"
    (LF.CppPrinter.renderOutputPortDecl
      outPortDecl)

  -- Stage D's widening at the port declaration site. Nothing in the translation can
  -- reach it, so without this assertion `renderGeneralType`'s boolean arm would be
  -- exercised in two of its three positions and claimed in the third.
  expectString
    "BOOL_PORT_DECL"
    "  input flagIn: bool"
    (LF.CppPrinter.renderInputPortDecl
      flagInPortDecl)

  expectString
    "PORT_DECLS_INPUTS_BEFORE_OUTPUTS"
    "  input back: int\n  output out: int"
    (LF.CppPrinter.renderGeneralPortDecls
      senderReactorWithInputPort)

  expectString
    "INT_STATE_DECL"
    "  state y: int = 0"
    (LF.CppPrinter.renderGeneralStateVariableDecl
      {
        name :=
          receiverStateName

        declaredType :=
          .int
      })

  -- The initial value is not written here either: it comes from
  -- `GeneralType.initialValue`, so this pins the composition rather than a literal.
  expectString
    "BOOL_STATE_DECL"
    "  state enabled: bool = false"
    (LF.CppPrinter.renderGeneralStateVariableDecl
      {
        name :=
          enabledStateName

        declaredType :=
          .boolean
      })

  -- All thirteen spellings in one assertion, in the declaration order of the type.
  -- Individually they are one string each and collectively they are the operator set
  -- this project chose (the paper gives none), so the audit that matters is reading
  -- the whole row at once.
  expectString
    "BINARY_OPERATOR_SPELLINGS"
    "+ - * / % == != < <= > >= && ||"
    (String.intercalate
      " "
      (([
        .add,
        .sub,
        .mul,
        .div,
        .mod,
        .eq,
        .ne,
        .lt,
        .le,
        .gt,
        .ge,
        .logicalAnd,
        .logicalOr
      ] : List LF.GeneralBinaryOp).map
        LF.CppPrinter.renderGeneralBinaryOp))

  expectString
    "UNARY_OPERATOR_SPELLINGS"
    "-|!"
    (LF.CppPrinter.renderGeneralUnaryOp
        .negate ++
      "|" ++
      LF.CppPrinter.renderGeneralUnaryOp
        .logicalNot)

  -- Every operator node is parenthesized, so the target's precedence never has to
  -- agree with Rebeca's. This is the same expression the widened program prints, and
  -- asserting it here as well is what tells a reader that the parentheses in that
  -- 37-line string are the rule and not that model's own bracketing.
  expectString
    "FULL_PARENTHESIZATION"
    "((left + (right * 2)) - 1)"
    (LF.CppPrinter.renderGeneralExpr
      (.binary
        .sub
        (.binary
          .add
          (.parameterVar leftParameter)
          (.binary
            .mul
            (.parameterVar rightParameter)
            (.intLiteral 2)))
        (.intLiteral 1)))

  expectString
    "BOOL_LITERALS_AND_NEGATION"
    "(false || (!true))"
    (LF.CppPrinter.renderGeneralExpr
      (.binary
        .logicalOr
        (.boolLiteral false)
        (.unary
          .logicalNot
          (.boolLiteral true))))

  expectString
    "VOID_ACTION_DECL"
    "  logical action deliver: void"
    (LF.CppPrinter.renderGeneralActionDecl
      receiverReactorName
      {
        name :=
          deliverAction

        parameters :=
          []
      })

  expectString
    "TYPED_ACTION_DECL"
    "  logical action deliver: bool"
    (LF.CppPrinter.renderGeneralActionDecl
      receiverReactorName
      booleanDeliverAction)

  -- Arity two or more is a struct, which stage C refused outright. Finding F23: real
  -- `lfc 0.11.0` compiled and ran it, so the limit was this printer's and not the
  -- target's.
  expectString
    "STRUCT_ACTION_DECL"
    "  logical action deliver: Receiver_deliver_Args"
    (LF.CppPrinter.renderGeneralActionDecl
      receiverReactorName
      twoParameterDeliverAction)

  expectString
    "PREAMBLE_OMITTED_WITHOUT_STRUCT"
    ""
    (LF.CppPrinter.renderGeneralPreamble
      (LF.CppPrinter.generalProgramStructDecls
        baseProgram.reactors))

  -- Derived from the reactors, never stored, so a struct nothing needs is not
  -- expressible. The declaration is reached through `generalProgramStructDecls`
  -- rather than asserted on `generalActionStructEntry?` directly, which keeps the
  -- assertion on the composition the program actually calls -- and as of stage E that
  -- composition includes the deduplication, which asserting on the entry would skip.
  expectString
    "PREAMBLE_DECLARES_ONE_STRUCT"
    ("public preamble {=\n" ++
      "  struct Receiver_deliver_Args { int v; bool w; };\n" ++
      "=}\n\n")
    (LF.CppPrinter.renderGeneralPreamble
      (LF.CppPrinter.generalProgramStructDecls
        [
          {
            receiverReactor with

            logicalActions :=
              [twoParameterDeliverAction]
          }
        ]))

  expectString
    "EFFECTS_OMITTED_WHEN_EMPTY"
    ""
    (LF.CppPrinter.renderGeneralEffects
      deliverReaction.body)

  -- Both effect kinds in one pass, interleaved as the body produces them. Fig. 1b's
  -- `-> reading,sendReading` matches its own body's statement order, which is what
  -- makes the paper evidence for this rule rather than merely consistent with it.
  expectString
    "EFFECTS_IN_FIRST_OCCURRENCE_ORDER"
    " -> out, deliver"
    (LF.CppPrinter.renderGeneralEffects
      [
        .setPort
          outPort
          [.intLiteral 0],

        .schedule
          deliverAction
          []
          ⟨5⟩
      ])

  expectString
    "EFFECTS_DEDUPLICATED"
    " -> out"
    (LF.CppPrinter.renderGeneralEffects
      [
        .setPort
          outPort
          [.intLiteral 0],

        .setPort
          outPort
          [.intLiteral 1]
      ])

  expectRendered
    "VOID_PAYLOAD_SCHEDULE"
    "deliver.schedule(0ms);"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
      receiverReactor.outputPorts
      (.schedule
        deliverAction
        []
        ⟨0⟩))

  expectRendered
    "TRACE_STATEMENT"
    "std::printf(\"G5_TRACE\\n\");"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
      receiverReactor.outputPorts
      (.trace
        "G5_TRACE"))

  expectRendered
    "SINGLE_VALUE_PAYLOAD_SCHEDULE"
    "deliver.schedule(1, 0ms);"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
      receiverReactor.outputPorts
      (.schedule
        deliverAction
        [.intLiteral 1]
        ⟨0⟩))

  -- The struct is *constructed* here and *declared* by the preamble above and *named*
  -- by the action declaration above that, all three through
  -- `generalPayloadStructName`. Three assertions on one function, which is why the
  -- reactor name has to be threaded this far.
  expectRendered
    "MULTI_VALUE_PAYLOAD_SCHEDULE"
    "deliver.schedule(Receiver_deliver_Args{1, true}, 0ms);"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
      receiverReactor.outputPorts
      (.schedule
        deliverAction
        [
          .intLiteral 1,
          .boolLiteral true
        ]
        ⟨0⟩))

  expectRendered
    "SINGLE_VALUE_PAYLOAD_BINDER"
    "    auto w = *deliver.get();"
    (LF.CppPrinter.renderGeneralParameterRead
      deliverReaction)

  expectRendered
    "MULTI_VALUE_PAYLOAD_BINDERS"
    ("    auto deliver_payload = *deliver.get();\n" ++
      "    auto v = deliver_payload.v;\n" ++
      "    auto w = deliver_payload.w;")
    (LF.CppPrinter.renderGeneralParameterRead
      twoParameterDeliverReaction)

  -- Finding F33, as an assertion. Stage C refused this shape; it is what
  -- `assembleGeneralStartupReaction` produces for every constructor with formals, and
  -- those names are the reactor's own parameters, readable with no binder. The right
  -- emission is nothing at all.
  expectRendered
    "STARTUP_PARAMETERS_READ_NOTHING"
    ""
    (LF.CppPrinter.renderGeneralParameterRead
      parameterisedStartupReaction)

  -- F30, retracted, with the retraction as an assertion rather than a note. Stage D
  -- refused this shape and recorded a disagreement with `docs/STAGE_D_DESIGN.md` §6,
  -- which had said all three go; §6 was right and F30 was wrong. The binder is derived
  -- from the *port* name, so the emitted text differs from the action case above in
  -- exactly one identifier — which is the sharpest available statement that a port and an
  -- action are read the same way, and the reason the two assertions are adjacent.
  expectRendered
    "MULTI_PARAMETER_PORT_DESTRUCTURED"
    ("    auto in_payload = *in.get();\n" ++
      "    auto v = in_payload.v;\n" ++
      "    auto w = in_payload.w;")
    (LF.CppPrinter.renderGeneralParameterRead
      twoParameterPortReaction)

  -- Fig. 5 spells the production `reactor R (ParamList?)`, so the absent form is the
  -- grammar's own — and it is what keeps every stage C fixture byte-identical.
  expectString
    "PARAMETER_LIST_OMITTED_WHEN_EMPTY"
    ""
    (LF.CppPrinter.renderGeneralParameterList
      [])

  expectString
    "PARAMETER_LIST_DECL"
    "(bound: int = 0, active: bool = false)"
    (LF.CppPrinter.renderGeneralParameterList
      [
        {
          name :=
            boundParameter

          declaredType :=
            .int
        },

        {
          name :=
            activeParameter

          declaredType :=
            .boolean
        }
      ])

  expectString
    "CONNECTION_CARRIES_AFTER"
    "  sender0.out -> receiver0.in after 0 msec"
    (LF.CppPrinter.renderGeneralConnection
      senderToReceiver)

  expectRendered
    "INSTANCE_IS_ARGUMENT_FREE"
    "  sender0 = new Sender()"
    (LF.CppPrinter.renderGeneralInstance
      baseProgram
      senderInstance)

  expectRendered
    "EMPTY_STARTUP_REACTION_OMITTED"
    ""
    (LF.CppPrinter.renderGeneralStartupReaction
      receiverReactor)

  expectRendered
    "PORT_TRIGGERED_REACTION"
    ("  reaction(in) -> deliver {=\n" ++
      "    auto v = *in.get();\n" ++
      "    deliver.schedule(v, 0ms);\n" ++
      "  =}")
    (LF.CppPrinter.renderGeneralReaction
      receiverReactorName
      receiverReactor.outputPorts
      receiveReaction)

  expectRendered
    "PROGRAM"
    expectedProgramText
    (LF.CppPrinter.renderGeneralProgram
      baseProgram)

private def wellFormednessAssertions :
    IO Unit := do

  expectWellFormed
    "ACCEPT_BASE_PROGRAM"
    baseProgram

  -- The three accept cases below are deliberate non-checks, each with a measured
  -- reason. They are assertions rather than comments because a later stage
  -- strengthening `wellFormed` would otherwise shut these doors silently.
  expectWellFormed
    "ACCEPT_UNCONNECTED_PORT"
    programWithUnconnectedPort

  expectWellFormed
    "ACCEPT_SELF_CONNECTION"
    programWithSelfConnection

  expectWellFormed
    "ACCEPT_BROADCAST_TO_TWO_INPUTS"
    programWithBroadcast

  expectIllFormed
    "REJECT_SET_ON_INPUT_PORT"
    programSettingInputPort

  expectIllFormed
    "REJECT_UNKNOWN_TARGET_PORT"
    programWithUnknownTargetPort

  expectIllFormed
    "REJECT_DUPLICATE_TARGET_ENDPOINT"
    programWithDuplicateTargetEndpoint

  expectIllFormed
    "REJECT_PORT_STATE_COLLISION"
    programWithPortStateCollision

  -- Stage D's own case: `declaredNames` gained the parameter list, and a predicate
  -- that gains a case nobody exercises is the defect stage B found one step earlier
  -- in `PrioritiesDistinct`. The instance supplies a matching argument on purpose, so
  -- the union check is the only conjunct that can fail.
  expectIllFormed
    "REJECT_PARAMETER_STATE_COLLISION"
    programWithParameterStateCollision

  expectIllFormed
    "REJECT_DANGLING_INSTANCE"
    programWithDanglingInstance

private def translationAssertions :
    IO Unit := do

  -- Stage D's whole claim in one assertion: a DTR model in, an LF file out, byte for
  -- byte. Everything after it is a narrowing, added because a 37-line diff does not
  -- say *which* rule broke.
  expectRendered
    "TRANSLATED_WIDENED_PROGRAM"
    expectedWidenedProgramText
    widenedProgramText

  -- Three refusals reached through `compileGeneralModel` and `compileGeneralStmt`. They
  -- are *not* the whole of what stage E will not carry, which is what this comment said
  -- until finding F47 counted: routing alone has eight refusal causes, and the six of
  -- them not covered here are asserted in `routedRefusalAssertions` below. What these
  -- three are is the whole of what is reachable at *this* layer — one construct routing
  -- cannot spell, one hand-built model shape routing catches on the way past, and one arm
  -- that can only fire if this translator is wrong.
  --
  -- Stage D asserted two refusals here as well, and it is worth being clear that these
  -- are not those two moved: stage D refused every external send and pinned the sentence
  -- that said so, and both that predicate and that sentence are gone. Each is pinned on
  -- its exact text, because all three are `.error` and a test that asked only for
  -- `.error` would pass on any of the three for any of them.
  expectRefusedTerm
    "PARAMETERLESS_EXTERNAL_SEND_REFUSED"
    parameterlessPortDiagnostic
    (Translation.compileGeneralModel
      externalSendModel)

  expectRefusedTerm
    "UNDECLARED_MESSAGE_SERVER_SEND_REFUSED"
    undeclaredMessageServerDiagnostic
    (Translation.compileGeneralModel
      undeclaredServerSendModel)

  -- The empty environment is the point. Inside `compileGeneralModel` this argument is
  -- always `outputPortEnvOf`'s output and so always contains the site, which is why #47
  -- can retire the arm; reaching it from here means calling the function directly with
  -- an environment the translator would never build.
  expectRefusedTerm
    "UNRESOLVED_SEND_SITE_IS_A_TRANSLATOR_DEFECT"
    unresolvedSendSiteDiagnostic
    (Translation.compileGeneralStmt
      []
      {
        bodyKey :=
          .messageServer settleMessageName,
        selfSends :=
          []
      }
      0
      (.send
        (.knownRebec peerKnownRebecName)
        pingMessageName
        []
        ⟨0⟩))

  expectRefused
    "INSTANCE_UNKNOWN_REACTOR_REFUSED"
    ("instance `ghost` names reactor `Missing`, " ++
      "which this program does not declare")
    (LF.CppPrinter.renderGeneralInstance
      baseProgram
      ghostInstance)

  match Translation.compileGeneralModel
    widenedModel
  with

  | .error diagnostic =>
      testFailure
        ("the widened model must translate, but it was refused: " ++
          diagnostic)

  | .ok program => do

      -- The translation's output is fed to the predicate the printer's own refusals
      -- are excluded by. Without this, "the printer never refuses a translated
      -- program" would rest on the printer having happened not to refuse this one.
      expectWellFormed
        "ACCEPT_TRANSLATED_WIDENED_PROGRAM"
        program

      expectBool
        "INSTANCE_ARGUMENTS_MATCH_POSITIVE"
        true
        program.instanceArgumentsMatch

      let programWithTransposedArguments :
          LF.GeneralProgram :=
        {
          program with

          instances :=
            [widenedInstanceWithWrongTypes]
        }

      expectBool
        "INSTANCE_ARGUMENTS_MATCH_NEGATIVE_TYPE"
        false
        programWithTransposedArguments.instanceArgumentsMatch

      let programWithMissingArgument :
          LF.GeneralProgram :=
        {
          program with

          instances :=
            [widenedInstanceWithWrongArity]
        }

      expectBool
        "INSTANCE_ARGUMENTS_MATCH_NEGATIVE_ARITY"
        false
        programWithMissingArgument.instanceArgumentsMatch

      -- Named arguments, recovered from the reactor's own parameter list. Fig. 5's
      -- `ArgList ::= Expr (, Expr)*` admits only positional arguments, so this form is
      -- a divergence from the grammar rather than an instance of it: finding F31.
      expectRendered
        "INSTANCE_WITH_NAMED_ARGUMENTS"
        "  configuredOn = new Configured(bound=7, active=true)"
        (LF.CppPrinter.renderGeneralInstance
          program
          widenedInstanceWithNamedArguments)

      -- Refused, not truncated. A `zip` here would drop the surplus and emit a program
      -- that compiles and is wrong, which is the worst outcome available.
      expectRefused
        "INSTANCE_ARITY_REFUSED"
        ("instance `configuredOn` supplies 1 argument(s) to reactor `Configured`, " ++
          "which declares 2 parameter(s)")
        (LF.CppPrinter.renderGeneralInstance
          program
          widenedInstanceWithWrongArity)

/--
Findings F34 and F42, asserted rather than argued: the port-naming rule is not injective,
and these are the witnesses `Relico/Translation/NameGeneration.lean` says live here.

Its own group, for the reason `collisionAssertions` is: the number that breaks should say
which claim broke. These are also the only assertions in this file that call a naming
function directly instead of reading a name off a translated program, so they fail for
different causes than anything else here.

**They exist because the docstring delegating to them was making a false statement.**
`NameGeneration.lean` explains, correctly, why no Lean refutation is attempted — a concrete
witness needs `String.front` and `String.drop` to reduce through the UTF-8 model, and a
parametric one needs idempotence of `Char.toUpper`, which core does not supply — and then
says the collision *"is asserted there"*, meaning here. It was not, for a day, while three
code comments pointed at it. That is finding F44, and a documented test that does not exist
is worse than an undocumented gap: it removes the signal that would have found the gap.

Each assertion pins **both** names against the literal they collide on, rather than asserting
only that the two are equal to each other. Equality alone would survive a change that moved
both names together, which is precisely the change a reader of this group must be told about.

Three channels, independent, which is the reason there are three:

* the unescaped separator (F34) — closed by escaping it;
* the unmarked boundary before the site suffix (F34, and the witness F42 shares) — closed by
  marking it;
* case folding in `capitalizeName` (F42) — closed by **neither**, since `hub` and `Hub` are
  both legal Rebeca identifiers and collapse before any separator is consulted.

None of this is a soundness defect, and the group is not evidence of one. Uniqueness is
decided on the assembled program, by the `Nodup` guard on `LF.GeneralReactor.declaredNames`,
which is strictly stronger than injectivity of these functions because it also covers
state-variable, action and parameter names that no naming rule can constrain. What these
assertions protect is the *claim* about the rule, which several docstrings now make.
-/
private def portNameCollisionAssertions :
    IO Unit := do

  -- F34, the unescaped separator: two different (message, known rebec) pairs, one name.
  -- Every readable separator has this property, underscores included, so the finding is
  -- about concatenation and not about this particular spelling.
  expectString
    "PORT_NAME_UNESCAPED_SEPARATOR_COLLIDES"
    "reportToToHub = reportToToHub"
    ((Translation.outputPortNameFor
          ⟨"reportTo"⟩
          ⟨"hub"⟩
          "").value ++
      " = " ++
      (Translation.outputPortNameFor
          ⟨"report"⟩
          ⟨"toHub"⟩
          "").value)

  -- F34 again, and this is the witness F42 shares: nothing marks where the capitalized
  -- rebec ends and the site ordinal begins. Site 2 of a class that sends twice to `hub`
  -- is indistinguishable from the sole site of a class that sends once to `hub2`.
  expectString
    "PORT_NAME_SITE_SUFFIX_BOUNDARY_COLLIDES"
    "reportToHub2 = reportToHub2"
    ((Translation.outputPortNameFor
          ⟨"report"⟩
          ⟨"hub"⟩
          "2").value ++
      " = " ++
      (Translation.outputPortNameFor
          ⟨"report"⟩
          ⟨"hub2"⟩
          "").value)

  -- F42's own channel, and the one that survives both fixes above. `capitalizeName` folds
  -- the first character's case, so two distinct known rebecs give one infix. This is why
  -- `docs/STAGE_E_DESIGN.md` §4.3's second one-sided injectivity lemma is false and why
  -- `outputPortInfixFor_eq_of_outputPortNameFor_eq` is the strongest form that holds.
  expectString
    "PORT_NAME_CASE_FOLDING_COLLIDES"
    "reportToHub = reportToHub"
    ((Translation.outputPortNameFor
          ⟨"report"⟩
          ⟨"hub"⟩
          "").value ++
      " = " ++
      (Translation.outputPortNameFor
          ⟨"report"⟩
          ⟨"Hub"⟩
          "").value)

/--
The collision model's translated program, assembled but not guarded.

This is `Translation.compileGeneralModel` with its last step left off, and it exists
because that last step is `guardGeneralProgram`: the program finding F32 is about is
exactly the program the guard refuses, so it cannot be obtained from the function that
refuses it.

Written as the guarded function's own three steps, in its own order and with its own
diagnostics, rather than as anything shorter. That is what keeps this a witness about the
translator: a hand-built ill-formed program would assert nothing at all, and a witness
built from a *different* routing or a *different* class compilation would stop tracking
`compileGeneralModel` the first time either changed.
-/
private def assembledCollisionProgram :
    Except String LF.GeneralProgram :=
  match Translation.routesOf
    collisionModel
  with

  | .error message =>
      .error message

  | .ok routes =>
      match
          Translation.compileGeneralReactiveClasses
            collisionModel.classes
            routes
            collisionModel.classes with

      | .error message =>
          .error message

      | .ok compiledReactors =>
          .ok
            (Translation.assembleGeneralProgram
              collisionModel
              routes
              compiledReactors)

/--
Finding F32, asserted rather than argued: the well-formedness preservation theorem
that stage E was to prove is **false**, and these five assertions are the witness.

Stage E moved the layer the witness has to be taken at, which is the rewrite the last
paragraph of this docstring asked for in advance. `Translation.compileGeneralModel` now
ends in `guardGeneralProgram`, so it returns `.ok` only for a program that is already
well-formed: an ill-formed translation comes back as a refusal instead of as output, and
the counterexample cannot be read off its result at all any more. So the three assertions
that exhibit it are taken against the program `Translation.assembleGeneralProgram` builds
-- see `assembledCollisionProgram` -- and the refusal itself is pinned as its own
assertion, which is finding F43.

That is a narrowing of F32 rather than a repair of it, and the distinction is the whole
reason the refusal is asserted instead of worked around. What the guard buys is that no
ill-formed LF text is ever emitted. What it does not buy is the theorem: the theorem says
a well-formed DTR model translates to a well-formed LF program, and a refusal is a witness
that this one does not. The visible cost is that `compileGeneralModel` is now partial on
models `DTR.GeneralModel.wellFormed` accepts, which the first assertion below and the
second read together state exactly.

Kept as its own group so that the number that breaks says which claim broke. Three
assertions state the divergence and one exists to stop another passing for the wrong
reason: `LF.GeneralProgram.wellFormed` is a conjunction, so a rejection proves only that
*some* clause failed, and asserting that the instance-argument clause still holds narrows
it to the name clause.

These assertions are about the theorem, not about the tool. The frontend rejects this
collision before a model reaches the translator -- see `collisionModel` -- so nothing
here says the pipeline is unsound. What they say is that `m.wellFormed` is too weak a
hypothesis to carry the conclusion, and any fix must either strengthen the hypothesis
or prove the elaborator's guarantee implies the LF predicate.

Whichever fix lands, `TRANSLATED_COLLISION_PROGRAM_ILL_FORMED` is the assertion that
changes meaning, and this group must be rewritten in the same commit rather than deleted:
a counterexample that stops being a counterexample is worth a line saying why.
-/
private def collisionAssertions :
    IO Unit := do

  expectBool
    "DTR_ACCEPTS_PARAMETER_STATE_COLLISION"
    true
    collisionModel.wellFormed

  -- F43. The exact text matters more than the fact of a refusal: `guardGeneralProgram`
  -- reports which clause of `LF.GeneralProgram.wellFormed` failed, and this pins that it
  -- is the reactor clause. A refusal for any other reason -- a routing failure, say, or a
  -- class that stopped compiling -- would satisfy a bare `.error` check while quietly
  -- meaning the model no longer reaches the guard at all.
  expectRefusedTerm
    "COLLISION_MODEL_REFUSED_BY_THE_GUARD"
    ("the translated LF program is not well-formed: some reactor is not well-formed, " ++
      "which for stage E most often means a generated name collided with another name " ++
      "in the same reactor, or a port was set that the reactor does not declare")
    (Translation.compileGeneralModel
      collisionModel)

  match assembledCollisionProgram with

  | .error diagnostic =>
      testFailure
        ("the collision model must route and compile for F32 to be a counterexample, " ++
          "but a step before assembly refused it: " ++
          diagnostic)

  | .ok program => do

      -- The counterexample itself.
      expectIllFormed
        "TRANSLATED_COLLISION_PROGRAM_ILL_FORMED"
        program

      expectBool
        "COLLISION_PROGRAM_INSTANCE_ARGUMENTS_STILL_MATCH"
        true
        program.instanceArgumentsMatch

      -- F32 is a claim about the reactor layer, and this says so in the one way that
      -- cannot drift: the counterexample program has no connections, so it has no
      -- routes, so nothing stage E added is holding it up. It replaces a stage D
      -- assertion that made the same point through `generalModelSelfSendOnly` — the
      -- model was self-send-only, so its translating was a fact about the model rather
      -- than an accident of the blanket refusal. That predicate is gone, and the
      -- property it was standing in for is better read off the output than off the
      -- input anyway. If a future edit gives this model an external send, the defect
      -- under test stops being isolated and this line fails first.
      expectBool
        "COLLISION_PROGRAM_HAS_NO_CONNECTIONS"
        true
        program.connections.isEmpty

/--
Stage E's own claims: the model that routes, asserted as a translation.

Kept apart from `translationAssertions` for the reason that block is kept apart from the
two above it. Everything there translates a model with no external sends and would still
pass with `Relico/Translation/GeneralRouting.lean` deleted; nothing here would. A count
that drops by seven says *routing* stopped, and that is a different morning from a
printer that stopped.

The first two assertions come before the program text on purpose. Both are decisions this
file cannot restate — a statement index and a name suffix — and both are visible in the
pinned text only as consequences. If the rule underneath one of them moves, the text
assertion fails too, and reading a diff of ninety lines to discover which of two rules
changed is exactly the work these two save.
-/
private def routedAssertions :
    IO Unit := do

  -- §7.1 against §4.1: a statement position, not a send ordinal. `"0|1|2"` is what the
  -- other reading computes, and `poll`'s leading assignment is the only reason the two
  -- can be told apart at all.
  expectString
    "ROUTED_SEND_SITE_INDICES"
    "1|2|3"
    routedSendSiteIndices

  -- §4.2's table against §4.2's prose. The trailing empty entry is not a formatting
  -- accident: `reset` is sent once, so its port carries no ordinal.
  expectString
    "ROUTED_SITE_SUFFIXES"
    "1|2|"
    routedSiteSuffixes

  expectRendered
    "TRANSLATED_ROUTED_PROGRAM"
    expectedRoutedProgramText
    routedProgramText

  match Translation.compileGeneralModel
    routedModel
  with

  | .error diagnostic =>
      testFailure
        ("the routed model must translate, but it was refused: " ++
          diagnostic)

  | .ok program => do

      -- Not implied by the text assertion above. The printer's refusals are excluded by
      -- this predicate, so a program it prints happily could still be one no theorem in
      -- `GeneralWellFormed.lean` ranges over. Its `connectionsWellFormed` and
      -- `targetEndpointsUnique` clauses are what say the three connections resolve at
      -- both ends, agree on payload at both ends, and land on three distinct target
      -- endpoints. Named rather than counted, because the conjunct count moves: G3
      -- appended a tenth.
      expectWellFormed
        "ACCEPT_TRANSLATED_ROUTED_PROGRAM"
        program

      -- §7.2's asymmetry as two numbers per reactor. Output ports are a projection of the
      -- sending class and input ports of the *receiving* class, so `Gateway` declares
      -- three inputs and `spare` gets all three whether or not a connection reaches it.
      -- Symmetrising this — input ports per instance — is the change `lfc 0.11.0`'s
      -- refusal of many-to-one connections rules out, and it would show up here first.
      expectString
        "ROUTED_PORT_COUNTS_BY_REACTOR"
        "0/3|3/0"
        (String.intercalate
          "|"
          (program.reactors.map
            (fun reactor =>
              toString
                reactor.inputPorts.length ++
                "/" ++
                toString
                  reactor.outputPorts.length)))

      -- Which payload *arm* the translation picked, as distinct from how the printer
      -- spells it. `bool` against `Gateway_report_action_Args` in the text is
      -- `renderGeneralPortType`; this is `generalPortPayloadFor` choosing `.scalar` at
      -- arity one and `.struct` at arity two, and the two halves being equal is the input
      -- port carrying the same payload as the output port that feeds it.
      expectString
        "ROUTED_PAYLOAD_ARITIES"
        "2,2,1|2,2,1"
        (String.intercalate
          "|"
          (program.reactors.map
            (fun reactor =>
              String.intercalate
                ","
                ((reactor.outputPorts ++
                  reactor.inputPorts).map
                  (fun port =>
                    toString
                      port.payload.arity)))))

      -- Construction against specification, and **an agreement claim rather than an
      -- ordering one**. `generalReactionNamesOf` is the function §7.3's two replacement
      -- theorems are stated against; `compileGeneralMessageServerReactionGroup` is what
      -- builds the reactions; this pins that the two do not drift apart.
      --
      -- It is not evidence for the ordering claim, and finding **F60** records that it once
      -- said it was. Neither side is a literal, and both consume `routesOf` — where level
      -- 1's sort is applied, upstream of both — so every permutation the sort can produce
      -- moves both sides together and this assertion stays green. It is not blind to level
      -- 2, whose sort enters on the constructor side only, but `routedModel` carries no
      -- priority annotation at all, so that sensitivity is unreachable here. The
      -- literal-backed version of the ordering claim is
      -- `PRIORITY_FAN_IN_EMITTED_REACTION_ORDER` in the twelfth block.
      expectRendered
        "ROUTED_REACTION_ORDER_MATCHES_SPECIFICATION"
        (String.intercalate
          "|"
          (program.reactors.map
            (fun reactor =>
              String.intercalate
                ","
                (reactor.messageReactions.map
                  (fun reaction =>
                    reaction.name.value)))))
        routedSpecifiedReactionOrder

/--
The six refusals `routesOf` can reach that `translationAssertions` does not cover.

Kept as its own block for a reason that is not organisational. `routedAssertions` above
asserts what routing *does*, and every assertion in it would still pass if all eight
refusal messages were replaced by the empty string. This block asserts what routing *says*
when it stops, and nothing else in the file does: a count that drops by six says the
refusal texts stopped being checked, which is a smaller and much quieter failure than
routing itself stopping.

The order is the order of finding F47's table, which is the order the causes are reached
in: the two from `generalOutputPortEntryFor`'s steps 1 and 2, then the three from
`generalRouteFor`, then the one from `routesOfInstances`. Reading them top to bottom is
reading a send being resolved from the class table inward.
-/
private def routedRefusalAssertions :
    IO Unit := do

  -- Step 1 of five. `sendTargetsDeclared` — D6 — is what stops this upstream, and the
  -- fixture `frontend/fixtures/general/lean-reject/invalid-send-target-undeclared.json`
  -- asserts that it does. These two are not the same assertion: that one says a document
  -- never arrives here, this one says what happens if one somehow does.
  expectRefusedTerm
    "KNOWN_REBEC_UNDECLARED_REFUSED"
    undeclaredKnownRebecDiagnostic
    (Translation.routesOf
      undeclaredKnownRebecModel)

  -- Step 2. Closed by `sendsResolveToMessageServers` through
  -- `DTR.GeneralModel.receivingClass?`, which returns `none` exactly when the declared
  -- class is missing from the table — not by `bindingsMatchDeclarations`, which never
  -- looks at a class nobody instantiates.
  expectRefusedTerm
    "KNOWN_REBEC_CLASS_UNDECLARED_REFUSED"
    undeclaredRebecClassDiagnostic
    (Translation.routesOf
      undeclaredRebecClassModel)

  -- The binding lookup, and the arm `externalSendModel`'s note says a model that stopped
  -- refusing arity-zero payloads would fall into next.
  expectRefusedTerm
    "KNOWN_REBEC_UNBOUND_REFUSED"
    unboundKnownRebecDiagnostic
    (Translation.routesOf
      unboundKnownRebecModel)

  expectRefusedTerm
    "BINDING_TARGET_NOT_INSTANTIATED_REFUSED"
    bindingNotInstantiatedDiagnostic
    (Translation.routesOf
      bindingNotInstantiatedModel)

  -- The one refusal of the eight whose message names a generated port, so it is also the
  -- one an edit to the naming rule would move without touching routing at all.
  expectRefusedTerm
    "BINDING_TARGET_CLASS_MISMATCH_REFUSED"
    bindingClassMismatchDiagnostic
    (Translation.routesOf
      bindingClassMismatchModel)

  expectRefusedTerm
    "INSTANCE_CLASS_UNDECLARED_REFUSED"
    instanceClassUndeclaredDiagnostic
    (Translation.routesOf
      instanceClassUndeclaredModel)

/--
Finding F48's model: two known rebecs aliased onto one actor, whose two sends collide.

The literals below are deliberately **not** shared with any other fixture in this file, and
that is the only unusual thing about this group. The collision depends on the exact spellings
`report`, `reportTo`, `hub` and `toHub` — reading them as `reportTo` + `hub` and as `report` +
`toHub` is what produces one name — so a fixture that reused a shared literal would lose the
effect under test the first time somebody renamed a rebec for an unrelated reason. Here a
rename fails `ALIASED_ENDPOINT_TARGET_UNIQUENESS_FALSE` loudly instead.

Three separately measured facts compose to lift F34's *name* collision to a *route* collision,
and none of the three is a defect on its own:

* `outputPortNameFor` concatenates the message, the literal `To`, the capitalized known rebec
  and the site suffix without escaping the separator, so the two pairs above spell
  `reportToToHub` (F34);
* `generalSiteSuffixFor` returns the empty string for a (rebec, message) pair the class sends
  to exactly once, so neither send here carries a disambiguating ordinal; and
* `bindingsMatchClass` constrains only that the binding keys are the declared known rebecs and
  that each bound actor exists with the declared class, so **binding two known rebecs to one
  actor is legal Rebeca** — which is what puts both arrows on one receiver instance.

Both message servers take one `int` because an arity-zero external send is a refusal cause in
its own right (see `externalSendModel`) and would mask this one.
-/
private def aliasedHubClassName :
    ClassName :=
  ⟨"Hub"⟩

private def aliasedProbeClassName :
    ClassName :=
  ⟨"Probe"⟩

private def aliasedReportMessageName :
    MsgName :=
  ⟨"report"⟩

private def aliasedReportToMessageName :
    MsgName :=
  ⟨"reportTo"⟩

private def aliasedTickMessageName :
    MsgName :=
  ⟨"tick"⟩

private def aliasedHubKnownRebecName :
    KnownRebecName :=
  ⟨"hub"⟩

private def aliasedToHubKnownRebecName :
    KnownRebecName :=
  ⟨"toHub"⟩

private def aliasedSeenStateName :
    VarName :=
  ⟨"seen"⟩

private def aliasedValueParameterName :
    VarName :=
  ⟨"value"⟩

private def aliasedHubActorName :
    ActorName :=
  ⟨"hubActor"⟩

private def aliasedProbeActorName :
    ActorName :=
  ⟨"probe"⟩

private def aliasedReportServer :
    DTR.GeneralMessageServer where
  name := aliasedReportMessageName
  parameters :=
    [ { name := aliasedValueParameterName,
        declaredType := .int } ]
  body :=
    [ .assign
        aliasedSeenStateName
        (.parameterVar aliasedValueParameterName) ]

private def aliasedReportToServer :
    DTR.GeneralMessageServer where
  name := aliasedReportToMessageName
  parameters :=
    [ { name := aliasedValueParameterName,
        declaredType := .int } ]
  body :=
    [ .assign
        aliasedSeenStateName
        (.parameterVar aliasedValueParameterName) ]

private def aliasedHubClass :
    DTR.GeneralReactiveClass where
  name := aliasedHubClassName
  knownRebecs := []
  stateVariables :=
    [ { name := aliasedSeenStateName,
        declaredType := .int } ]
  constructor :=
    { parameters := []
      body := [] }
  messageServers :=
    [ aliasedReportServer,
      aliasedReportToServer ]

private def aliasedTickServer :
    DTR.GeneralMessageServer where
  name := aliasedTickMessageName
  parameters :=
    [ { name := aliasedValueParameterName,
        declaredType := .int } ]
  body := []

private def aliasedProbeClass :
    DTR.GeneralReactiveClass where
  name := aliasedProbeClassName
  knownRebecs :=
    [ { name := aliasedHubKnownRebecName,
        className := aliasedHubClassName },
      { name := aliasedToHubKnownRebecName,
        className := aliasedHubClassName } ]
  stateVariables := []
  constructor :=
    { parameters := []
      body :=
        [ .send
            (.knownRebec aliasedHubKnownRebecName)
            aliasedReportToMessageName
            [.intLiteral 1]
            ⟨0⟩,
          .send
            (.knownRebec aliasedToHubKnownRebecName)
            aliasedReportMessageName
            [.intLiteral 2]
            ⟨0⟩ ] }
  messageServers :=
    [ aliasedTickServer ]

private def aliasedHubActor :
    DTR.GeneralActorInstance where
  name := aliasedHubActorName
  className := aliasedHubClassName
  bindings := []
  arguments := []

/--
The aliasing itself, in two lines: both known rebecs are bound to `hubActor`.
-/
private def aliasedProbeActor :
    DTR.GeneralActorInstance where
  name := aliasedProbeActorName
  className := aliasedProbeClassName
  bindings :=
    [ (aliasedHubKnownRebecName, aliasedHubActorName),
      (aliasedToHubKnownRebecName, aliasedHubActorName) ]
  arguments := []

private def aliasedEndpointModel :
    DTR.GeneralModel where
  classes :=
    [ aliasedProbeClass,
      aliasedHubClass ]
  instances :=
    [ aliasedProbeActor,
      aliasedHubActor ]

/--
The aliased-endpoint model's translated program, assembled but not guarded.

Built for the reason `assembledCollisionProgram` is built and in the same three steps: the
guard collapses every clause of `LF.GeneralProgram.wellFormed` into one `String`, and
`reactorsWellFormed` precedes `targetEndpointsUnique` in that `&&` chain, so a claim about the
later clause cannot be read off the guarded result. Two separate definitions rather than one
parameterised helper, because each is a witness for a different finding and folding them would
make a change made for F32's sake silently change F48's.
-/
private def assembledAliasedEndpointProgram :
    Except String LF.GeneralProgram :=
  match Translation.routesOf
    aliasedEndpointModel
  with

  | .error message =>
      .error message

  | .ok routes =>
      match
          Translation.compileGeneralReactiveClasses
            aliasedEndpointModel.classes
            routes
            aliasedEndpointModel.classes with

      | .error message =>
          .error message

      | .ok compiledReactors =>
          .ok
            (Translation.assembleGeneralProgram
              aliasedEndpointModel
              routes
              compiledReactors)

/--
The sending class's output port names, read off the environment routing actually builds.

Not `outputPortNameFor` applied to two pairs by hand — that assertion already exists three
blocks above as `PORT_NAME_UNESCAPED_SEPARATOR_COLLIDES`, and it has existed since the name
collisions were first measured. It is precisely why the *route*-level consequence went
unnoticed for as long as it did: a name-level collision says two calls agree, and says nothing
about whether one program can reach both calls. This reads the pair out of
`outputPortEnvOf`, so it says the translator reaches both.
-/
private def aliasedEndpointOutputPortNames :
    String :=
  match
      Translation.outputPortEnvOf
        aliasedEndpointModel.classes
        aliasedProbeClass with

  | .error diagnostic =>
      "the sending class did not route: " ++
        diagnostic

  | .ok environment =>
      String.intercalate
        " | "
        (environment.map
          (fun (entry : Translation.GeneralOutputPortEntry) =>
            entry.outputPort.value))

/--
The endpoints the generated connections land on, as `instance.port`.

The two halves being equal is the many-to-one connection `lfc 0.11.0` rejects, and it arises
here without any port being declared twice by hand: `generalConnectionsOf` maps over the routes
into the receiving class with no dedup, so two routes that agree on the target give two
connections that agree on the endpoint.
-/
private def aliasedEndpointTargetEndpoints :
    String :=
  match Translation.routesOf
    aliasedEndpointModel
  with

  | .error diagnostic =>
      "the model did not route: " ++
        diagnostic

  | .ok routes =>
      String.intercalate
        " | "
        ((Translation.generalConnectionsOf routes).map
          (fun (connection : LF.GeneralConnection) =>
            connection.targetInstance.value ++
              "." ++
              connection.targetPort.value))

/--
Finding F48, asserted rather than argued: routing **can** produce a repeated target endpoint,
so `targetEndpointsUnique` cannot be retired as a dead clause, and these six assertions are
what say so.

The claim these replace was a docstring on
`Relico/Translation/GeneralBasic.lean`'s `compileGeneralModel_targetEndpointsUnique`, which
said a construction proof "would say the routing *cannot* produce a repeated target" and was
"deferred" with the site-totality induction. Both halves were wrong: no such proof exists,
because the property is false, and site totality is the wrong instrument anyway — it governs
the sending side and statement compilation, while an endpoint collision is about *input* ports
on the receiver. That the docstring was wrong is not the interesting part.
`Relico/Translation/NameGeneration.lean` had documented the correct story all along, so two
docstrings in one build closure gave opposite answers and no gate could compare them. This
group is the answer that a `grep` can falsify.

The refusal is asserted before the match rather than inside it, because the match's `.error`
arm is a `testFailure` and not an assertion: if a step before assembly ever refuses this model,
the count drops and the reason is printed, which is the behaviour `collisionAssertions` chose
for the same reason.

Two clauses fail here, not one, and the last two assertions are what keep the attribution
narrow. `reactorsWellFormed` fails independently — the collision is over-determined, since the
sender duplicates its own output port while the receiver duplicates its input port — so a bare
refusal check would pass on the reactor clause alone and say nothing about endpoints.
`ALIASED_ENDPOINT_TARGET_UNIQUENESS_FALSE` is the first witness anywhere in this repository
that this clause can fail at all, and `ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED` records the
neighbouring clause that still holds: `connectionsWellFormed` asks that an endpoint be
*declared*, not that it be declared once.

If a future change to the naming rule makes the two names differ, four of these six fail
together and the fix is to record why rather than to delete them — a counterexample that stops
being a counterexample is worth a line saying so.
-/
private def aliasedEndpointAssertions :
    IO Unit := do

  -- Without this the group proves nothing: a source model the frontend would reject makes the
  -- refusal downstream a fact about the frontend. All five conjuncts of
  -- `DTR.GeneralModel.wellFormed` hold, aliasing included.
  expectBool
    "ALIASED_ENDPOINT_SOURCE_WELLFORMED"
    true
    aliasedEndpointModel.wellFormed

  expectString
    "ALIASED_ENDPOINT_OUTPUT_PORTS_COLLIDE"
    "reportToToHub | reportToToHub"
    aliasedEndpointOutputPortNames

  expectString
    "ALIASED_ENDPOINT_TARGETS_COLLIDE"
    "hubActor.reportToToHubFromProbe | hubActor.reportToToHubFromProbe"
    aliasedEndpointTargetEndpoints

  -- The whole text, both clauses. `generalProgramExplanation` enumerates every failing clause
  -- rather than the first, which is worth pinning: a change that made it report only the first
  -- would silently stop reporting the endpoint collision, and nothing else here would notice.
  expectRefusedTerm
    "ALIASED_ENDPOINT_COLLISION_REFUSED"
    ("the translated LF program is not well-formed: some reactor is not well-formed, " ++
      "which for stage E most often means a generated name collided with another name " ++
      "in the same reactor, or a port was set that the reactor does not declare; " ++
      "two connections target the same input port of the same instance, which the LF " ++
      "compiler rejects as a many-to-one connection")
    (Translation.compileGeneralModel
      aliasedEndpointModel)

  match assembledAliasedEndpointProgram with

  | .error diagnostic =>
      testFailure
        ("the aliased-endpoint model must route and compile for F48 to be a witness, " ++
          "but a step before assembly refused it: " ++
          diagnostic)

  | .ok program => do

      expectBool
        "ALIASED_ENDPOINT_TARGET_UNIQUENESS_FALSE"
        false
        program.targetEndpointsUnique

      expectBool
        "ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED"
        true
        program.connectionsWellFormed

/-!
## Finding F49's witness: the ninth clause, on its own

Hand-built LF rather than a translated model, and that is the point of the group. F48's witness
came out of `compileGeneralModel` and answered "can routing produce a repeated target endpoint".
This one answers a different question — "is `targetEndpointsUnique` derivable from the other
clauses of `LF.GeneralProgram.wellFormed`" — and no translated program can answer it, because on
translation output the relative statement is *true*: routing that duplicates an endpoint
duplicates an input port name too, so `reactorsWellFormed` fails alongside it, which is exactly
what F48 measured. Building the program by hand is what separates a fact about programs from a
fact about programs the translator assembles.

The construction is minimal on purpose. One sender declaring two **different** output ports, one
receiver declaring **one** input port, and two connections from the two different outputs both
landing on that one port. Every connection resolves, since `connectionWellFormed` finds each
source in the sender's output list and each target in the receiver's input list; the receiver's
`declaredNames` holds `incoming` exactly once; both reactors are well-formed. Every other clause
holds and this one does not.

Both startup reactions have empty bodies, which keeps `reactionWellFormed` down to
`triggerWellFormed`, and `.startup` satisfies that outright. Nothing here is contrived except the
one thing under test.
-/

private def sharedTargetSenderReactorName :
    ReactorName :=
  ⟨"SharedSender"⟩

private def sharedTargetReceiverReactorName :
    ReactorName :=
  ⟨"SharedReceiver"⟩

private def sharedTargetSenderInstanceName :
    ActorName :=
  ⟨"sharedSenderActor"⟩

private def sharedTargetReceiverInstanceName :
    ActorName :=
  ⟨"sharedReceiverActor"⟩

private def sharedTargetFirstOutputPortName :
    PortName :=
  ⟨"outOne"⟩

private def sharedTargetSecondOutputPortName :
    PortName :=
  ⟨"outTwo"⟩

private def sharedTargetInputPortName :
    PortName :=
  ⟨"incoming"⟩

private def sharedTargetStartupReaction
    (label : ReactionName) :
    LF.GeneralReaction where
  name := label
  trigger := .startup
  parameters := []
  body := []

private def sharedTargetSenderReactor :
    LF.GeneralReactor where
  name := sharedTargetSenderReactorName
  parameters := []
  inputPorts := []
  outputPorts :=
    [ { name := sharedTargetFirstOutputPortName,
        payload := .scalar .int },
      { name := sharedTargetSecondOutputPortName,
        payload := .scalar .int } ]
  stateVariables := []
  logicalActions := []
  startupReaction :=
    sharedTargetStartupReaction
      ⟨"shared_sender_startup"⟩
  messageReactions := []

private def sharedTargetReceiverReactor :
    LF.GeneralReactor where
  name := sharedTargetReceiverReactorName
  parameters := []
  inputPorts :=
    [ { name := sharedTargetInputPortName,
        payload := .scalar .int } ]
  outputPorts := []
  stateVariables := []
  logicalActions := []
  startupReaction :=
    sharedTargetStartupReaction
      ⟨"shared_receiver_startup"⟩
  messageReactions := []

/--
One connection onto the receiver's only input port, parameterised by the source port.

Parameterised rather than written twice so that the two connections cannot drift in any field
but the one that must differ. Two hand-written copies could come to disagree about the target,
and the group would then be asserting something else.
-/
private def sharedTargetConnectionFrom
    (sourcePortName : PortName) :
    LF.GeneralConnection where
  sourceInstance := sharedTargetSenderInstanceName
  sourcePort := sourcePortName
  targetInstance := sharedTargetReceiverInstanceName
  targetPort := sharedTargetInputPortName
  delay := ⟨0⟩

private def sharedTargetProgram :
    LF.GeneralProgram where
  reactors :=
    [ sharedTargetSenderReactor,
      sharedTargetReceiverReactor ]
  instances :=
    [ { name := sharedTargetSenderInstanceName,
        reactorName := sharedTargetSenderReactorName,
        arguments := [] },
      { name := sharedTargetReceiverInstanceName,
        reactorName := sharedTargetReceiverReactorName,
        arguments := [] } ]
  connections :=
    [ sharedTargetConnectionFrom
        sharedTargetFirstOutputPortName,
      sharedTargetConnectionFrom
        sharedTargetSecondOutputPortName ]

/--
Every clause of `LF.GeneralProgram.wellFormed` other than `targetEndpointsUnique`, each named
with its own verdict.

Rendered as a string rather than folded into one `Bool` so that a failure names the clause that
moved. A conjunction would report `false` for any of them and leave the reader to find out which,
and the whole content of F49 is *which*.

There were eight when F49 landed and there are nine since G3 appended `reactionPrioritiesAbsent`,
which is why neither this docstring nor the list is written in terms of a count. The new clause
holds here for a reason worth stating: `LF.GeneralReaction.priority` defaults to `none` and the
two startup reactions this witness builds do not set it, so adding the entry *strengthened* F49 —
independence from a larger set of clauses is the stronger statement, and it cost one line.
-/
private def sharedTargetOtherClauses :
    String :=
  String.intercalate
    " "
    [
      "reactorsNonEmpty=" ++
        toString sharedTargetProgram.reactorsNonEmpty,
      "instancesNonEmpty=" ++
        toString sharedTargetProgram.instancesNonEmpty,
      "reactorsWellFormed=" ++
        toString sharedTargetProgram.reactorsWellFormed,
      "reactorNamesUnique=" ++
        toString sharedTargetProgram.reactorNamesUnique,
      "instanceNamesUnique=" ++
        toString sharedTargetProgram.instanceNamesUnique,
      "instancesResolve=" ++
        toString sharedTargetProgram.instancesResolve,
      "instanceArgumentsMatch=" ++
        toString sharedTargetProgram.instanceArgumentsMatch,
      "connectionsWellFormed=" ++
        toString sharedTargetProgram.connectionsWellFormed,
      "reactionPrioritiesAbsent=" ++
        toString sharedTargetProgram.reactionPrioritiesAbsent
    ]

/--
Finding F49, asserted rather than argued: `targetEndpointsUnique` is **independent** of every
other clause, so it cannot be dropped from `LF.GeneralProgram.wellFormed`, and these four
assertions are what say so.

The claim these replace was two docstrings in `Relico/Translation/GeneralRouting.lean` — one
arguing that `generalInputPortsOf` needs no deduplication, on two premises F48 had already
refuted, and one stating flatly that `targetEndpointsUnique` "holds by construction rather than
by check". The second cited a real theorem, `inputPortNameFor_outputPort_injective`, which is
true and does not carry the weight: it rules out one sender's two *different* output ports
yielding one input port name, and says nothing about two routes sharing one output port *name*.
Both are rewritten. This group is the part a `grep` can falsify.

`SHARED_TARGET_ISOLATED_REFUSAL` is the one that could not be folded into F48's group, and it is
the reason four assertions rather than three. F48's model fails two clauses, so its refusal text
is two sentences joined, and it pins `generalProgramExplanation` at the *multiple* end of its
range. Here exactly one clause fails, so the text is one sentence with no reactor prefix, which
pins the *singleton* end. Together they establish that the explanation enumerates precisely the
failing clauses; until this assertion existed the singleton case was assumed, and the assumption
is the kind that a first-failure-only rewrite would break without any gate noticing.

If a future tightening makes this program ill-formed for some further reason, the first assertion
fails and names the clause that moved, which is the outcome to want: the witness stops being a
witness loudly rather than by becoming vacuous.
-/
private def sharedTargetAssertions :
    IO Unit := do

  -- The load-bearing half. Every clause but `targetEndpointsUnique`, each by name, so that a
  -- failure here says which one and this group does not quietly weaken into "some clause holds".
  --
  -- The label says EIGHT and the group now checks nine, and that is left alone on purpose: four
  -- transcripts in `docs/STAGE_E_FINDINGS.md` quote `PASS_SHARED_TARGET_EIGHT_CLAUSES_HOLD` as
  -- run, and renaming the marker would make those records irreproducible to buy something the
  -- expected string below already says. The count survives in the label and nowhere else.
  expectString
    "SHARED_TARGET_EIGHT_CLAUSES_HOLD"
    ("reactorsNonEmpty=true instancesNonEmpty=true reactorsWellFormed=true " ++
      "reactorNamesUnique=true instanceNamesUnique=true instancesResolve=true " ++
      "instanceArgumentsMatch=true connectionsWellFormed=true " ++
      "reactionPrioritiesAbsent=true")
    sharedTargetOtherClauses

  -- What separates F49 from F48: there the receiver declared its input port twice, so the
  -- endpoint collision was visible as a name collision. Here it is not.
  expectBool
    "SHARED_TARGET_RECEIVER_NAMES_NODUP"
    true
    (decide
      sharedTargetReceiverReactor.declaredNames.Nodup)

  expectBool
    "SHARED_TARGET_UNIQUENESS_FALSE"
    false
    sharedTargetProgram.targetEndpointsUnique

  -- One failing clause, one sentence, no "some reactor is not well-formed" prefix. The other
  -- end of the range `ALIASED_ENDPOINT_COLLISION_REFUSED` pins.
  expectRefusedTerm
    "SHARED_TARGET_ISOLATED_REFUSAL"
    ("the translated LF program is not well-formed: two connections target the same " ++
      "input port of the same instance, which the LF compiler rejects as a many-to-one " ++
      "connection")
    (Translation.guardGeneralProgram
      sharedTargetProgram)

/-!
## Finding F50's witness: one reaction, one output port, set twice

F48's model is reused rather than a new one built, and that is deliberate. The collision that
makes two routes share a target endpoint is the *same* collision that makes one reaction set
one output port twice; a second model would let a future change fix one and leave the other,
and would hide that both are consequences of one unescaped separator.

What is new is where the assertions look. F48 read the sending class's output port
*environment* and the emitted *connection* list, both program-level objects. `docs/STAGE_E_DESIGN.md`
§10.2's sentence — *"no reaction of an emitted reactor sets one output port twice"* — is not a
claim about either: it is a claim about the statement list inside one compiled reaction body,
and this is the only block in the file that opens one.

Which reaction it is carries the finding, and `LF.GeneralReactor` names it for us: the structure
has no flat `reactions` list at all, but a `startupReaction` field beside a `messageReactions`
list, so the doubling reaction is projected rather than searched for. The colliding sends sit in
`aliasedProbeClass`'s *constructor*, which is exactly what compiles to `startupReaction`; any
restatement of §10.2 scoped to message-server reactions would be true and would miss this
entirely.
-/

/--
The emitted `startup` reaction of the aliasing sender, with its reactor, or the step that
refused.

The reactor comes back alongside the reaction because `LF.GeneralReactor.reactionWellFormed`
resolves a body against its reactor's declarations, so the second assertion below cannot ask
its question with the reaction alone.
-/
private def aliasedEndpointStartup :
    Except String (LF.GeneralReactor × LF.GeneralReaction) :=
  match assembledAliasedEndpointProgram with

  | .error diagnostic =>
      .error
        ("the aliased-endpoint model did not assemble: " ++
          diagnostic)

  | .ok program =>
      match
          LF.findReactor?
            program.reactors
            (Translation.reactorNameFor
              aliasedProbeClassName) with

      | none =>
          .error
            "the aliasing sender emitted no reactor"

      | some reactor =>
          .ok
            (reactor, reactor.startupReaction)

/--
The output ports the sender's startup reaction sets, in order, repeats included.
-/
private def aliasedEndpointStartupSetPorts :
    String :=
  match aliasedEndpointStartup with

  | .error diagnostic =>
      diagnostic

  | .ok (_, reaction) =>
      String.intercalate
        " | "
        ((LF.setPortNamesOfBody
          reaction.body).map
          (fun port =>
            port.value))

/--
Whether that same reaction satisfies `LF.GeneralReactor.reactionWellFormed`.
-/
private def aliasedEndpointStartupReactionWellFormed :
    Bool :=
  match aliasedEndpointStartup with

  | .error _ =>
      false

  | .ok (reactor, reaction) =>
      reactor.reactionWellFormed
        reaction

/--
Finding F50, asserted rather than argued: §10.2's owed theorem is false unqualified, and the
counterexample is one reaction of one emitted reactor.

Two assertions, and the second is what keeps the attribution narrow — the same move
`ALIASED_ENDPOINT_CONNECTIONS_WELLFORMED` makes for F48. `reactionWellFormed` is expected to
**accept** this reaction: its `.setPort` arm asks that the port be *declared* on the reactor
with a matching payload arity, and `reportToToHub` is declared, twice over. So the repetition
is invisible to every clause that inspects a reaction, and the refusal F48 already asserts
comes from `declaredNames` and from the connection list — never from the body that does the
doubling.

If that second assertion ever reports `false`, it is not a regression to paper over: it would
mean some clause of `LF.GeneralWellFormed` had started catching the repetition, which is news,
and the honest response is to find which clause and rewrite F50 rather than adjust the
expected value.
-/
private def perReactionSetPortAssertions :
    IO Unit := do

  expectString
    "ALIASED_SETPORT_TWICE_IN_ONE_REACTION"
    "reportToToHub | reportToToHub"
    aliasedEndpointStartupSetPorts

  expectBool
    "ALIASED_SETPORT_REACTION_STILL_WELLFORMED"
    true
    aliasedEndpointStartupReactionWellFormed

/--
The F56 witness, as four assertions.

The text assertion is load-bearing and would fail on its own if the repair regressed. The
three structural assertions exist to **localise**: a failure in the text alone says the bytes
moved, a failure in the action names says the site suffix stopped being applied, and a
failure in the reaction names says the sibling-naming rule changed. Reading which one broke
is cheaper than diffing a twenty-seven line program.
-/
private def repeatedSelfSendAssertions :
    IO Unit := do

  expectRendered
    "REPEATED_SELF_SEND_PROGRAM"
    expectedRepeatedSelfSendProgramText
    repeatedSelfSendProgramText

  match Translation.compileGeneralModel
    repeatedSelfSendModel
  with

  | .error diagnostic =>
      testFailure
        ("the repeated-self-send model must translate, but it was refused: " ++
          diagnostic)

  | .ok program => do

      -- The clause that matters here is `declaredNames` being `Nodup`. Two sites of one
      -- message declare two actions on one reactor, so dropping the site suffix would
      -- collide them against each other, and this is the check that would catch it rather
      -- than the text assertion, which would merely differ.
      expectWellFormed
        "ACCEPT_REPEATED_SELF_SEND_PROGRAM"
        program

      -- Distinct, because action names are printed identifiers under the `Nodup` guard.
      expectString
        "REPEATED_SELF_SEND_ACTION_NAMES"
        "tick_action1,tick_action2"
        (String.intercalate
          "|"
          (program.reactors.map
            (fun reactor =>
              String.intercalate
                ","
                (reactor.logicalActions.map
                  (fun action =>
                    action.name.value)))))

      -- Shared, and that is the asymmetry against the line above.
      -- `renderGeneralReaction` prints `reaction(<trigger>)` and drops the name, reaction
      -- names are absent from `declaredNames`, and `Relico/LF/GeneralWellFormed.lean:37`
      -- records that requiring them to be unique would constrain an identifier the target
      -- language never sees. What separates these two reactions in the emitted text is
      -- their triggers, which the text assertion above pins.
      expectString
        "REPEATED_SELF_SEND_REACTION_NAMES_SHARED"
        "tick_reaction,tick_reaction"
        (String.intercalate
          "|"
          (program.reactors.map
            (fun reactor =>
              String.intercalate
                ","
                (reactor.messageReactions.map
                  (fun reaction =>
                    reaction.name.value)))))

/-!
## The priority fan-in family

**The first priority annotation of any kind in this file, and finding F59 is why it is
owed.** Every one of the thirteen models above takes the default `priority := none`, so
every pair of instances is *tied* under the reflexive `PriorityPrecedesOrEqual`
(`Relico/DTR/GeneralPriority.lean:55`); `insert` (`:266`) tests that reflexive relation, so
on all-tied input it never displaces an element and `normalize` (`:299`) is the identity.
The ninety-two assertions above therefore could not have moved for *any* stable sort. They
are a witness for **stability** — the one property the sortedness development structurally
cannot pin, because `Sorted` holds for both orders of a tied pair — and they are not a
witness for ordering. This family is the witness for ordering.

Its instance list is a **derangement** of its priority order: declared `collector, alpha,
beta, gamma` carrying priorities `4, 3, 1, 2`, emitted `beta, gamma, alpha, collector`. No
instance keeps its declared position, so the expected text below fails under declaration
order and fails under any single transposition of it.

Two things are deliberately *not* here.

There is no `.rebeca` fixture. By F59's first fact no gate carries a fixture through
translation — `PRINTER_TEST_MAIN` is invoked with no arguments at
`frontend/check-general-lean.sh:248-252` — so a fixture pair would add one decoder
assertion and move no emitted text.

And the expected order is a **literal**, never a value recomputed from `routesOf`. An
assertion whose two sides both consume the sorted route table moves with the sort and
cannot fail: that is finding **F60**, against
`ROUTED_REACTION_ORDER_MATCHES_SPECIFICATION` above. Both assertions below are compared
against the same literal precisely so that they cannot be satisfied by agreeing with each
other.

The receiver's two message servers carry distinct priorities in disagreeing declaration
order as well. When this block was written that was a **negative control** rather than a
second claim: level 2 did not exist, `DTR.GeneralMessageServerPriority` had zero references
under `Relico/Translation/` and `Relico/Correctness/`, message-server priority was inert,
and `drain_reaction` was emitted last where its *declaration* puts it. Task #87 then moved
it to the front, and the literal below changed in exactly that one way — one predicted
permutation of text written before the behaviour existed, rather than text written to match
behaviour after the fact.

The prediction was checked in that order rather than merely claimed in it. The gate was run
with the old literal still in place, and the diagnostic reported the new order character for
character *before* any text was edited. So this is a claim now rather than a control, and
the control it used to be is what makes the claim worth anything.
-/

private def fanInSenderClassName :
    ClassName :=
  ⟨"Probe"⟩

private def fanInReceiverClassName :
    ClassName :=
  ⟨"Collector"⟩

private def fanInSampleMessageName :
    MsgName :=
  ⟨"sample"⟩

private def fanInPingMessageName :
    MsgName :=
  ⟨"ping"⟩

private def fanInDrainMessageName :
    MsgName :=
  ⟨"drain"⟩

private def alphaInstanceName :
    ActorName :=
  ⟨"alpha"⟩

private def betaInstanceName :
    ActorName :=
  ⟨"beta"⟩

private def gammaInstanceName :
    ActorName :=
  ⟨"gamma"⟩

private def collectorInstanceName :
    ActorName :=
  ⟨"collector"⟩

/--
The sender's one server, and the source of every route in this model.

One external send to one known rebec, so `generalSiteSuffixFor`
(`Relico/Translation/GeneralRouting.lean:454-468`) returns the empty string and the output
port is `pingToHub` with no ordinal — the shape `resetToHub` has in the routed family,
not the shape `reportToHub1` has.

Its payload is arity one on purpose. Arity zero is the one refusal a well-formed model
reaches (`Relico/Translation/GeneralRouting.lean:871`) and it fires on any message a
*port* must carry, because a port carrying nothing has no measured spelling. `sample`
itself takes no parameters and that is legal and deliberate: nothing sends to `sample`,
so it has a logical action and no port, and `pollMessageServer` above is the
already-asserted witness that a parameterless server compiles.
-/
private def fanInSampleMessageServer :
    DTR.GeneralMessageServer where

  name :=
    fanInSampleMessageName

  parameters :=
    []

  body :=
    [
      .send
        (.knownRebec hubKnownRebecName)
        fanInPingMessageName
        [.intLiteral 1]
        ⟨0⟩
    ]

/--
The server every route lands on: declared **first**, priority **second**.

Its body reads the formal and writes the state variable, so the reaction is not empty and
the parameter is not an unused local.
-/
private def fanInPingMessageServer :
    DTR.GeneralMessageServer where

  name :=
    fanInPingMessageName

  parameters :=
    [
      {
        name :=
          levelParameter

        declaredType :=
          .int
      }
    ]

  body :=
    [
      .assign
        lastLevelStateName
        (.parameterVar levelParameter)
    ]

  priority :=
    some 2

/--
The server no route lands on: declared **second**, priority **first**.

Nothing sends `drain`, so its group is one action reaction and nothing else — which is the
whole reason it is shaped this way. Level 2 moving it was then a single token moving from
the end of the expected literal to the front, and a one-token difference is the cheapest
predicted permutation task #87 could be held to. It was held to exactly that: the token
moved, and nothing else in the literal did.
-/
private def fanInDrainMessageServer :
    DTR.GeneralMessageServer where

  name :=
    fanInDrainMessageName

  parameters :=
    []

  body :=
    [
      .assign
        lastLevelStateName
        (.intLiteral 0)
    ]

  priority :=
    some 1

/--
The sending class. No state variables and an empty constructor, both legal:
`Relico/DTR/GeneralSyntax.lean` records that a class may declare no known rebecs, no state
variables and no message servers, because the paper's own figures need all three.
-/
private def fanInSenderClass :
    DTR.GeneralReactiveClass where

  name :=
    fanInSenderClassName

  knownRebecs :=
    [
      {
        name :=
          hubKnownRebecName

        className :=
          fanInReceiverClassName
      }
    ]

  stateVariables :=
    []

  constructor :=
    {
      parameters :=
        []

      body :=
        []
    }

  messageServers :=
    [fanInSampleMessageServer]

/--
The receiving class, and the only reactor in this model whose reaction group has more than
one entry.

Its two servers are declared in the order `ping, drain` and prioritized in the order
`drain, ping`, which is the level-2 disagreement this model carries as a negative control.
-/
private def fanInReceiverClass :
    DTR.GeneralReactiveClass where

  name :=
    fanInReceiverClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name :=
          lastLevelStateName

        declaredType :=
          .int
      }
    ]

  constructor :=
    {
      parameters :=
        []

      body :=
        []
    }

  messageServers :=
    [
      fanInPingMessageServer,
      fanInDrainMessageServer
    ]

/--
The receiver: declared **first**, priority **last**.

It contributes no route, so its own position in the walked instance list is not observable
in the expected text at all. It carries a priority anyway, for two reasons. The whole
instance list is then a derangement rather than only its sender prefix; and
`ActorPrioritiesDistinct` is witnessed over four *explicit* priorities rather than three
explicit ones plus an absence, which matters because an absence is a priority class of its
own and would make the guard hold for a weaker reason than the one under test.
-/
private def collectorActor :
    DTR.GeneralActorInstance where

  name :=
    collectorInstanceName

  className :=
    fanInReceiverClassName

  bindings :=
    []

  arguments :=
    []

  priority :=
    some 4

/--
The first sender declared, and the **last** of the three in priority.

`arguments := []` because `Probe`'s constructor has no formals, so `instanceArgumentsMatch`
holds vacuously rather than by agreement.
-/
private def alphaProbe :
    DTR.GeneralActorInstance where

  name :=
    alphaInstanceName

  className :=
    fanInSenderClassName

  bindings :=
    [(hubKnownRebecName, collectorInstanceName)]

  arguments :=
    []

  priority :=
    some 3

/--
The second sender declared, and the **first** of the three in priority.

A structure update on `alphaProbe`, so the name and the priority are the only differences
and the emitted position cannot be explained by anything else — the discipline `spareActor`
follows against `stationActor`.
-/
private def betaProbe :
    DTR.GeneralActorInstance :=
  {
    alphaProbe with

    name :=
      betaInstanceName

    priority :=
      some 1
  }

/--
The third sender declared, and the **second** of the three in priority.
-/
private def gammaProbe :
    DTR.GeneralActorInstance :=
  {
    alphaProbe with

    name :=
      gammaInstanceName

    priority :=
      some 2
  }

/--
The fan-in model.

Class order fixes reactor order, so the expected text's two `|`-separated halves are
`Probe` then `Collector`. Instance order is where the derangement lives: every one of the
four instances moves, and the three senders move in a 3-cycle.
-/
private def priorityFanInModel :
    DTR.GeneralModel where

  classes :=
    [
      fanInSenderClass,
      fanInReceiverClass
    ]

  instances :=
    [
      collectorActor,
      alphaProbe,
      betaProbe,
      gammaProbe
    ]

/--
The emitted reaction order: what `compileGeneralModel` actually built.
-/
private def priorityFanInEmittedReactionOrder :
    Except String String := do
  let program ←
    Translation.compileGeneralModel
      priorityFanInModel

  pure
    (String.intercalate
      "|"
      (program.reactors.map
        (fun reactor =>
          String.intercalate
            ","
            (reactor.messageReactions.map
              (fun reaction =>
                reaction.name.value)))))

/--
The specified reaction order: what `generalReactionNamesOf` predicts.

The same shape as `routedSpecifiedReactionOrder` above, and asserted very differently. There the
two sides are compared to *each other*, which finding **F60** records as an assertion no
permutation the sort can produce could fail. Here this value and the constructor's own answer are
each compared against the same **literal**, which is what lets either of them fail without the
other.

This walks `generalPriorityOrderedMessageServers reactiveClass` rather than
`reactiveClass.messageServers`, and that changed with task #87. The reason is that this function is
the executable counterpart of `compileGeneralReactiveClass_reactionNames`, whose right-hand side
became `generalReactionNamesOf … (generalPriorityOrderedMessageServers reactiveClass)` when level 2
was wired. The alternative considered was to leave the argument unsorted and give this assertion a
declaration-order literal of its own, asserting the specification function's parametricity in
whatever list it is handed. That was rejected because it would pin a value **no theorem mentions**:
a change to the sort would become invisible here, and the single purpose of this value is to be the
runnable form of a statement that is proved.

What the pair can and cannot report is finding **F61**. Either side can fail alone, but at most one
failure per run is ever *observed*: `testFailure` throws, `runGeneralLfPrinterTests` catches once,
and the emitted assertion is sequenced ahead of this one. So a fault in `generalReactionNamesOf`
alone is reported here with the emitted assertion passing, and a fault in the constructor's group
walk alone is reported there — but a fault that moves **both** reports only the constructor and
says nothing whatever about this value. That asymmetry is why the sentence this docstring replaces
was wrong to promise that the two "will disagree and say which one moved": in the one direction
task #87 actually moved, this assertion never runs.
-/
private def priorityFanInSpecifiedReactionOrder :
    Except String String := do
  let routes ←
    Translation.routesOf
      priorityFanInModel

  pure
    (String.intercalate
      "|"
      (priorityFanInModel.classes.map
        (fun reactiveClass =>
          String.intercalate
            ","
            ((Translation.generalReactionNamesOf
              (Translation.selfSendsOfClass reactiveClass)
              routes
              reactiveClass.name
              (Translation.generalPriorityOrderedMessageServers
                reactiveClass)).map
              (fun reactionName => reactionName.value)))))

/--
The one literal both orders are asserted against, and every token in it is derivable by
hand.

`Probe` first, because class order fixes reactor order. Its only group is `sample`'s, and
`generalMessageReactionNamesOf` (`Relico/Translation/GeneralBasic.lean:4285`) yields the
single name `sample_reaction` when nothing self-sends to the server. No route lands on
`Probe`, so the group ends there.

`Collector` second. `ping`'s group opens with its own action reaction, then carries one port
reaction per route into it, in route order. A port reaction is named after the input port
that triggers it, and the chain that spells that name is:
`outputPortNameFor` → `ping` ++ `To` ++ `Hub` ++ `""` = `pingToHub`, the suffix empty
because the class has exactly one send to that pair; then `inputPortNameFor` appends
`From` ++ the capitalized *sender instance*; then `portReactionNameFor` appends
`_reaction`. So the three names differ only in the sender, which is exactly what makes a
name list able to witness sender-priority order at all.

Route order is priority order, because `routesOf` walks
`priorityOrderedInstances` (`Relico/Translation/GeneralRouting.lean:1496`) and filtering
preserves order. Priorities `beta = 1`, `gamma = 2`, `alpha = 3` therefore give
`Beta, Gamma, Alpha` — a 3-cycle away from the declared `alpha, beta, gamma`.

`drain_reaction` **opens** `Collector`'s group rather than closing it, and its position is the
whole of level 2's observation. The two servers are declared `ping, drain` and prioritized
`drain = 1, ping = 2`, so declaration order and priority order disagree at this class, and
`compileGeneralReactiveClass` walks `generalPriorityOrderedMessageServers reactiveClass` rather
than `reactiveClass.messageServers`. Level 1's 3-cycle inside `ping`'s group survives that move
untouched, because the two sorts act on different lists — one on instances, one on servers — and
this literal is the one place in the repository where both are visible at once.

This token's position is also where level 2 *not* being implemented used to be visible. It sat
last, in declaration order, from task #86 until task #87, and the commitment at `:4896-4899` was
that #87 would move it to the front and change this literal in exactly that one way. It did, and
the order of events is the part worth keeping: the run that first exercised level 2 reported
`drain_reaction` leading with the rest of the list unchanged, character for character, **before**
this literal was touched. Editing the literal first would have left a green gate equally
consistent with the sort working and with the text having been fitted to whatever the sort
happened to produce, which is the defect F51 and F53 record.
-/
private def expectedPriorityFanInReactionOrder :
    String :=
  "sample_reaction" ++
    "|" ++
    "drain_reaction," ++
    "ping_reaction," ++
    "pingToHubFromBeta_reaction," ++
    "pingToHubFromGamma_reaction," ++
    "pingToHubFromAlpha_reaction"

/--
Stage F's ordering evidence: four assertions on one model whose declaration order and
priority order agree nowhere.
-/
private def priorityFanInAssertions :
    IO Unit := do

  -- Without this the group proves nothing about the translator: a source model the
  -- frontend would reject makes anything downstream a fact about the frontend. The same
  -- discipline `ALIASED_ENDPOINT_SOURCE_WELLFORMED` follows.
  expectBool
    "PRIORITY_FAN_IN_SOURCE_WELLFORMED"
    true
    priorityFanInModel.wellFormed

  -- The level-1 theorems in `Relico/Correctness/GeneralPriorityOrder.lean` are
  -- guard-relative: `portReactions_realizeActorPriority` composes the guard-relative split
  -- result with instance declaration order, and its hypothesis is this predicate. A
  -- witness that failed it would exercise the unconditional form only, so this pins that
  -- the model is in the theorems' range. It is not in `DTR.GeneralModel.wellFormed` and
  -- must not be — three servers in `expressions.rebeca` are unannotated — so nothing above
  -- implies it.
  expectBool
    "PRIORITY_FAN_IN_ACTOR_PRIORITIES_DISTINCT"
    true
    (decide priorityFanInModel.ActorPrioritiesDistinct)

  -- The claim itself. Under `normalize := id` this reads
  -- `pingToHubFromAlpha_reaction,pingToHubFromBeta_reaction,pingToHubFromGamma_reaction`
  -- and fails, which is the property the ninety-three assertions above do not have.
  expectRendered
    "PRIORITY_FAN_IN_EMITTED_REACTION_ORDER"
    expectedPriorityFanInReactionOrder
    priorityFanInEmittedReactionOrder

  -- And the specification agrees with the same literal, rather than with the line above.
  expectRendered
    "PRIORITY_FAN_IN_SPECIFIED_REACTION_ORDER"
    expectedPriorityFanInReactionOrder
    priorityFanInSpecifiedReactionOrder

/--
Run every assertion: 35 printing, then 10 well-formedness, then 11 translation, then
3 for the port-name collisions F34 and F42, then 5 for finding F32's counterexample,
then 7 for the routed model, then 6 for the refusals routing reaches, then 6 for finding
F48's aliased endpoints, then 4 for finding F49's shared target endpoint, then 2 for
finding F50's doubled set port, then 4 for finding F56's repeated self-send, then 4 for
stage F's priority fan-in, 97 in all.

The count is stated here because `frontend/check-general-lean.sh` compares the
number of `PASS_` lines against a literal. There are no fixtures to count, so a
literal is the only way the gate can notice an assertion that stopped running —
which is the failure a marker check alone cannot see.

Stage C ran 25 of these, in two blocks. The third block is the one that mentions
`Relico.Translation`: everything above it would still pass if `compileGeneralModel` did
not exist. The fourth is the only one that calls into
`Relico.Translation.NameGeneration` directly, rather than reading names off a program
something else built. The sixth is the one that mentions
`Relico.Translation.GeneralRouting`, and everything above *it* would still pass if
routing did not exist. The seventh reads routing's **diagnostics** rather than its
output, and it is the only block in the file that would survive routing returning a
correct answer for the wrong reason and still fail if the reasons were mislabelled.

Stage E moved this number in both directions, and the down direction is the one worth
recording. It first went **60 to 59**: stage D asserted `generalModelSelfSendOnly`'s
verdict on two models and the text of its one refusal, stage E deletes the predicate, so
three of those four assertions had nothing left to call, and the three that replaced them
are two refusals plus one statement about the collision program's connections. Then the
routed model took it to 66, and the F32 group's move to the assembly layer added the
refusal assertion F43 records, taking it to 67. A number that only ever rises is a number
nobody is reading.

Then **67 to 70**, and this rise is the one to read rather than wave through: the three
assertions are not new coverage, they are coverage `Relico/Translation/NameGeneration.lean`
had already claimed in prose while the assertions did not exist. That is finding F44. The
count moving is the cheap part; what was actually repaired is a docstring that had been
telling readers a gap was discharged.

Then **70 to 76**, which is the same repair a second time and by now not a coincidence.
`Relico/Translation/GeneralBasic.lean` credited eight translation refusals to two
`lean-reject` documents that structurally cannot reach a translation function; measuring
the inventory found eight causes with two texts asserted. That is finding F47, and the six
here are the missing six. F44 and F47 are two of the four instances
`docs/STAGE_E_FINDINGS.md` records of one root cause: a claim about this suite written as
prose instead of as a label a `grep` can falsify. Every assertion added in both rounds is
named, and the names are the point.

Then **76 to 82**, which is the same root cause a fifth time and the first instance of it that
was not about this suite. F44 and F47 were docstrings claiming coverage that did not exist;
F48 is a docstring claiming a *theorem* was merely deferred when the property it would prove is
false, which is the more expensive kind, because a deferred proof gets scheduled and a false
one cannot be. The six here are the witness. The eighth block is also the first one that asserts
a named clause of `LF.GeneralProgram.wellFormed` to be **false**: everything above it either
accepts a program or reads a refusal's text, and neither can say which clause failed.

Then **82 to 86**, and this rise is not another instance of that root cause — it is the first
time in stage E that a number moved because a *theorem* was refuted rather than because a
docstring had over-claimed. F48's own entry recorded a relative statement as provable;
`reactorsWellFormed` and `instancesResolve` do **not** imply `targetEndpointsUnique` over an
arbitrary program, and the four assertions here are the counterexample, which is finding F49.
What they buy is the reverse of what a counterexample usually buys: the clause is independent of
every other clause, so it must **stay** in `wellFormed`, and independence is a stronger reason to
keep it than the absence of a construction proof was. The ninth block is also the only one whose
program is built by hand *for a clause*, rather than to be printed or to be refused — the eighth
block's model has to go through the translation to be a witness, and this one has to not.

Then **86 to 88**, and this pair is the first in stage E to be added because a theorem the
*design document* owed was refuted, rather than one a docstring claimed. `docs/STAGE_E_DESIGN.md`
§10.2 owes *"no reaction of an emitted reactor sets one output port twice"* and derives it from
sites being addresses; distinct sites do not give distinct names, so the sentence is false and
`ALIASED_SETPORT_TWICE_IN_ONE_REACTION` is one emitted reaction that breaks it. That is finding
F50. The tenth block is the only one that reads inside a compiled *reaction body* — every block
above it stops at the program, the reactor, or a diagnostic's text, and none of them can see a
statement list at all. It is also the second block to reuse an earlier block's model on purpose:
F48's collision and F50's are one collision seen at two depths, and splitting the model would
let a repair fix one and silently leave the other.

Then **88 to 92**, and this rise is the first in stage E that came from measuring the *target
language* rather than from refuting something written in this repository. F45 through F50 were
all cases where a docstring, a design section or a theorem said something false about code that
was already here; F56 is a case where `lfc 0.11.0` accepts two `schedule` calls on one logical
action at one tag, keeps only the last value, and exits 0 — so no assertion in this file could
have failed, and none of the three programs the target gate already compiled could have caught
it. The eleventh block is also the only one whose model exists to be emitted *twice*: it is
asserted here as text, and it is also one of the four programs
`frontend/check-general-lf-target.sh` compiles and runs against a real `lfc`. It is the only
one of those four in which a message server owns more than one logical action, so it is the
only one whose acceptance says anything about whether the repair produces legal LF.

Then **92 to 96**, and this rise is unlike all of the ones above it: every earlier block was
added because something in this repository or in `lfc` was found to be *false*, and this one
is added because something was found to be **unfalsifiable**. Finding F59 measured that no
gate carries a fixture through translation and that `grep -c priority` over this file
returned zero, so every pair of instances in every model above was tied, `normalize` was the
identity on all of them, and the ninety-two assertions could not have moved for any stable
sort. They witness stability, which the sortedness theorems cannot pin, and they do not
witness ordering. The twelfth block is the first model in this file with a priority
annotation of any kind, and the first whose expected text a permutation of the emitted order
would break. It is also the only block whose literal was written to be **changed** on a schedule: its last token
sat in declaration order because level 2 did not exist yet, and task #87 moved it to the front. That
schedule is now discharged, and the literal is an ordinary pin again — with the one difference that
the permutation it records was written down before it could be observed, and then observed to be
right.
-/
def runGeneralLfPrinterTests :
    IO UInt32 := do

  try
    printerAssertions

    wellFormednessAssertions

    translationAssertions

    portNameCollisionAssertions

    collisionAssertions

    routedAssertions

    routedRefusalAssertions

    aliasedEndpointAssertions

    sharedTargetAssertions

    perReactionSetPortAssertions

    repeatedSelfSendAssertions

    priorityFanInAssertions

    IO.println
      "GENERAL_LF_PRINTER_TESTS_OK"

    pure 0

  catch exception => do
    IO.eprintln
      (toString exception)

    pure 1

/--
Print the exact text the printer produces for `baseProgram`, and nothing else.

This exists so that the emitted program can be handed to a real `lfc` instead of
only being compared against a string written in this file. The `PROGRAM`
assertion above pins the text; `lfc` is what decides whether that text is a legal
LF program at all. Those are two different questions, and only the second one can
catch a construct that this file and the printer agree on and the compiler does
not accept.

Nothing is printed but the program, so the caller can redirect straight into a
`.lf` file. A refusal goes to stderr and exits non-zero, because an empty `.lf`
file would otherwise reach `lfc` and fail there with a misleading diagnostic.
-/
def emitBaseProgram :
    IO UInt32 :=
  match
    LF.CppPrinter.renderGeneralProgram
      baseProgram with

  | .ok programText => do
      IO.print programText

      pure 0

  | .error reason => do
      IO.eprintln
        ("the printer refused the base program: " ++
          reason)

      pure 1

/--
Print the text the *translation* of `widenedModel` produces, and nothing else.

The second emitter, and the reason stage D's `lfc` gate compiles two programs rather
than one. The base program above is hand-built LF and answers "is this printer's output
legal LF". This one starts from a Timed Rebeca model and answers the question stage D
exists for: does what the translator produces compile and run. A gate that only ran the
first could go green with a translation that emits nothing at all.

`widenedProgramText` is shared with `TRANSLATED_WIDENED_PROGRAM`, so the bytes `lfc`
compiles are the bytes that assertion pinned. Two paths each recomputing the program
would be two chances to compile something no assertion checked.
-/
def emitWidenedProgram :
    IO UInt32 :=
  match widenedProgramText with

  | .ok programText => do
      IO.print programText

      pure 0

  | .error reason => do
      IO.eprintln
        ("the translation or the printer refused the widened model: " ++
          reason)

      pure 1

/--
Print the text the translation of `routedModel` produces, and nothing else.

The third emitter, and the one the stage E gate exists for. The base program answers
"is this printer's output legal LF"; the widened program answers "does a translated
single-actor model compile and run"; this one answers the question no earlier stage
could ask, because no earlier stage emitted a port: does a translated *multi-actor*
model compile and run.

Three of its claims are established here and nowhere else in this repository. Nonzero
connection delays — `after 3 msec` and `after 7 msec` — have never been compiled by any
probe under `tools/paper-measurements/`, which has only ever written `after 0 msec`. A
reactor with no startup reaction has never reached `lfc` either. Nor has an instance
whose input ports no connection reaches. All three are ordinary LF and all three are
now compiled and run rather than assumed.

`routedProgramText` is shared with `TRANSLATED_ROUTED_PROGRAM`, so the bytes `lfc`
compiles are the bytes that assertion pinned.
-/
def emitRoutedProgram :
    IO UInt32 :=
  match routedProgramText with

  | .ok programText => do
      IO.print programText

      pure 0

  | .error reason => do
      IO.eprintln
        ("the translation or the printer refused the routed model: " ++
          reason)

      pure 1

/--
Print the repeated-self-send program, for the target gate to hand to `lfc`.

This is the only emitted program in which one message server owns two logical actions and
two reactions, so it is the only one whose acceptance says anything about whether the
per-site repair produces legal LF. The other three would compile unchanged if the repair
were reverted.
-/
def emitRepeatedSelfSendProgram :
    IO UInt32 :=
  match repeatedSelfSendProgramText with

  | .ok programText => do
      IO.print programText

      pure 0

  | .error reason => do
      IO.eprintln
        ("the translation or the printer refused the repeated-self-send model: " ++
          reason)

      pure 1

/-!
### The G5 witness: priority order deranging declaration order, observed at run time

`docs/STAGE_G_DESIGN.md` §10 asks for one model whose run distinguishes priority order
from declaration order, because everything before it gated priority as *text*: a
translator that emitted the right declaration order while running in the wrong one would
pass every gate in this repository. This model is that witness, and the observation
happens in `frontend/check-general-lf-target.sh`, not here.

Two derangements are carried, one per level, and only one of them is observable at run
time — that asymmetry is a property of the target, not a choice of this file:

* **Level 2, observable.** `WitnessHub` declares its servers in the order
  `early, late`, and annotates only `late` (`priority := some 0`); an absent priority is
  a priority class ordered after every explicit one, so
  `Translation.generalPriorityOrderedMessageServers` walks them `late, early`, and the
  hub reactor's reactions are **declared** in that order. Both deliveries arrive at one
  complete tag on two port-triggered reactions of one reactor — the exact shape stage F
  measured (`STAGE_F_DESIGN.md` §2.1, probe pair `stageF_onesender_twoports`): at one
  tag, **declaration order decides**. So the run prints `LATE` before `EARLY`, while the
  class declares `early` first.
* **Level 1, text only.** The two senders are declared `early, late` and prioritised the
  other way round (`some 2` vs `some 1`), so `routesOf` emits `late`'s connection first.
  Cross-reactor and connection order are not run-time observables (P1: LF's cross-reactor
  order comes from the dependency graph), so this derangement is visible in the emitted
  text and nowhere else. The senders' payloads differ (`1` vs `2`) so the two connections
  are distinguishable in that text.

Both senders send from their constructors with `after 0`, the hub's servers send nothing,
and the hub's constructor is empty, so the event queue empties and the binary exits — the
termination property every program in the target gate owes.

What this witness does **not** claim: that stdout is part of the formal observable
alphabet. Option A (F-milestone `general: add G5 trace semantics`) made `.trace` a τ
step on both sides precisely so the theorem boundary stays where it was; the bytes on
stdout are target-runtime evidence, owned by the gate, not by `GeneralLabel`.
-/

private def witnessHubClassName :
    ClassName :=
  ⟨"WitnessHub"⟩

private def earlySenderClassName :
    ClassName :=
  ⟨"EarlySender"⟩

private def lateSenderClassName :
    ClassName :=
  ⟨"LateSender"⟩

private def witnessHubInstanceName :
    ActorName :=
  ⟨"hub"⟩

private def earlySenderInstanceName :
    ActorName :=
  ⟨"early"⟩

private def lateSenderInstanceName :
    ActorName :=
  ⟨"late"⟩

private def earlyMessageName :
    MsgName :=
  ⟨"early"⟩

private def lateMessageName :
    MsgName :=
  ⟨"late"⟩

private def witnessValueParameter :
    VarName :=
  ⟨"value"⟩

private def witnessStateName :
    VarName :=
  ⟨"last"⟩

/--
The server declared **first** and prioritised **last**.

Its priority field is omitted rather than set to `none`: an absent priority is a priority
class of its own — the convention fixed at `Relico/DTR/GeneralSyntax.lean`'s
`GeneralMessageServer` docstring — and omitting the field is how the syntax spells that
class, so the omission *is* the point being witnessed.

The formal is read rather than ignored, so the emitted reaction neither warns about an
unused parameter nor runs empty; the trace tag is the observable.
-/
private def witnessEarlyMessageServer :
    DTR.GeneralMessageServer where

  name :=
    earlyMessageName

  parameters :=
    [
      {
        name :=
          witnessValueParameter

        declaredType :=
          .int
      }
    ]

  body :=
    [
      .assign
        witnessStateName
        (.parameterVar
          witnessValueParameter),

      .trace
        "EARLY"
    ]

/--
The server declared **second** and prioritised **first**.

The only annotated server in the model, and therefore the whole of the level-2
derangement: `generalPriorityOrderedMessageServers` puts this block ahead of `early`'s
despite the declaration order, and that block order is what `lfc` executes first.
-/
private def witnessLateMessageServer :
    DTR.GeneralMessageServer where

  name :=
    lateMessageName

  parameters :=
    [
      {
        name :=
          witnessValueParameter

        declaredType :=
          .int
      }
    ]

  body :=
    [
      .assign
        witnessStateName
        (.parameterVar
          witnessValueParameter),

      .trace
        "LATE"
    ]

  priority :=
    some 0

/--
The receiving class: servers declared `early, late`, prioritised `late, early`.

No message servers send anything and its constructor is empty, so the hub contributes no
routes; its role is to own the two port-triggered reaction blocks whose declaration order
the level-2 sort deranges.
-/
private def witnessHubClass :
    DTR.GeneralReactiveClass where

  name :=
    witnessHubClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name :=
          witnessStateName

        declaredType :=
          .int
      }
    ]

  constructor :=
    {
      parameters :=
        []

      body :=
        []
    }

  messageServers :=
    [
      witnessEarlyMessageServer,
      witnessLateMessageServer
    ]

/--
The sender declared **first**, prioritised **last** (`some 2`).

Sends payload `1` so the two connections are distinguishable in the emitted text — the
same discipline the F56 model follows for its two schedules.
-/
private def earlySenderClass :
    DTR.GeneralReactiveClass where

  name :=
    earlySenderClassName

  knownRebecs :=
    [
      {
        name :=
          hubKnownRebecName

        className :=
          witnessHubClassName
      }
    ]

  stateVariables :=
    []

  constructor :=
    {
      parameters :=
        []

      body :=
        [
          .send
            (.knownRebec
              hubKnownRebecName)
            earlyMessageName
            [.intLiteral 1]
            ⟨0⟩
        ]
    }

  messageServers :=
    []

/--
The sender declared **second**, prioritised **first** (`some 1`).

A structure update on `earlySenderClass` differing in name, message and payload only, so
the emitted difference between the two senders cannot be explained by anything else.
-/
private def lateSenderClass :
    DTR.GeneralReactiveClass :=
  {
    earlySenderClass with

    name :=
      lateSenderClassName

    constructor :=
      {
        parameters :=
          []

        body :=
          [
            .send
              (.knownRebec
                hubKnownRebecName)
              lateMessageName
              [.intLiteral 2]
              ⟨0⟩
          ]
      }
  }

/--
The sender declared first, priority `some 2`.
-/
private def earlySenderActor :
    DTR.GeneralActorInstance where

  name :=
    earlySenderInstanceName

  className :=
    earlySenderClassName

  bindings :=
    [(hubKnownRebecName, witnessHubInstanceName)]

  arguments :=
    []

  priority :=
    some 2

/--
The sender declared second, priority `some 1` — the level-1 derangement.
-/
private def lateSenderActor :
    DTR.GeneralActorInstance :=
  {
    earlySenderActor with

    name :=
      lateSenderInstanceName

    className :=
      lateSenderClassName

    priority :=
      some 1
  }

/--
The receiver. No priority annotation: it sends nothing, a non-sender's priority is inert,
and leaving it absent keeps the two annotated priorities exactly the two the derangement
is about.
-/
private def witnessHubActor :
    DTR.GeneralActorInstance where

  name :=
    witnessHubInstanceName

  className :=
    witnessHubClassName

  bindings :=
    []

  arguments :=
    []

/--
The witness model.

Class order fixes reactor order; instance order is declared `early, late, hub` and
prioritised `late, early, (hub absent)`; the hub's servers are declared `early, late` and
prioritised `late, early`. Every order that a sort controls disagrees with every order
that declaration controls, which is what makes this a witness rather than a fixture.
-/
private def priorityWitnessModel :
    DTR.GeneralModel where

  classes :=
    [
      earlySenderClass,
      lateSenderClass,
      witnessHubClass
    ]

  instances :=
    [
      earlySenderActor,
      lateSenderActor,
      witnessHubActor
    ]

/--
Translate the witness model and print it, in one `Except`.

The same shared-text discipline as `widenedProgramText` and `routedProgramText`: the
bytes the target gate hands to `lfc` come from here and from nowhere else, so the
witness cannot compile something no other path ever saw.
-/
private def priorityWitnessProgramText :
    Except String String := do

  let program ←
    Translation.compileGeneralModel
      priorityWitnessModel

  LF.CppPrinter.renderGeneralProgram
    program

/--
Print the priority-witness program, for the target gate to hand to `lfc`.

The only emitted program in this file whose *run* is asserted on, not just its exit
code: the gate captures stdout and requires `LATE` to precede `EARLY`, against a
declaration order that says the opposite.
-/
def emitPriorityWitnessProgram :
    IO UInt32 :=
  match priorityWitnessProgramText with

  | .ok programText => do
      IO.print programText

      pure 0

  | .error reason => do
      IO.eprintln
        ("the translation or the printer refused the priority-witness model: " ++
          reason)

      pure 1

/-!
### The stage I0 conditional witness: a generated `if` through real `lfc`

Stage H taught the printer to emit a conditional and pinned the text by `rfl` in
`Relico/Tests/GeneralConditional.lean`. What no gate did was hand that text to the target
compiler: every program this file emitted before this one is branch-free, so a green
`GENERAL_LF_TARGET_OK` said nothing about whether `lfc` accepts
`if (…) { … } else { … }` inside a reaction body. `docs/STAGE_I_FINDINGS.md`'s F90 records
the gap and the measurement that established it, `grep -c 'if ('` over the gate's own log
returning zero. This model closes it.

**Minimal on purpose, and the minimality is the argument.** One class, one instance, one
state variable, no known rebecs, no ports and no connections. The only construct that
distinguishes it from a program the gate already compiles is the conditional, so an `lfc`
complaint here can only be about the conditional. Both branches are non-empty, because an
empty `else` prints `{}` and would leave the interesting half of the emitted text
unexercised.

It terminates for the same reason the sibling models do: the constructor self-sends `flip`
once, `flip` assigns to a state variable and sends nothing, so the event queue drains.
-/

private def toggleClassName :
    ClassName :=
  ⟨"Toggle"⟩

private def toggleInstanceName :
    ActorName :=
  ⟨"toggle0"⟩

private def flipMessageName :
    MsgName :=
  ⟨"flip"⟩

private def onStateName :
    VarName :=
  ⟨"on"⟩

private def toggleConstructor :
    DTR.GeneralConstructor where

  parameters :=
    []

  body :=
    [
      .assign
        onStateName
        (.boolLiteral false),
      .send
        .selfTarget
        flipMessageName
        []
        { value := 1 }
    ]

private def flipMessageServer :
    DTR.GeneralMessageServer where

  name :=
    flipMessageName

  parameters :=
    []

  body :=
    [
      .ifThenElse
        (.stateVar onStateName)
        [
          .assign
            onStateName
            (.boolLiteral false)
        ]
        [
          .assign
            onStateName
            (.boolLiteral true)
        ]
    ]

private def toggleClass :
    DTR.GeneralReactiveClass where

  name :=
    toggleClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name :=
          onStateName

        declaredType :=
          .boolean
      }
    ]

  constructor :=
    toggleConstructor

  messageServers :=
    [flipMessageServer]

private def toggleActor :
    DTR.GeneralActorInstance where

  name :=
    toggleInstanceName

  className :=
    toggleClassName

  bindings :=
    []

  arguments :=
    []

/--
One class, one instance, one conditional, nothing else.
-/
private def conditionalWitnessModel :
    DTR.GeneralModel where

  classes :=
    [toggleClass]

  instances :=
    [toggleActor]

/--
Translate the conditional witness and print it, in one `Except`.
-/
private def conditionalWitnessProgramText :
    Except String String := do

  let program ←
    Translation.compileGeneralModel
      conditionalWitnessModel

  LF.CppPrinter.renderGeneralProgram
    program

/--
Emit the conditional witness for `frontend/check-general-lf-target.sh`.
-/
def emitConditionalWitnessProgram :
    IO UInt32 :=
  match conditionalWitnessProgramText with

  | .ok programText => do
      IO.print programText

      pure 0

  | .error reason => do
      IO.eprintln
        ("the translation or the printer refused the conditional witness model: " ++
          reason)

      pure 1

end GeneralLfPrinterTests
end Relico

def main
    (arguments : List String) :
    IO UInt32 :=
  -- The emit selectors carry no leading dashes on purpose. This module runs
  -- under `lake env lean --run`, which reads its own flags before handing the
  -- rest to `main`, so a `--`-prefixed argument would be ambiguous with the
  -- driver's own options. The sibling runner already proves that a bare
  -- positional argument arrives intact, since that is how it receives its
  -- fixture directory.
  match arguments with

  | [] =>
      Relico.GeneralLfPrinterTests.runGeneralLfPrinterTests

  | ["emit-program"] =>
      Relico.GeneralLfPrinterTests.emitBaseProgram

  | ["emit-widened"] =>
      Relico.GeneralLfPrinterTests.emitWidenedProgram

  | ["emit-routed"] =>
      Relico.GeneralLfPrinterTests.emitRoutedProgram

  | ["emit-repeated"] =>
      Relico.GeneralLfPrinterTests.emitRepeatedSelfSendProgram

  | ["emit-priority-witness"] =>
      Relico.GeneralLfPrinterTests.emitPriorityWitnessProgram

  | ["emit-conditional"] =>
      Relico.GeneralLfPrinterTests.emitConditionalWitnessProgram

  | _ => do
      IO.eprintln
        "usage: GeneralLfPrinterTestMain [emit-program|emit-widened|emit-routed|emit-repeated|emit-priority-witness|emit-conditional]"

      pure 2
