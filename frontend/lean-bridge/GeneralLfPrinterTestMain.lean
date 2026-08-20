import Relico.LF.GeneralWellFormed
import Relico.LF.GeneralCppPrinter
import Relico.Translation.GeneralBasic

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

  declaredType :=
    .int

/--
An integer output port.
-/
private def outPortDecl :
    LF.GeneralPortDecl where

  name :=
    outPort

  declaredType :=
    .int

/--
The sender's own input port, used by the unconnected-port and self-connection cases.
-/
private def backPortDecl :
    LF.GeneralPortDecl where

  name :=
    backPort

  declaredType :=
    .int

/--
A boolean input port.

Declared for one assertion and used in no program. Stage D emits no ports at all,
so a boolean port cannot reach the `lfc` gate through the translation, and the
alternative to asserting it on the port renderer directly is not asserting it —
which would leave `renderGeneralType`'s boolean arm exercised in two of its three
positions and claimed in the third.
-/
private def flagInPortDecl :
    LF.GeneralPortDecl where

  name :=
    ⟨"flagIn"⟩

  declaredType :=
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

  declaredType :=
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
        (.intLiteral 1)
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

The one refusal left in the parameter reader, and unreachable in stage D: a
`GeneralPortDecl` carries a single declared type and so delivers one value.
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
        (.parameterVar payloadParameter)
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
The same model with one message server replaced by an external send.

Written as a structure update so that the only difference from `widenedModel` is
the construct under test. A second hand-written class could differ in some other
way and the refusal would still be reported, which would make this assertion pass
for the wrong reason.
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
The refusal a known-rebec send earns in stage D.

Asserted on its exact text, not merely on being an error. The message names the
stage that will implement the construct, and a diagnostic that decays into a bare
`.error` later would still be an error and would no longer tell a reader where the
work went.
-/
private def externalSendDiagnostic :
    String :=
  "send to known rebec `peer`.`ping` is an external send; " ++
    "stage D translates self-sends only, and external sends are stage E"

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

  -- Derived from the reactors, never stored, so a struct the actions do not need is
  -- not expressible. The declaration is reached through `generalProgramStructDecls`
  -- rather than asserted on `generalActionStructDecl?` directly, which keeps the
  -- assertion on the composition the program actually calls.
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
          (.intLiteral 0),

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
          (.intLiteral 0),

        .setPort
          outPort
          (.intLiteral 1)
      ])

  expectString
    "VOID_PAYLOAD_SCHEDULE"
    "deliver.schedule(0ms);"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
      (.schedule
        deliverAction
        []
        ⟨0⟩))

  expectString
    "SINGLE_VALUE_PAYLOAD_SCHEDULE"
    "deliver.schedule(1, 0ms);"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
      (.schedule
        deliverAction
        [.intLiteral 1]
        ⟨0⟩))

  -- The struct is *constructed* here and *declared* by the preamble above and *named*
  -- by the action declaration above that, all three through
  -- `generalPayloadStructName`. Three assertions on one function, which is why the
  -- reactor name has to be threaded this far.
  expectString
    "MULTI_VALUE_PAYLOAD_SCHEDULE"
    "deliver.schedule(Receiver_deliver_Args{1, true}, 0ms);"
    (LF.CppPrinter.renderGeneralStmt
      receiverReactorName
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

  -- The one refusal left in the parameter reader, and a recorded disagreement with
  -- `docs/STAGE_D_DESIGN.md` §6, which said all three go. A `GeneralPortDecl` carries
  -- one declared type and so delivers one value: there is no struct to name and no
  -- second value to bind. Finding F30.
  expectRefused
    "MULTI_PARAMETER_PORT_REFUSED"
    ("reaction `receive_reaction` for input port `in` declares more than one parameter; " ++
      "a port declares one type and so carries one value, " ++
      "and unlike a logical action it has no parameter list to destructure")
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

  expectBool
    "SELF_SEND_ONLY_ACCEPTS_WIDENED_MODEL"
    true
    (Translation.generalModelSelfSendOnly
      widenedModel)

  expectBool
    "SELF_SEND_ONLY_REJECTS_EXTERNAL_SEND"
    false
    (Translation.generalModelSelfSendOnly
      externalSendModel)

  -- The refusal is asserted on its exact text at both levels. The statement level is
  -- where it is produced and the model level is where a caller meets it, and
  -- `compileGeneralModel_ok_iff_selfSendOnly` is what makes the second follow from the
  -- first — a theorem about a diagnostic nobody pinned would be a theorem about a
  -- string that could quietly become `.error ""`.
  expectRefusedTerm
    "EXTERNAL_SEND_STATEMENT_REFUSED"
    externalSendDiagnostic
    (Translation.compileGeneralStmt
      (.send
        (.knownRebec peerKnownRebecName)
        pingMessageName
        []
        ⟨0⟩))

  expectRefusedTerm
    "EXTERNAL_SEND_MODEL_REFUSED"
    externalSendDiagnostic
    (Translation.compileGeneralModel
      externalSendModel)

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
Run every assertion: 34 printing, then 10 well-formedness, then 12 translation, 56 in all.

The count is stated here because `frontend/check-general-lean.sh` compares the
number of `PASS_` lines against a literal. There are no fixtures to count, so a
literal is the only way the gate can notice an assertion that stopped running —
which is the failure a marker check alone cannot see.

Stage C ran 25 of these, in two blocks. The third block is new and is the one that
mentions `Relico.Translation`: everything above it would still pass if
`compileGeneralModel` did not exist.
-/
def runGeneralLfPrinterTests :
    IO UInt32 := do

  try
    printerAssertions

    wellFormednessAssertions

    translationAssertions

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

  | _ => do
      IO.eprintln
        "usage: GeneralLfPrinterTestMain [emit-program|emit-widened]"

      pure 2
