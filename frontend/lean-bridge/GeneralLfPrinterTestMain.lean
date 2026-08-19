import Relico.LF.GeneralWellFormed
import Relico.LF.GeneralCppPrinter

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Relico
namespace GeneralLfPrinterTests

/-!
# Executable assertions for the general generated-LF family

Every value here is built by hand in Lean. Unlike `GeneralFrontendTestMain`, this
runner reads no fixtures and takes no arguments: there is no exporter and no
decoder for this family yet, so there is nothing on disk to read. What is being
pinned is the exact text `renderGeneralProgram` produces and the exact accept or
reject verdict `wellFormed` returns.

Two departures from the stage design are recorded rather than buried.

**This one file covers both printing and well-formedness**, though §4 names it a
printer test. Both are pure total functions over hand-built values, both need the
same handful of reactors to exercise, and a second main would double the gate's
cost to assert nothing the first could not. The alternative — leaving
`GeneralWellFormed.lean` with no executable assertion at all while its two
theorems only ever range over an arbitrary program — is worse.

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
a `String`, and the whole point of these three assertions is that the inherited
payload limits are refused in the same words the sibling printers use, so that a
reader of the generated-artifact log sees one vocabulary rather than four.
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
    (inputPortList : List PortName) :
    LF.GeneralReactor where

  name :=
    senderReactorName

  inputPorts :=
    inputPortList

  outputPorts :=
    [outPort]

  stateVariables :=
    [
      {
        name :=
          senderStateName

        initialValue :=
          0
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
program `lfc` rejects is the `outputPorts.contains` check this pins.
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
    (inputPortList : List PortName)
    (messageReactionList :
      List LF.GeneralReaction) :
    LF.GeneralReactor where

  name :=
    receiverReactorName

  inputPorts :=
    inputPortList

  outputPorts :=
    []

  stateVariables :=
    [
      {
        name :=
          receiverStateName

        initialValue :=
          0
      }
    ]

  logicalActions :=
    [
      {
        name :=
          deliverAction

        parameters :=
          [arrivedParameter]
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
    [backPort]

private def receiverReactor :
    LF.GeneralReactor :=
  receiverReactorWith
    [inPort]
    [
      receiveReaction,
      deliverReaction
    ]

private def senderInstance :
    LF.ReactorInstance where

  name :=
    senderInstanceName

  reactorName :=
    senderReactorName

private def receiverInstance :
    LF.ReactorInstance where

  name :=
    receiverInstanceName

  reactorName :=
    receiverReactorName

/--
A second instance of the *same* receiver reactor.

Two instances sharing one reactor declaration is the structural point of the
family: Table III maps a reactive class to a reactor, so a per-instance reactor
would make the paper's own mapping unrepresentable.
-/
private def secondReceiverInstance :
    LF.ReactorInstance where

  name :=
    secondReceiverInstanceName

  reactorName :=
    receiverReactorName

/--
An instance of a reactor nobody declares.
-/
private def ghostInstance :
    LF.ReactorInstance where

  name :=
    ⟨"ghost"⟩

  reactorName :=
    ⟨"Missing"⟩

/--
A port name colliding with the receiver's state variable.

Spelled out here rather than reusing `receiverStateName`, because the two are
different *types* — `PortName` and `VarName` — and it is exactly that type-level
separation which makes the collision invisible to anything but the union check.
-/
private def collidingPort :
    PortName :=
  ⟨"y"⟩

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
      List LF.ReactorInstance)
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
    List LF.ReactorInstance :=
  [
    senderInstance,
    receiverInstance
  ]

/--
The program every printer assertion renders and the accept assertion accepts.
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
        [inPort]
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
          inPort,
          collidingPort
        ]
        [
          receiveReaction,
          deliverReaction
        ]
    ]
    baseInstances
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
reactor whose connections carry `after`.
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
      inPort)

  expectString
    "OUTPUT_PORT_DECL"
    "  output out: int"
    (LF.CppPrinter.renderOutputPortDecl
      outPort)

  expectString
    "PORT_DECLS_INPUTS_BEFORE_OUTPUTS"
    "  input back: int\n  output out: int"
    (LF.CppPrinter.renderGeneralPortDecls
      senderReactorWithInputPort)

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
    "CONNECTION_CARRIES_AFTER"
    "  sender0.out -> receiver0.in after 0 msec"
    (LF.CppPrinter.renderGeneralConnection
      senderToReceiver)

  expectString
    "INSTANCE_IS_ARGUMENT_FREE"
    "  sender0 = new Sender()"
    (LF.CppPrinter.renderGeneralInstance
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
      receiveReaction)

  expectRendered
    "PROGRAM"
    expectedProgramText
    (LF.CppPrinter.renderGeneralProgram
      baseProgram)

  expectRefused
    "MULTI_VALUE_PAYLOAD_REFUSED"
    ("logical action `deliver` has more than one payload value; " ++
      "the current C++ printer foundation supports at most one integer payload")
    (LF.CppPrinter.renderGeneralStmt
      (.schedule
        deliverAction
        [
          .intLiteral 1,
          .intLiteral 2
        ]
        ⟨0⟩))

  expectRefused
    "MULTI_PARAMETER_ACTION_REFUSED"
    ("logical action `deliver` declares more than one parameter; " ++
      "the current C++ printer foundation supports at most one integer payload")
    (LF.CppPrinter.renderGeneralActionDecl
      {
        name :=
          deliverAction

        parameters :=
          [
            arrivedParameter,
            payloadParameter
          ]
      })

  expectRefused
    "STARTUP_WITH_PARAMETERS_REFUSED"
    "startup reaction `sender_startup` must not declare payload parameters"
    (LF.CppPrinter.renderGeneralParameterRead
      {
        name :=
          senderStartupReactionName

        trigger :=
          .startup

        parameters :=
          [arrivedParameter]

        body :=
          []
      })

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

  expectIllFormed
    "REJECT_DANGLING_INSTANCE"
    programWithDanglingInstance

/--
Run every assertion: 16 printing, then 9 well-formedness, 25 in all.

The count is stated here because `frontend/check-general-lean.sh` compares the
number of `PASS_` lines against a literal. There are no fixtures to count, so a
literal is the only way the gate can notice an assertion that stopped running —
which is the failure a marker check alone cannot see.
-/
def runGeneralLfPrinterTests :
    IO UInt32 := do

  try
    printerAssertions

    wellFormednessAssertions

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

end GeneralLfPrinterTests
end Relico

def main
    (arguments : List String) :
    IO UInt32 :=
  -- The emit selector carries no leading dashes on purpose. This module runs
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

  | _ => do
      IO.eprintln
        "usage: GeneralLfPrinterTestMain [emit-program]"

      pure 2
