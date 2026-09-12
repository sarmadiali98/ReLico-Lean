import Relico.Translation.GeneralBasic
import Relico.Translation.GeneralRouting
import Relico.DTR.GeneralWellFormed

set_option autoImplicit false

/-!
# Fan-in pins: three senders, one server, per-site ports

Fan-in is the topology the fragment's routing supports through per-site input ports: one
message server may be reached by several sender instances, and the receiving reactor carries
one input port per route so that two deliveries never collapse onto one port. That shape was
measured by the `general--fan-in--positive` fixture's pipeline run; this module is its pin
instrument, holding the three facts the shape theorems cannot see because they are
quantified over arbitrary route lists:

1. the model's connections include exactly three whose target is the gateway, and their
   target ports are pairwise distinct, which is the per-site property;
2. the priority-ordered instance list realizes the senders' declared priorities 1, 2, 3
   ahead of the unprioritized gateway, which is the level-1 ordering the deterministic
   delivery claim rests on;
3. the whole model compiles with the program guard green, which includes
   `targetEndpointsUnique` over exactly this many-to-one topology.

The model mirrors the fixture: three `Sensor` instances with priorities 1, 2, 3 and seeds
10, 20, 30, one `Gateway` with a `collect` server, and a gateway-driven request/collect
cycle. The pacing is scaffolding for the mandatory RMC stage, as the fixture README records;
the pins are about the topology, not the pacing.

Every pin is `rfl`, for the reducibility reason the sibling modules record. The fan-in
model is the largest pin-model in this suite, and evaluating the five well-formedness
clauses and the whole compilation needs more than the default kernel heartbeats, so the
budget is raised file-wide below; the pins stay `rfl` and only the budget moves.
-/

set_option maxHeartbeats 2000000

namespace Relico
namespace Tests

/-! ## The model -/

def faninSensorClassName : ClassName :=
  ClassName.mk "Sensor"

def faninGatewayClassName : ClassName :=
  ClassName.mk "Gateway"

def faninSensorFirstName : ActorName :=
  ActorName.mk "sensorFirst"

def faninSensorSecondName : ActorName :=
  ActorName.mk "sensorSecond"

def faninSensorThirdName : ActorName :=
  ActorName.mk "sensorThird"

def faninGatewayName : ActorName :=
  ActorName.mk "gateway0"

def faninGatewayKnownRebec : KnownRebecName :=
  KnownRebecName.mk "gateway"

def faninReadingName : VarName :=
  VarName.mk "reading"

def faninLatestName : VarName :=
  VarName.mk "latest"

def faninResolvedName : VarName :=
  VarName.mk "resolved"

def faninRoundName : VarName :=
  VarName.mk "round"

def faninSeedName : VarName :=
  VarName.mk "seed"

def faninRequestRoundName : VarName :=
  VarName.mk "round"

def faninCollectValueName : VarName :=
  VarName.mk "value"

def faninRequestName : MsgName :=
  MsgName.mk "request"

def faninCollectName : MsgName :=
  MsgName.mk "collect"

def faninPollName : MsgName :=
  MsgName.mk "poll"

def faninSensorKnownRebecs :
    List DTR.GeneralKnownRebecDecl :=
  [
    {
      name := faninGatewayKnownRebec
      className := faninGatewayClassName
    }
  ]

def faninSensorClass : DTR.GeneralReactiveClass where
  name :=
    faninSensorClassName

  knownRebecs :=
    faninSensorKnownRebecs

  stateVariables :=
    [
      {
        name := faninReadingName
        declaredType := .int
      }
    ]

  constructor :=
    {
      parameters :=
        [
          {
            name := faninSeedName
            declaredType := .int
          }
        ]
      body :=
        [
          DTR.GeneralStmt.assign
            faninReadingName
            (DTR.GeneralExpr.parameterVar
              faninSeedName)
        ]
    }

  messageServers :=
    [
      {
        name := faninRequestName
        parameters :=
          [
            {
              name := faninRequestRoundName
              declaredType := .int
            }
          ]
        body :=
          [
            DTR.GeneralStmt.send
              (DTR.GeneralSendTarget.knownRebec
                faninGatewayKnownRebec)
              faninCollectName
              [DTR.GeneralExpr.stateVar
                faninReadingName]
              { value := 0 }
          ]
      }
    ]

def faninGatewayKnownRebecs :
    List DTR.GeneralKnownRebecDecl :=
  [
    {
      name := KnownRebecName.mk "sensorFirst"
      className := faninSensorClassName
    },
    {
      name := KnownRebecName.mk "sensorSecond"
      className := faninSensorClassName
    },
    {
      name := KnownRebecName.mk "sensorThird"
      className := faninSensorClassName
    }
  ]

def faninGatewayClass : DTR.GeneralReactiveClass where
  name :=
    faninGatewayClassName

  knownRebecs :=
    faninGatewayKnownRebecs

  stateVariables :=
    [
      {
        name := faninLatestName
        declaredType := .int
      },
      {
        name := faninResolvedName
        declaredType := .int
      },
      {
        name := faninRoundName
        declaredType := .int
      }
    ]

  constructor :=
    {
      parameters := []
      body :=
        [
          DTR.GeneralStmt.assign
            faninLatestName
            (DTR.GeneralExpr.intLiteral 0),
          DTR.GeneralStmt.assign
            faninResolvedName
            (DTR.GeneralExpr.intLiteral 0),
          DTR.GeneralStmt.assign
            faninRoundName
            (DTR.GeneralExpr.intLiteral 0),
          DTR.GeneralStmt.send
            DTR.GeneralSendTarget.selfTarget
            faninPollName
            []
            { value := 1 }
        ]
    }

  messageServers :=
    [
      {
        name := faninPollName
        parameters := []
        body :=
          [
            DTR.GeneralStmt.assign
              faninResolvedName
              (DTR.GeneralExpr.intLiteral 0),
            DTR.GeneralStmt.ifThenElse
              (DTR.GeneralExpr.binary
                .eq
                (DTR.GeneralExpr.stateVar
                  faninRoundName)
                (DTR.GeneralExpr.intLiteral 0))
              [
                DTR.GeneralStmt.assign
                  faninRoundName
                  (DTR.GeneralExpr.intLiteral 1)
              ]
              [
                DTR.GeneralStmt.assign
                  faninRoundName
                  (DTR.GeneralExpr.intLiteral 0)
              ],
            DTR.GeneralStmt.send
              (DTR.GeneralSendTarget.knownRebec
                (KnownRebecName.mk "sensorFirst"))
              faninRequestName
              [DTR.GeneralExpr.stateVar
                faninRoundName]
              { value := 0 },
            DTR.GeneralStmt.send
              (DTR.GeneralSendTarget.knownRebec
                (KnownRebecName.mk "sensorSecond"))
              faninRequestName
              [DTR.GeneralExpr.stateVar
                faninRoundName]
              { value := 0 },
            DTR.GeneralStmt.send
              (DTR.GeneralSendTarget.knownRebec
                (KnownRebecName.mk "sensorThird"))
              faninRequestName
              [DTR.GeneralExpr.stateVar
                faninRoundName]
              { value := 0 }
          ]
      },
      {
        name := faninCollectName
        parameters :=
          [
            {
              name := faninCollectValueName
              declaredType := .int
            }
          ]
        body :=
          [
            DTR.GeneralStmt.assign
              faninLatestName
              (DTR.GeneralExpr.parameterVar
                faninCollectValueName),
            DTR.GeneralStmt.assign
              faninResolvedName
              (DTR.GeneralExpr.binary
                .add
                (DTR.GeneralExpr.stateVar
                  faninResolvedName)
                (DTR.GeneralExpr.intLiteral 1)),
            DTR.GeneralStmt.ifThenElse
              (DTR.GeneralExpr.binary
                .eq
                (DTR.GeneralExpr.stateVar
                  faninResolvedName)
                (DTR.GeneralExpr.intLiteral 3))
              [
                DTR.GeneralStmt.send
                  DTR.GeneralSendTarget.selfTarget
                  faninPollName
                  []
                  { value := 1 }
              ]
              []
          ]
      }
    ]

def faninSensorFirst : DTR.GeneralActorInstance where
  name :=
    faninSensorFirstName

  className :=
    faninSensorClassName

  bindings :=
    [
      (faninGatewayKnownRebec, faninGatewayName)
    ]

  arguments :=
    [DTR.GeneralValue.int 10]

  priority :=
    some 1

def faninSensorSecond : DTR.GeneralActorInstance where
  name :=
    faninSensorSecondName

  className :=
    faninSensorClassName

  bindings :=
    [
      (faninGatewayKnownRebec, faninGatewayName)
    ]

  arguments :=
    [DTR.GeneralValue.int 20]

  priority :=
    some 2

def faninSensorThird : DTR.GeneralActorInstance where
  name :=
    faninSensorThirdName

  className :=
    faninSensorClassName

  bindings :=
    [
      (faninGatewayKnownRebec, faninGatewayName)
    ]

  arguments :=
    [DTR.GeneralValue.int 30]

  priority :=
    some 3

def faninGateway : DTR.GeneralActorInstance where
  name :=
    faninGatewayName

  className :=
    faninGatewayClassName

  bindings :=
    [
      (KnownRebecName.mk "sensorFirst",
        faninSensorFirstName),
      (KnownRebecName.mk "sensorSecond",
        faninSensorSecondName),
      (KnownRebecName.mk "sensorThird",
        faninSensorThirdName)
    ]

  arguments :=
    []

def faninModel : DTR.GeneralModel where
  classes :=
    [faninSensorClass, faninGatewayClass]

  instances :=
    [
      faninSensorFirst,
      faninSensorSecond,
      faninSensorThird,
      faninGateway
    ]

/-! ## Pin 0: the fragment accepts the model -/

/- Test 0: the model is well-formed, circular known-rebec references included. The pingpong
   case study is the registered precedent for the topology; this `rfl` evaluates the five
   clauses, `bindingsMatchDeclarations` over both directions among them. -/
example :
    faninModel.wellFormed =
      true := by
  rfl

/-! ## Pin 1: the model compiles, guard included -/

/- Test 1: the whole model compiles. `guardGeneralProgram`'s `targetEndpointsUnique` runs over
   exactly this many-to-one topology, so its green verdict here is the checked, not earned,
   half of the fan-in claim. -/
example :
    (Translation.compileGeneralModel
      faninModel).isOk =
      true := by
  rfl

def faninCompiledProgram : LF.GeneralProgram :=
  match
      Translation.compileGeneralModel
        faninModel with
  | .ok program =>
      program
  | .error _ =>
      default

/-! ## Pin 2: three connections reach the gateway, at three distinct per-site ports -/

/- Test 2: exactly three connections target the gateway. That is the fan-in count: every
   sender's route into the shared server survives translation. A translator that dropped a
   route fails here. -/
example :
    faninCompiledProgram.connections.countP
        (fun connection =>
          connection.targetInstance ==
            faninGatewayName) =
      3 := by
  rfl

/- Test 3: the three gateway-targeted connections land on pairwise distinct input ports.
   That is the per-site property: several senders, one server, one input port per route, no
   collapse. A translator that emitted one shared port fails here, and so does the guard's
   `targetEndpointsUnique` clause, which is why pin 1 and this pin hold together. -/
example :
    (List.map
        (fun connection =>
          connection.targetPort)
        (faninCompiledProgram.connections.filter
          (fun connection =>
            connection.targetInstance ==
              faninGatewayName))).eraseDups.length =
      3 := by
  rfl

/-! ## Pin 3: the senders' priorities realize the delivery order -/

/- Test 4: the priority-ordered instance list places the three sensors ahead of the
   unprioritized gateway, in priority order 1, 2, 3. This is the level-1 ordering the
   deterministic same-tag delivery claim rests on; a normalization that lost a priority or
   reordered equals fails here. -/
example :
    (Translation.priorityOrderedInstances
      faninModel).map
      (fun row =>
        row.name) =
      [
        faninSensorFirstName,
        faninSensorSecondName,
        faninSensorThirdName,
        faninGatewayName
      ] := by
  rfl

/-! ## Pin 4: the gateway reactor carries the per-site input ports -/

/- Test 5: the compiled gateway reactor declares three input ports, one per collect route.
   Together with pin 2's three distinct connection targets this is the full port shape:
   the ports exist on the reactor, and the connections land on them one per site. -/
example :
    (
      match
          faninCompiledProgram.reactors.filter
            (fun reactor =>
              reactor.name ==
                ReactorName.mk "Gateway") with
      | [gateway] =>
          gateway.inputPorts.length
      | _ =>
          4294967295
    ) =
      3 := by
  rfl

end Tests
end Relico
