import Relico.Correctness.GeneralCorrespondence
import Relico.DTR.GeneralInitialization
import Relico.LF.GeneralInitialization

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GeneralInitialization

/-!
# Compile-time pins for the two general initializers and the initial correspondence

Row 11's regression half, over `Relico/DTR/GeneralInitialization.lean`,
`Relico/LF/GeneralInitialization.lean` and the unconditional `generalCorrespondence_initial` in
`Relico/Correctness/GeneralCorrespondence.lean`.

The standard is F60's: a pin earns its place only if some specific wrong implementation fails it. Every
fixture below is hand-written, and each targets one decision the theorem's statement cannot see:

* **Constructor entry, not continuation-free lift.** The source actor's `activeBody` is pinned to the
  constructor's body (test 1) and the target reactor's to the compiled startup reaction's body (test 6).
  An initializer built as `ofConfiguration` — empty continuations everywhere — passes neither, and that
  is the F85 discrepancy made checkable: nothing else in the tree can fail this way, because
  `DTR.GeneralStep.take` cannot install a constructor body and `LF.GeneralEventKind` has no `startup`
  arm.

* **Parameters are bound into the initial valuation, not stored elsewhere.** The class's constructor
  takes one parameter, the instance supplies one argument, and test 2 pins the lookup. An initializer
  that dropped the bind (or stored arguments in a second environment this family does not have) leaves
  the lookup at `none` and fails.

* **State-variable defaults come from the declaration list.** Test 3 pins the default under its own
  name, at the value `DTR.GeneralType.initialValue` gives, so an initializer that started every actor
  at an empty valuation — the `idleDefault` shape — fails on two counts, this one and test 2.

* **Time and queue start at zero.** Test 5 pins `now = 0`, `currentTag = ⟨0, 0⟩` and `pending = []`
  against literals.

* **The correspondence itself.** Test 7 is `generalCorrespondence_initial` applied to a model that
  compiles — the one place an end-to-end regression can catch a constructor-entry theorem that stopped
  applying to real compilations while still elaborating against fixtures built by the initializers
  themselves. The compilation is `decide`d, and the theorem's conclusion is consumed, not restated.

What is deliberately not pinned: valuation agreement at a name neither side binds (it is
`generalValuationAgrees_empty`, already pinned by its own existence proof), and the idle-default
branches of the two initializers (unreachable for compiled programs, and a pin there would hold under
any resolution order).
-/

/-! ## A one-class, one-instance model whose constructor binds a parameter -/

def pinClassName : ClassName :=
  ClassName.mk "Pin"

def pinActorName : ActorName :=
  ActorName.mk "pin0"

def pinStateName : VarName :=
  VarName.mk "count"

def pinParameterName : VarName :=
  VarName.mk "start"

def pinClass : DTR.GeneralReactiveClass where
  name :=
    pinClassName

  knownRebecs :=
    []

  stateVariables :=
    [
      {
        name := pinStateName
        declaredType := .int
      }
    ]

  constructor :=
    {
      parameters :=
        [
          {
            name := pinParameterName
            declaredType := .int
          }
        ]

      body :=
        [
          DTR.GeneralStmt.assign
            pinStateName
            (DTR.GeneralExpr.parameterVar
              pinParameterName)
        ]
    }

  messageServers :=
    []

def pinActor : DTR.GeneralActorInstance where
  name :=
    pinActorName

  className :=
    pinClassName

  bindings :=
    []

  arguments :=
    [
      .int 7
    ]

def pinModel : DTR.GeneralModel where
  classes :=
    [pinClass]

  instances :=
    [pinActor]

/-! ## The source initializer -/

/- Test 1: the source actor store is exactly one constructor-entry actor. -/
example :
    (DTR.GeneralModel.initialState
        pinModel).actors =
      [
        (
          pinActorName,
          DTR.GeneralModel.initialActorRuntime
            pinClass
            pinActor
        )
      ] := by
  rfl

/- Test 2: the constructor argument is bound into the initial valuation. -/
example :
    (match
        Store.lookup
          (DTR.GeneralModel.initialState
            pinModel).actors
          pinActorName with

    | some runtime =>
        Store.lookup
          runtime.state.valuation
          pinParameterName

    | none =>
        none) =
      some
        (DTR.GeneralValue.int 7) := by
  rfl

/- Test 3: the state variable's default is the declaration's, not a zero-store. -/
example :
    (match
        Store.lookup
          (DTR.GeneralModel.initialState
            pinModel).actors
          pinActorName with

    | some runtime =>
        Store.lookup
          runtime.state.valuation
          pinStateName

    | none =>
        none) =
      some
        (DTR.GeneralValue.int 0) := by
  rfl

/- Test 4: the source active body is the constructor body. -/
example :
    (match
        Store.lookup
          (DTR.GeneralModel.initialState
            pinModel).actors
          pinActorName with

    | some runtime =>
        some runtime.activeBody

    | none =>
        none) =
      some
        pinClass.constructor.body := by
  rfl

/-! ## The target initializer -/

def pinProgram :
    LF.GeneralProgram :=
  match
    Translation.compileGeneralModel
      pinModel with

  | .ok program =>
      program

  | .error _ =>
      Inhabited.default

/- Test 5: logical time, tag and queue start at zero. -/
example :
    (LF.GeneralProgram.initialState
        pinProgram).now =
      0 ∧
      (LF.GeneralProgram.initialState
        pinProgram).currentTag =
        {
          time := 0
          microstep := 0
        } ∧
      (LF.GeneralProgram.initialState
        pinProgram).pending =
        [] := by
  refine ⟨rfl, rfl, rfl⟩

/- Test 6: the target reactor's active body is the compiled startup reaction's body,
   and the compiled argument is bound into the initial valuation.

   The body is pinned against the literal compiled statement — an `assign` of the
   compiled parameter variable — rather than against `pinReactor.startupReaction.body`,
   so the pair catches a `pinReactor` that quietly fell to its default arm as well as
   an initializer that installs no body. -/
example :
    (match
        Store.lookup
          (LF.GeneralProgram.initialState
            pinProgram).reactors
          pinActorName with

    | some runtime =>
        some runtime.activeBody

    | none =>
        none) =
      some
        [
          LF.GeneralStmt.assign
            pinStateName
            (LF.GeneralExpr.parameterVar
              pinParameterName)
        ] ∧
      (match
          Store.lookup
            (LF.GeneralProgram.initialState
              pinProgram).reactors
            pinActorName with

      | some runtime =>
          Store.lookup
            runtime.valuation
            pinParameterName

      | none =>
          none) =
        some
          (LF.GeneralValue.int 7) := by
  refine ⟨rfl, rfl⟩

/-! ## The correspondence -/

/- Test 7: the compilation succeeds, and the unconditional theorem applies to it.

   The success is pinned as its own equation on `pinProgram` — the same `def` the other
   target pins build from — and the existential then consumes both it and the theorem,
   so the theorem's conclusion is used, not restated. -/
theorem pinModel_compiles :
    Translation.compileGeneralModel
        pinModel =
      .ok pinProgram := by
  rfl

example :
    ∃ program,
      Translation.compileGeneralModel
          pinModel =
        .ok program ∧
      Correctness.GeneralStateCorrespondence
        (DTR.GeneralModel.initialState
          pinModel)
        (LF.GeneralProgram.initialState
          program) := by
  exact
    ⟨
      pinProgram,
      pinModel_compiles,
      Correctness.generalCorrespondence_initial
        pinModel
        pinProgram
        pinModel_compiles
    ⟩

end GeneralInitialization
end Tests
end Relico
