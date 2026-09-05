import Relico.DTR.GeneralSyntax
import Relico.Frontend.GeneralDiagnostic
import Relico.Frontend.GeneralSchema

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/-!
# `general-v1` elaborator

Narrows a `RawGeneralModel`, which mirrors the wire format and rejects nothing,
into a `DTR.GeneralModel`, which can express only the general fragment. Every way
that narrowing can fail is a named `GeneralDiagnosticReason`.

What belongs here and what does not is recorded in `GeneralDiagnostic`, whose
module documentation states the division across the three layers that can reject
a document. In short: this layer does the narrowing that constructing the abstract
syntax tree requires, plus scope resolution and the name hygiene that makes a
scope unambiguous, and it repeats nothing that `DTR.GeneralModel.wellFormed`
already decides about an assembled model.

## The one structural constraint, which is measured and not stylistic

`elaborateExpr` destructures its argument in its own top-level pattern instead of
reading fields as `raw.left` and `raw.operand`. That is required, not preferred.
Measured on this toolchain: the projection form fails to terminate-check both
ways, structurally with "cannot use parameter raw: failed to eliminate recursive
application" and by well-founded recursion with the unprovable goal
`sizeOf child < sizeOf raw`, because a bare `match raw.operand with` records no
equation relating the child to the parent. The destructured form succeeds, and
succeeds *structurally* — an explicit `termination_by structural` request was
accepted — so it needs no annotation, and it reduces in the kernel.

This is a trap worth naming because all four sibling decoders read fields by
projection. They can: their expression language is flat, so not one of them
recurses. Only the recursive function is constrained, so the readable
projection style is kept everywhere else, and the destructured function is kept
as small as it can be.

If a future change to this file ever does defeat the structural check, the
measured one-line repair is `termination_by scope context raw => sizeOf raw`,
naming all three parameters in order; the default `decreasing_tactic` closes the
resulting goals without a `decreasing_by` block.

## `elaborateStmt` recurses, into a conditional's branches only

`for` and `declare` are rejected by `kind` before anything descends into `body`, `init`
or `update`, so nothing in this module ever visits those three slots. `if` is not: as
of stage I0 `elaborateStmt` reads `condition`, `then` and `else` and elaborates them,
so it and `elaborateBody` are a `mutual` pair and a statement body is a hand-written
recursion rather than `List.mapM` — a lambda would hide the recursive call from the
equation compiler, which is F89's shape on the Lean side of the translation.

The prediction this paragraph replaced was right about the trap and wrong about the
stage. It said stage H would make `elaborateStmt` recursive and that it "will have to
destructure for the same measured reason". Stage H did not touch this module; stage I0
did, and it did have to destructure: the projection form was tried first and left
`sizeOf thenRaw < sizeOf raw` unprovable, exactly as the paragraph above records for
`elaborateExpr`. The one thing the prediction missed is that structural recursion is
*not* inferred for the statement pair, so unlike `elaborateExpr` it carries explicit
`termination_by` measures. No `partial` is used anywhere in this module.

## Two restrictions this fragment inherits from the exporter

Neither is repaired here, because repairing either would make this layer more
permissive than the layer upstream of it and so would produce code that no
document can reach.

An instance argument must be an integer or boolean literal, and the exporter
emits no negative integer literal anywhere: a source `-5` reaches the wire as
`unary(-, intLiteral 5)`. Those two facts together mean **no actor can be
instantiated with a negative constructor argument** — `Worker(-5)` is rejected,
by the exporter as a non-literal argument and here as
`nonLiteralInstanceArgument`. The two layers agree, which is the property worth
having; that they agree on a restriction neither states explicitly is worth
recording.

Expressions are not type-checked. `DTR.GeneralExpr` is untyped, so `x + true`
has no representation in which the error could be recorded, and nothing in
`wellFormed` inspects an expression's type. Upstream, the Rebeca compiler
type-checks before the exporter ever runs. The obligation therefore lands on the
evaluator that stage D introduces, which is where an ill-typed operation first
has somewhere to go.
-/

/--
The names a body may read.

Two lists of plain `String`s rather than of `VarName`s, because what a scope is
asked is always "did the document mention this name", and the document's names
arrive as strings. Wrapping happens once, at the point a resolved name becomes a
`DTR.GeneralExpr`.

A scope is per message server and per constructor, not per class: parameters
differ between them while state variables do not.
-/
structure GeneralScope where

  /-- The state variables of the enclosing class. -/
  stateVariables :
    List String

  /-- The formal parameters of the enclosing message server or constructor. -/
  parameters :
    List String

  /-- The local variables declared by the enclosing body, in declaration order.

  Stage I. A live local's name is here and nowhere else: the state-variable and
  parameter lists are fixed when a body starts, while this one grows as
  declarations are elaborated and shrinks when a branch body ends. The list is
  ordered, though nothing depends on the order — every question asked of it is
  membership, and the elaborator refuses a duplicate before it can matter.
  -/
  locals :
    List String

/--
Resolve a `variable` node against a scope.

`GeneralExpr` splits `stateVar` from `parameterVar` while the frontend emits one
`variable` node for both, so this resolution is what makes the split recoverable
and it is the reason a scope has to exist at all.

State variables are consulted first. That order is deliberately unobservable: a
parameter sharing a name with a state variable is rejected as
`parameterShadowsStateVariable` before any body is elaborated, and a local
sharing a name with either is rejected by the `"declare"` arm's own shadowing
check before the next statement is elaborated, so no name is ever in two of the
three lists and any two orders agree on every input this function is reached
with. Stating that here is what keeps the choice from quietly becoming a
shadowing rule that nothing else in the development knows about.

A name in no list is `undeclaredVariable`. That is also the reason a read of
the implicit `sender` receives, and a read of `now` — none of which this
fragment admits, and all of which the exporter reports the same way, since its
own scope holds exactly the declared names too. A read of a for-loop counter
received it as well before stage I; with locals admitted, a counter declared by
a future `for` support would be a local like any other, read through
`.parameterVar`.

**A local reads as `.parameterVar`**, which is one of stage I's approved
rulings. It is the accurate model of the emitted target rather than an
overload: `renderGeneralParameterRead` in `Relico/LF/GeneralCppPrinter.lean`
already emits a block-scoped C++ binding under the source name, so in the
generated reaction body a local and a parameter are the same thing — a
declaration and a read of a bare identifier.
-/
def resolveVariable
    (scope : GeneralScope)
    (name : String)
    (context : String)
    (line : Option Nat) :
    GeneralElab DTR.GeneralExpr :=
  if scope.stateVariables.contains name then
    .ok (.stateVar { value := name })
  else if scope.parameters.contains name then
    .ok (.parameterVar { value := name })
  else if scope.locals.contains name then
    .ok (.parameterVar { value := name })
  else
    .error (generalDiagnostic .undeclaredVariable name context line)


/--
Narrow a declared type string.

Measured types across the corpus: `int` and `boolean`, and nothing else.
-/
def elaborateDeclaredType
    (declared : String)
    (context : String)
    (line : Option Nat) :
    GeneralElab DTR.GeneralType :=
  match declared with
  | "int" => .ok .int
  | "boolean" => .ok .boolean
  | unsupported =>
      .error (generalDiagnostic .unknownDeclaredType unsupported context line)

/--
Narrow a literal's `value` payload to an integer.

The diagnostic's detail is the message `fromJson?` produced rather than a
rendering of the payload. That is not a shortcut: it is the description Lean's own
`FromJson Int` instance gives of what it found, and taking it means this module
needs no way to print a `Json`, which in turn means it needs neither
`Lean.Json.pretty` nor a hand-written shape describer — and `Lean.Json` has no
`Repr` and no `ToString` that could be leaned on instead.
-/
def narrowIntegerLiteral
    (payload : Json)
    (context : String)
    (line : Option Nat) :
    GeneralElab Int :=
  match (Lean.fromJson? payload : Except String Int) with
  | .error message =>
      .error (generalDiagnostic .expectedIntegerLiteral message context line)
  | .ok value =>
      .ok value

/--
Narrow a literal's `value` payload to a boolean.

`value` is one key carrying two JSON types — a number under `intLiteral` and a
boolean under `boolLiteral` — which is why the schema leaves it as an undecoded
`Json` and why the narrowing lands here, where the enclosing `kind` is known.
-/
def narrowBooleanLiteral
    (payload : Json)
    (context : String)
    (line : Option Nat) :
    GeneralElab Bool :=
  match (Lean.fromJson? payload : Except String Bool) with
  | .error message =>
      .error (generalDiagnostic .expectedBooleanLiteral message context line)
  | .ok value =>
      .ok value

/--
Narrow an `assign` statement's `target` payload to a name.

`target` is the second overloaded key: a bare string on an `assign`, an object on
a `send`.
-/
def narrowAssignTargetName
    (payload : Json)
    (context : String)
    (line : Option Nat) :
    GeneralElab String :=
  match (Lean.fromJson? payload : Except String String) with
  | .error message =>
      .error (generalDiagnostic .expectedAssignTargetName message context line)
  | .ok name =>
      .ok name

/--
Read a signed integer literal, accepting both wire encodings of a negative one.

A negative integer has two possible shapes in a `general-v1` document. It may
arrive as an `intLiteral` whose payload is negative, or as `unary(-, intLiteral n)`
if the upstream parser reports the sign as an operator. This reads both, so the
question "is this argument a constant integer?" has one answer in one place rather
than one answer per caller.

Exactly one level of negation is folded. `-(-5)` is still refused, which is the
intended reading of "a literal, possibly signed" — nothing here evaluates
expressions, and a folding pass that recursed would be an evaluator.

The failure reason is a parameter because the two callers owe different
diagnostics for the same malformed input: a non-constant instance argument and a
non-constant delay are different complaints about the same shape.

No recursion, so projections are used freely: the inner match reads the child's
fields directly and makes no recursive call.
-/
def signedIntegerLiteral
    (reason : GeneralDiagnosticReason)
    (context : String)
    (raw : RawGeneralExpr) :
    GeneralElab Int :=
  match raw.kind, raw.operator, raw.operand with

  | "intLiteral", _, _ =>
      match raw.value with
      | none =>
          .error (generalDiagnostic .missingField "value" context raw.line)
      | some payload =>
          narrowIntegerLiteral payload context raw.line

  | "unary", some "-", some child =>
      match child.kind, child.value with
      | "intLiteral", some payload => do
          let magnitude ←
            narrowIntegerLiteral payload context child.line

          pure (-magnitude)

      | _, _ =>
          .error (generalDiagnostic reason child.kind context raw.line)

  | kind, _, _ =>
      .error (generalDiagnostic reason kind context raw.line)

/--
Narrow a binary operator symbol.

Thirteen, measured from the exporter rather than taken from the design note,
which listed eleven and was short by `/` and `%`.
-/
def elaborateBinaryOperator
    (symbol : String)
    (context : String)
    (line : Option Nat) :
    GeneralElab DTR.GeneralBinaryOp :=
  match symbol with
  | "+" => .ok .add
  | "-" => .ok .sub
  | "*" => .ok .mul
  | "/" => .ok .div
  | "%" => .ok .mod
  | "==" => .ok .eq
  | "!=" => .ok .ne
  | "<" => .ok .lt
  | "<=" => .ok .le
  | ">" => .ok .gt
  | ">=" => .ok .ge
  | "&&" => .ok .logicalAnd
  | "||" => .ok .logicalOr
  | unsupported =>
      .error (generalDiagnostic .unknownBinaryOperator unsupported context line)

/--
Narrow a unary operator symbol.

Two, and `-` is the reason no negative integer literal exists on the wire: the
exporter's own literal renderer rejects a negative signum, so a source `-5`
arrives here as a `unary` node over `intLiteral 5`.
-/
def elaborateUnaryOperator
    (symbol : String)
    (context : String)
    (line : Option Nat) :
    GeneralElab DTR.GeneralUnaryOp :=
  match symbol with
  | "-" => .ok .negate
  | "!" => .ok .logicalNot
  | unsupported =>
      .error (generalDiagnostic .unknownUnaryOperator unsupported context line)


/--
Narrow an expression node.

**The argument is destructured in this function's own top-level pattern, and that
is required rather than preferred.** See this module's header: the projection form
fails to terminate-check both structurally and by well-founded recursion, because
`match raw.operand with` records no equation relating the child to the parent.
Every field is therefore bound as a pattern variable, including the five this
function only reads, so that the three recursive slots are subterms of a pattern.

The five kinds are the five the exporter emits. `self` and `knownRebec` also
arrive through `RawGeneralExpr`, but only ever as a send target, so they are
narrowed by `elaborateSendTarget` and are `unsupportedExpressionKind` here — a
send target is not an expression, and admitting one would let a target appear as
an operand.
-/
def elaborateExpr
    (scope : GeneralScope)
    (context : String) :
    RawGeneralExpr →
    GeneralElab DTR.GeneralExpr

  | {
      kind := kind,
      line := line,
      value := value,
      name := name,
      operator := operator,
      operand := operand,
      left := left,
      right := right
    } =>

    match kind with

    | "intLiteral" =>
        match value with

        | none =>
            .error (generalDiagnostic .missingField "value" context line)

        | some payload => do
            let literal ←
              narrowIntegerLiteral payload context line

            pure (.intLiteral literal)

    | "boolLiteral" =>
        match value with

        | none =>
            .error (generalDiagnostic .missingField "value" context line)

        | some payload => do
            let literal ←
              narrowBooleanLiteral payload context line

            pure (.boolLiteral literal)

    | "variable" =>
        match name with

        | none =>
            .error (generalDiagnostic .missingField "name" context line)

        | some identifier =>
            resolveVariable scope identifier context line

    | "unary" =>
        match operator, operand with

        | none, _ =>
            .error (generalDiagnostic .missingField "operator" context line)

        | _, none =>
            .error (generalDiagnostic .missingField "operand" context line)

        | some symbol, some child => do
            let unaryOperator ←
              elaborateUnaryOperator symbol context line

            let inner ←
              elaborateExpr scope context child

            pure (.unary unaryOperator inner)

    | "binary" =>
        match operator, left, right with

        | none, _, _ =>
            .error (generalDiagnostic .missingField "operator" context line)

        | _, none, _ =>
            .error (generalDiagnostic .missingField "left" context line)

        | _, _, none =>
            .error (generalDiagnostic .missingField "right" context line)

        | some symbol, some leftChild, some rightChild => do
            let binaryOperator ←
              elaborateBinaryOperator symbol context line

            let leftExpr ←
              elaborateExpr scope context leftChild

            let rightExpr ←
              elaborateExpr scope context rightChild

            pure (.binary binaryOperator leftExpr rightExpr)

    | unsupported =>
        .error (generalDiagnostic .unsupportedExpressionKind unsupported context line)


/--
Narrow a send's `target` payload.

The payload is read through `RawGeneralExpr`, which is what the schema uses for a
target: a target carries nothing an expression node does not already have, and one
node type means a traversal cannot forget a case.

Both target kinds are measured to carry no `line` of their own, so the enclosing
statement's line is passed in and used throughout. That is the more useful
location anyway — it points at the send rather than at its receiver.

Nothing here checks that the named known rebec is *declared*. That is
`statementTargetDeclared`, reached through `sendTargetsDeclared`, and it needs the
class the statement belongs to, which is a property of an assembled model rather
than of a statement.
-/
def elaborateSendTarget
    (payload : Json)
    (context : String)
    (line : Option Nat) :
    GeneralElab DTR.GeneralSendTarget :=
  match (Lean.fromJson? payload : Except String RawGeneralExpr) with

  | .error message =>
      .error (generalDiagnostic .unsupportedSendTargetKind message context line)

  | .ok target =>
      match target.kind with

      | "self" =>
          .ok .selfTarget

      | "knownRebec" =>
          match target.name with

          | none =>
              .error (generalDiagnostic .missingField "name" context line)

          | some peer =>
              .ok (.knownRebec { value := peer })

      | unsupported =>
          .error (generalDiagnostic .unsupportedSendTargetKind unsupported context line)

/--
Narrow a send's optional `after` expression to a delay.

Three things happen here, and each is forced by a difference between the wire
format and `DTR.GeneralStmt`.

An absent `after` becomes delay zero. `GeneralSyntax` says so explicitly: the
statement carries a `Delay` and not an optional one, because the frontend's output
is an abstract syntax tree and applying the default is this side's responsibility.
Five `after` fields in the corpus are explicitly null.

A non-literal delay is rejected. `Delay` holds a `Nat`, so a computed delay has no
representation at all; the exporter independently emits only a literal here, with
the stated justification that a Lingua Franca connection delay must be static.
Whether that premise holds of real `lfc` is an open question recorded in the
paper-corrections ledger, but it does not change this function: a non-constant
delay is unrepresentable either way.

A negative delay is rejected rather than truncated. `Int.toNat` would silently
send `-2` to zero, turning a rejected program into a *differently behaving*
accepted one, which is the worst of the three outcomes.

`negativeDelay` is reachable. It was not before: reading only a bare `intLiteral`
meant `after(-2)` arrived as a unary node and was reported as a *non-constant*
delay, which is both the wrong complaint and a dead check. Reading the sign here is
what makes the two diagnostics say what they mean.

The fallback line applies to the negative-delay report. A non-constant delay is
reported against the offending node's own line, or against no line at all if it
carries none, which is absent rather than wrong.
-/
def elaborateDelay
    (after : Option RawGeneralExpr)
    (context : String)
    (line : Option Nat) :
    GeneralElab Delay :=
  match after with

  | none =>
      .ok { value := 0 }

  | some raw =>
      let delayLine :=
        match raw.line with
        | none => line
        | some own => some own

      do
        let literal ←
          signedIntegerLiteral .nonConstantDelay context raw

        if literal < 0 then
          .error
            (generalDiagnostic .negativeDelay (toString literal) context delayLine)
        else
          pure { value := literal.toNat }

/- `elaborateStmt` and `elaborateBody` are mutually recursive as of stage I0, because a
conditional's branches are bodies. A `mutual` block cannot carry a docstring, so each
definition carries its own. -/
mutual

/--
Narrow a statement node.

**This function recurses as of stage I0, into a conditional's branch bodies and nowhere else.**
The paragraph replaced here said it did not recurse, and that `if`, `for` and `declare` were all
rejected by `kind` before anything descended into `then`, `else`, `body`, `init` or `update`. `for`
and `declare` are still rejected in exactly that way, so nothing descends into `body`, `init` or
`update`. `if` is no longer rejected: its `condition`, `then` and `else` are read and elaborated.

**Two things about the recursion are measured rather than chosen.** Structural recursion is not
inferred for this pair: Lean reports that it is "skipping arguments of type `List RawGeneralStmt`, as
`elaborateStmt` has no compatible argument", so the pair is well founded on `sizeOf` and both
measures are written out. And the `if` arm destructures `raw` with a **structure pattern** rather than
reading `raw.condition`, `raw.«then»` and `raw.«else»` by projection, because the projection form was
tried first and left `sizeOf thenRaw < sizeOf raw` unprovable: a projection carries no subterm
relation back to the record, while a pattern does. `partial` was not used and is not needed.

An absent `else` elaborates to the empty body rather than being refused. That is the same defaulting
decision the elaborator already makes for an absent `after`, and `LF.stmtWellFormed` accepts an empty
branch, so the empty case is represented rather than avoided.

The assignment-target check is the one thing here that no other layer performs.
**Stage I ended its divergence from the exporter.** Until locals were admitted,
this layer accepted only state-variable targets while the exporter's scope
called a value anything in `locals ∪ stateVariables` — so a message server
writing to its own parameter exported successfully and was refused here, the
one disagreement between the layers. With the check widened to exactly the
exporter's `isValue` — state variables or a **live local**, parameters still
refused on both sides — the two layers agree on every document, and a write to
a formal parameter remains refused here for the reason it always was:
`DTR.GeneralActorState.valuation` binds parameters when a message is taken, so
an assignment to one before that binding has nowhere to land that survives.
-/
def elaborateStmt
    (scope : GeneralScope)
    (context : String)
    (raw : RawGeneralStmt) :
    GeneralElab DTR.GeneralStmt :=
  match raw.kind with

  | "assign" =>
      match raw.target, raw.value with

      | none, _ =>
          .error (generalDiagnostic .missingField "target" context raw.line)

      | _, none =>
          .error (generalDiagnostic .missingField "value" context raw.line)

      | some targetPayload, some valueRaw => do
          let targetName ←
            narrowAssignTargetName targetPayload context raw.line

          if
            scope.stateVariables.contains targetName ||
              scope.locals.contains targetName then
            do
              let valueExpr ←
                elaborateExpr scope context valueRaw

              pure (.assign { value := targetName } valueExpr)
          else
            .error
              (generalDiagnostic
                .assignmentTargetNotStateVariable targetName context raw.line)

  | "send" =>
      match raw.target, raw.messageServer with

      | none, _ =>
          .error (generalDiagnostic .missingField "target" context raw.line)

      | _, none =>
          .error (generalDiagnostic .missingField "messageServer" context raw.line)

      | some targetPayload, some serverName => do
          let target ←
            elaborateSendTarget targetPayload context raw.line

          let arguments ←
            (raw.arguments.getD []).mapM (elaborateExpr scope context)

          let delay ←
            elaborateDelay raw.after context raw.line

          pure (.send target { value := serverName } arguments delay)

  | "if" =>
      match raw with

      | { condition := none, .. } =>
          .error (generalDiagnostic .missingField "condition" context raw.line)

      | { «then» := none, .. } =>
          .error (generalDiagnostic .missingField "then" context raw.line)

      | { condition := some conditionRaw,
          «then» := some thenRaw,
          «else» := elseOption,
          .. } => do
          let condition ←
            elaborateExpr scope context conditionRaw

          let thenBody ←
            elaborateBody scope context thenRaw

          let elseBody ←
            match elseOption with

            | none =>
                pure []

            | some elseRaw =>
                elaborateBody scope context elseRaw

          pure (.ifThenElse condition thenBody elseBody)

  | "for" =>
      .error (generalDiagnostic .iterationNotSupported "for" context raw.line)

  | "declare" =>
      match raw.name, raw.type, raw.value with

      | none, _, _ =>
          .error (generalDiagnostic .missingField "name" context raw.line)

      | _, none, _ =>
          .error (generalDiagnostic .missingField "type" context raw.line)

      | _, _, none =>
          .error (generalDiagnostic .missingField "value" context raw.line)

      | some name, some declaredType, some valueRaw => do
          if
            scope.stateVariables.contains name ||
              scope.parameters.contains name ||
              scope.locals.contains name then
            .error
              (generalDiagnostic .localShadowsDeclaredName name context raw.line)
          else
            let declaredType ←
              elaborateDeclaredType declaredType context raw.line

            let valueExpr ←
              elaborateExpr scope context valueRaw

            pure (.localDecl { value := name } declaredType valueExpr)

  | unsupported =>
      .error (generalDiagnostic .unsupportedStatementKind unsupported context raw.line)

termination_by
  sizeOf raw

/--
Narrow a statement body.

**A hand-written recursion as of stage I0, not `List.mapM`.** The paragraph replaced here said the
element function was independent of the list, so nothing was recursive and the destructuring
constraint did not apply. Both halves of that stopped being true when `elaborateStmt` began
descending into a conditional's branches: this function is now one half of a `mutual` pair, and a
`List.mapM` would hide the recursive call inside a lambda, where the equation compiler cannot see it.
That is the same shape F89 records on the Lean side of the translation, and the repair is the same
one: an explicit `match` on the list.

**Stage I makes the walk scope-threading.** A declaration elaborated at one
position extends the scope for every statement after it in the same body, so the
recursion's second argument is no longer the scope the body started with: after
a `declare` head, the tail is elaborated under `{ scope with locals :=
scope.locals ++ [name] }`. The extension is *not* threaded out — this function
returns a body, not a scope — which is exactly the branch-scope rule: a name
declared inside a `then` or `else` body dies with that body, because the
conditional's parent elaboration continues with its own unextended scope. The
rule costs nothing here and needs no mechanism, because `elaborateStmt`'s `if`
arm already passes `scope` into `elaborateBody` for each branch and discards
what comes back.
-/
def elaborateBody
    (scope : GeneralScope)
    (context : String) :
    List RawGeneralStmt →
    GeneralElab DTR.GeneralBody

  | [] =>
      pure []

  | raw :: rest => do
      let statement ←
        elaborateStmt scope context raw

      let extendedScope :=
        match statement with

        | .localDecl name _ _ =>
            {
              scope with
                locals := scope.locals ++ [name.value]
            }

        | _ =>
            scope

      let remaining ←
        elaborateBody extendedScope context rest

      pure (statement :: remaining)

termination_by
  raws => sizeOf raws

end


/--
Elaborate a state variable declaration.

The empty-name check lives here because `namesUniqueAndValid` does not see state
variable names: that clause constrains actor, class and known-rebec names, which
are the ones a store is keyed by. An empty state variable name would otherwise
reach the valuation store as a usable key.
-/
def elaborateStateVariable
    (raw : RawGeneralStateVariable)
    (context : String) :
    GeneralElab DTR.GeneralStateVariableDecl :=
  if raw.name == "" then
    .error (generalDiagnostic .emptyName "state variable" context raw.line)
  else do
    let declaredType ←
      elaborateDeclaredType raw.type context raw.line

    pure {
      name := { value := raw.name },
      declaredType := declaredType
    }

/--
Elaborate a formal parameter of a constructor or a message server.
-/
def elaborateParameter
    (raw : RawGeneralParameter)
    (context : String) :
    GeneralElab DTR.GeneralTypedParameter :=
  if raw.name == "" then
    .error (generalDiagnostic .emptyName "parameter" context raw.line)
  else do
    let declaredType ←
      elaborateDeclaredType raw.type context raw.line

    pure {
      name := { value := raw.name },
      declaredType := declaredType
    }

/--
The first name that repeats later in the list, if any.

Written as structural recursion with the list destructured in the function's own
top-level pattern, which is both the measured requirement for recursion in this
module and the shape `decodeMultiStorePayloadDistinctNames` already uses at
`MultiStorePayloadDecoder.lean:72`.

Returning the offending name rather than a Bool is what lets the diagnostic name
it: a caller that only knew "there is a duplicate" would have to search again to
say which.
-/
def firstDuplicateName? :
    List String →
    Option String

  | [] =>
      none

  | name :: remaining =>
      if remaining.contains name then
        some name
      else
        firstDuplicateName? remaining

/--
The first name in the second list that also appears in the first, if any.

Used for parameter-shadows-state-variable, which is rejected rather than resolved
by a scoping rule. That rejection is what makes `resolveVariable`'s decision to
consult state variables before parameters unobservable: no accepted model can have
a name in both.
-/
def firstShadowedName?
    (stateVariables : List String) :
    List String →
    Option String

  | [] =>
      none

  | name :: remaining =>
      if stateVariables.contains name then
        some name
      else
        firstShadowedName? stateVariables remaining

/--
Build a known-rebec declaration.

Non-failing on purpose. Uniqueness and non-emptiness of known-rebec names are
`namesUniqueAndValid`'s business, because they are properties of the assembled
model's topology rather than of this declaration in isolation, and duplicating the
check here would give one question two answers that nothing keeps in agreement.
-/
def knownRebecDeclOf
    (raw : RawGeneralKnownRebec) :
    DTR.GeneralKnownRebecDecl :=
  {
    name := { value := raw.name },
    className := { value := raw.className }
  }

/--
Elaborate a message server.

`priority` is carried through unchanged, including its absence. Absence is a
priority class rather than a missing value, so replacing `none` with a default
here would erase the distinction the later priority layer is built on.
-/
def elaborateMessageServer
    (stateVariableNames : List String)
    (className : String)
    (raw : RawGeneralMessageServer) :
    GeneralElab DTR.GeneralMessageServer := do
  let context := className ++ "." ++ raw.name

  if raw.name == "" then
    .error (generalDiagnostic .emptyName "message server" context raw.line)
  else
    let parameterNames :=
      raw.parameters.map (fun parameter => parameter.name)

    match firstDuplicateName? parameterNames with
    | some duplicated =>
        .error (generalDiagnostic .duplicateParameter duplicated context raw.line)

    | none =>
        match firstShadowedName? stateVariableNames parameterNames with
        | some shadowed =>
            .error
              (generalDiagnostic .parameterShadowsStateVariable shadowed context raw.line)

        | none => do
            let parameters ←
              raw.parameters.mapM
                (fun parameter => elaborateParameter parameter context)

            let body ←
              elaborateBody
                {
                  stateVariables := stateVariableNames,
                  parameters := parameterNames,
                  locals := []
                }
                context
                raw.body

            pure {
              name := { value := raw.name },
              parameters := parameters,
              body := body,
              priority := raw.priority
            }

/--
Elaborate a constructor.

The same three name checks as a message server, against a context naming the class
rather than a message, since a constructor has no name of its own.
-/
def elaborateConstructor
    (stateVariableNames : List String)
    (className : String)
    (raw : RawGeneralConstructor) :
    GeneralElab DTR.GeneralConstructor := do
  let context := className ++ " constructor"

  let parameterNames :=
    raw.parameters.map (fun parameter => parameter.name)

  match firstDuplicateName? parameterNames with
  | some duplicated =>
      .error (generalDiagnostic .duplicateParameter duplicated context raw.line)

  | none =>
      match firstShadowedName? stateVariableNames parameterNames with
      | some shadowed =>
          .error
            (generalDiagnostic .parameterShadowsStateVariable shadowed context raw.line)

      | none => do
          let parameters ←
            raw.parameters.mapM
              (fun parameter => elaborateParameter parameter context)

          let body ←
            elaborateBody
              {
                stateVariables := stateVariableNames,
                parameters := parameterNames,
                locals := []
              }
              context
              raw.body

          pure {
            parameters := parameters,
            body := body
          }

/--
Elaborate a reactive class.

Only state-variable names are checked here. `namesUniqueAndValid` already requires
class names to be unique and non-empty and message-server names to be distinct, and
its own comment hands parameter and state-variable names to this layer — so the two
layers partition the question rather than both answering it.

`queueBound` is read by the schema and dropped here: `GeneralMessageBag` is
unbounded, so there is nothing in this development for a bound to constrain.
Dropping it is recorded rather than silent, because it means a model whose queue
bound the upstream tool enforces is translated as though it had none.
-/
def elaborateClass
    (raw : RawGeneralClass) :
    GeneralElab DTR.GeneralReactiveClass := do
  let context := raw.name

  let stateVariableNames :=
    raw.stateVariables.map (fun stateVariable => stateVariable.name)

  match firstDuplicateName? stateVariableNames with
  | some duplicated =>
      .error
        (generalDiagnostic .duplicateStateVariable duplicated context raw.line)

  | none => do
      let stateVariables ←
        raw.stateVariables.mapM
          (fun stateVariable => elaborateStateVariable stateVariable context)

      let constructor ←
        elaborateConstructor stateVariableNames raw.name raw.constructor

      let messageServers ←
        raw.messageServers.mapM
          (fun messageServer =>
            elaborateMessageServer stateVariableNames raw.name messageServer)

      pure {
        name := { value := raw.name },
        knownRebecs := raw.knownRebecs.map knownRebecDeclOf,
        stateVariables := stateVariables,
        constructor := constructor,
        messageServers := messageServers
      }

/--
Elaborate one positional constructor argument.

Constants only, but a *signed* constant: `Worker(-5)` is accepted. That is a
deliberate correction. An earlier draft admitted only a bare `intLiteral`, and
because a negative integer may reach the wire as `unary(-, intLiteral 5)`, the
effect was that no actor could be instantiated with a negative constructor
argument anywhere in the language — a restriction that appeared in no document and
that nothing in the paper, the fragment spec or the exporter's own comments claims.
`signedIntegerLiteral` is what removes it here.

Booleans stay strictly literal: `Worker(!true)` is refused, matching the exporter,
which requires the argument's text to be one of the boolean literals.

Projections are used freely because this function does not recurse.
-/
def elaborateInstanceArgument
    (context : String)
    (raw : RawGeneralExpr) :
    GeneralElab DTR.GeneralValue :=
  match raw.kind with

  | "boolLiteral" =>
      match raw.value with
      | none =>
          .error (generalDiagnostic .missingField "value" context raw.line)
      | some payload => do
          let value ←
            narrowBooleanLiteral payload context raw.line

          pure (.bool value)

  | _ => do
      let value ←
        signedIntegerLiteral .nonLiteralInstanceArgument context raw

      pure (.int value)

/--
Build one known-rebec binding.

Non-failing, and the wire's `className` is deliberately discarded rather than
cross-checked: `classOfActor?` recovers the bound instance's class from the model,
so keeping the exporter's copy would store a second answer to a question the model
already answers.
-/
def bindingOf
    (raw : RawGeneralBinding) :
    KnownRebecName × ActorName :=
  (
    { value := raw.knownRebec },
    { value := raw.«instance» }
  )

/--
Elaborate an actor instance.

No name check. `namesUniqueAndValid` requires instance names to be non-empty and
the derived topology's keys to be unique, so both questions are answered once, at
the layer that can see the whole model.
-/
def elaborateInstance
    (raw : RawGeneralInstance) :
    GeneralElab DTR.GeneralActorInstance := do
  let context := raw.name

  let arguments ←
    raw.arguments.mapM
      (fun argument => elaborateInstanceArgument context argument)

  pure {
    name := { value := raw.name },
    className := { value := raw.className },
    bindings := raw.bindings.map bindingOf,
    arguments := arguments,
    priority := raw.priority
  }

/--
Elaborate a whole document into a general model.

`family` and `schemaVersion` are not examined here. They are the decoder's
business, checked before elaboration begins, which is what `GeneralDiagnostic`
records for `unexpectedFamily` and `unsupportedSchemaVersion`; by the time this
function runs, the document has already been accepted as a `general-v1` one.

Nothing in this function consults `wellFormed` either. Elaboration builds the
model; the decoder gates it. Keeping the two apart is what lets a well-formedness
failure be reported against an assembled model rather than against a fragment.
-/
def elaborateGeneralModel
    (raw : RawGeneralModel) :
    GeneralElab DTR.GeneralModel := do
  let classes ←
    raw.classes.mapM elaborateClass

  let instances ←
    raw.instances.mapM elaborateInstance

  pure {
    classes := classes,
    instances := instances
  }

end Frontend
end Relico
