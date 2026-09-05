set_option autoImplicit false

namespace Relico
namespace Frontend

/-!
# Frontend diagnostics for the general family

Every way a `general-v1` document can fail to become a `DTR.GeneralModel`, named.

The four earlier families report `Except String`, so a rejection is a sentence
and a test can only assert on that sentence. Here the reason is a value. A
negative test names the constructor it expects, which makes the test insensitive
to wording and makes an accidental change of *which* check fired a test failure
rather than a diff in a string literal. The sentence still exists — `render`
produces it — but it is derived from the reason instead of being the reason.

## What this layer checks, and what it deliberately does not

Three layers can reject a document, and a check placed in two of them gives one
question two answers that nothing keeps in agreement. That failure mode is one
this family exists to correct, so the division is recorded here rather than left
to be inferred.

`RebecaGeneralJsonExporter` rejects at the source level, with the widest view: it
has the parser's object model, so it alone can say that a compound assignment or
a bare expression statement occurred. It also *guarantees* things about its
output that this layer must nonetheless re-derive, because nothing between a JSON
document and this development checks anything: measured, it emits no negative
integer literal anywhere (`integerLiteralText` rejects a negative sign), it
admits only a literal as an instance argument and only a literal as an `after`
delay, and its `Scope` forbids a parameter that shadows a state variable. A
document violating any of those is not one the exporter can produce — and this
layer still rejects it by name, because the exporter having run is an assumption
and not a fact.

`DTR.GeneralModel.wellFormed` checks what is a property of an assembled model:
that bindings match declarations, that instance arguments match constructor
parameters, that send targets are declared, that sends reach declared message
servers with the declared arity, and that the names lookups depend on are unique.
None of those is repeated below. Two further restrictions are unrepresentable in
`GeneralSyntax` and so appear in no layer at all.

This layer checks exactly what constructing the abstract syntax tree requires,
and one thing more that nothing else covers.

What construction requires is narrowing: a `kind` string to a constructor, an
operator symbol to a `GeneralBinaryOp` or `GeneralUnaryOp`, a declared type
string to a `GeneralType`, the overloaded `value` key to an `Int` or a `Bool`, the
overloaded `target` key to a name or to a send target, a literal to a
`GeneralValue`, and a nullable `after` expression to a `Delay`. Each of those can
fail on a document the schema reads, so each has a reason below.

The one thing more is scope. `GeneralExpr` distinguishes `stateVar` from
`parameterVar` while the frontend emits a single `variable` node, so resolving a
variable is not optional and it needs a scope. Since a scope exists here, name
hygiene *of that scope* is checked here too: `GeneralWellFormed` says so
explicitly, having excluded state-variable and parameter names from
`namesUniqueAndValid` on the grounds that unambiguous scope is this layer's
concern. Those two name positions are the only ones in a model that no other
layer validates, so unchecked here they would be unchecked everywhere.

## One asymmetry worth stating, because it is a divergence

An assignment target is not checked by `wellFormed`: `GeneralStmt.assign` carries
a bare `VarName` and no clause constrains it. The exporter checks only that the
target is *in scope*, and its scope includes formal parameters, so a message
server that writes to its own parameter exports successfully. It cannot be
elaborated: `GeneralActorState.valuation` is keyed by state-variable names, so
there is nowhere for such a write to land, and accepting it would produce a
statement whose effect the semantics silently discards. So
`assignmentTargetNotStateVariable` is checked here — not because the fragment
document lists it, but because the exporter is more permissive than the state
semantics and this is the only layer positioned to notice.
-/

/--
Why a `general-v1` document was rejected.

Ordered by the stage that raises it: document, declarations, expressions,
statements, instances, then the assembled model.
-/
inductive GeneralDiagnosticReason where

  -- Document level. Raised by the decoder, before elaboration.

  /-- The text is not JSON at all. -/
  | invalidJson

  /-- The JSON does not have the shape `RawGeneralModel` describes. -/
  | schemaDecodeFailed

  /-- The document declares a `schemaVersion` this reader does not accept. -/
  | unsupportedSchemaVersion

  /-- The document declares a `family` other than `general`. -/
  | unexpectedFamily

  -- Declarations.

  /-- A declared type other than `int` or `boolean`. -/
  | unknownDeclaredType

  /-- A state variable or parameter declared with an empty name. -/
  | emptyName

  /-- Two state variables of one class share a name. -/
  | duplicateStateVariable

  /-- Two parameters of one message server or constructor share a name. -/
  | duplicateParameter

  /-- A parameter has the name of a state variable of its class. -/
  | parameterShadowsStateVariable

  -- Expressions.

  /-- An expression `kind` this fragment has no constructor for. -/
  | unsupportedExpressionKind

  /-- A field the node's own `kind` requires is absent. -/
  | missingField

  /-- An `intLiteral` whose `value` is not a JSON integer. -/
  | expectedIntegerLiteral

  /-- A `boolLiteral` whose `value` is not a JSON boolean. -/
  | expectedBooleanLiteral

  /-- A binary operator symbol outside the thirteen this fragment admits. -/
  | unknownBinaryOperator

  /-- A unary operator symbol outside the two this fragment admits. -/
  | unknownUnaryOperator

  /--
  A `variable` naming neither a state variable nor a parameter in scope.

  This is the reason a read of the implicit `sender` receives, and a read of
  `now`, and a read of a for-loop counter in a body this stage does not admit.
  -/
  | undeclaredVariable

  -- Statements.

  /-- A statement `kind` this fragment has no constructor for. -/
  | unsupportedStatementKind

  /-- An `if`. Read faithfully by the schema, admitted by no stage before H. -/
  | branchingNotSupported

  /-- A `for`. Read faithfully by the schema, admitted by no stage before H. -/
  | iterationNotSupported

  /--
  A `declare`. Admitted by stage I as a local variable declaration; **unreachable
  for every document the exporter emits**, because the exporter emits a `declare`
  node only as a `for` counter and refuses a body declaration of its own
  (`RebecaGeneralJsonExporter.java`'s R15 refusal), and a `for` is refused here
  with `iterationNotSupported` before its counter can be reached. Retained rather
  than deleted for the same reason `branchingNotSupported` above was: a future
  document shape — most plausibly a `for` counter reaching this layer when
  iteration support lands — needs the reason to already exist, and a deleted
  constructor takes its render text with it.
  -/
  | localDeclarationNotSupported

  /--
  A `declare` whose name is already in scope, as a state variable, a formal
  parameter, or a live local of the same body.

  Stage I. The refusal is what keeps the three scope lists disjoint, which is
  what `resolveVariable`'s order-independence argument above leans on, and it is
  the Lean-side mirror of the exporter's own three shadowing checks on a loop
  counter: reserved name, state variable, known rebec, duplicate.
  -/
  | localShadowsDeclaredName

  /-- An `assign` whose `target` is not a JSON string. -/
  | expectedAssignTargetName

  /--
  An `assign` to a name that is not a state variable of the enclosing class.

  See the note above: the exporter admits a write to a formal parameter and the
  state semantics has nowhere to put one.
  -/
  | assignmentTargetNotStateVariable

  /-- A send `target` whose `kind` is neither `self` nor `knownRebec`. -/
  | unsupportedSendTargetKind

  /-- An `after` delay that is not an integer literal. -/
  | nonConstantDelay

  /-- An `after` delay that is a negative integer literal. -/
  | negativeDelay

  -- Instances.

  /-- A constructor argument that is not an integer or boolean literal. -/
  | nonLiteralInstanceArgument

  -- The assembled model.

  /-- `bindingsMatchDeclarations` is false. -/
  | bindingsMatchDeclarationsFailed

  /-- `argumentsMatchConstructor` is false. -/
  | argumentsMatchConstructorFailed

  /-- `sendTargetsDeclared` is false. -/
  | sendTargetsDeclaredFailed

  /-- `sendsResolveToMessageServers` is false. -/
  | sendsResolveToMessageServersFailed

  /-- `namesUniqueAndValid` is false. -/
  | namesUniqueAndValidFailed

  /--
  `wellFormed` is false and all five clauses are true.

  Unreachable, because `wellFormed` is exactly their conjunction. It exists so
  that classification is total without the classifier being trusted to agree
  with the gate: the gate decides, and this reason is what remains if the two
  ever disagree.
  -/
  | modelNotWellFormed

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralDiagnosticReason

/--
The sentence for a reason.

Phrased as a noun for what was found, so that `render` can put a name and a
location after it and read as one clause. This mirrors the exporter's own
diagnostic style, which the fixtures pin, so a reader who has seen one layer's
message recognises the other's.
-/
def message :
    GeneralDiagnosticReason →
    String

  | invalidJson =>
      "invalid JSON"

  | schemaDecodeFailed =>
      "a document that does not match the general-v1 schema"

  | unsupportedSchemaVersion =>
      "an unsupported schema version"

  | unexpectedFamily =>
      "an unexpected family"

  | unknownDeclaredType =>
      "a declared type outside the general fragment"

  | emptyName =>
      "an empty name"

  | duplicateStateVariable =>
      "a repeated state-variable name"

  | duplicateParameter =>
      "a repeated parameter name"

  | parameterShadowsStateVariable =>
      "a parameter shadowing a state variable"

  | unsupportedExpressionKind =>
      "an expression kind outside the general fragment"

  | missingField =>
      "a missing required field"

  | expectedIntegerLiteral =>
      "an integer literal whose value is not an integer"

  | expectedBooleanLiteral =>
      "a boolean literal whose value is not a boolean"

  | unknownBinaryOperator =>
      "a binary operator outside the general fragment"

  | unknownUnaryOperator =>
      "a unary operator outside the general fragment"

  | undeclaredVariable =>
      "a read of a name that is neither a state variable nor a parameter"

  | unsupportedStatementKind =>
      "a statement kind outside the general fragment"

  | branchingNotSupported =>
      "a conditional statement, which this stage does not admit"

  | iterationNotSupported =>
      "a loop statement, which this stage does not admit"

  | localDeclarationNotSupported =>
      "a local variable declaration, which this stage does not admit"

  | localShadowsDeclaredName =>
      "a local variable declaration of a name already in scope"

  | expectedAssignTargetName =>
      "an assignment whose target is not a name"

  | assignmentTargetNotStateVariable =>
      "an assignment to a name that is not a state variable"

  | unsupportedSendTargetKind =>
      "a send target that is neither self nor a known rebec"

  | nonConstantDelay =>
      "an after delay that is not an integer literal"

  | negativeDelay =>
      "a negative after delay"

  | nonLiteralInstanceArgument =>
      "a constructor argument that is not a literal"

  | bindingsMatchDeclarationsFailed =>
      "an instance whose bindings do not match its class's declarations"

  | argumentsMatchConstructorFailed =>
      "an instance whose arguments do not match its constructor's parameters"

  | sendTargetsDeclaredFailed =>
      "a send to an undeclared known rebec"

  | sendsResolveToMessageServersFailed =>
      "a send that does not reach a declared message server"

  | namesUniqueAndValidFailed =>
      "a repeated or empty name that a lookup depends on"

  | modelNotWellFormed =>
      "a model that is not well formed"

end GeneralDiagnosticReason

/--
A rejection: a named reason, the text it was found in, where it was found, and
the source line if the document recorded one.

`detail` and `context` are plain strings and no field holds `Lean.Json`. That is
deliberate and it is what lets this type derive `Repr` and `DecidableEq`, which
the raw schema cannot: a diagnostic naming a construct is comparable, while one
embedding a subtree is not. A test can therefore compare a whole diagnostic, and
a `#guard` over the reason alone stays readable.

`line` is `Option Nat` because the exporter omits it on literals and on send
targets, and reports it as null on one constructor. An absent line is reported as
absent rather than as line zero.
-/
structure GeneralDiagnostic where

  /-- Which check rejected the document. -/
  reason :
    GeneralDiagnosticReason

  /-- The offending name, symbol, or kind, if the reason has one. -/
  detail :
    String :=
      ""

  /-- Where it was found: a class, a message server, a constructor, a main-block instance. -/
  context :
    String :=
      ""

  /-- The source line the document recorded, if it recorded one. -/
  line :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

namespace GeneralDiagnostic

/--
The sentence for a diagnostic.

Each optional part is omitted when empty rather than rendered as an empty
fragment, so a diagnostic with no detail and no context is one clean clause.
-/
def render
    (diagnostic : GeneralDiagnostic) :
    String :=
  "general-v1: " ++
    diagnostic.reason.message ++
    (if diagnostic.detail == "" then
      ""
    else
      ": `" ++ diagnostic.detail ++ "`") ++
    (if diagnostic.context == "" then
      ""
    else
      " in " ++ diagnostic.context) ++
    (match diagnostic.line with
      | none => ""
      | some line => " at line " ++ toString line)

instance : ToString GeneralDiagnostic where
  toString diagnostic :=
    diagnostic.render

end GeneralDiagnostic

/--
Build a diagnostic.

A function rather than the structure's own constructor so that every call site
states all four parts positionally and none is silently defaulted. Defaults exist
on the fields for the benefit of tests, which write the parts they assert on.
-/
def generalDiagnostic
    (reason : GeneralDiagnosticReason)
    (detail : String)
    (context : String)
    (line : Option Nat) :
    GeneralDiagnostic :=
  {
    reason :=
      reason

    detail :=
      detail

    context :=
      context

    line :=
      line
  }

/--
The elaborator's result type.

An abbreviation because it appears in every signature in the elaborator and the
decoder, and because writing it once means the diagnostic type can gain a field
without touching thirty signatures.
-/
abbrev GeneralElab
    (α : Type) :=
  Except GeneralDiagnostic α

end Frontend
end Relico
