import Lean.Data.Json

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/-!
# `general-v1` raw schema

A faithful, total reader for the JSON that `RebecaGeneralJsonExporter` emits. It
mirrors the wire format and narrows nothing: a document the exporter can produce
is a document this schema can read, including the constructs the DTR general
fragment excludes. Narrowing is the elaborator's job, so that stages C through H
widen the elaborator and never touch this file, and so that a rejected program is
rejected by name rather than by failing to parse.

Every field here was measured from the nine committed fixtures in
`frontend/fixtures/general/`, and the whole schema was validated by decoding all
nine before this file existed. Four measurements decide its shape.

`value` is overloaded across two axes. On an `intLiteral` it is a JSON number, on
a `boolLiteral` a JSON boolean, under the same key; on an `assign` or a `declare`
it is an expression object. So the expression-level `value` is `Option Json` and
the statement-level `value` is `Option RawGeneralExpr`. Typing the former as
`Option Int` would make the reader reject `{"kind":"boolLiteral","value":false}`,
which the exporter emits seven times. `frontend/fixtures/general/README.md:114`
records the same overload from the other direction: it is why `check-general.sh`
compares canonical serializations rather than parsed equality, since Python holds
`True == 1` and would call a corrupted document equal.

`target` is overloaded the same way. On an `assign` it is a bare string naming
the assigned variable; on a `send` it is an object whose `kind` is `self` or
`knownRebec`. It is therefore `Option Json`, and deciding which reading applies
belongs to the elaborator, which knows the statement kind.

`line` is present on every node except `intLiteral` (28 of 40 occurrences),
`boolLiteral` (5 of 7), `self`, and `knownRebec`, and is explicitly `null` on one
constructor. It is `Option Nat` throughout rather than defaulting to zero, so
that "the exporter recorded no line" and "line zero" stay distinguishable in a
diagnostic.

Explicit JSON `null` is load-bearing, not incidental: it appears 32 times across
the corpus, covering all 13 instance priorities, all 13 message-server
priorities, five `send.after` fields, and one constructor `line`. The derived
reader maps `null` to `none`, which was verified rather than assumed — no
pre-existing module in this repository decodes an explicit `null`.

## Why this schema derives less than its four siblings

`MultiStorePayloadSchema` and the other three families derive
`Repr, DecidableEq, FromJson, ToJson`. This one derives `FromJson` alone, for two
measured reasons rather than by preference.

`Repr` cannot be derived for any type carrying a `Json` field, because
`Lean.Json` has no `Repr` instance: the deriving handler fails with
`failed to synthesize Repr (Option Json)`. Since the overloaded `value` and
`target` keys force `Option Json`, `Repr` is unavailable here.

`DecidableEq` cannot be derived for a type whose field is `Option Self`. A
recursive structure has no base case unless its self-references are optional, so
recursion through `Option` is forced, and with it the loss. This was measured on
a type with no `Json` field at all, so it is the recursion and not the payload.

Both losses are contained, because nothing needs either instance. Test
assertions compare the *elaborated* `GeneralModel`, which derives `DecidableEq`
normally, and a diagnostic names the offending construct and line rather than
embedding a raw subtree. Deriving a class that is not needed would mean deriving
one that cannot be verified, so this file derives exactly what it uses.
-/

/--
The schema version this reader accepts. Measured: all nine fixtures emit `1`.
-/
def generalBridgeSchemaVersion : Nat := 1

/--
The family tag this reader accepts. Measured: all nine fixtures emit `general`.
-/
def generalBridgeFamily : String := "general"

/--
An expression node, self-recursive through the optional child slots.

The five expression kinds the exporter emits are `intLiteral`, `boolLiteral`,
`variable`, `binary`, and `unary`, discriminated by `kind`. Two further kinds
appear only as a `send` target, `self` and `knownRebec`; they are read through
this same structure because a target carries nothing a target does not have, and
keeping one node type means a traversal cannot forget a case.

`value` holds the payload of a literal undecoded, because `intLiteral` and
`boolLiteral` share the key with different JSON types. `operand` serves `unary`;
`left` and `right` serve `binary`. Measured operators: thirteen binary,
`!= % && * + - / < <= == > >= ||`, and two unary, `!` and `-`.
-/
structure RawGeneralExpr where
  kind : String
  line : Option Nat := none
  value : Option Json := none
  name : Option String := none
  operator : Option String := none
  operand : Option RawGeneralExpr := none
  left : Option RawGeneralExpr := none
  right : Option RawGeneralExpr := none

deriving instance Lean.FromJson for RawGeneralExpr

/--
A statement node, recursive through both an optional slot and a list.

The five statement kinds are `assign`, `declare`, `send`, `if`, and `for`.
Control flow is read faithfully here and rejected by the elaborator, which is
what makes `control-flow` a `general-v1` positive that stage B declines by name;
stage H then widens the elaborator alone.

`then` and `else` are Lean keywords and are written as guillemet identifiers.
The derived reader maps `«then»` and `«else»` to the JSON keys `then` and `else`,
which was verified by decoding the `control-flow` fixture rather than assumed.

`target` is `Option Json` because `assign` writes a string there and `send`
writes an object. `after` is an expression rather than a number: the exporter
only ever emits an `intLiteral` in the five places it occurs, but the wire format
admits any expression, and whether a non-constant connection delay survives
translation to Lingua Franca is an open question about the target language, not
something this reader should prejudge.

`targetClassName` is supplied by the exporter, which has already resolved the
receiver's class. The elaborator can therefore cross-check a send against the
class table instead of resolving it from scratch.
-/
structure RawGeneralStmt where
  kind : String
  line : Option Nat := none
  target : Option Json := none
  name : Option String := none
  type : Option String := none
  value : Option RawGeneralExpr := none
  messageServer : Option String := none
  targetClassName : Option String := none
  after : Option RawGeneralExpr := none
  arguments : Option (List RawGeneralExpr) := none
  condition : Option RawGeneralExpr := none
  «then» : Option (List RawGeneralStmt) := none
  «else» : Option (List RawGeneralStmt) := none
  init : Option RawGeneralStmt := none
  update : Option RawGeneralStmt := none
  body : Option (List RawGeneralStmt) := none

deriving instance Lean.FromJson for RawGeneralStmt

/--
A message-server or constructor parameter. Measured types: `int` and `boolean`.
-/
structure RawGeneralParameter where
  line : Option Nat := none
  name : String
  type : String
deriving FromJson

/--
A state-variable declaration. Carries no initializer field, which is why "an
initialized state variable" is unrepresentable rather than rejected.
-/
structure RawGeneralStateVariable where
  line : Option Nat := none
  name : String
  type : String
deriving FromJson

/--
A known-rebec declaration: the name a class uses for a peer, and that peer's
class. This is the field whose absence made the external-send layer dead code in
the `globalMultiStorePayload` family, where every actor's binding store was
hardwired empty because no schema could express one.
-/
structure RawGeneralKnownRebec where
  className : String
  line : Option Nat := none
  name : String
deriving FromJson

/--
A class constructor. Unlike every other node it carries no `kind`, and its `line`
is the one field measured as explicitly `null` in the corpus.
-/
structure RawGeneralConstructor where
  body : List RawGeneralStmt
  line : Option Nat := none
  parameters : List RawGeneralParameter
deriving FromJson

/--
A message server. `priority` is `Option Nat` because the exporter writes `null`
for an unannotated server, and `none` is the lowest priority class rather than an
absence of order.
-/
structure RawGeneralMessageServer where
  body : List RawGeneralStmt
  line : Option Nat := none
  name : String
  parameters : List RawGeneralParameter
  priority : Option Nat := none
deriving FromJson

/--
A reactive class.

`queueBound` is carried even though the conditions that consume it, a bounded
queue and overflow freedom, are conditions on executions rather than on syntax
and are outside stage B. Dropping it here would delete it from the pipeline
silently; carrying it costs one field and keeps the later obligation reachable.
-/
structure RawGeneralClass where
  constructor : RawGeneralConstructor
  knownRebecs : List RawGeneralKnownRebec
  line : Option Nat := none
  messageServers : List RawGeneralMessageServer
  name : String
  queueBound : Nat
  stateVariables : List RawGeneralStateVariable
deriving FromJson

/--
One entry of an instance's binding list: the known-rebec name as declared in the
class, the instance bound to it, and that instance's class.

`instance` is a Lean keyword and is written as a guillemet identifier; the
derived reader maps `«instance»` to the JSON key `instance`, verified by decoding
the `two-instances` and `fan-in` fixtures.

Binding order is significant and must never be sorted: it decides the topology.
-/
structure RawGeneralBinding where
  className : String
  «instance» : String
  knownRebec : String
deriving FromJson

/--
An instance from the main block, with its constructor arguments, its bindings,
and its actor-level priority.
-/
structure RawGeneralInstance where
  arguments : List RawGeneralExpr
  bindings : List RawGeneralBinding
  className : String
  line : Option Nat := none
  name : String
  priority : Option Nat := none
deriving FromJson

/--
A whole `general-v1` document.

Unlike the earlier families there is no top-level `className` or `actorName`: a
document describes many classes and many instances, which is the entire point of
the general family and the reason the earlier schemas could not express the
models the paper describes.

List order is significant throughout and must never be sorted. Declaration order
decides same-tag firing order in the Lingua Franca target, and binding order
decides the topology.
-/
structure RawGeneralModel where
  classes : List RawGeneralClass
  family : String
  instances : List RawGeneralInstance
  schemaVersion : Nat
deriving FromJson

end Frontend
end Relico
