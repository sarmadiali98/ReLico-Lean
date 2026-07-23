import Lean.Data.Json

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/--
Version of the parser-independent interchange format used by the
trusted Timed Rebeca frontend bridge.
-/
def bridgeSchemaVersion : Nat :=
  1

/--
Parser-independent expression representation for vertical slice v0.

Expected forms are:

- `intLiteral`, with `value`;
- `stateVar`, with `name`.
-/
structure RawExpr where
  kind : String
  value? : Option Int := none
  name? : Option String := none
  deriving Repr, DecidableEq, FromJson, ToJson

/--
Parser-independent statement representation for vertical slice v0.

Expected forms are:

- `assign`, with `target` and `expression`;
- `selfSend`, with `message` and `delay`.
-/
structure RawStmt where
  kind : String
  target? : Option String := none
  expression? : Option RawExpr := none
  message? : Option String := none
  delay? : Option Nat := none
  deriving Repr, DecidableEq, FromJson, ToJson

/--
Stable parser-bridge representation for the current DTR fragment.

This structure deliberately contains no classes from the existing Java
compiler object model. That prevents the Lean frontend from depending
on parser implementation details.
-/
structure RawModel where
  schemaVersion : Nat
  className : String
  actorName : String
  actorClass : String
  stateVar : String
  messageServer : String
  constructorBody : List RawStmt
  messageServerBody : List RawStmt
  deriving Repr, DecidableEq, FromJson, ToJson

end Frontend
end Relico
