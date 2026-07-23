import Relico.Common.Name
import Relico.Common.Time
import Relico.Common.Value

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Expressions supported by vertical slice v0.

The initial fragment contains integer literals and references to the
single state variable declared by the reactive class.
-/
inductive Expr where
  | intLiteral : Int → Expr
  | stateVar : VarName → Expr
deriving Repr, DecidableEq, BEq, Inhabited

/--
Statements supported by vertical slice v0.

An assignment updates the declared state variable.
A self-send schedules an occurrence of the declared message server
after a nonnegative logical delay.
-/
inductive Stmt where
  | assign :
      VarName →
      Expr →
      Stmt
  | selfSend :
      MsgName →
      Delay →
      Stmt
deriving Repr, DecidableEq, BEq, Inhabited

abbrev Body := List Stmt

/--
The constructor executed when the actor instance is initialized.
-/
structure Constructor where
  body : Body
deriving Repr, DecidableEq, BEq, Inhabited

/--
The single message server supported by vertical slice v0.
-/
structure MessageServer where
  name : MsgName
  body : Body
deriving Repr, DecidableEq, BEq, Inhabited

/--
The single reactive class supported by vertical slice v0.
-/
structure ReactiveClass where
  name : ClassName
  stateVar : VarName
  constructor : Constructor
  messageServer : MessageServer
deriving Repr, DecidableEq, BEq, Inhabited

/--
The single actor instance supported by vertical slice v0.
-/
structure ActorInstance where
  name : ActorName
  className : ClassName
deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete DTR model in vertical slice v0.
-/
structure Model where
  reactiveClass : ReactiveClass
  actor : ActorInstance
deriving Repr, DecidableEq, BEq, Inhabited

end DTR
end Relico
