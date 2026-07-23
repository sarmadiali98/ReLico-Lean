import Relico.Common.Name
import Relico.Common.Time
import Relico.Common.Value

set_option autoImplicit false

namespace Relico
namespace LF

/--
Expressions supported by the generated LF subset in vertical slice v0.
-/
inductive Expr where
  | intLiteral : Int → Expr
  | stateVar : VarName → Expr
deriving Repr, DecidableEq, BEq, Inhabited

/--
Statements supported inside generated LF reactions.

An assignment updates reactor state.
A schedule statement schedules a logical action after a delay.
-/
inductive Stmt where
  | assign :
      VarName →
      Expr →
      Stmt
  | schedule :
      ActionName →
      Delay →
      Stmt
deriving Repr, DecidableEq, BEq, Inhabited

abbrev Body := List Stmt

/--
Triggers supported by the generated LF subset.
-/
inductive Trigger where
  | startup
  | logicalAction : ActionName → Trigger
deriving Repr, DecidableEq, BEq, Inhabited

/--
A reaction in the generated LF subset.
-/
structure Reaction where
  name : ReactionName
  trigger : Trigger
  body : Body
deriving Repr, DecidableEq, BEq, Inhabited

/--
The generated reactor corresponding to the single DTR reactive class.

Vertical slice v0 contains one state variable, one logical action,
one startup reaction, and one message reaction.
-/
structure Reactor where
  name : ReactorName
  stateVar : VarName
  logicalAction : ActionName
  startupReaction : Reaction
  messageReaction : Reaction
deriving Repr, DecidableEq, BEq, Inhabited

/--
The generated reactor instance corresponding to the DTR actor instance.
-/
structure ReactorInstance where
  name : ActorName
  reactorName : ReactorName
deriving Repr, DecidableEq, BEq, Inhabited

/--
A complete generated LF program in vertical slice v0.
-/
structure Program where
  reactor : Reactor
  instance : ReactorInstance
deriving Repr, DecidableEq, BEq, Inhabited

end LF
end Relico
