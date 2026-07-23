set_option autoImplicit false

namespace Relico

structure ClassName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

structure ActorName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

structure VarName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

structure MsgName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

structure ReactorName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

structure ReactionName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

structure ActionName where
  value : String
deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString ClassName where
  toString name := name.value

instance : ToString ActorName where
  toString name := name.value

instance : ToString VarName where
  toString name := name.value

instance : ToString MsgName where
  toString name := name.value

instance : ToString ReactorName where
  toString name := name.value

instance : ToString ReactionName where
  toString name := name.value

instance : ToString ActionName where
  toString name := name.value

namespace ClassName

def isValid (name : ClassName) : Prop :=
  name.value ≠ ""

end ClassName

namespace ActorName

def isValid (name : ActorName) : Prop :=
  name.value ≠ ""

end ActorName

namespace VarName

def isValid (name : VarName) : Prop :=
  name.value ≠ ""

end VarName

namespace MsgName

def isValid (name : MsgName) : Prop :=
  name.value ≠ ""

end MsgName

namespace ReactorName

def isValid (name : ReactorName) : Prop :=
  name.value ≠ ""

end ReactorName

namespace ReactionName

def isValid (name : ReactionName) : Prop :=
  name.value ≠ ""

end ReactionName

namespace ActionName

def isValid (name : ActionName) : Prop :=
  name.value ≠ ""

end ActionName

end Relico
