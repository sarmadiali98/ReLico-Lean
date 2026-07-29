import Relico.DTR.MultiStorePayloadSyntax

set_option autoImplicit false

namespace Relico
namespace DTR
namespace MultiStorePayloadMessageServerPriority

/--
Local priority order for payload-aware message servers.

Smaller explicit numbers have higher priority. Every explicit priority
precedes `none`. Equal priorities are still representable in the raw
AST, but Option-C correctness theorems will require
`MultiStorePayloadMessageServers.PrioritiesDistinct`.
-/
def PrecedesOrEqual
    (left right :
      DTR.MultiStorePayloadMessageServer) :
    Prop :=
  match left.priority, right.priority with

  | some leftPriority,
    some rightPriority =>
      leftPriority ≤
        rightPriority

  | some _,
    none =>
      True

  | none,
    some _ =>
      False

  | none,
    none =>
      True

instance
    (left right :
      DTR.MultiStorePayloadMessageServer) :
    Decidable
      (PrecedesOrEqual
        left
        right) := by

  unfold PrecedesOrEqual

  cases left.priority <;>
    cases right.priority <;>
    infer_instance

/--
Insert one declaration into a priority-normalized list.
-/
def insert
    (messageServer :
      DTR.MultiStorePayloadMessageServer) :
    List DTR.MultiStorePayloadMessageServer →
    List DTR.MultiStorePayloadMessageServer

  | [] =>
      [messageServer]

  | current :: remaining =>
      if
        PrecedesOrEqual
          messageServer
          current
      then
        messageServer ::
          current ::
          remaining
      else
        current ::
          insert
            messageServer
            remaining

/--
Stable local-priority normalization for payload-aware message servers.
-/
def normalize :
    List DTR.MultiStorePayloadMessageServer →
    List DTR.MultiStorePayloadMessageServer

  | [] =>
      []

  | messageServer :: remaining =>
      insert
        messageServer
        (normalize remaining)

@[simp]
theorem normalize_nil :
    normalize [] =
      ([] :
        List DTR.MultiStorePayloadMessageServer) := by
  rfl

@[simp]
theorem normalize_singleton
    (messageServer :
      DTR.MultiStorePayloadMessageServer) :
    normalize [messageServer] =
      [messageServer] := by
  rfl

end MultiStorePayloadMessageServerPriority
end DTR
end Relico
