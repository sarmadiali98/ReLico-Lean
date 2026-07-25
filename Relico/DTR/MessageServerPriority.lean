import Relico.DTR.Syntax

set_option autoImplicit false

namespace Relico
namespace DTR
namespace MessageServerPriority

/--
The local-priority preorder used for DTR message-server declarations.

The ordering follows the supported legacy policy:

- smaller explicit numbers have higher priority;
- every explicit priority precedes an unannotated declaration;
- two unannotated declarations have equal priority.

Declaration order is handled separately by the stable normalization
algorithm.
-/
def PrecedesOrEqual
    (left right : DTR.MessageServer) :
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
    (left right : DTR.MessageServer) :
    Decidable
      (PrecedesOrEqual
        left
        right) := by

  unfold PrecedesOrEqual

  cases left.priority <;>
    cases right.priority <;>
    infer_instance

theorem precedesOrEqual_refl
    (messageServer : DTR.MessageServer) :
    PrecedesOrEqual
      messageServer
      messageServer := by

  cases hPriority :
      messageServer.priority <;>
    simp [
      PrecedesOrEqual,
      hPriority
    ]

theorem explicit_precedes_unannotated
    {explicitServer unannotatedServer :
      DTR.MessageServer}
    {priority : Nat}
    (hExplicit :
      explicitServer.priority =
        some priority)
    (hUnannotated :
      unannotatedServer.priority =
        none) :
    PrecedesOrEqual
      explicitServer
      unannotatedServer := by

  simp [
    PrecedesOrEqual,
    hExplicit,
    hUnannotated
  ]

theorem lower_numeric_precedes
    {left right : DTR.MessageServer}
    {leftPriority rightPriority : Nat}
    (hLeft :
      left.priority =
        some leftPriority)
    (hRight :
      right.priority =
        some rightPriority)
    (hPriority :
      leftPriority ≤
        rightPriority) :
    PrecedesOrEqual
      left
      right := by

  simpa [
    PrecedesOrEqual,
    hLeft,
    hRight
  ] using
    hPriority

/--
Insert one declaration into an already priority-normalized list.

Insertion occurs before the first declaration of equal or lower
priority. Because `normalize` processes the original list from right to
left, this preserves source declaration order among equal-priority
servers.
-/
def insert
    (messageServer : DTR.MessageServer) :
    List DTR.MessageServer →
    List DTR.MessageServer

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
Stable local-priority normalization of a message-server declaration
list.

The input list remains the source declaration order. This function
produces the scheduling and generated-reaction order.
-/
def normalize :
    List DTR.MessageServer →
    List DTR.MessageServer

  | [] =>
      []

  | messageServer :: remaining =>
      insert
        messageServer
        (normalize remaining)

@[simp]
theorem mem_insert_iff
    (candidate messageServer :
      DTR.MessageServer)
    (messageServers :
      List DTR.MessageServer) :
    candidate ∈
        insert
          messageServer
          messageServers ↔
      candidate =
          messageServer ∨
        candidate ∈
          messageServers := by

  induction messageServers with

  | nil =>
      simp [
        insert
      ]

  | cons current remaining inductionHypothesis =>
      by_cases hOrder :
          PrecedesOrEqual
            messageServer
            current

      · simp [
          insert,
          hOrder
        ]

      · simp [
          insert,
          hOrder,
          inductionHypothesis,
          or_left_comm
        ]

@[simp]
theorem length_insert
    (messageServer : DTR.MessageServer)
    (messageServers :
      List DTR.MessageServer) :
    (insert
      messageServer
      messageServers).length =
      messageServers.length + 1 := by

  induction messageServers with

  | nil =>
      rfl

  | cons current remaining inductionHypothesis =>
      by_cases hOrder :
          PrecedesOrEqual
            messageServer
            current

      · simp [
          insert,
          hOrder
        ]

      · simp [
          insert,
          hOrder,
          inductionHypothesis,
          Nat.add_assoc
        ]

@[simp]
theorem mem_normalize_iff
    (candidate : DTR.MessageServer)
    (messageServers :
      List DTR.MessageServer) :
    candidate ∈
        normalize
          messageServers ↔
      candidate ∈
        messageServers := by

  induction messageServers with

  | nil =>
      simp [
        normalize
      ]

  | cons messageServer remaining inductionHypothesis =>
      simp [
        normalize,
        inductionHypothesis
      ]

@[simp]
theorem length_normalize
    (messageServers :
      List DTR.MessageServer) :
    (normalize
      messageServers).length =
      messageServers.length := by

  induction messageServers with

  | nil =>
      rfl

  | cons messageServer remaining inductionHypothesis =>
      simp [
        normalize,
        inductionHypothesis
      ]

@[simp]
theorem normalize_nil :
    normalize [] =
      ([] : List DTR.MessageServer) := by
  rfl

@[simp]
theorem normalize_singleton
    (messageServer : DTR.MessageServer) :
    normalize [messageServer] =
      [messageServer] := by
  rfl

/--
Priority normalization neither introduces nor removes message-server
names.
-/
theorem name_mem_normalize_iff
    (messageName : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    messageName ∈
        (normalize
          messageServers).map
            (fun messageServer =>
              messageServer.name) ↔
      messageName ∈
        messageServers.map
          (fun messageServer =>
            messageServer.name) := by

  constructor

  · intro hMember

    rcases
        List.mem_map.mp
          hMember
      with
        ⟨messageServer,
         hServerMember,
         hName⟩

    apply
      List.mem_map.mpr

    exact
      ⟨messageServer,
       (mem_normalize_iff
          messageServer
          messageServers).mp
            hServerMember,
       hName⟩

  · intro hMember

    rcases
        List.mem_map.mp
          hMember
      with
        ⟨messageServer,
         hServerMember,
         hName⟩

    apply
      List.mem_map.mpr

    exact
      ⟨messageServer,
       (mem_normalize_iff
          messageServer
          messageServers).mpr
            hServerMember,
       hName⟩

end MessageServerPriority
end DTR
end Relico
