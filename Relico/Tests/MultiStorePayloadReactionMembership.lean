import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadReactionMembership

theorem insertion_preserves_membership
    (candidate messageServer :
      DTR.MultiStorePayloadMessageServer)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    candidate ∈
        DTR.MultiStorePayloadMessageServerPriority.insert
          messageServer
          messageServers ↔
      candidate =
          messageServer ∨
        candidate ∈
          messageServers :=

  DTR.MultiStorePayloadMessageServerPriority.mem_insert_iff
    candidate
    messageServer
    messageServers

theorem normalization_preserves_membership
    (candidate :
      DTR.MultiStorePayloadMessageServer)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    candidate ∈
        DTR.MultiStorePayloadMessageServerPriority.normalize
          messageServers ↔
      candidate ∈
        messageServers :=

  DTR.MultiStorePayloadMessageServerPriority.mem_normalize_iff
    candidate
    messageServers

theorem priority_ordered_preserves_membership
    (candidate :
      DTR.MultiStorePayloadMessageServer)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    candidate ∈
        Translation.priorityOrderedMultiStorePayloadMessageServers
          messageServers ↔
      candidate ∈
        messageServers :=

  Translation.priorityOrderedMultiStorePayloadMessageServers_mem_iff
    candidate
    messageServers

theorem declared_server_generates_reaction
    {messageServer :
      DTR.MultiStorePayloadMessageServer}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hMember :
      messageServer ∈
        messageServers) :
    Translation.compileMultiStorePayloadReaction
          messageServer ∈
        Translation.compileMultiStorePayloadMessageReactions
          messageServers :=

  Translation.compileMultiStorePayloadReaction_mem
    hMember

theorem generated_reaction_has_declared_server
    {reaction :
      LF.MultiStorePayloadReaction}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hMember :
      reaction ∈
        Translation.compileMultiStorePayloadMessageReactions
          messageServers) :
    ∃ messageServer,
      messageServer ∈
          messageServers ∧
        Translation.compileMultiStorePayloadReaction
            messageServer =
          reaction :=

  Translation.mem_compileMultiStorePayloadMessageReactions
    hMember

theorem generated_reaction_inversion_orientation
    {reaction :
      LF.MultiStorePayloadReaction}
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hMember :
      reaction ∈
        Translation.compileMultiStorePayloadMessageReactions
          messageServers) :
    ∃ messageServer,
      messageServer ∈
          messageServers ∧
        reaction =
          Translation.compileMultiStorePayloadReaction
            messageServer := by

  obtain
    ⟨messageServer,
     hServerMember,
     hCompiled⟩ :=
      Translation.mem_compileMultiStorePayloadMessageReactions
        hMember

  exact
    ⟨messageServer,
     hServerMember,
     hCompiled.symm⟩

end MultiStorePayloadReactionMembership
end Tests
end Relico
