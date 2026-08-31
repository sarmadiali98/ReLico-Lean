/-
! # The kind-origin invariant of the general family, target side

Milestone C7. **Every pending target event's `kind` is one the translation put there**, and
every statement a running reactor has left to execute would, if it produced an event, produce
one of those kinds too. The invariant is what turns a `.consume`-labelled step's *event* into
the premise package the routing/resolution theorems take — `hReaction`, `hParams`, `hBody` —
without a `message → kind` function anywhere, which is what **F78** forbids.

## Why there is no provenance field, and no message-to-kind function

`LF.GeneralPendingEvent` is unchanged by this module. The event already carries its `kind`, and
the kind is exactly what the resolution theorems match on, so the invariant reads the kind off
the event and quantifies the *origin* existentially. Adding a provenance field would make the
runtime state carry a fact the static layer already proves, and two places for one fact is the
defect class this repository keeps finding.

The same argument is why no function from a DTR message name to an LF event kind is declared.
**F78** measured that one DTR message can be sent from several source sites and that stage E
gives each site its own action, so the map is not a function; every clause below therefore
reasons from the *actual* LF kind plus an existential origin witness, and never from a message
value. Occurrences are never collapsed: nothing here is a `Nodup`, a multiplicity claim, or a
value-uniqueness claim, and duplicate pending events are individually witnessed.

## The two conjuncts, and why the body side is per statement

`GeneralKindOrigin` is the conjunction of an **event** side over `state.pending` and a **body**
side over every statement of every active reactor body. Both are membership-shaped, which is
what makes them transport through α-equivalence's queue permutation and reactor-membership
equivalence for free.

The body side is a predicate on **one statement**, quantified over membership in the body. That
is the trick that makes preservation cheap: every body-consuming τ rule replaces
`statement :: remaining` by `remaining`, and a membership-quantified predicate over a list is
inherited by every tail by `List.mem_cons_of_mem`. No rule has to re-derive anything about the
statements it did not consume, and the rule that *does* consume one reads the new event's origin
straight off that statement's own clause.

## What the public theorems assume, and what they do not

The port half of the event origin needs to know, of the route the runtime resolved, which class
receives it, which message server of that class, and which compiled reactor stands at the receiving
instance. Those are facts about `Translation.routesOf` and `Translation.compileGeneralModel` rather
than about the runtime, and they are **proved here**, not assumed: `GeneralRouteOrigin` names the
per-route bundle and `generalRouteOrigin_of_compile` discharges it from the compilation succeeding
and the routing table being that compilation's own.

Getting there needed five traversal inversions that did not exist in the tree — through `routesOf`,
`routesOfInstances`, `routesOfEntries`, `generalRouteFor` and `generalOutputPortEntriesOf` — and the
`Translation` section below is those inversions and nothing more. The load-bearing discovery is that
the receiver class and message server never have to be re-resolved: `generalOutputPortEntryFor`
resolved them when it built the entry, and `generalRouteFor` refuses to build a route unless the
bound instance's class equals the entry's, so the entry's provenance transfers to the route for free.

**Every public theorem of this module therefore takes only the ordinary eligibility assumptions** —
`model.wellFormed = true` where source structure is needed, `compileGeneralModel model = .ok program`,
and `routesOf model = .ok routes`. `GeneralRouteOrigin` survives as a definition because it is the
seam between the source and target halves of that discharge, and it is applied internally at each of
the four public consumers. A future block-transfer theorem consumes the eligibility assumptions and
inherits no fresh static hypothesis.

None of this assumes route uniqueness, send-site uniqueness, or injectivity of `outputPortNameFor`.
`outputPortNameFor` is not injective (**F48**) and the layer is existential about routes throughout;
the two `Nodup` facts the discharge does use are about *instance names* and *reactor names*, which
the compilation guard decides.
-/
import Relico.LF.GeneralInitialization
import Relico.LF.GeneralAlphaEquivalence
import Relico.Correctness.GeneralCorrespondence

set_option autoImplicit false

namespace Relico

namespace LF

/-!
## The one missing lookup fact

`LF.connectionFrom?` had no lemma of any kind — verified absent under every name. B needs exactly
one: a successful lookup returns a connection that is really in the list and really carries the
source endpoint asked for. Both halves are used, the membership to reach the route behind it and
the endpoint equations to line the recovered route's sender up with the resolving reactor.

Deliberately not a general lookup library. The `Option`-returning lookups of this family each get
the lemmas their callers need and no more — `generalEntryAtSite?` has three, `findReactionForKind?`
has two — and a shared development would have to fix one notion of key equality across functions
that were written with different ones on purpose.
-/

/--
A resolved connection is a member of the connection list, and its source endpoint is the one the
lookup asked for.

Only this direction holds and only this direction is wanted. `connectionFrom?` returns the
**first** match, so the converse is false as soon as two connections share a source endpoint —
which F48's non-injective `outputPortNameFor` permits and which is exactly why B recovers *a*
route rather than *the* route.
-/
theorem connectionFrom?_mem_and_source :
    ∀ (connections : List LF.GeneralConnection)
      (instanceName : ActorName)
      (portName : PortName)
      (connection : LF.GeneralConnection),
      LF.connectionFrom?
          connections
          instanceName
          portName =
        some connection →
      connection ∈ connections ∧
        connection.sourceInstance = instanceName ∧
        connection.sourcePort = portName := by

  intro connections
  induction connections with

  | nil =>
      intro instanceName portName connection hLookup

      simp [
        LF.connectionFrom?
      ] at hLookup

  | cons head remaining inductionHypothesis =>
      intro instanceName portName connection hLookup

      by_cases hInstance :
          head.sourceInstance = instanceName

      · by_cases hPort :
            head.sourcePort = portName

        · rw [
            LF.connectionFrom?,
            if_pos hInstance,
            if_pos hPort
          ] at hLookup

          obtain rfl :=
            Option.some.inj hLookup

          exact
            ⟨List.mem_cons_self,
             hInstance,
             hPort⟩

        · rw [
            LF.connectionFrom?,
            if_pos hInstance,
            if_neg hPort
          ] at hLookup

          obtain ⟨hMember, hSource⟩ :=
            inductionHypothesis
              instanceName
              portName
              connection
              hLookup

          exact
            ⟨List.mem_cons_of_mem
               head
               hMember,
             hSource⟩

      · rw [
          LF.connectionFrom?,
          if_neg hInstance
        ] at hLookup

        obtain ⟨hMember, hSource⟩ :=
          inductionHypothesis
            instanceName
            portName
            connection
            hLookup

        exact
          ⟨List.mem_cons_of_mem
             head
             hMember,
           hSource⟩

end LF

namespace DTR

namespace GeneralModel

/--
A resolved message server is a member of the list, with the name asked for.

`DTR.findMessageServer?` had no lemma; this is the one its consumers here need, in the same shape
`LF.connectionFrom?_mem_and_source` takes above and for the same reason — a lookup that succeeded
has to become a membership before anything can quantify over the list.

Placed before the routing section rather than beside its other DTR neighbours further down, because
the route-provenance ladder is its first consumer and Lean reads a file forwards.
-/
theorem findMessageServer?_mem_and_name :
    ∀ (servers : List DTR.GeneralMessageServer)
      (messageName : MsgName)
      (server : DTR.GeneralMessageServer),
      DTR.findMessageServer?
          servers
          messageName =
        some server →
      server ∈ servers ∧
        server.name = messageName := by

  intro servers
  induction servers with

  | nil =>
      intro messageName server hLookup

      simp [
        DTR.findMessageServer?
      ] at hLookup

  | cons head remaining inductionHypothesis =>
      intro messageName server hLookup

      by_cases hHead :
          head.name = messageName

      · rw [
          DTR.findMessageServer?,
          if_pos hHead
        ] at hLookup

        obtain rfl :=
          Option.some.inj hLookup

        exact
          ⟨List.mem_cons_self,
           hHead⟩

      · rw [
          DTR.findMessageServer?,
          if_neg hHead
        ] at hLookup

        obtain ⟨hMember, hName⟩ :=
          inductionHypothesis
            messageName
            server
            hLookup

        exact
          ⟨List.mem_cons_of_mem
             head
             hMember,
           hName⟩

end GeneralModel
end DTR

namespace Translation

/-!
## Self-send site traversal equations

`selfSendsFromIndex` is declared with the index in the matched position and no equation lemmas,
because until now every consumer unfolded it once. The schedule-origin induction below rewrites
with it four times per step, so the four arms are stated as the directed equations that
induction wants. Each is `rfl`; they exist so that the induction never unfolds the recursion the
equation compiler generated, following `compileGeneralBody_cons_ok_inversion`'s reason for
preferring the three body equations over the `match` behind them.
-/

@[simp]
theorem selfSendsFromIndex_nil
    (bodyKey : GeneralBodyKey)
    (index : Nat) :
    selfSendsFromIndex
        bodyKey
        index
        [] =
      [] := by
  rfl

@[simp]
theorem selfSendsFromIndex_assign
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (target : VarName)
    (value : DTR.GeneralExpr)
    (remaining : DTR.GeneralBody) :
    selfSendsFromIndex
        bodyKey
        index
        (
          .assign
            target
            value ::
          remaining
        ) =
      selfSendsFromIndex
        bodyKey
        (index + 1)
        remaining := by
  rfl

@[simp]
theorem selfSendsFromIndex_trace
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (tag : String)
    (remaining : DTR.GeneralBody) :
    selfSendsFromIndex
        bodyKey
        index
        (
          .trace
            tag ::
          remaining
        ) =
      selfSendsFromIndex
        bodyKey
        (index + 1)
        remaining := by
  rfl

@[simp]
theorem selfSendsFromIndex_send_knownRebec
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (rebec : KnownRebecName)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay)
    (remaining : DTR.GeneralBody) :
    selfSendsFromIndex
        bodyKey
        index
        (
          .send
            (.knownRebec
              rebec)
            message
            arguments
            delay ::
          remaining
        ) =
      selfSendsFromIndex
        bodyKey
        (index + 1)
        remaining := by
  rfl

@[simp]
theorem selfSendsFromIndex_send_selfTarget
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (message : MsgName)
    (arguments : List DTR.GeneralExpr)
    (delay : Delay)
    (remaining : DTR.GeneralBody) :
    selfSendsFromIndex
        bodyKey
        index
        (
          .send
            .selfTarget
            message
            arguments
            delay ::
          remaining
        ) =
      {
        site :=
          {
            body :=
              bodyKey

            index :=
              index
          }

        message :=
          message

        delay :=
          delay
      } ::
        selfSendsFromIndex
          bodyKey
          (index + 1)
          remaining := by
  rfl

/-!
## Site membership, in the introduction direction

`generalRoutesIntoMessageServer` and `generalSelfSendSitesOf` both had only elimination lemmas —
`mem_generalRoutesIntoClass_of_mem_generalRoutesIntoMessageServer` and
`message_of_mem_generalRoutesIntoMessageServer` run *out* of a filtered list. The origin
predicates need to run *into* one: a route the runtime resolved has to be exhibited inside the
filter its receiving message server's reactions were built from, and a self-send site has to be
exhibited inside the filter its action name was built from. Both are the shape
`mem_generalRoutesIntoClass` already has for the weaker filter, and both are proved the same
way, by induction with a case split on the head that matches the definition's own test.
-/

/--
A self-send whose message is the one asked for survives the site filter.
-/
theorem mem_generalSelfSendSitesOf_of_mem
    (message : MsgName)
    (selfSend : GeneralSelfSend) :
    ∀ (allSelfSends : List GeneralSelfSend),
      selfSend ∈ allSelfSends →
      selfSend.message = message →
        selfSend ∈
          generalSelfSendSitesOf
            message
            allSelfSends := by

  intro allSelfSends
  induction allSelfSends with

  | nil =>
      intro hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro hMember hMessage

      by_cases hHead :
          head.message = message

      · rw [
          show
              generalSelfSendSitesOf
                  message
                  (head :: remaining) =
                head ::
                  generalSelfSendSitesOf
                    message
                    remaining from by
            simp [
              generalSelfSendSitesOf,
              hHead
            ],
          List.mem_cons
        ]

        cases List.mem_cons.mp hMember with

        | inl hEqual =>
            exact Or.inl hEqual

        | inr hTail =>
            exact
              Or.inr
                (inductionHypothesis
                  hTail
                  hMessage)

      · rw [
          show
              generalSelfSendSitesOf
                  message
                  (head :: remaining) =
                generalSelfSendSitesOf
                  message
                  remaining from by
            simp [
              generalSelfSendSitesOf,
              hHead
            ]
        ]

        cases List.mem_cons.mp hMember with

        | inl hEqual =>
            rw [hEqual] at hMessage

            exact absurd hMessage hHead

        | inr hTail =>
            exact
              inductionHypothesis
                hTail
                hMessage

/--
Every route survives the filter for its own receiving class and message server.

The introduction counterpart of `mem_generalRoutesIntoClass_of_mem_generalRoutesIntoMessageServer`,
and the one fact B needs about the filter: the runtime resolves a connection, B recovers the
route behind it, and the port reactions that could answer the resulting event are the ones built
from `generalRoutesIntoMessageServer route.receiverClass route.message routes`. Without this the
recovered route is a member of the table and of nothing narrower, which is not what
`Correctness.generalReactionFor?_eq_some_of_portRoute` takes.
-/
theorem mem_generalRoutesIntoMessageServer_self
    (route : GeneralRoute) :
    ∀ (routes : List GeneralRoute),
      route ∈ routes →
        route ∈
          generalRoutesIntoMessageServer
            route.receiverClass
            route.message
            routes := by

  intro routes
  induction routes with

  | nil =>
      intro hMember

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro hMember

      by_cases hHead :
          (head.receiverClass,
            head.message) =
            (route.receiverClass,
              route.message)

      · rw [
          generalRoutesIntoMessageServer_cons_self
            route.receiverClass
            route.message
            head
            remaining
            hHead,
          List.mem_cons
        ]

        cases List.mem_cons.mp hMember with

        | inl hEqual =>
            exact Or.inl hEqual

        | inr hTail =>
            exact
              Or.inr
                (inductionHypothesis
                  hTail)

      · rw [
          generalRoutesIntoMessageServer_cons_of_ne
            route.receiverClass
            route.message
            head
            remaining
            hHead
        ]

        cases List.mem_cons.mp hMember with

        | inl hEqual =>
            rw [hEqual] at hHead

            exact absurd rfl hHead

        | inr hTail =>
            exact
              inductionHypothesis
                hTail

/-!
## Class-level self-send membership

The three lemmas that lift a self-send from one body to its class's canonical list, mirroring
`mem_externalSendsOfClass_of_mem_constructor` and
`mem_externalSendsOfClass_of_mem_messageServer` exactly. They are stated separately for the
constructor and for a message server because `selfSendsOfClass` is an append of those two
sources and a caller holds one or the other, never their union.
-/

/--
A constructor self-send is one of its class's self-sends.
-/
theorem mem_selfSendsOfClass_of_mem_constructor
    {reactiveClass : DTR.GeneralReactiveClass}
    {selfSend : GeneralSelfSend}
    (hMember :
      selfSend ∈
        selfSendsOfBody
          .constructor
          reactiveClass.constructor.body) :
    selfSend ∈
      selfSendsOfClass
        reactiveClass := by

  unfold selfSendsOfClass

  rw [
    List.mem_append
  ]

  exact
    Or.inl
      hMember

/--
One message server's self-sends are among the whole list's self-sends.
-/
theorem mem_selfSendsOfMessageServers_of_mem
    (servers : List DTR.GeneralMessageServer)
    {server : DTR.GeneralMessageServer}
    {selfSend : GeneralSelfSend} :
    server ∈ servers →
    selfSend ∈
      selfSendsOfBody
        (.messageServer
          server.name)
        server.body →
    selfSend ∈
      selfSendsOfMessageServers
        servers := by

  induction servers with

  | nil =>
      intro hServer _

      simp at hServer

  | cons candidate remaining inductionHypothesis =>
      intro hServer hSelfSend

      unfold selfSendsOfMessageServers

      rw [
        List.mem_append
      ]

      rw [
        List.mem_cons
      ] at hServer

      cases hServer with

      | inl hHead =>
          subst hHead

          exact
            Or.inl
              hSelfSend

      | inr hTail =>
          exact
            Or.inr
              (inductionHypothesis
                hTail
                hSelfSend)

/--
A message server's self-sends are among its class's self-sends.
-/
theorem mem_selfSendsOfClass_of_mem_messageServer
    {reactiveClass : DTR.GeneralReactiveClass}
    {server : DTR.GeneralMessageServer}
    {selfSend : GeneralSelfSend}
    (hServer :
      server ∈
        reactiveClass.messageServers)
    (hMember :
      selfSend ∈
        selfSendsOfBody
          (.messageServer
            server.name)
          server.body) :
    selfSend ∈
      selfSendsOfClass
        reactiveClass := by

  unfold selfSendsOfClass

  rw [
    List.mem_append
  ]

  exact
    Or.inr
      (mem_selfSendsOfMessageServers_of_mem
        reactiveClass.messageServers
        hServer
        hMember)

/-!
## Route provenance, from the routing construction

The ladder that discharges what was a carried premise. The claim: every route of `routesOf model`
lands on a declared message server of a declared class, and its receiver instance is one the model
declares of that same class.

**Where the fact lives is not where the sketch expects.** The natural reading is that a route's
`receiverClass` and `message` have to be re-resolved against the model. They do not:
`generalOutputPortEntryFor` resolved them *when it built the entry* — its step 2 through
`DTR.findClass?` and step 3 through `messageServer?` — and it copies `receivingClass.name` and
`send.message` straight into the entry's fields. So class-and-server membership is determined at
entry-construction time, and the route inherits it, because `generalRouteFor` copies `entry.message`
verbatim and *checks* `receiver.className = entry.receiverClass` before it will build a route at all.

That equality check is load-bearing here, and its own docstring already says why it exists: without
it the receiving reactor would get an input port whose payload struct belongs to another reactor. It
is kept for payload soundness; this section is the second thing it buys, and that is the reason the
premise turned out to be discharge­able at all rather than needing a new well-formedness clause.

**No uniqueness of any kind is proved or used below.** Not route uniqueness, not send-site
uniqueness, not injectivity of `outputPortNameFor`. Every lemma is a one-directional membership
statement about the route in hand, which is exactly what the existential shape of
`LF.GeneralRouteOrigin` asks for.
-/

/--
A resolved actor is a member of the instance list.
-/
private theorem findActor?_mem :
    ∀ (instances : List DTR.GeneralActorInstance)
      (actorName : ActorName)
      (actor : DTR.GeneralActorInstance),
      DTR.findActor?
          instances
          actorName =
        some actor →
      actor ∈ instances := by

  intro instances
  induction instances with

  | nil =>
      intro actorName actor hFound

      simp [
        DTR.findActor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro actorName actor hFound

      by_cases hHead :
          head.name = actorName

      · rw [
          DTR.findActor?,
          if_pos hHead
        ] at hFound

        obtain rfl :=
          Option.some.inj hFound

        exact List.mem_cons_self

      · rw [
          DTR.findActor?,
          if_neg hHead
        ] at hFound

        exact
          List.mem_cons_of_mem
            head
            (inductionHypothesis
              actorName
              actor
              hFound)

/--
A resolved class is a member of the class list, with the name asked for.
-/
private theorem findClass?_mem_and_name :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (className : ClassName)
      (reactiveClass : DTR.GeneralReactiveClass),
      DTR.findClass?
          classes
          className =
        some reactiveClass →
      reactiveClass ∈ classes ∧
        reactiveClass.name = className := by

  intro classes
  induction classes with

  | nil =>
      intro className reactiveClass hFound

      simp [
        DTR.findClass?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro className reactiveClass hFound

      by_cases hHead :
          head.name = className

      · rw [
          DTR.findClass?,
          if_pos hHead
        ] at hFound

        obtain rfl :=
          Option.some.inj hFound

        exact
          ⟨List.mem_cons_self,
           hHead⟩

      · rw [
          DTR.findClass?,
          if_neg hHead
        ] at hFound

        obtain ⟨hMember, hName⟩ :=
          inductionHypothesis
            className
            reactiveClass
            hFound

        exact
          ⟨List.mem_cons_of_mem
             head
             hMember,
           hName⟩

/--
The receiver provenance of one resolved output-port entry.

Reads the first three steps of `generalOutputPortEntryFor` off its four-way case split. The
`.error` branches close by the hypothesis becoming `.error … = .ok …`; the payload step is cased on
for the same reason `generalOutputPortEntryFor_ok` cases on it, namely that its refusal is a
different `Except` value rather than a different entry.
-/
private theorem generalOutputPortEntryFor_receiverProvenance
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {allSends : List GeneralExternalSend}
    {send : GeneralExternalSend}
    {ordinal : Nat}
    {entry : GeneralOutputPortEntry}
    (hEntry :
      generalOutputPortEntryFor
          classes
          sendingClass
          allSends
          send
          ordinal =
        .ok entry) :
    ∃ (receivingClass : DTR.GeneralReactiveClass)
      (server : DTR.GeneralMessageServer),
      receivingClass ∈ classes ∧
        receivingClass.name = entry.receiverClass ∧
        server ∈ receivingClass.messageServers ∧
        server.name = entry.message := by

  cases hKnown :
      sendingClass.knownRebec?
        send.knownRebec with

  | none =>
      simp [
        generalOutputPortEntryFor,
        hKnown
      ] at hEntry

  | some declaration =>

      cases hClass :
          DTR.findClass?
            classes
            declaration.className with

      | none =>
          simp [
            generalOutputPortEntryFor,
            hKnown,
            hClass
          ] at hEntry

      | some receivingClass =>

          cases hServer :
              receivingClass.messageServer?
                send.message with

          | none =>
              simp [
                generalOutputPortEntryFor,
                hKnown,
                hClass,
                hServer
              ] at hEntry

          | some receivingServer =>

              cases hPayload :
                  generalPortPayloadFor
                    receivingClass.name
                    send.message
                    receivingServer.parameters with

              | error diagnostic =>
                  simp [
                    generalOutputPortEntryFor,
                    hKnown,
                    hClass,
                    hServer,
                    hPayload
                  ] at hEntry

              | ok portPayload =>

                  -- `generalOutputPortEntryFor_ok` is `private` in
                  -- `Relico/Translation/GeneralRouting.lean` and stays that way, so the four
                  -- resolutions are rewritten into the definition directly rather than through it.
                  simp only [
                    generalOutputPortEntryFor,
                    hKnown,
                    hClass,
                    hServer,
                    hPayload,
                    Except.ok.injEq
                  ] at hEntry

                  subst hEntry

                  obtain ⟨hClassMember, _hClassName⟩ :=
                    findClass?_mem_and_name
                      classes
                      declaration.className
                      receivingClass
                      hClass

                  obtain ⟨hServerMember, hServerName⟩ :=
                    DTR.GeneralModel.findMessageServer?_mem_and_name
                      receivingClass.messageServers
                      send.message
                      receivingServer
                      hServer

                  exact
                    ⟨receivingClass,
                     receivingServer,
                     hClassMember,
                     rfl,
                     hServerMember,
                     hServerName⟩

/--
Every entry of a resolved environment carries its receiver provenance.
-/
private theorem generalOutputPortEntriesOf_receiverProvenance
    (classes : List DTR.GeneralReactiveClass)
    (sendingClass : DTR.GeneralReactiveClass)
    (allSends : List GeneralExternalSend) :
    ∀ (numbered : List (GeneralExternalSend × Nat))
      (env : GeneralOutputPortEnv),
      generalOutputPortEntriesOf
          classes
          sendingClass
          allSends
          numbered =
        .ok env →
      ∀ entry ∈ env,
        ∃ (receivingClass : DTR.GeneralReactiveClass)
          (server : DTR.GeneralMessageServer),
          receivingClass ∈ classes ∧
            receivingClass.name = entry.receiverClass ∧
            server ∈ receivingClass.messageServers ∧
            server.name = entry.message := by

  intro numbered
  induction numbered with

  | nil =>
      intro env hEntries entry hMember

      simp [
        generalOutputPortEntriesOf
      ] at hEntries

      subst hEntries

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro env hEntries entry hMember

      rcases head with
        ⟨send, ordinal⟩

      cases hHead :
          generalOutputPortEntryFor
            classes
            sendingClass
            allSends
            send
            ordinal with

      | error diagnostic =>
          simp [
            generalOutputPortEntriesOf,
            hHead
          ] at hEntries

      | ok headEntry =>

          cases hTail :
              generalOutputPortEntriesOf
                classes
                sendingClass
                allSends
                remaining with

          | error diagnostic =>
              simp [
                generalOutputPortEntriesOf,
                hHead,
                hTail
              ] at hEntries

          | ok tailEntries =>

              rw [
                show
                    generalOutputPortEntriesOf
                        classes
                        sendingClass
                        allSends
                        ((send, ordinal) :: remaining) =
                      .ok
                        (headEntry ::
                          tailEntries) from by
                  simp [
                    generalOutputPortEntriesOf,
                    hHead,
                    hTail
                  ]
              ] at hEntries

              obtain rfl :=
                Except.ok.inj
                  hEntries.symm

              cases List.mem_cons.mp hMember with

              | inl hHere =>
                  subst hHere

                  exact
                    generalOutputPortEntryFor_receiverProvenance
                      hHead

              | inr hThere =>
                  exact
                    inductionHypothesis
                      tailEntries
                      hTail
                      entry
                      hThere

/--
Every entry of a class's output-port environment carries its receiver provenance.

`outputPortEnvOf` is `generalOutputPortEntriesOf` at the class's own send list, so this is the
previous lemma with one `unfold`. It exists separately because every consumer holds the
`outputPortEnvOf` spelling — that is what `routesOfInstances` produces — and unfolding at each of
them would be the same line three times.
-/
private theorem outputPortEnvOf_receiverProvenance
    {classes : List DTR.GeneralReactiveClass}
    {sendingClass : DTR.GeneralReactiveClass}
    {env : GeneralOutputPortEnv}
    (hEnv :
      outputPortEnvOf
          classes
          sendingClass =
        .ok env) :
    ∀ entry ∈ env,
      ∃ (receivingClass : DTR.GeneralReactiveClass)
        (server : DTR.GeneralMessageServer),
        receivingClass ∈ classes ∧
          receivingClass.name = entry.receiverClass ∧
          server ∈ receivingClass.messageServers ∧
          server.name = entry.message := by

  unfold outputPortEnvOf at hEnv

  exact
    generalOutputPortEntriesOf_receiverProvenance
      classes
      sendingClass
      (externalSendsOfClass
        sendingClass)
      (numberedExternalSendsOfClass
        sendingClass)
      env
      hEnv

/--
One route's receiver provenance, from the entry it was resolved from.

`generalRouteFor` copies `entry.message` into `route.message` and sets
`route.receiverClass := receiver.className`, and it only builds a route once
`receiver.className = entry.receiverClass` holds — so the entry's provenance transfers to the route,
and the resolved receiver instance is exhibited at the same time. The three refusal branches close
the way the definition's own docstring says they do.
-/
private theorem generalRouteFor_receiverProvenance
    {model : DTR.GeneralModel}
    {actor : DTR.GeneralActorInstance}
    {entry : GeneralOutputPortEntry}
    {route : GeneralRoute}
    (hRoute :
      generalRouteFor
          model
          actor
          entry =
        .ok route) :
    route.message = entry.message ∧
      route.receiverClass = entry.receiverClass ∧
      ∃ receiver ∈ model.instances,
        receiver.name = route.receiverInstance ∧
          receiver.className = route.receiverClass := by

  cases hBinding :
      Store.lookup
        actor.bindings
        entry.knownRebec with

  | none =>
      simp [
        generalRouteFor,
        hBinding
      ] at hRoute

  | some receiverInstance =>

      cases hActor :
          model.actor? receiverInstance with

      | none =>
          simp [
            generalRouteFor,
            hBinding,
            hActor
          ] at hRoute

      | some receiver =>

          by_cases hClassMatch :
              receiver.className = entry.receiverClass

          · rw [
              show
                  generalRouteFor
                      model
                      actor
                      entry =
                    .ok
                      {
                        senderInstance :=
                          actor.name

                        senderClass :=
                          actor.className

                        site :=
                          entry.site

                        knownRebec :=
                          entry.knownRebec

                        message :=
                          entry.message

                        receiverInstance :=
                          receiver.name

                        receiverClass :=
                          receiver.className

                        outputPort :=
                          entry.outputPort

                        payload :=
                          entry.payload

                        delay :=
                          entry.delay
                      } from by
                simp [
                  generalRouteFor,
                  hBinding,
                  hActor,
                  hClassMatch
                ]
            ] at hRoute

            obtain rfl :=
              Except.ok.inj
                hRoute.symm

            refine
              ⟨rfl,
               hClassMatch,
               receiver,
               findActor?_mem
                 model.instances
                 receiverInstance
                 receiver
                 (by
                   unfold DTR.GeneralModel.actor? at hActor
                   exact hActor),
               rfl,
               rfl⟩

          · simp [
              generalRouteFor,
              hBinding,
              hActor,
              hClassMatch
            ] at hRoute

/-!
### Route membership inversion

Two inversions, one per level of the routing recursion, both in the direction no lemma in the tree
went: out of a successful table and a route in it, back to the construction step that produced it.
The audit recorded that neither `routesOfEntries_*` nor `generalRouteFor_*` existed, and these are
the two it named.

They stay `private`. Their only plausible consumer is the discharger below, and a public route
inversion would invite exactly the per-site reasoning the non-uniqueness note above rules out.
-/

/--
A route of one instance's table came from an entry of that instance's environment.
-/
private theorem mem_of_routesOfEntries
    (model : DTR.GeneralModel)
    (actor : DTR.GeneralActorInstance) :
    ∀ (env : GeneralOutputPortEnv)
      (routes : List GeneralRoute),
      routesOfEntries
          model
          actor
          env =
        .ok routes →
      ∀ route ∈ routes,
        ∃ entry ∈ env,
          generalRouteFor
              model
              actor
              entry =
            .ok route := by

  intro env
  induction env with

  | nil =>
      intro routes hRoutes route hMember

      simp [
        routesOfEntries
      ] at hRoutes

      subst hRoutes

      cases hMember

  | cons entry remaining inductionHypothesis =>
      intro routes hRoutes route hMember

      cases hHead :
          generalRouteFor
            model
            actor
            entry with

      | error diagnostic =>
          simp [
            routesOfEntries,
            hHead
          ] at hRoutes

      | ok headRoute =>

          cases hTail :
              routesOfEntries
                model
                actor
                remaining with

          | error diagnostic =>
              simp [
                routesOfEntries,
                hHead,
                hTail
              ] at hRoutes

          | ok tailRoutes =>

              rw [
                show
                    routesOfEntries
                        model
                        actor
                        (entry :: remaining) =
                      .ok
                        (headRoute ::
                          tailRoutes) from by
                  simp [
                    routesOfEntries,
                    hHead,
                    hTail
                  ]
              ] at hRoutes

              obtain rfl :=
                Except.ok.inj
                  hRoutes.symm

              cases List.mem_cons.mp hMember with

              | inl hHere =>
                  subst hHere

                  exact
                    ⟨entry,
                     List.mem_cons_self,
                     hHead⟩

              | inr hThere =>
                  obtain ⟨tailEntry, hTailEntry, hTailRoute⟩ :=
                    inductionHypothesis
                      tailRoutes
                      hTail
                      route
                      hThere

                  exact
                    ⟨tailEntry,
                     List.mem_cons_of_mem
                       entry
                       hTailEntry,
                     hTailRoute⟩

/--
A route of a multi-instance table came from one instance's environment entry.

Uses `routesOfInstances_cons_inv`, which already exhibits the four successes of one `cons` step, so
the induction never unfolds `routesOfInstances` itself.
-/
private theorem mem_of_routesOfInstances
    (model : DTR.GeneralModel) :
    ∀ (instances : List DTR.GeneralActorInstance)
      (routes : List GeneralRoute),
      routesOfInstances
          model
          instances =
        .ok routes →
      ∀ route ∈ routes,
        ∃ (actor : DTR.GeneralActorInstance)
          (sendingClass : DTR.GeneralReactiveClass)
          (env : GeneralOutputPortEnv)
          (entry : GeneralOutputPortEntry),
          actor ∈ instances ∧
            model.class? actor.className =
              some sendingClass ∧
            outputPortEnvOf
                model.classes
                sendingClass =
              .ok env ∧
            entry ∈ env ∧
            generalRouteFor
                model
                actor
                entry =
              .ok route := by

  intro instances
  induction instances with

  | nil =>
      intro routes hRoutes route hMember

      simp [
        routesOfInstances
      ] at hRoutes

      subst hRoutes

      cases hMember

  | cons actor remaining inductionHypothesis =>
      intro routes hRoutes route hMember

      obtain
          ⟨sendingClass,
           env,
           headRoutes,
           tailRoutes,
           hClass,
           hEnv,
           hHead,
           hTail,
           hSplit⟩ :=
        routesOfInstances_cons_inv
          model
          actor
          remaining
          routes
          hRoutes

      subst hSplit

      cases List.mem_append.mp hMember with

      | inl hHere =>
          obtain ⟨entry, hEntry, hRoute⟩ :=
            mem_of_routesOfEntries
              model
              actor
              env
              headRoutes
              hHead
              route
              hHere

          exact
            ⟨actor,
             sendingClass,
             env,
             entry,
             List.mem_cons_self,
             hClass,
             hEnv,
             hEntry,
             hRoute⟩

      | inr hThere =>
          obtain
              ⟨tailActor,
               tailClass,
               tailEnv,
               tailEntry,
               hTailActor,
               hTailClass,
               hTailEnv,
               hTailEntry,
               hTailRoute⟩ :=
            inductionHypothesis
              tailRoutes
              hTail
              route
              hThere

          exact
            ⟨tailActor,
             tailClass,
             tailEnv,
             tailEntry,
             List.mem_cons_of_mem
               actor
               hTailActor,
             hTailClass,
             hTailEnv,
             hTailEntry,
             hTailRoute⟩

/--
**Route membership inversion, at the model level.** Every route of `routesOf model` names a declared
class as its receiver class, one of that class's declared message servers as its message, and an
instance the model declares of that class as its receiver instance.

The three static facts `LF.GeneralRouteOrigin` needs about the *source* side, with the target side
left to the discharger. Composing the two inversions with the two provenance lemmas is the whole
proof; the only step worth naming is `mem_priorityOrderedInstances_iff`, which is what turns
membership in the walked order into membership in the declared order — the priority sort is a
permutation and nothing here depends on which order it produced.
-/
theorem routeProvenance_of_routesOf
    {model : DTR.GeneralModel}
    {routes : List GeneralRoute}
    (hRoutes :
      routesOf model =
        .ok routes) :
    ∀ route ∈ routes,
      ∃ (receivingClass : DTR.GeneralReactiveClass)
        (server : DTR.GeneralMessageServer)
        (receiver : DTR.GeneralActorInstance),
        receivingClass ∈ model.classes ∧
          receivingClass.name = route.receiverClass ∧
          server ∈ receivingClass.messageServers ∧
          server.name = route.message ∧
          receiver ∈ model.instances ∧
          receiver.name = route.receiverInstance ∧
          receiver.className = route.receiverClass := by

  intro route hMember

  unfold routesOf at hRoutes

  obtain
      ⟨actor,
       sendingClass,
       env,
       entry,
       _hActor,
       _hClass,
       hEnv,
       hEntry,
       hRoute⟩ :=
    mem_of_routesOfInstances
      model
      (priorityOrderedInstances
        model)
      routes
      hRoutes
      route
      hMember

  obtain
      ⟨receivingClass,
       server,
       hClassMember,
       hClassName,
       hServerMember,
       hServerName⟩ :=
    outputPortEnvOf_receiverProvenance
      hEnv
      entry
      hEntry

  obtain
      ⟨hMessage,
       hReceiverClass,
       receiver,
       hReceiverMember,
       hReceiverName,
       hReceiverClassName⟩ :=
    generalRouteFor_receiverProvenance
      hRoute

  refine
    ⟨receivingClass,
     server,
     receiver,
     hClassMember,
     ?_,
     hServerMember,
     ?_,
     hReceiverMember,
     hReceiverName,
     hReceiverClassName⟩

  · rw [
      hReceiverClass,
      hClassName
    ]

  · rw [
      hMessage,
      hServerName
    ]

/-!
### The compiled reactor of a declared class

The target half. `compileGeneralReactiveClasses_startupBody` walks reactor-to-class; this walks
class-to-reactor, which no lemma did. Cased directly on the definition rather than through
`exists_of_compileGeneralReactiveClasses_cons_ok`, which is `private` in
`Relico/Translation/GeneralBasic.lean` and stays that way.
-/

/--
Every class of a successfully compiled class list has a compiled reactor in the result.
-/
private theorem exists_reactor_of_mem_compileGeneralReactiveClasses
    (allClasses : List DTR.GeneralReactiveClass)
    (routes : List GeneralRoute) :
    ∀ (classes : List DTR.GeneralReactiveClass)
      (compiled : List LF.GeneralReactor),
      compileGeneralReactiveClasses
          allClasses
          routes
          classes =
        .ok compiled →
      ∀ reactiveClass ∈ classes,
        ∃ reactor ∈ compiled,
          compileGeneralReactiveClass
              allClasses
              routes
              reactiveClass =
            .ok reactor := by

  intro classes
  induction classes with

  | nil =>
      intro compiled hCompiled reactiveClass hMember

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro compiled hCompiled reactiveClass hMember

      cases hHead :
          compileGeneralReactiveClass
            allClasses
            routes
            head with

      | error diagnostic =>
          rw [
            compileGeneralReactiveClasses_cons_error_head
              hHead
          ] at hCompiled

          simp at hCompiled

      | ok headReactor =>

          cases hTail :
              compileGeneralReactiveClasses
                allClasses
                routes
                remaining with

          | error diagnostic =>
              rw [
                compileGeneralReactiveClasses_cons_error_tail
                  hHead
                  hTail
              ] at hCompiled

              simp at hCompiled

          | ok tailReactors =>

              rw [
                compileGeneralReactiveClasses_cons_ok
                  hHead
                  hTail
              ] at hCompiled

              obtain rfl :=
                Except.ok.inj
                  hCompiled.symm

              cases List.mem_cons.mp hMember with

              | inl hHere =>
                  subst hHere

                  exact
                    ⟨headReactor,
                     List.mem_cons_self,
                     hHead⟩

              | inr hThere =>
                  obtain ⟨tailReactor, hTailMember, hTailCompiled⟩ :=
                    inductionHypothesis
                      tailReactors
                      hTail
                      reactiveClass
                      hThere

                  exact
                    ⟨tailReactor,
                     List.mem_cons_of_mem
                       headReactor
                       hTailMember,
                     hTailCompiled⟩

/--
Every class a compiled model declares has a reactor in the compiled program, compiled from it.

The model-level form, stated at the same `routes` the program was built with so that the reactor it
returns is the one the routing-dependent theorems talk about.
-/
theorem exists_reactor_of_mem_classes
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List GeneralRoute}
    (hCompiled :
      compileGeneralModel model =
        .ok program)
    (hRoutes :
      routesOf model =
        .ok routes) :
    ∀ reactiveClass ∈ model.classes,
      ∃ reactor ∈ program.reactors,
        compileGeneralReactiveClass
            model.classes
            routes
            reactiveClass =
          .ok reactor := by

  intro reactiveClass hClass

  -- `exists_of_compileGeneralModel_ok` is `private`, so the one `cases` it would have supplied is
  -- done here off the three public equations. The guard is transparent to shape, which is what
  -- `eq_of_guardGeneralProgram_ok` says and what makes the reactor list readable off the assembly.
  cases hClasses :
      compileGeneralReactiveClasses
        model.classes
        routes
        model.classes with

  | error diagnostic =>
      rw [
        compileGeneralModel_error_classes
          hRoutes
          hClasses
      ] at hCompiled

      simp at hCompiled

  | ok compiledReactors =>

      rw [
        compileGeneralModel_ok
          hRoutes
          hClasses
      ] at hCompiled

      obtain ⟨reactor, hMember, hReactor⟩ :=
        exists_reactor_of_mem_compileGeneralReactiveClasses
          model.classes
          routes
          model.classes
          compiledReactors
          hClasses
          reactiveClass
          hClass

      refine
        ⟨reactor,
         ?_,
         hReactor⟩

      rw [
        ← eq_of_guardGeneralProgram_ok
            hCompiled,
        assembleGeneralProgram_reactors
      ]

      exact hMember

/-!
## B — the connection-to-route bridge

**This recovers *a* route, not *the* route of the send site, and that is the strongest true
statement.** The temptation is to conclude that the connection the runtime followed is the one
emitted for the very send site whose `setPort` statement produced it. It is not provable:
`LF.connectionFrom?` returns the **first** connection with a matching source endpoint, and
`outputPortNameFor` is not injective — `Relico/Translation/NameGeneration.lean` says so on the
function itself and finding **F48** measured it on translation output — so two distinct send sites
of one instance can carry one output port name, emit two connections with one source endpoint, and
the lookup will answer with whichever came first in route order. `targetEndpointsUnique` does not
help: it constrains *target* endpoints, and it is a guard check rather than a construction fact
(F49).

The existential absorbs the gap. The event-origin predicate below quantifies its receiving class
and message server existentially, so what it needs of the resolved connection is that *some* route
of the table produced it — whichever route that is, the event's `.inputPort connection.targetPort`
is that route's own input port, its target is that route's receiver instance, and the route sits in
the filter its receiver's port reactions were built from. Nothing downstream asks which send site
the route came from, and adding a per-site uniqueness claim here would be adding a false one.
-/

/--
**B.** Every connection of a compiled program is the connection of some route of that program's
routing table, and the route agrees with the connection on all four endpoints and the delay.

The composition is short because both halves are equations rather than searches:
`compileGeneralModel_connections` pins the connection list to `generalConnectionsOf routes`,
`generalConnectionsOf` is `routes.map generalConnectionOf`, so membership in the list is a
`List.mem_map` preimage, and `generalConnectionOf`'s five fields are definitional.

Stated over `route ∈ routes` with the four field equations spelled out rather than as
`connection = generalConnectionOf route`, because every consumer wants the fields and the
structure equation would make each of them unfold the same definition. The `routesOf` equation is
returned too, since the route filter a consumer applies has to be applied to the *same* table.
-/
theorem exists_route_of_connection_mem
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {connection : LF.GeneralConnection}
    (hCompiled :
      compileGeneralModel model =
        .ok program)
    (hMember :
      connection ∈ program.connections) :
    ∃ (routes : List GeneralRoute)
      (route : GeneralRoute),
      routesOf model =
          .ok routes ∧
        route ∈ routes ∧
        connection.sourceInstance = route.senderInstance ∧
        connection.sourcePort = route.outputPort ∧
        connection.targetInstance = route.receiverInstance ∧
        connection.targetPort =
          generalInputPortOfRoute
            route ∧
        connection.delay = route.delay := by

  obtain ⟨routes, hRoutes, hConnections⟩ :=
    compileGeneralModel_connections
      hCompiled

  rw [
    hConnections
  ] at hMember

  unfold generalConnectionsOf at hMember

  obtain ⟨route, hRouteMember, hConnectionEq⟩ :=
    List.mem_map.mp hMember

  subst hConnectionEq

  exact
    ⟨routes,
     route,
     hRoutes,
     hRouteMember,
     rfl,
     rfl,
     rfl,
     rfl,
     rfl⟩

/--
**B, in the form the `setPort` rule hands over.** A connection the runtime resolved from a sending
instance and an output port is the connection of some route whose receiver is the event's target,
whose input port is the event's kind, and which survives the filter for its own receiving class and
message server.

The last conjunct is the one the resolution corollary consumes:
`Correctness.generalReactionFor?_eq_some_of_portRoute` asks for
`route ∈ generalRoutesIntoMessageServer reactiveClass.name server.name routes` where
`reactiveClass` and `server` are the receiving class and message server, and
`mem_generalRoutesIntoMessageServer_self` supplies it at the route's own pair. Which class and
which server those *are* is a fact about the model, packaged as `LF.GeneralRouteOrigin` and proved
by `LF.generalRouteOrigin_of_compile`, because it is not recoverable from the connection alone.
-/
theorem exists_route_of_connectionFrom?
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {instanceName : ActorName}
    {portName : PortName}
    {connection : LF.GeneralConnection}
    (hCompiled :
      compileGeneralModel model =
        .ok program)
    (hConnection :
      LF.connectionFrom?
          program.connections
          instanceName
          portName =
        some connection) :
    ∃ (routes : List GeneralRoute)
      (route : GeneralRoute),
      routesOf model =
          .ok routes ∧
        route ∈ routes ∧
        route.senderInstance = instanceName ∧
        route.outputPort = portName ∧
        connection.targetInstance = route.receiverInstance ∧
        connection.targetPort =
          generalInputPortOfRoute
            route ∧
        route ∈
          generalRoutesIntoMessageServer
            route.receiverClass
            route.message
            routes := by

  obtain ⟨hMember, hSourceInstance, hSourcePort⟩ :=
    LF.connectionFrom?_mem_and_source
      program.connections
      instanceName
      portName
      connection
      hConnection

  obtain
      ⟨routes,
       route,
       hRoutes,
       hRouteMember,
       hSender,
       hOutputPort,
       hTargetInstance,
       hTargetPort,
       _hDelay⟩ :=
    exists_route_of_connection_mem
      hCompiled
      hMember

  refine
    ⟨routes,
     route,
     hRoutes,
     hRouteMember,
     ?_,
     ?_,
     hTargetInstance,
     hTargetPort,
     mem_generalRoutesIntoMessageServer_self
       route
       routes
       hRouteMember⟩

  · rw [
      ← hSender,
      hSourceInstance
    ]

  · rw [
      ← hOutputPort,
      hSourcePort
    ]

/-!
## A — compiled-body schedule origin

The static half of the action side. Mirrors the `setPort` pair
`compileGeneralStmt_setPort_inversion` / `compileGeneralBody_setPortNames_provenance` in
`Relico/Translation/GeneralBasic.lean` statement for statement, and deliberately reuses their
index bookkeeping rather than introducing a second indexing framework: the head statement sits at
`index`, everything the tail contributes comes from `index + 1` or later, and the site traversal
`selfSendsFromIndex` advances in step because both functions advance once per statement whatever
the statement is.

The one asymmetry with the port half is that this needs **no environment lookup**.
`compileGeneralStmt_send_selfTarget` is an unconditional equation — a self-send compiles to a
`.schedule` carrying `generalActionNameAtSite context.selfSends ⟨context.bodyKey, index⟩ message`
whether or not any port was resolved — so the induction never has to case on
`generalEntryAtSite?`, and no site-totality fact is consumed.
-/

/--
A compiled `.schedule` came from a self-send at *this* site, and carries the action name the
site numbering put there.

The `.schedule` constructor has exactly one producing arm in `compileGeneralStmt`, the
`.send .selfTarget` one, so the content of the lemma is that the other three arms cannot produce
it: `.assign` and `.trace` compile to their own constructors, and an external send compiles to
`.setPort` or refuses. The external arm still needs a case split on `generalEntryAtSite?`, because
its refusal branch is a different `Except` value rather than a different statement.

The site is built here rather than taken as an argument, for the reason
`compileGeneralStmt_send_knownRebec_ok` gives for doing the same: it is the *statement's* own
position, and a caller free to pass another one could satisfy this lemma while talking about a
different statement.
-/
private theorem compileGeneralStmt_schedule_inversion
    {env : GeneralOutputPortEnv}
    {context : GeneralBodyContext}
    {index : Nat}
    {statement : DTR.GeneralStmt}
    {actionName : ActionName}
    {arguments : List LF.GeneralExpr}
    {delay : Delay}
    (hStatement :
      compileGeneralStmt
          env
          context
          index
          statement =
        .ok
          (.schedule
            actionName
            arguments
            delay)) :
    ∃ (message : MsgName)
      (sourceArguments : List DTR.GeneralExpr)
      (sourceDelay : Delay),
      statement =
          .send
            .selfTarget
            message
            sourceArguments
            sourceDelay ∧
      actionName =
        generalActionNameAtSite
          context.selfSends
          {
            body :=
              context.bodyKey

            index :=
              index
          }
          message := by

  cases statement with

  | assign target value =>
      simp [
        compileGeneralStmt
      ] at hStatement

  | trace tag =>
      simp [
        compileGeneralStmt
      ] at hStatement

  | send target message sourceArguments sourceDelay =>

      cases target with

      | selfTarget =>
          simp only [
            compileGeneralStmt,
            Except.ok.injEq,
            LF.GeneralStmt.schedule.injEq
          ] at hStatement

          exact
            ⟨message,
             sourceArguments,
             sourceDelay,
             rfl,
             hStatement.left.symm⟩

      | knownRebec rebec =>

          cases hEntry :
              generalEntryAtSite?
                env
                {
                  body :=
                    context.bodyKey

                  index :=
                    index
                } with

          | none =>
              simp [
                compileGeneralStmt,
                hEntry
              ] at hStatement

          | some entry =>
              simp [
                compileGeneralStmt,
                hEntry
              ] at hStatement

/--
A self-send site of a body's tail is a self-send site of the body.

The site-traversal counterpart of `List.mem_cons_of_mem`, and what lets the induction below
return a witness in the *whole* body's site list after obtaining one in the tail's. Four arms
rather than a wildcard, matching `selfSendsFromIndex`'s own refusal to use one: the three
non-self-send arms leave the list untouched, the self-send arm prepends, and a fifth statement
constructor should break this proof loudly.
-/
theorem mem_selfSendsFromIndex_cons_of_mem
    (bodyKey : GeneralBodyKey)
    (index : Nat)
    (statement : DTR.GeneralStmt)
    (remaining : DTR.GeneralBody)
    {selfSend : GeneralSelfSend}
    (hMember :
      selfSend ∈
        selfSendsFromIndex
          bodyKey
          (index + 1)
          remaining) :
    selfSend ∈
      selfSendsFromIndex
        bodyKey
        index
        (statement :: remaining) := by

  cases statement with

  | assign target value =>
      rw [
        selfSendsFromIndex_assign
      ]

      exact hMember

  | trace tag =>
      rw [
        selfSendsFromIndex_trace
      ]

      exact hMember

  | send target message arguments delay =>

      cases target with

      | selfTarget =>
          rw [
            selfSendsFromIndex_send_selfTarget
          ]

          exact
            List.mem_cons_of_mem
              _
              hMember

      | knownRebec rebec =>
          rw [
            selfSendsFromIndex_send_knownRebec
          ]

          exact hMember

/--
**A.** Every action a compiled body schedules was named by a self-send site of that body, at or
after the index the compilation started from.

The theorem the action side of the kind-origin invariant rests on. Read in the direction the
invariant uses it: a `.schedule` statement sitting in a reactor's active body is a *witness* that
the class has a self-send site whose generated action name is the one the statement carries, so the
event the `schedule` rule would enqueue has its origin already, with no name analysis at run time
and no appeal to the compiler's code.

The `index ≤ selfSend.site.index` conjunct is carried for the same reason the port half carries
it — it is what a positional argument would need — and is proved by the same `omega` step off the
recursion. Nothing in this milestone consumes it; it is cheaper to state than to add later, and
dropping it would make the two halves of the provenance pair differ in shape for no reason.

Quantified over the three `.schedule` components rather than over a name-extracting function,
unlike `compileGeneralBody_setPortNames_provenance`'s `LF.setPortNamesOfBody`. That function
exists because `docs/STAGE_E_DESIGN.md` §10.2 owes a `Nodup` claim about the *list* of set ports;
no claim here is about a list of action names, so a second extraction function would be a
definition with one caller.
-/
theorem compileGeneralBody_schedule_provenance
    (env : GeneralOutputPortEnv)
    (context : GeneralBodyContext) :
    ∀ (statements : DTR.GeneralBody)
      (index : Nat)
      (compiled : LF.GeneralBody),
      compileGeneralBody
          env
          context
          index
          statements =
        .ok compiled →
      ∀ (actionName : ActionName)
        (arguments : List LF.GeneralExpr)
        (delay : Delay),
        LF.GeneralStmt.schedule
            actionName
            arguments
            delay ∈
          compiled →
        ∃ (selfSend : GeneralSelfSend),
          selfSend ∈
            selfSendsFromIndex
              context.bodyKey
              index
              statements ∧
          index ≤ selfSend.site.index ∧
          actionName =
            generalActionNameAtSite
              context.selfSends
              selfSend.site
              selfSend.message := by

  intro statements
  induction statements with

  | nil =>
      intro index compiled hCompiled actionName arguments delay hMember

      rw [
        compileGeneralBody_nil
      ] at hCompiled

      injection hCompiled with hEqual

      subst hEqual

      cases hMember

  | cons statement remaining inductionHypothesis =>
      intro index compiled hCompiled actionName arguments delay hMember

      obtain
          ⟨compiledStatement,
           compiledRemaining,
           hStatement,
           hRemaining,
           hShape⟩ :=
        compileGeneralBody_cons_ok_inversion
          hCompiled

      subst hShape

      cases List.mem_cons.mp hMember with

      | inl hHere =>

          rw [
            ← hHere
          ] at hStatement

          obtain
              ⟨message,
               sourceArguments,
               sourceDelay,
               hSource,
               hName⟩ :=
            compileGeneralStmt_schedule_inversion
              hStatement

          subst hSource

          rw [
            selfSendsFromIndex_send_selfTarget
          ]

          exact
            ⟨{
               site :=
                 {
                   body :=
                     context.bodyKey

                   index :=
                     index
                 }

               message :=
                 message

               delay :=
                 sourceDelay
             },
             List.mem_cons_self,
             Nat.le_refl index,
             hName⟩

      | inr hThere =>

          obtain ⟨selfSend, hSite, hIndex, hName⟩ :=
            inductionHypothesis
              (index + 1)
              compiledRemaining
              hRemaining
              actionName
              arguments
              delay
              hThere

          exact
            ⟨selfSend,
             mem_selfSendsFromIndex_cons_of_mem
               context.bodyKey
               index
               statement
               remaining
               hSite,
             by omega,
             hName⟩

end Translation

namespace Store

/--
Every binding of an updated store is either the new binding or an old one.

`Store.update` replaces the first binding for its key and appends when the key is absent, so
this is the only direction that holds: the *old* binding at the key is gone, which is what makes
the converse false and what makes this lemma enough. Every body-consuming target rule rebuilds
`state.reactors` with one `update`, and the kind-origin invariant is quantified over membership,
so this is exactly the step from "a reactor of the successor state" to "the updated reactor, or a
reactor of the predecessor".

Declared here by reopening the namespace rather than in `Relico/Common/Store.lean`, following
`Relico/LF/PendingNotPast.lean`'s reopening of `namespace Tag` — the store module holds the
lemmas its own consumers needed, and adding one from outside keeps one name for one convention
without rebuilding the module's import closure.
-/
theorem mem_update
    {Key : Type}
    {Value : Type}
    [DecidableEq Key]
    (key : Key)
    (value : Value) :
    ∀ (store : Store Key Value)
      (binding : Key × Value),
      binding ∈
        Store.update
          store
          key
          value →
      binding = (key, value) ∨
        binding ∈ store := by

  intro store
  induction store with

  | nil =>
      intro binding hMember

      simp [
        Store.update
      ] at hMember

      exact Or.inl hMember

  | cons head remaining inductionHypothesis =>
      intro binding hMember

      rcases head with
        ⟨candidate, currentValue⟩

      by_cases hCandidate :
          candidate = key

      · subst candidate

        rw [
          Store.update,
          if_pos rfl
        ] at hMember

        cases List.mem_cons.mp hMember with

        | inl hHere =>
            exact Or.inl hHere

        | inr hThere =>
            exact
              Or.inr
                (List.mem_cons_of_mem
                  _
                  hThere)

      · rw [
          Store.update,
          if_neg hCandidate
        ] at hMember

        cases List.mem_cons.mp hMember with

        | inl hHere =>
            subst hHere

            exact
              Or.inr
                List.mem_cons_self

        | inr hThere =>
            cases
                inductionHypothesis
                  binding
                  hThere with

            | inl hNew =>
                exact Or.inl hNew

            | inr hOld =>
                exact
                  Or.inr
                    (List.mem_cons_of_mem
                      _
                      hOld)

end Store

namespace LF

/-!
## The origin predicates

Three definitions, in dependency order: an origin package for one `(target, kind)` pair, its
reading on a pending event, and a per-statement predicate on the statements a reactor has left to
run.

`GeneralKindOriginAt` is stated on a target and a kind rather than on an event, and that is
load-bearing rather than tidiness. The statement side has to speak about the event a statement
*would* produce, which has no tag and no payload yet; taking the pair keeps one predicate for both
sides instead of forcing the statement side to invent junk components. `GeneralPendingOrigin` is
then literally the pair applied to an event's two fields, which is why the invariant reads nothing
else off an event.

The package is **exactly** the premise set of the two resolution theorems in
`Relico/Correctness/GeneralCorrespondence.lean` — `generalReactionFor?_eq_some_of_actionRoute` and
`generalReactionFor?_eq_some_of_portRoute` — minus the three F81 `Nodup` facts, which are facts
about the model rather than about an event and so stay where F81 put them. That is the whole
design: the invariant is chosen to be the thing those theorems consume, so the resolution
corollary at the end of this module is an application and not an argument.
-/

/--
The origin package of one target-and-kind pair: some declared class, some message server of it,
the compiled reactor standing at the target, and a reason the kind is one of that server's.

Two disjuncts, one per send shape, and no third: `LF.GeneralEventKind` has two constructors, and a
`.startup` event is unrepresentable by that type's own argument.

**No `message → kind` direction is asserted, and none exists.** The disjuncts read the kind that
is *there* and exhibit a site or a route that generates it. F78 measured that one DTR message can
be sent from several sites with several generated actions, so a function from a message to a kind
would be a function that does not exist; asking instead for a witness that the kind was generated
is both weaker and sufficient, because the resolution theorems match on the kind.
-/
def GeneralKindOriginAt
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (target : ActorName)
    (kind : LF.GeneralEventKind) :
    Prop :=
  ∃ (reactiveClass : DTR.GeneralReactiveClass)
    (server : DTR.GeneralMessageServer)
    (reactor : LF.GeneralReactor),
    reactiveClass ∈ model.classes ∧
      server ∈ reactiveClass.messageServers ∧
      program.reactorOfInstance? target =
        some reactor ∧
      Translation.compileGeneralReactiveClass
          model.classes
          routes
          reactiveClass =
        .ok reactor ∧
      (
        (∃ selfSend ∈
            Translation.generalSelfSendSitesOf
              server.name
              (Translation.selfSendsOfClass
                reactiveClass),
          kind =
            .logicalAction
              (Translation.generalActionNameAtSite
                (Translation.selfSendsOfClass
                  reactiveClass)
                selfSend.site
                server.name)) ∨
        (∃ route ∈
            Translation.generalRoutesIntoMessageServer
              reactiveClass.name
              server.name
              routes,
          kind =
            .inputPort
              (Translation.generalInputPortOfRoute
                route))
      )

/--
A pending event's kind is one the translation generated, at the reactor it is addressed to.
-/
def GeneralPendingOrigin
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (event : LF.GeneralPendingEvent) :
    Prop :=
  GeneralKindOriginAt
    model
    program
    routes
    event.target
    event.kind

/--
The event one statement of a running reactor would produce has a valid origin.

**Suffix-hereditary by construction**, which is the property that makes preservation cheap. The
predicate is about one statement and says nothing about its neighbours, so a body-consuming rule
that replaces `statement :: remaining` by `remaining` inherits the whole body side of the
invariant through `List.mem_cons_of_mem`, with no re-derivation for the statements it did not
touch.

`.assign` and `.trace` produce no event and so carry no obligation. `.schedule` is a self-send:
`LF.GeneralStep.schedule` enqueues at the **executing** reactor with the statement's own action
name, so the obligation is at `instanceName` and reads the name off the statement. `.setPort`
resolves through the program's connection table at run time, and the clause is quantified over
that resolution — `LF.connectionFrom?` is a function, so this is one obligation and not many, and
stating it as an implication is what lets the `setPort` rule discharge it by handing over its own
`hConnection`.

Nothing is stored on `LF.GeneralReactorRuntime` to support this. The predicate is a statement
*about* the body the runtime already carries, so no provenance field is added and the runtime
state of this family is unchanged by the whole milestone.
-/
def GeneralStmtOrigin
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (instanceName : ActorName) :
    LF.GeneralStmt →
    Prop

  | .assign _ _ =>
      True

  | .trace _ =>
      True

  | .schedule actionName _ _ =>
      GeneralKindOriginAt
        model
        program
        routes
        instanceName
        (.logicalAction
          actionName)

  | .setPort portName _ =>
      ∀ connection : LF.GeneralConnection,
        LF.connectionFrom?
            program.connections
            instanceName
            portName =
          some connection →
        GeneralKindOriginAt
          model
          program
          routes
          connection.targetInstance
          (.inputPort
            connection.targetPort)

/-!
### Arm equations

Four `rfl` facts, `@[simp]`, so that a `cases statement` in a preservation proof rewrites into the
arm instead of unfolding a `match` the equation compiler generated — the same reason
`compileGeneralBody`'s three equations exist.
-/

@[simp]
theorem generalStmtOrigin_assign
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (instanceName : ActorName)
    (target : VarName)
    (expression : LF.GeneralExpr) :
    GeneralStmtOrigin
        model
        program
        routes
        instanceName
        (.assign
          target
          expression) :=
  True.intro

@[simp]
theorem generalStmtOrigin_trace
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (instanceName : ActorName)
    (tag : String) :
    GeneralStmtOrigin
        model
        program
        routes
        instanceName
        (.trace
          tag) :=
  True.intro

@[simp]
theorem generalStmtOrigin_schedule_iff
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (instanceName : ActorName)
    (actionName : ActionName)
    (arguments : List LF.GeneralExpr)
    (delay : Delay) :
    GeneralStmtOrigin
        model
        program
        routes
        instanceName
        (.schedule
          actionName
          arguments
          delay) =
      GeneralKindOriginAt
        model
        program
        routes
        instanceName
        (.logicalAction
          actionName) := by
  rfl

@[simp]
theorem generalStmtOrigin_setPort_iff
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (instanceName : ActorName)
    (portName : PortName)
    (arguments : List LF.GeneralExpr) :
    GeneralStmtOrigin
        model
        program
        routes
        instanceName
        (.setPort
          portName
          arguments) =
      ∀ connection : LF.GeneralConnection,
        LF.connectionFrom?
            program.connections
            instanceName
            portName =
          some connection →
        GeneralKindOriginAt
          model
          program
          routes
          connection.targetInstance
          (.inputPort
            connection.targetPort) := by
  rfl

/--
The routing table's own provenance: every route lands on a declared message server of a declared
class, and the compiled reactor standing at its receiver instance is that class's.

**A named intermediate, not an assumption.** `generalRouteOrigin_of_compile` below proves this of
every accepted translation, so no public theorem of this module takes it as a premise and no
consumer outside the module can be asked for it. It survives as a definition because it is the
interface between the two halves of the discharge — the source half in the `Translation` ladder
above and the target half beside its discharger — and collapsing it into either would make the
statement of `generalStmtOrigin_of_mem_compiledBody` carry nine conjuncts instead of one name.

It records, per route, that: the receiver class is one the model declares; that class's name is the
route's `receiverClass`; the class declares a message server; that server's name is the route's
`message`; the program's instance table resolves the route's `receiverInstance`; and the reactor it
resolves to is what that class compiled to.

Name equalities rather than a direct `generalRoutesIntoMessageServer` membership, because a consumer
holds `Translation.mem_generalRoutesIntoMessageServer_self` at the route's own pair and needs to
rewrite it to the class's and server's names — which is what these equations are for.

It is a fact about a **static** program and a **static** table, so no step can falsify it and it
never appears in the state invariant.

Earlier revisions of this docstring said the fact was true but unproved, and named the five
traversal inversions that were missing (`routesOf`, `routesOfInstances`, `routesOfEntries`,
`generalRouteFor`, `generalOutputPortEntriesOf`). That was accurate when written; all five now exist
above, and the sentence is kept in past tense rather than deleted because the shape of the eventual
proof is exactly what that list predicted.
-/
def GeneralRouteOrigin
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute) :
    Prop :=
  ∀ route ∈ routes,
    ∃ (reactiveClass : DTR.GeneralReactiveClass)
      (server : DTR.GeneralMessageServer)
      (reactor : LF.GeneralReactor),
      reactiveClass ∈ model.classes ∧
        reactiveClass.name = route.receiverClass ∧
        server ∈ reactiveClass.messageServers ∧
        server.name = route.message ∧
        program.reactorOfInstance? route.receiverInstance =
          some reactor ∧
        Translation.compileGeneralReactiveClass
            model.classes
            routes
            reactiveClass =
          .ok reactor

/--
The kind-origin invariant of a target runtime state.

Two membership-shaped conjuncts and nothing else. No `Nodup`, no multiplicity claim, no
value-uniqueness claim: duplicate pending events are each witnessed separately and a duplicated
store key is harmless because the body side quantifies over *every* binding rather than over
`Store.lookup`. That is what makes the invariant transport through α-equivalence, whose reactor
clause is a membership iff and whose queue clause is a permutation.
-/
def GeneralKindOrigin
    (model : DTR.GeneralModel)
    (program : LF.GeneralProgram)
    (routes : List Translation.GeneralRoute)
    (state : GeneralRuntimeState) :
    Prop :=
  (∀ event ∈ state.pending,
    GeneralPendingOrigin
      model
      program
      routes
      event) ∧
  (∀ entry ∈ state.reactors,
    ∀ statement ∈ entry.2.activeBody,
      GeneralStmtOrigin
        model
        program
        routes
        entry.1
        statement)

end LF

namespace DTR

namespace GeneralModel

/--
Every self-send site of a resolving body names a message server its own class declares.

The bridge from `sendsResolveToMessageServers` to the action half of the origin package. Read on
the source side of the translation: a self-send resolves to the *sending* class
(`receivingClass?`'s `.selfTarget` arm returns it outright), so the message server is one of that
class's, which is what the origin package's `server ∈ reactiveClass.messageServers` conjunct asks
for.

Quantified over "every statement of this body resolves" rather than over model
well-formedness, because the two callers hold different bodies of one class — the constructor's and
one message server's — and `sendsResolveToMessageServers` is a traversal of
`DTR.GeneralReactiveClass.bodies` that each of them projects out of differently. Taking the
per-body hypothesis is what lets one induction serve both.

Four arms and no wildcard, matching `selfSendsFromIndex`'s own shape.
-/
theorem exists_messageServer_of_mem_selfSendsFromIndex
    (model : DTR.GeneralModel)
    (reactiveClass : DTR.GeneralReactiveClass)
    (bodyKey : Translation.GeneralBodyKey) :
    ∀ (body : DTR.GeneralBody)
      (index : Nat),
      (∀ statement ∈ body,
        model.statementResolves
            reactiveClass
            statement =
          true) →
      ∀ selfSend ∈
          Translation.selfSendsFromIndex
            bodyKey
            index
            body,
        ∃ server ∈ reactiveClass.messageServers,
          server.name = selfSend.message := by

  intro body
  induction body with

  | nil =>
      intro index _ selfSend hMember

      rw [
        Translation.selfSendsFromIndex_nil
      ] at hMember

      cases hMember

  | cons statement remaining inductionHypothesis =>
      intro index hResolves selfSend hMember

      have hTailResolves :
          ∀ candidate ∈ remaining,
            model.statementResolves
                reactiveClass
                candidate =
              true := by
        intro candidate hCandidate

        exact
          hResolves
            candidate
            (List.mem_cons_of_mem
              statement
              hCandidate)

      cases statement with

      | assign target value =>
          rw [
            Translation.selfSendsFromIndex_assign
          ] at hMember

          exact
            inductionHypothesis
              (index + 1)
              hTailResolves
              selfSend
              hMember

      | trace tag =>
          rw [
            Translation.selfSendsFromIndex_trace
          ] at hMember

          exact
            inductionHypothesis
              (index + 1)
              hTailResolves
              selfSend
              hMember

      | send target message arguments delay =>

          cases target with

          | knownRebec rebec =>
              rw [
                Translation.selfSendsFromIndex_send_knownRebec
              ] at hMember

              exact
                inductionHypothesis
                  (index + 1)
                  hTailResolves
                  selfSend
                  hMember

          | selfTarget =>
              rw [
                Translation.selfSendsFromIndex_send_selfTarget,
                List.mem_cons
              ] at hMember

              cases hMember with

              | inr hThere =>
                  exact
                    inductionHypothesis
                      (index + 1)
                      hTailResolves
                      selfSend
                      hThere

              | inl hHere =>

                  have hHeadResolves :
                      model.statementResolves
                          reactiveClass
                          (.send
                            .selfTarget
                            message
                            arguments
                            delay) =
                        true :=
                    hResolves
                      _
                      List.mem_cons_self

                  cases hServer :
                      reactiveClass.messageServer?
                        message with

                  | none =>
                      simp [
                        DTR.GeneralModel.statementResolves,
                        DTR.GeneralModel.receivingClass?,
                        hServer
                      ] at hHeadResolves

                  | some server =>
                      obtain ⟨hMemberServer, hName⟩ :=
                        findMessageServer?_mem_and_name
                          reactiveClass.messageServers
                          message
                          server
                          hServer

                      subst hHere

                      exact
                        ⟨server,
                         hMemberServer,
                         hName⟩

/--
Every statement of every body of every declared class resolves, in a well-formed model.

The `sendsResolveToMessageServers` clause read at one class and one body. Stated over
`body ∈ reactiveClass.bodies` rather than at the constructor and at a message server separately,
because that is the list the clause traverses; the two projections a caller wants are the two
`List.mem_cons` steps below.
-/
theorem statementResolves_of_wellFormed
    {model : DTR.GeneralModel}
    (hWellFormed :
      model.wellFormed =
        true)
    {reactiveClass : DTR.GeneralReactiveClass}
    (hClass :
      reactiveClass ∈ model.classes)
    {body : DTR.GeneralBody}
    (hBody :
      body ∈
        reactiveClass.bodies) :
    ∀ statement ∈ body,
      model.statementResolves
          reactiveClass
          statement =
        true := by

  intro statement hStatement

  have hClause :
      model.sendsResolveToMessageServers =
        true :=
    DTR.GeneralModel.sendsResolveToMessageServers_of_wellFormed
      model
      hWellFormed

  unfold DTR.GeneralModel.sendsResolveToMessageServers at hClause

  exact
    List.all_eq_true.mp
      (List.all_eq_true.mp
        (List.all_eq_true.mp
          hClause
          reactiveClass
          hClass)
        body
        hBody)
      statement
      hStatement

/--
The constructor's body is one of its class's bodies.
-/
theorem mem_bodies_constructor
    (reactiveClass : DTR.GeneralReactiveClass) :
    reactiveClass.constructor.body ∈
      reactiveClass.bodies := by

  unfold DTR.GeneralReactiveClass.bodies

  exact List.mem_cons_self

/--
A message server's body is one of its class's bodies.
-/
theorem mem_bodies_messageServer
    {reactiveClass : DTR.GeneralReactiveClass}
    {server : DTR.GeneralMessageServer}
    (hServer :
      server ∈
        reactiveClass.messageServers) :
    server.body ∈
      reactiveClass.bodies := by

  unfold DTR.GeneralReactiveClass.bodies

  exact
    List.mem_cons_of_mem
      _
      (List.mem_map_of_mem
        hServer)

end GeneralModel
end DTR

namespace LF

/-!
## The static origin theorems

Two, one per event shape, and they are where A and B are actually spent.

The port one needs **no compiled body at all**: a `setPort` statement's obligation is quantified
over the connection the runtime resolves, and B plus the route-origin package answer that for any
resolution whatsoever. So it is stated on its own and the compiled-body theorem below simply cites
it. That asymmetry is real and worth naming: the action side's kind is determined by the
*statement*, so it needs the statement's provenance; the port side's kind is determined by the
*connection table*, so it does not.
-/

/--
Any connection the runtime resolves yields a valid input-port origin at its target.

**B composed with the route-origin package, and nothing else.** B recovers a route behind the
resolved connection and places it in the filter for its own `(receiverClass, message)` pair; the
package names the class and server those two are the names of, and supplies the compiled reactor at
the route's receiver instance. Rewriting the filter membership along the two name equalities is the
whole proof.

No claim is made about *which* send site the connection belongs to — see the note above
`exists_route_of_connection_mem` for why that claim is false. The existential class and server here
are the *route's*, which is what the consumer needs and all that is available.
-/
theorem generalKindOriginAt_inputPort_of_routeOrigin
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {instanceName : ActorName}
    {portName : PortName}
    {connection : LF.GeneralConnection}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hRouteOrigin :
      GeneralRouteOrigin
        model
        program
        routes)
    (hConnection :
      LF.connectionFrom?
          program.connections
          instanceName
          portName =
        some connection) :
    GeneralKindOriginAt
      model
      program
      routes
      connection.targetInstance
      (.inputPort
        connection.targetPort) := by

  obtain
      ⟨tableRoutes,
       route,
       hTableRoutes,
       hRouteMember,
       _hSender,
       _hOutputPort,
       hTargetInstance,
       hTargetPort,
       hFilter⟩ :=
    Translation.exists_route_of_connectionFrom?
      hCompiled
      hConnection

  rw [
    hRoutes
  ] at hTableRoutes

  injection hTableRoutes with hTableEq

  subst hTableEq

  obtain
      ⟨reactiveClass,
       server,
       reactor,
       hClass,
       hClassName,
       hServer,
       hServerName,
       hReactor,
       hClassCompiled⟩ :=
    hRouteOrigin
      route
      hRouteMember

  refine
    ⟨reactiveClass,
     server,
     reactor,
     hClass,
     hServer,
     ?_,
     hClassCompiled,
     Or.inr
       ⟨route,
        ?_,
        ?_⟩⟩

  · rw [
      hTargetInstance
    ]

    exact hReactor

  · rw [
      hClassName,
      hServerName
    ]

    exact hFilter

  · rw [
      hTargetPort
    ]

/--
Every statement of a compiled body has a valid statement origin.

**A and B, in the form the runtime consumes.** Read the `.schedule` case in the direction the
invariant uses: a scheduled action in a running body is a witness, by A, that the class has a
self-send site generating that exact name, and `sendsResolveToMessageServers` says that site's
message names a message server of the class it is sending to — which for a self-send *is* the
sending class. Composing the two gives the origin package's class-and-server without ever mapping
a message to a kind. The `.setPort` case cites
`generalKindOriginAt_inputPort_of_routeOrigin` and consumes nothing from the body.

Three of the hypotheses are per-body rather than per-model, and each is discharged by a one-line
projection at the two call sites (the startup body and a message-server body):
`hResolves` by `DTR.GeneralModel.statementResolves_of_wellFormed` at
`mem_bodies_constructor` or `mem_bodies_messageServer`, and `hSites` by
`Translation.mem_selfSendsOfClass_of_mem_constructor` or
`Translation.mem_selfSendsOfClass_of_mem_messageServer`. Taking them per body is what lets one
theorem serve both bodies; deriving them here would need the theorem to know which body it has,
which is exactly the fact its caller holds and it does not.

**This is the low-level rung and takes the `GeneralRouteOrigin` package.** It has to: the package's
discharger `generalRouteOrigin_of_compile` needs the target-half helpers that appear further down, so
this theorem is elaborated before the discharger exists. Every *public* consumer of it —
`generalStmtOrigin_of_pending_reaction`, `generalKindOrigin_initial` — applies the discharger at its
own call site, so no caller outside this module ever supplies the package.
-/
theorem generalStmtOrigin_of_mem_compiledBody
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    {instanceName : ActorName}
    {env : Translation.GeneralOutputPortEnv}
    {bodyKey : Translation.GeneralBodyKey}
    {body : DTR.GeneralBody}
    {compiled : LF.GeneralBody}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hRouteOrigin :
      GeneralRouteOrigin
        model
        program
        routes)
    (hClass :
      reactiveClass ∈ model.classes)
    (hClassCompiled :
      Translation.compileGeneralReactiveClass
          model.classes
          routes
          reactiveClass =
        .ok reactor)
    (hReactor :
      program.reactorOfInstance? instanceName =
        some reactor)
    (hResolves :
      ∀ statement ∈ body,
        model.statementResolves
            reactiveClass
            statement =
          true)
    (hSites :
      ∀ selfSend ∈
          Translation.selfSendsFromIndex
            bodyKey
            0
            body,
        selfSend ∈
          Translation.selfSendsOfClass
            reactiveClass)
    (hBody :
      Translation.compileGeneralBody
          env
          {
            bodyKey :=
              bodyKey

            selfSends :=
              Translation.selfSendsOfClass
                reactiveClass
          }
          0
          body =
        .ok compiled) :
    ∀ statement ∈ compiled,
      GeneralStmtOrigin
        model
        program
        routes
        instanceName
        statement := by

  intro statement hStatement

  cases statement with

  | assign target expression =>
      exact
        generalStmtOrigin_assign
          model
          program
          routes
          instanceName
          target
          expression

  | trace tag =>
      exact
        generalStmtOrigin_trace
          model
          program
          routes
          instanceName
          tag

  | setPort portName arguments =>
      rw [
        generalStmtOrigin_setPort_iff
      ]

      intro connection hConnection

      exact
        generalKindOriginAt_inputPort_of_routeOrigin
          hCompiled
          hRoutes
          hRouteOrigin
          hConnection

  | schedule actionName arguments delay =>
      rw [
        generalStmtOrigin_schedule_iff
      ]

      obtain ⟨selfSend, hSite, _hIndex, hName⟩ :=
        Translation.compileGeneralBody_schedule_provenance
          env
          {
            bodyKey :=
              bodyKey

            selfSends :=
              Translation.selfSendsOfClass
                reactiveClass
          }
          body
          0
          compiled
          hBody
          actionName
          arguments
          delay
          hStatement

      obtain ⟨server, hServer, hServerName⟩ :=
        DTR.GeneralModel.exists_messageServer_of_mem_selfSendsFromIndex
          model
          reactiveClass
          bodyKey
          body
          0
          hResolves
          selfSend
          hSite

      refine
        ⟨reactiveClass,
         server,
         reactor,
         hClass,
         hServer,
         hReactor,
         hClassCompiled,
         Or.inl
           ⟨selfSend,
            ?_,
            ?_⟩⟩

      · exact
          Translation.mem_generalSelfSendSitesOf_of_mem
            server.name
            selfSend
            (Translation.selfSendsOfClass
              reactiveClass)
            (hSites
              selfSend
              hSite)
            hServerName.symm

      · rw [
          hName,
          hServerName
        ]

/-!
## Reactor membership from instance resolution

The resolution theorems' F81 premises are discharged from a reactor's *own* well-formedness, and
that is read off `program.reactorsWellFormed` at a **member** of `program.reactors`. The origin
package holds a resolution instead, so one step is missing: a resolved reactor is a member. The
same fact exists `private` in `Relico/Correctness/GeneralCorrespondence.lean` as
`mem_of_findReactor?_eq_some`; it is proved again here rather than de-privatised, following the
house rule that duplicating a small lemma is preferred to widening an interface — and
`Relico/LF/GeneralSemantics.lean` records the same duplication of `eq_of_nodup_map` for the same
reason.
-/

/--
A resolved reactor is a member of the reactor list.
-/
theorem mem_of_findReactor?_eq_some :
    ∀ (reactors : List LF.GeneralReactor)
      (reactorName : ReactorName)
      (reactor : LF.GeneralReactor),
      LF.findReactor?
          reactors
          reactorName =
        some reactor →
      reactor ∈ reactors := by

  intro reactors
  induction reactors with

  | nil =>
      intro reactorName reactor hFound

      simp [
        LF.findReactor?
      ] at hFound

  | cons head remaining inductionHypothesis =>
      intro reactorName reactor hFound

      by_cases hHead :
          head.name = reactorName

      · rw [
          LF.findReactor?,
          if_pos hHead
        ] at hFound

        obtain rfl :=
          Option.some.inj hFound

        exact List.mem_cons_self

      · rw [
          LF.findReactor?,
          if_neg hHead
        ] at hFound

        exact
          List.mem_cons_of_mem
            head
            (inductionHypothesis
              reactorName
              reactor
              hFound)

/--
The reactor an instance resolves to is one of the program's reactors.
-/
theorem mem_reactors_of_reactorOfInstance?
    {program : LF.GeneralProgram}
    {instanceName : ActorName}
    {reactor : LF.GeneralReactor}
    (hReactor :
      program.reactorOfInstance? instanceName =
        some reactor) :
    reactor ∈ program.reactors := by

  unfold LF.GeneralProgram.reactorOfInstance? at hReactor

  cases hInstance :
      program.instance? instanceName with

  | none =>
      rw [hInstance] at hReactor

      simp at hReactor

  | some reactorInstance =>
      rw [hInstance] at hReactor

      exact
        mem_of_findReactor?_eq_some
          program.reactors
          reactorInstance.reactorName
          reactor
          hReactor

/-!
## Discharging the route-origin premise

`GeneralRouteOrigin` was carried as a premise when this module first landed, because the route
provenance it asks for needed five traversal inversions that did not exist. They exist now — the
`Translation` ladder above — and this section spends them.

What is left is the **target** half: turning "the model declares this class and this instance of it"
into "the program's instance table resolves that instance to the reactor that class compiled to".
Two lookups, both first-match, so both need a `Nodup`, and both `Nodup`s come from the guard the
compilation already ran. The four helpers below are the minimum for that: two clause extractions and
two lookup lemmas.

The extractions are spelled `_of_programWellFormed` rather than `_of_wellFormed` deliberately.
`Relico/LF/GeneralWellFormed.lean` has `private` theorems of the latter names, and the two lookup
lemmas exist `private` in `Relico/Correctness/GeneralCorrespondence.lean` as
`findInstance?_of_mem_of_nodup` and `findReactor?_of_mem_of_nodup`. Neither is de-privatised;
duplicating a four-line lemma is the house preference over widening an interface, and distinct names
keep the two copies from colliding in one namespace.
-/

private theorem instanceNamesUnique_of_programWellFormed
    (program : LF.GeneralProgram)
    (hWellFormed :
      program.wellFormed =
        true) :
    program.instanceNamesUnique =
      true := by
  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.instanceNamesUnique <;> simp

private theorem reactorNamesUnique_of_programWellFormed
    (program : LF.GeneralProgram)
    (hWellFormed :
      program.wellFormed =
        true) :
    program.reactorNamesUnique =
      true := by
  revert hWellFormed
  unfold LF.GeneralProgram.wellFormed
  cases program.reactorNamesUnique <;> simp

/--
On a duplicate-free list, a member instance is what the lookup returns.
-/
private theorem findInstance?_of_mem_of_nodup :
    ∀ (instances : List LF.GeneralReactorInstance)
      (reactorInstance : LF.GeneralReactorInstance),
      reactorInstance ∈ instances →
      (instances.map
        (fun candidate =>
          candidate.name)).Nodup →
      LF.findInstance?
          instances
          reactorInstance.name =
        some reactorInstance := by

  intro instances
  induction instances with

  | nil =>
      intro reactorInstance hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro reactorInstance hMember hNodup

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          simp [
            LF.findInstance?
          ]

      | inr hTail =>
          have hHeadName :
              head.name ≠ reactorInstance.name := by
            intro hEqual

            refine
              (List.nodup_cons.mp hNodup).1
                ?_

            dsimp only

            rw [hEqual]

            exact
              List.mem_map_of_mem
                hTail

          rw [
            LF.findInstance?,
            if_neg hHeadName
          ]

          exact
            inductionHypothesis
              reactorInstance
              hTail
              (List.nodup_cons.mp hNodup).2

/--
On a duplicate-free list, a member reactor is what the lookup returns.
-/
private theorem findReactor?_of_mem_of_nodup :
    ∀ (reactors : List LF.GeneralReactor)
      (reactor : LF.GeneralReactor),
      reactor ∈ reactors →
      (reactors.map
        (fun candidate =>
          candidate.name)).Nodup →
      LF.findReactor?
          reactors
          reactor.name =
        some reactor := by

  intro reactors
  induction reactors with

  | nil =>
      intro reactor hMember _

      cases hMember

  | cons head remaining inductionHypothesis =>
      intro reactor hMember hNodup

      cases List.mem_cons.mp hMember with

      | inl hHead =>
          subst hHead

          simp [
            LF.findReactor?
          ]

      | inr hTail =>
          have hHeadName :
              head.name ≠ reactor.name := by
            intro hEqual

            refine
              (List.nodup_cons.mp hNodup).1
                ?_

            dsimp only

            rw [hEqual]

            exact
              List.mem_map_of_mem
                hTail

          rw [
            LF.findReactor?,
            if_neg hHeadName
          ]

          exact
            inductionHypothesis
              reactor
              hTail
              (List.nodup_cons.mp hNodup).2

/--
The reactor an instance of a compiled program resolves to is the reactor its class compiled to.

The target half of the discharge, and the only place two first-match lookups are chased. The
instance table resolves by name, so the compiled instance of a declared actor is what
`instance?` returns — because compilation refuses a program with colliding instance names — and its
`reactorName` is `reactorNameFor` of the actor's class, so `reactor?` finds the reactor that class
compiled to, because compilation also refuses colliding reactor names.

Both `Nodup`s come from the guard rather than from the model, which is the same choice
`modelInstanceNames_nodup_of_compiled` records: assuming the model's well-formedness here would be a
second hypothesis saying what the compiled side already knows.
-/
private theorem reactorOfInstance?_of_mem_instances
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {actor : DTR.GeneralActorInstance}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hActor :
      actor ∈ model.instances)
    (hClassName :
      reactiveClass.name = actor.className)
    (hMember :
      reactor ∈ program.reactors)
    (hClassCompiled :
      Translation.compileGeneralReactiveClass
          model.classes
          routes
          reactiveClass =
        .ok reactor) :
    program.reactorOfInstance? actor.name =
      some reactor := by

  have hWellFormed :
      program.wellFormed =
        true :=
    Translation.compileGeneralModel_wellFormed
      hCompiled

  have hCompiledInstance :
      (Translation.compileGeneralActorInstance
          actor) ∈
        program.instances := by
    rw [
      Translation.compileGeneralModel_instances
        hCompiled
    ]

    exact
      List.mem_map_of_mem
        hActor

  have hInstance :
      program.instance? actor.name =
        some
          (Translation.compileGeneralActorInstance
            actor) := by
    unfold LF.GeneralProgram.instance?

    rw [
      ← Translation.compileGeneralActorInstance_name
          actor
    ]

    exact
      findInstance?_of_mem_of_nodup
        program.instances
        _
        hCompiledInstance
        (of_decide_eq_true
          (instanceNamesUnique_of_programWellFormed
            program
            hWellFormed))

  have hReactorName :
      reactor.name =
        Translation.reactorNameFor
          actor.className := by
    rw [
      Translation.compileGeneralReactiveClass_name
        hClassCompiled,
      hClassName
    ]

  unfold LF.GeneralProgram.reactorOfInstance?

  rw [
    hInstance
  ]

  dsimp only

  unfold LF.GeneralProgram.reactor?

  rw [
    Translation.compileGeneralActorInstance_reactorName,
    ← hReactorName
  ]

  exact
    findReactor?_of_mem_of_nodup
      program.reactors
      reactor
      hMember
      (of_decide_eq_true
        (reactorNamesUnique_of_programWellFormed
          program
          hWellFormed))

/--
**`GeneralRouteOrigin` holds of every accepted translation.** The premise this module carried when it
landed is now a theorem.

Two halves, both already proved. `Translation.routeProvenance_of_routesOf` gives the source half —
the receiver class is declared, its message server is declared, and the receiver instance is one the
model declares of that class. `Translation.exists_reactor_of_mem_classes` and
`reactorOfInstance?_of_mem_instances` give the target half, identifying the reactor the receiver
instance resolves to with the reactor that class compiled to.

**No uniqueness claim about routes is used.** The route is arbitrary and the conclusion is existential
in class, server and reactor; `outputPortNameFor`'s non-injectivity is irrelevant here because
nothing asks which send site the route came from. Both `Nodup` facts consumed are about *instance
names* and *reactor names*, which the guard decides, and neither is a claim about routes.

Takes no model well-formedness hypothesis. Everything comes from the compilation succeeding and the
routing table being that compilation's own — which is the strongest statement available and also the
weakest premise set, since a model that compiles need not have been checked by
`DTR.GeneralModel.wellFormed` at all.
-/
theorem generalRouteOrigin_of_compile
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes) :
    GeneralRouteOrigin
      model
      program
      routes := by

  intro route hRoute

  obtain
      ⟨receivingClass,
       server,
       receiver,
       hClassMember,
       hClassName,
       hServerMember,
       hServerName,
       hReceiverMember,
       hReceiverName,
       hReceiverClassName⟩ :=
    Translation.routeProvenance_of_routesOf
      hRoutes
      route
      hRoute

  obtain ⟨reactor, hReactorMember, hClassCompiled⟩ :=
    Translation.exists_reactor_of_mem_classes
      hCompiled
      hRoutes
      receivingClass
      hClassMember

  refine
    ⟨receivingClass,
     server,
     reactor,
     hClassMember,
     hClassName,
     hServerMember,
     hServerName,
     ?_,
     hClassCompiled⟩

  rw [
    ← hReceiverName
  ]

  exact
    reactorOfInstance?_of_mem_instances
      hCompiled
      hReceiverMember
      (by
        rw [
          hClassName,
          ← hReceiverClassName
        ])
      hReactorMember
      hClassCompiled

/--
The three F81 distinctness facts, at a class of an accepted translation whose compiled reactor was
reached by instance resolution rather than by list membership.

`Correctness.generalTriggerDistinctness_of_wellFormed` is the same discharge from the same three
sources, keyed on `reactor ∈ program.reactors` and returning the class existentially. Here the class
is already in hand — the origin package named it — so what is wanted is the three facts *at that
class*, and re-deriving them is three citations rather than a second search. Its internals are not
reproved: the two per-class dischargers and the model-level one are cited directly.
-/
theorem generalTriggerDistinctnessAt
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {reactiveClass : DTR.GeneralReactiveClass}
    {reactor : LF.GeneralReactor}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hClass :
      reactiveClass ∈ model.classes)
    (hClassCompiled :
      Translation.compileGeneralReactiveClass
          model.classes
          routes
          reactiveClass =
        .ok reactor)
    (hMember :
      reactor ∈ program.reactors) :
    ((Translation.generalInputPortsOf
        reactiveClass.name
        routes).map
      (fun port =>
        port.name.value)).Nodup ∧
    ((Translation.generalActionNamesOf
        (Translation.selfSendsOfClass
          reactiveClass)
        reactiveClass.messageServers).map
      (fun name =>
        name.value)).Nodup ∧
    (reactiveClass.messageServers.map
      (fun server =>
        server.name)).Nodup := by

  have hProgramWellFormed :
      program.wellFormed =
        true :=
    Translation.compileGeneralModel_wellFormed
      hCompiled

  have hReactorsWellFormed :
      program.reactorsWellFormed =
        true := by
    revert hProgramWellFormed
    unfold LF.GeneralProgram.wellFormed
    cases program.reactorsWellFormed <;>
      simp

  have hReactorWellFormed :
      reactor.wellFormed =
        true :=
    List.all_eq_true.mp
      hReactorsWellFormed
      reactor
      hMember

  refine ⟨?_, ?_, ?_⟩

  · exact
      Translation.compileGeneralReactiveClass_inputPortNames_nodup
        hClassCompiled
        hReactorWellFormed

  · exact
      Translation.compileGeneralReactiveClass_actionNames_nodup
        hClassCompiled
        hReactorWellFormed

  · exact
      DTR.GeneralModel.messageServerNames_nodup_of_wellFormed
        hModelWellFormed
        hClass

/-!
## The resolution corollary

The composition the whole milestone exists for. A pending event of a state satisfying the invariant
resolves, through `LF.GeneralProgram.reactionFor?`, to a reaction whose parameters are its message
server's parameter names and whose body is a successful compilation of that server's source body —
which is exactly the `hReaction`/`hParams`/`hBody` package the forward consume core takes.

Two branches, one per disjunct of the origin package, and each is a direct application of the
matching routing theorem in `Relico/Correctness/GeneralCorrespondence.lean`. Neither theorem's
internals are touched: the `parameters` and `body` equations come out as `rfl` because both
theorems return an explicit reaction record.
-/

/--
**The kind-origin resolution corollary.** Every pending event of a state satisfying the invariant
resolves to a compiled message-server reaction, with its parameter names and its compiled body.

The output is the consume-core package. `hReaction` is the `reactionFor?` equation, `hParams` the
`reaction.parameters = server.parameters.map (·.name)` equation, and `hBody` the pair of an
`outputPortEnvOf` success and a `compileGeneralBody` success at `reaction.body` — with the server's
own `bodyKey` and the class's own self-send list, which is the context the reaction was compiled
against and therefore the one a statement-level argument has to use.

**F78 is preserved throughout.** No step of this proof maps a message to a kind. The event's kind
is matched on as it stands, the origin disjunct says which family generated it, and the two routing
theorems take that witness. Nothing collapses two events carrying one payload, and nothing assumes
the kind is determined by anything other than itself.

The class-and-server facts are returned alongside the package rather than left inside the
existentials. Without them a caller cannot use the returned `compileGeneralBody` equation for
anything, because that equation is stated at *this* class's self-send list and *this* server's body
key: re-obtaining the class from the invariant would give an unrelated pair of existential
witnesses. That is a real trap and it caught this theorem's first shape.
-/
theorem generalKindOrigin_resolution
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state : GeneralRuntimeState}
    {event : LF.GeneralPendingEvent}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hOrigin :
      GeneralKindOrigin
        model
        program
        routes
        state)
    (hEvent :
      event ∈ state.pending) :
    ∃ (reaction : LF.GeneralReaction)
      (reactiveClass : DTR.GeneralReactiveClass)
      (server : DTR.GeneralMessageServer)
      (reactor : LF.GeneralReactor)
      (env : Translation.GeneralOutputPortEnv)
      (compiledBody : LF.GeneralBody),
      program.reactionFor?
          event.target
          event.kind =
        some reaction ∧
      reaction.parameters =
        server.parameters.map
          (fun parameter =>
            parameter.name) ∧
      reaction.body = compiledBody ∧
      reactiveClass ∈ model.classes ∧
      server ∈ reactiveClass.messageServers ∧
      program.reactorOfInstance? event.target =
        some reactor ∧
      Translation.compileGeneralReactiveClass
          model.classes
          routes
          reactiveClass =
        .ok reactor ∧
      Translation.outputPortEnvOf
          model.classes
          reactiveClass =
        .ok env ∧
      Translation.compileGeneralBody
          env
          {
            bodyKey :=
              .messageServer
                server.name

            selfSends :=
              Translation.selfSendsOfClass
                reactiveClass
          }
          0
          server.body =
        .ok compiledBody := by

  obtain
      ⟨reactiveClass,
       server,
       reactor,
       hClass,
       hServer,
       hReactor,
       hClassCompiled,
       hKind⟩ :=
    hOrigin.left
      event
      hEvent

  obtain ⟨hInputPortNames, hActionNames, hServerNames⟩ :=
    generalTriggerDistinctnessAt
      hModelWellFormed
      hCompiled
      hClass
      hClassCompiled
      (mem_reactors_of_reactorOfInstance?
        hReactor)

  cases hKind with

  | inl hAction =>

      obtain ⟨selfSend, hSelfSend, hEventKind⟩ :=
        hAction

      obtain ⟨compiledBody, hReaction, env, hEnv, hBody⟩ :=
        Correctness.generalReactionFor?_eq_some_of_actionRoute
          hClassCompiled
          hInputPortNames
          hActionNames
          hServerNames
          hReactor
          server
          hServer
          selfSend
          hSelfSend

      rw [
        hEventKind
      ]

      exact
        ⟨_,
         reactiveClass,
         server,
         reactor,
         env,
         compiledBody,
         hReaction,
         rfl,
         rfl,
         hClass,
         hServer,
         hReactor,
         hClassCompiled,
         hEnv,
         hBody⟩

  | inr hPort =>

      obtain ⟨route, hRoute, hEventKind⟩ :=
        hPort

      obtain ⟨compiledBody, hReaction, env, hEnv, hBody⟩ :=
        Correctness.generalReactionFor?_eq_some_of_portRoute
          hClassCompiled
          hInputPortNames
          hActionNames
          hServerNames
          hReactor
          server
          hServer
          route
          hRoute

      rw [
        hEventKind
      ]

      exact
        ⟨_,
         reactiveClass,
         server,
         reactor,
         env,
         compiledBody,
         hReaction,
         rfl,
         rfl,
         hClass,
         hServer,
         hReactor,
         hClassCompiled,
         hEnv,
         hBody⟩

/-!
## The body a `fire` installs

`LF.GeneralStep.fire` sets the target reactor's `activeBody` to `reaction.body`, so preservation's
`fire` case owes the statement side of the invariant at that body. The resolution corollary already
produces the compile fact for it; this theorem is that plus
`generalStmtOrigin_of_mem_compiledBody`, with the two per-body hypotheses discharged at the message
server's body.

Stated separately from the resolution corollary rather than as a further conjunct of it, because the
corollary's job is the consume-core package and a caller that wants only `hReaction` should not have
to carry a body-origin conclusion it does not read.
-/

/--
Every statement of the reaction a pending event resolves to has a valid statement origin, at the
event's own target.

The `instanceName` of the conclusion is `event.target`, which is where `fire` installs the body, and
the resolution corollary's own reactor equation is what makes that the right instance: the reaction
was found by `reactionFor? program event.target event.kind`, so it belongs to the reactor standing at
`event.target`, and its `setPort` statements resolve through that instance's connections.

Every ingredient comes from the **one** application of the resolution corollary, deliberately. The
compile equation it returns is stated at that application's own class and server, so re-obtaining
either from the invariant would produce different existential witnesses and the equation would not
apply — which is exactly why the corollary returns them.

Takes the ordinary compilation eligibility assumptions and no route-origin package: it applies
`generalRouteOrigin_of_compile` internally.
-/
theorem generalStmtOrigin_of_pending_reaction
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state : GeneralRuntimeState}
    {event : LF.GeneralPendingEvent}
    {reaction : LF.GeneralReaction}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hOrigin :
      GeneralKindOrigin
        model
        program
        routes
        state)
    (hEvent :
      event ∈ state.pending)
    (hReaction :
      program.reactionFor?
          event.target
          event.kind =
        some reaction) :
    ∀ statement ∈ reaction.body,
      GeneralStmtOrigin
        model
        program
        routes
        event.target
        statement := by

  obtain
      ⟨resolvedReaction,
       reactiveClass,
       server,
       reactor,
       env,
       compiledBody,
       hResolvedReaction,
       _hParams,
       hResolvedBody,
       hClass,
       hServer,
       hReactor,
       hClassCompiled,
       _hEnv,
       hCompiledBody⟩ :=
    generalKindOrigin_resolution
      hModelWellFormed
      hCompiled
      hOrigin
      hEvent

  rw [
    hReaction
  ] at hResolvedReaction

  obtain rfl :=
    Option.some.inj hResolvedReaction

  rw [
    hResolvedBody
  ]

  refine
    generalStmtOrigin_of_mem_compiledBody
      hCompiled
      hRoutes
      (generalRouteOrigin_of_compile
        hCompiled
        hRoutes)
      hClass
      hClassCompiled
      hReactor
      ?_
      ?_
      hCompiledBody

  · exact
      DTR.GeneralModel.statementResolves_of_wellFormed
        hModelWellFormed
        hClass
        (DTR.GeneralModel.mem_bodies_messageServer
          hServer)

  · intro selfSend hSite

    exact
      Translation.mem_selfSendsOfClass_of_mem_messageServer
        hServer
        hSite

/-!
## Initialization

The initial queue is empty, so the event side is vacuous. The body side is the startup bodies, and
`Translation.compileGeneralModel_startupBody` says every compiled reactor's startup reaction body is
a successful compilation of its class's constructor body — so the whole content is
`generalStmtOrigin_of_mem_compiledBody` at `bodyKey := .constructor`, with no compilation reasoning
repeated here.
-/

/--
Every initial state of a compiled program satisfies the kind-origin invariant.

The `idleDefault` branch of the initializer is reached only when an instance fails to resolve, which
`instancesResolve` makes impossible for an accepted program — but it needs no argument here at all,
because its `activeBody` is `[]` and the body side is vacuous on it. That is why the theorem takes no
well-formedness premise beyond the ones the origin package needs.

Route origin is discharged internally by `generalRouteOrigin_of_compile`.
-/
theorem generalKindOrigin_initial
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes) :
    GeneralKindOrigin
      model
      program
      routes
      (LF.GeneralProgram.initialState
        program) := by

  refine ⟨?_, ?_⟩

  · intro event hEvent

    rw [
      LF.GeneralProgram.initialState_pending
        program
    ] at hEvent

    cases hEvent

  · intro entry hEntry statement hStatement

    unfold LF.GeneralProgram.initialState at hEntry

    obtain ⟨reactorInstance, _hInstanceMember, hPair⟩ :=
      List.mem_map.mp hEntry

    cases hResolution :
        program.reactorOfInstance? reactorInstance.name with

    | none =>
        rw [
          hResolution
        ] at hPair

        rw [
          ← hPair
        ] at hStatement

        simp [
          LF.GeneralReactorRuntime.idleDefault
        ] at hStatement

    | some reactor =>
        rw [
          hResolution
        ] at hPair

        rw [
          ← hPair
        ] at hStatement ⊢

        dsimp only at hStatement ⊢

        unfold LF.GeneralProgram.initialReactorRuntime at hStatement

        dsimp only at hStatement

        obtain ⟨startupRoutes, hStartupRoutes, walk⟩ :=
          Translation.compileGeneralModel_startupBody
            hCompiled

        rw [
          hRoutes
        ] at hStartupRoutes

        injection hStartupRoutes with hRoutesEq

        subst hRoutesEq

        obtain
            ⟨reactiveClass,
             env,
             compiledBody,
             hClass,
             hClassCompiled,
             _hEnv,
             hBody,
             hStartupBody,
             _hStateVariables,
             _hParameters⟩ :=
          walk
            reactor
            (mem_reactors_of_reactorOfInstance?
              hResolution)

        rw [
          hStartupBody
        ] at hStatement

        refine
          generalStmtOrigin_of_mem_compiledBody
            hCompiled
            hRoutes
            (generalRouteOrigin_of_compile
              hCompiled
              hRoutes)
            hClass
            hClassCompiled
            hResolution
            ?_
            ?_
            hBody
            statement
            hStatement

        · exact
            DTR.GeneralModel.statementResolves_of_wellFormed
              hModelWellFormed
              hClass
              (DTR.GeneralModel.mem_bodies_constructor
                reactiveClass)

        · intro selfSend hSite

          exact
            Translation.mem_selfSendsOfClass_of_mem_constructor
              hSite

/-!
## Step preservation

Two private helpers first, because four of the seven rules differ only in the valuation they write
and every one of them needs the same two facts: the head statement's origin (to build the event it
enqueues, if it enqueues one) and the tail's origin transported through the store update.

Extracting them is not only economy. The store step is the one place where a *duplicated* store key
could matter, and doing it once means the argument is written once: `Store.mem_update` says every
binding of the updated store is the new one or an old one, and the old-binding case is discharged by
the incoming invariant at that same binding — **not** by a lookup. A lookup-shaped invariant would
be unsound here for the reason `Relico/Common/Store.lean` records on `mem_of_lookup`, since a
shadowed binding is a binding the runtime can still be observed at through membership.
-/

/--
The consumed head statement of a running reactor has a valid statement origin.
-/
private theorem generalStmtOrigin_head
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state : GeneralRuntimeState}
    {instanceName : ActorName}
    {reactor : GeneralReactorRuntime}
    {statement : LF.GeneralStmt}
    {remaining : LF.GeneralBody}
    (hBodySide :
      ∀ entry ∈ state.reactors,
        ∀ candidate ∈ entry.2.activeBody,
          GeneralStmtOrigin
            model
            program
            routes
            entry.1
            candidate)
    (hReactor :
      Store.lookup
          state.reactors
          instanceName =
        some reactor)
    (hBody :
      reactor.activeBody =
        statement :: remaining) :
    GeneralStmtOrigin
      model
      program
      routes
      instanceName
      statement := by

  refine
    hBodySide
      (instanceName, reactor)
      (Store.mem_of_lookup
        state.reactors
        instanceName
        reactor
        hReactor)
      statement
      ?_

  rw [
    hBody
  ]

  exact List.mem_cons_self

/--
The body side survives replacing one reactor's body by its own tail.

Every binding of the updated store is the new one — whose body is the tail, inherited from the head
statement's own binding by `List.mem_cons_of_mem` — or an old one, which the incoming invariant
already covers. The valuation is arbitrary because no clause of `GeneralStmtOrigin` reads it.
-/
private theorem generalStmtOrigin_update_tail
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state : GeneralRuntimeState}
    {instanceName : ActorName}
    {reactor : GeneralReactorRuntime}
    {statement : LF.GeneralStmt}
    {remaining : LF.GeneralBody}
    (hBodySide :
      ∀ entry ∈ state.reactors,
        ∀ candidate ∈ entry.2.activeBody,
          GeneralStmtOrigin
            model
            program
            routes
            entry.1
            candidate)
    (hReactor :
      Store.lookup
          state.reactors
          instanceName =
        some reactor)
    (hBody :
      reactor.activeBody =
        statement :: remaining)
    (valuation :
      Store VarName LF.GeneralValue) :
    ∀ entry ∈
        Store.update
          state.reactors
          instanceName
          {
            valuation :=
              valuation

            activeBody :=
              remaining
          },
      ∀ candidate ∈ entry.2.activeBody,
        GeneralStmtOrigin
          model
          program
          routes
          entry.1
          candidate := by

  intro entry hEntry candidate hCandidate

  cases
      Store.mem_update
        instanceName
        {
          valuation :=
            valuation

          activeBody :=
            remaining
        }
        state.reactors
        entry
        hEntry with

  | inl hNew =>
      subst hNew

      dsimp only at hCandidate ⊢

      refine
        hBodySide
          (instanceName, reactor)
          (Store.mem_of_lookup
            state.reactors
            instanceName
            reactor
            hReactor)
          candidate
          ?_

      rw [
        hBody
      ]

      exact
        List.mem_cons_of_mem
          statement
          hCandidate

  | inr hOld =>
      exact
        hBodySide
          entry
          hOld
          candidate
          hCandidate

/--
The kind-origin invariant survives every target step.

Rule by rule. `assign` and `trace` produce no event, so the event side is unchanged and the body side
is the tail helper. `schedule` and `setPort` append one event, and its origin is *exactly* the
consumed statement's own `GeneralStmtOrigin` clause — read off the statement, with no name analysis
at run time, which is the whole point of making the body side per statement. `fire` removes one
occurrence from the queue by decomposition and installs `reaction.body`, whose origin comes from
`generalStmtOrigin_of_pending_reaction` at the fired event. Both advance rules leave the queue and
the reactor store untouched and move only the tag, which the invariant does not read.

**Duplicates are handled occurrence-wise and nothing here assumes uniqueness.** The `fire` case maps
each survivor of `earlier ++ later` back into `earlier ++ event :: later` individually, so a queue
holding the fired event twice keeps the second copy witnessed; no `Nodup` and no multiplicity fact is
used or needed. `hRoutes` is a fact about the program and its routing table, which no step can change,
so it is a premise rather than a conjunct of the invariant; route origin is discharged internally.
-/
theorem generalKindOrigin_of_step
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state state' : GeneralRuntimeState}
    {label : LF.GeneralLabel}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hOrigin :
      GeneralKindOrigin
        model
        program
        routes
        state)
    (hStep :
      GeneralStep
        program
        state
        label
        state') :
    GeneralKindOrigin
      model
      program
      routes
      state' := by

  obtain ⟨hEventSide, hBodySide⟩ :=
    hOrigin

  cases hStep with

  | assign hReactor hBody hEvaluate =>
      exact
        ⟨hEventSide,
         generalStmtOrigin_update_tail
           hBodySide
           hReactor
           hBody
           _⟩

  | trace hReactor hBody =>
      exact
        ⟨hEventSide,
         generalStmtOrigin_update_tail
           hBodySide
           hReactor
           hBody
           _⟩

  | schedule hReactor hBody hArguments =>
      refine
        ⟨?_,
         generalStmtOrigin_update_tail
           hBodySide
           hReactor
           hBody
           _⟩

      intro event hEvent

      dsimp only at hEvent

      rcases
          List.mem_append.mp hEvent with
        hOld | hNew

      · exact
          hEventSide
            event
            hOld

      · obtain rfl :=
          List.mem_singleton.mp hNew

        exact
          generalStmtOrigin_head
            hBodySide
            hReactor
            hBody

  | setPort hReactor hBody hArguments hConnection =>
      refine
        ⟨?_,
         generalStmtOrigin_update_tail
           hBodySide
           hReactor
           hBody
           _⟩

      intro event hEvent

      dsimp only at hEvent

      rcases
          List.mem_append.mp hEvent with
        hOld | hNew

      · exact
          hEventSide
            event
            hOld

      · obtain rfl :=
          List.mem_singleton.mp hNew

        exact
          generalStmtOrigin_head
            hBodySide
            hReactor
            hBody
            _
            hConnection

  | fire hSelected hTag hQueue hReactor hIdle hReaction =>

      refine ⟨?_, ?_⟩

      · intro event hEvent

        refine
          hEventSide
            event
            ?_

        rw [hQueue]

        rcases
            List.mem_append.mp hEvent with
          hEarlier | hLater

        · exact
            List.mem_append.mpr
              (Or.inl hEarlier)

        · exact
            List.mem_append.mpr
              (Or.inr
                (List.mem_cons_of_mem
                  _
                  hLater))

      · intro entry hEntry candidate hCandidate

        cases
            Store.mem_update
              _
              {
                valuation :=
                  LF.bindReactionParameters
                    _
                    _
                    _

                activeBody :=
                  _
              }
              state.reactors
              entry
              hEntry with

        | inl hNew =>
            subst hNew

            dsimp only at hCandidate ⊢

            -- The fired event is an implicit field of `fire`, so it is inaccessible by name; it is
            -- determined here by unification against `hReaction`, and the membership premise is a
            -- postponed tactic block for exactly that reason.
            exact
              generalStmtOrigin_of_pending_reaction
                hModelWellFormed
                hCompiled
                hRoutes
                ⟨hEventSide, hBodySide⟩
                (by
                  rw [hQueue]

                  exact
                    List.mem_append.mpr
                      (Or.inr
                        List.mem_cons_self))
                hReaction
                candidate
                hCandidate

        | inr hOld =>
            exact
              hBodySide
                entry
                hOld
                candidate
                hCandidate

  | microstepAdvance hSelected hTime hMicrostep =>
      exact ⟨hEventSide, hBodySide⟩

  | timeAdvance hSelected hForward =>
      exact ⟨hEventSide, hBodySide⟩

/--
The kind-origin invariant survives a τ closure.

The closure lift, in the shape `generalNoPastPending_of_tauSteps` established: the instant-block
spine's alignment premises are `Common.TauSteps`, and every τ step is a `GeneralStep`, so the label
plays no role and the induction is two cases.
-/
theorem generalKindOrigin_of_tauSteps
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state state' : GeneralRuntimeState}
    (hModelWellFormed :
      model.wellFormed =
        true)
    (hCompiled :
      Translation.compileGeneralModel model =
        .ok program)
    (hRoutes :
      Translation.routesOf model =
        .ok routes)
    (hOrigin :
      GeneralKindOrigin
        model
        program
        routes
        state)
    (hSteps :
      Common.TauSteps
        (LF.GeneralStep program)
        LF.GeneralLabel.isTau
        state
        state') :
    GeneralKindOrigin
      model
      program
      routes
      state' := by

  revert hOrigin

  induction hSteps with

  | refl current =>
      intro hOriginCurrent

      exact hOriginCurrent

  | cons headStep headIsTau remainingSteps IH =>
      intro hOriginStep

      exact
        IH
          (generalKindOrigin_of_step
            hModelWellFormed
            hCompiled
            hRoutes
            hOriginStep
            headStep)

/--
The kind-origin invariant transports across α-equivalence.

Only two of α-equivalence's four conjuncts are read, and that is the payoff of keeping the invariant
membership-shaped. The queue clause gives a `List.Perm`, whose `mem_iff` carries the event side; the
reactor clause is already a membership iff, which carries the body side directly. The tag equality
and the pointwise `Store.lookup` agreement are **not** used — the invariant reads neither the tag nor
any lookup, and depending on the lookup clause where membership suffices would make the transport
theorem stronger-premised than it needs to be, which is what the same theorem for the no-past
invariant avoids for the same reason.
-/
theorem generalKindOrigin_of_generalStateAlphaEquiv
    {model : DTR.GeneralModel}
    {program : LF.GeneralProgram}
    {routes : List Translation.GeneralRoute}
    {state state' : GeneralRuntimeState}
    (hOrigin :
      GeneralKindOrigin
        model
        program
        routes
        state)
    (hAlpha :
      generalStateAlphaEquiv
        state
        state') :
    GeneralKindOrigin
      model
      program
      routes
      state' := by

  obtain ⟨_hTag, hReactors, _hLookup, hQueue⟩ :=
    hAlpha

  obtain ⟨hEventSide, hBodySide⟩ :=
    hOrigin

  refine ⟨?_, ?_⟩

  · intro event hEvent

    exact
      hEventSide
        event
        (hQueue.perm.mem_iff.mpr
          hEvent)

  · intro entry hEntry candidate hCandidate

    exact
      hBodySide
        entry
        ((hReactors
          entry.1
          entry.2).mpr
          hEntry)
        candidate
        hCandidate

end LF
end Relico


