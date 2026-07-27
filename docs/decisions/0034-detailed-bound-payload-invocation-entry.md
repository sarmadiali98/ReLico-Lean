# Detailed bound-payload invocation entry

Status: accepted

Date: 2026-07-27

## Problem

Canonical detailed bound-payload initialization is intentionally idle.

Both the source and generated-LF states begin with:

- no active body;
- an empty pending-event queue;
- an empty activation-local parameter environment.

Those states cannot initiate a nontrivial payload execution. The repository
contains no general environment-input or event-injection transition to extend.

The payload development therefore needs an explicit semantic boundary that
represents one invocation supplied by the environment.

## Decision

Use direct invocation-entry state construction rather than introducing a new
environment transition system.

One source pending message and one generated-LF pending logical action are
constructed directly from:

- the payload message server;
- the complete ordered payload;
- a logical delay;
- the canonical source time and LF initial tag.

## Source occurrence

`DTR.PayloadMessageServer.invocationPendingMessage` uses
`DTR.PendingMessage.scheduleWithPayload` at source time zero.

The source invocation-ready state contains exactly this occurrence in its
pending-message queue.

It otherwise retains the canonical idle initialization fields:

- logical time zero;
- the supplied persistent state value;
- `ParameterStore.empty`;
- no active body.

## Generated-LF occurrence

`LF.PayloadReaction.invocationPendingAction` uses
`LF.PendingAction.scheduleWithPayload` at `LF.initialTag`.

The generated invocation-ready state contains exactly this action in its
pending-action queue.

It otherwise retains:

- `LF.initialTag`;
- the same persistent state value;
- `ParameterStore.empty`;
- no active body.

## Pending-event correspondence

`boundPayloadInvocationPending_correspond` proves that the two occurrences
preserve:

- generated action naming;
- logical arrival time;
- exact ordered payload equality.

`boundPayloadInvocationQueues_correspond` lifts this result to the singleton
pending-event queues.

## Invocation-state correspondence

`boundPayloadInvocationStates_correspond` proves runtime-state correspondence
for the two invocation-ready states.

`detailedBoundPayloadInvocationStates_correspond` lifts the result to stable
detailed states.

## Scheduler admissibility

`initialTag_precedesOrEqual_schedule` proves that scheduling from
`LF.initialTag` never creates an action in the past.

The proof distinguishes:

- zero delay, which retains logical time and advances the microstep;
- positive delay, which advances logical time.

Singleton queues make their unique source and target occurrences earliest.

## Forward dispatch compatibility

`boundPayloadInvocation_forwardDispatchCompatible` discharges the complete
conditional scheduler premise required by detailed forward payload simulation.

The witness is the unique generated-LF pending action, with:

- singleton removal;
- pending-payload correspondence;
- empty residual-queue correspondence;
- earliest-target eligibility;
- not-past target scheduling.

## Exact dispatch

When

`ParameterStore.bindPayload server.parameters payload = some boundParameters`,

the checkpoint proves:

- `boundPayloadInvocation_sourceDispatch`;
- `boundPayloadInvocation_targetDispatch`.

Both dispatches:

- remove their singleton occurrence;
- install the same ordered parameter binding;
- advance to the corresponding logical time or tag;
- activate the source body and compiled target body;
- leave empty residual queues.

## Activated-state correspondence

`boundPayloadInvocationDispatchedStates_correspond` proves correspondence
between the two post-dispatch runtime states.

The resulting states preserve:

- logical time;
- persistent state;
- activation-local parameter environment;
- empty residual queues;
- body compilation.

## Package theorem

`boundPayloadInvocationEntry_package` exposes the complete invocation boundary:

- stable detailed entry-state correspondence;
- forward dispatch compatibility;
- exact source dispatch;
- exact target dispatch;
- activated runtime-state correspondence.

## Scope

This checkpoint models one externally supplied payload invocation.

It does not yet provide:

- a reusable environment transition relation;
- multiple simultaneous external invocations;
- arbitrary initial pending-event queues;
- preservation of scheduler invariants across later self-sends;
- recursive finite compatibility discharge;
- premise-free finite observable execution correspondence;
- public executable translator packaging.
