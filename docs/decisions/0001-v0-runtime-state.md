# Decision 0001: Vertical-Slice Runtime State

## Status

Accepted for vertical slice v0.

## DTR runtime state

The initial DTR runtime state contains:

- the current logical time;
- the integer value of the single state variable;
- an occurrence-preserving list of pending messages;
- the remaining statements of the currently executing constructor or message server.

A pending message contains:

- its message-server name;
- its arrival time.

The list representation preserves multiplicity. Two structurally identical list elements represent two pending message occurrences.

## LF runtime state

The generated-LF runtime state contains:

- the current LF tag;
- the integer value of the single reactor state variable;
- an occurrence-preserving list of pending logical actions;
- the remaining statements of the currently executing reaction.

An LF tag contains:

- logical time;
- microstep.

A pending logical action contains:

- its action name;
- its scheduled tag.

## Scheduling convention

Scheduling an action with zero delay at tag `(t, m)` produces tag:

```text
(t, m + 1)

Scheduling an action with positive delay d produces tag:

(t + d, 0)

This convention will be reviewed when the generated-LF operational semantics is compared in detail with the LF runtime semantics.

Expression evaluation

Vertical slice v0 contains one integer state variable. Expression evaluation therefore receives the current integer state value directly.

Well-formedness separately guarantees that every source or target variable reference names the declared state variable.


## Source-target correspondence

DTR states contain logical time but no microstep. LF states contain a
complete tag with both logical time and microstep.

The initial correspondence relation therefore preserves the logical-time
projection of LF tags rather than asserting equality between DTR time and
the complete LF tag.

A pending DTR message corresponds to a pending LF logical action when:

- its message name maps to the generated action name;
- both occurrences have the same logical arrival time.

The LF microstep remains target-level scheduling information. Message and
action multiplicity is preserved occurrence by occurrence.


## Constructor and startup entry

Constructor/startup entry states use logical time zero, LF microstep
zero, and empty pending-event collections.

The pre-constructor integer value is an explicit parameter. The
formalization does not silently assume a source-language or LF runtime
default value. Corresponding DTR and LF entry states receive the same
value.

The DTR active body is the constructor body. The corresponding LF
active body is the generated startup-reaction body.


## Scheduler selection

Pending messages and actions are stored as occurrence-preserving lists.
Scheduler selection removes one occurrence by position; duplicate values
are not collapsed.

DTR selects an occurrence with minimum logical arrival time. Multiple
occurrences at the same minimum time remain nondeterministically
selectable.

LF selects an occurrence with the minimum lexicographic tag. Logical
time is compared first, followed by microstep.

Consequently, source equal-time nondeterminism and target microstep
ordering are not represented by a simple one-step bijection. Dispatch
correctness will require an explicitly stated abstraction or weak
execution correspondence.


## Dispatch transitions

Dispatch is enabled only when the active statement body is empty.

A DTR dispatch removes one earliest pending message occurrence, advances
logical time to its arrival time, and loads the declared message-server
body. An additional premise prevents dispatching an event in the past.

An LF dispatch removes one earliest pending logical-action occurrence,
advances the complete LF tag to the action tag, and loads the generated
message-reaction body. The selected tag must not precede the current tag.

These dispatch rules are currently separate from statement execution.
A later combined transition system will connect dispatch and active-body
steps.


## Conditional forward dispatch

Backward dispatch correspondence is unconditional: an LF-earliest action
always maps to a DTR message with minimum logical arrival time.

Forward dispatch correspondence requires an additional compatibility
condition. The LF occurrence aligned with the selected DTR message must:

- be earliest under lexicographic LF tag ordering;
- not precede the current LF tag;
- leave a target queue corresponding to the residual source queue.

This condition is necessary. A DTR scheduler may select either of two
messages at the same logical time, while LF may require the action with
the lower microstep to execute first.


## Combined machine transitions

The complete one-step machine relation contains two rule classes:

- statement execution while an active body is present;
- dispatch when the active body is empty and an eligible pending event
  is selected.

The combined relation preserves the existing statement and dispatch
labels by wrapping them in machine-level labels. This layer introduces
no additional scheduling policy.


## Machine runtime invariant

Runtime well-formedness is preserved by both classes of DTR machine
transition.

Statement execution preserves well-formedness by consuming a
well-formed statement. Dispatch preserves it because the activated
message-server body is well formed in a well-formed model, and every
remaining pending message was already present before occurrence
removal.

Consequently, finite backward machine simulation may carry the source
runtime invariant inductively across statement and dispatch steps.


## Finite backward machine execution

The unconditional backward one-step theorem lifts to arbitrary finite
generated-LF machine executions.

For a well-formed DTR model and corresponding initial runtime states,
every finite LF sequence of statement and dispatch transitions has:

- a finite DTR machine execution;
- pointwise-corresponding machine labels;
- corresponding final runtime states;
- a well-formed final DTR state.

The finite forward theorem remains conditional because LF scheduler
compatibility must hold at each source dispatch step.
