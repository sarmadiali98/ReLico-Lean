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
