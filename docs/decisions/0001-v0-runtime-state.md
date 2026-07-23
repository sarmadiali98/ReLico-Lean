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
