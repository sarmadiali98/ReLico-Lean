# `bound-payload--priority-preservation--positive`

This positive benchmark demonstrates preservation of one explicit local
message-server priority value through the supported bound-payload frontend and
translation route.

The source contains one `@priority(2)` annotation on a payload message server.
The benchmark does not claim priority-based selection and does not use actor
priority.

## Explicit metadata witnesses

- source: local message-server `@priority(2)`;
- parser JSON: message-server priority `2`;
- decoded DTR AST: payload message-server priority `some 2`;
- formal witness: `bound_payload_priority_preserved`;
- translated LF AST: payload reaction priority `some 2`.

## Downstream witnesses

Generated LF source is a generation witness, not a literal priority-metadata
witness for this single-reaction model. The `lfc` result is a successful
compilation witness.

Runtime is intentionally excluded.
