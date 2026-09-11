# bound-payload--payload-binding--positive

This positive bound-payload benchmark exercises message-payload parameter
binding and payload-to-state assignment.

The source declares `dispatch(int payload)`, assigns the incoming payload to
state with `x = payload`, and recursively schedules the same payload.

Formal evidence covers:

- observable weak execution;
- phase weak bisimulation;
- detailed bound-payload semantics;
- weak-foundation interfaces;
- preservation of payload information through observable consumption.

The formal witness covers 44 canonical accepted obligations across four Lean
modules: 20 `#check` obligations and 24 theorem obligations.

The source is recurring. Runtime evidence is therefore a bounded observation
using `--timeout 5 msec --fast`.

This benchmark does not establish source self-termination.
This benchmark does not establish universal program termination.
This benchmark does not establish general scheduler liveness.
This benchmark does not exercise priority selection.
This benchmark does not exercise actor-priority semantics.

Expected route:

1. source
2. rmc
3. parser-json
4. decoded-dtr-ast
5. formal-witness
6. translated-lf-ast
7. lf-source
8. lfc
9. runtime

The package contains exactly 13 files.
