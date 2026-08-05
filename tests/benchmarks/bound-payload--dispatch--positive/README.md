# bound-payload--dispatch--positive

This positive benchmark exercises a recurring Timed Rebeca self-send whose
message server binds and consumes an integer payload.

Its executable source semantics intentionally match the accepted
`bound-payload--dispatch--negative` boundary benchmark. The distinction is the
selected frontend and artifact route:

- the negative benchmark uses the default legacy V0 route and records the
  parameterized-message boundary;
- this positive benchmark explicitly selects the dedicated
  `multi-store-payload` parser and Lean artifact-export routes.

The production pipeline contains nine stages:

1. source validation;
2. official RMC generation, native compilation, and model checking;
3. dedicated multi-store-payload parser JSON generation;
4. deterministic Lean DTR payload-model export;
5. elaboration of all eight mapped formal-evidence modules;
6. deterministic translated LF payload-program export;
7. payload-aware LF/C++ source rendering;
8. official `lfc` compilation;
9. bounded native execution with `--timeout "5 msec" --fast`.

The source remains recursively scheduled so RMC verifies deadlock freedom.
Native execution terminates at the accepted five-millisecond logical-time
horizon.
