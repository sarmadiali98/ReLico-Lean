# core--initialization--positive

This is the first tracked schema-conforming ReLico production benchmark.
It exercises the singleton initialization model already used by the reviewed
prototype, but the benchmark source is now tracked independently under this
benchmark identifier.

The nine mandatory stages are:

1. source validation;
2. official RMC code generation, generated-C++ compilation, and model checking;
3. trusted Java parser JSON generation;
4. Lean DTR decoding and deterministic AST export;
5. Lean elaboration of the five mapped formal-evidence modules;
6. verified Lean translation and deterministic LF AST export;
7. Lean LF/C++ source printing;
8. official lfc compilation;
9. bounded native execution with `--timeout "5 msec" --fast`.

The deterministic expected artifacts omit absolute paths, durations, build
logs, and generated binary hashes. The `actual/` directory is generated
evidence and is ignored by Git.
