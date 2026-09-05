# `general--local-declaration--positive`

This positive benchmark belongs to the **general** family and its source is the corpus candidate `local-declaration`, selected in the stage K
pilot wave by measured construct profile from `tests/benchmarks/registry/general-corpus-selection.tsv`
and by the mandatory RMC gate, which reports `satisfied` for it.

## Stages

7 stages, terminal `lfc`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`.

The stage list is the one this benchmark's registry row already declared; it is not widened here. Runtime observation and, where absent, the formal witness were measured to work for this model during selection, so adding them is a registry decision rather than a capability question.

## Evidence

- source: the commented Timed Rebeca model: the corpus candidate verbatim under a benchmark header;
- RMC: `Deadlock-Freedom and No Deadline Missed` is satisfied. A safety witness, not a claim about a particular runtime ordering;
- parser JSON: produced by `frontend/java-bridge/run-general-from-zip.sh` through the `parser-json --family general` arm. Measured against the committed `frontend/fixtures/general/local-declaration.parser.json`, the two documents have identical shape and differ only in `line` fields, each shifted by the 5 header comment lines this benchmark source adds;
- decoded DTR AST, translated LF AST and LF source: the three `lean-export --family general` modes;
- lfc: the generated LF compiles under `lfc 0.11.0` with the C++ target.

## Keep-alive

This model terminates on its own; no bounded-run policy is needed.
