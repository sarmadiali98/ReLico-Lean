# Core frontend decoder software tests

These are focused, table-driven software tests for the core bridge decoder. Each row in `cases.tsv`
is an independently runnable positive or negative test, implemented by the named Lean value in
`Relico/Tests/FrontendDecoder.lean` and executed through `relico-translator-test`.

Unlike broad source-to-runtime fixtures, each case isolates one decoder decision or error precedence
rule. Coverage includes valid and invalid JSON, semantic error propagation, both model bodies, and
zero-delay and signed-integer boundaries. The unified runner exposes every row as
`lean-case::<case_id>`.
