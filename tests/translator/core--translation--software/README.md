# Core translation software tests

These focused cases exercise the executable core translator directly. Each `cases.tsv` row is an
independently runnable assertion over a minimal source value and an exact expected LF value.

The cases cover every core expression and statement constructor, zero-delay preservation, body
ordering, startup and message reaction assembly, actor instance assembly, and the exact public
translation result.
