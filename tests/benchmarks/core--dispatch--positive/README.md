# core--dispatch--positive

Positive end-to-end benchmark for the implemented core dispatch boundary.

## Semantic contract

Base DTR and LF dispatch is occurrence-sensitive and removes exactly one
earliest pending message or action. DTR advances to the selected message
arrival time; LF advances to the selected complete tag. Dispatch installs the
selected message-server or reaction body.

The formal boundary covers forward and backward state correspondence, machine
steps, runtime well-formedness preservation, and trace correspondence.

Message-server priority eligibility and generated-reaction priority order are
formal refinements over base dispatch. The source model does not require
priority syntax. Actor priority is outside this benchmark because the core
boundary has no global actor-selection interface.

## Evidence

The benchmark requires source-plus-runtime-observation evidence. Java parsing,
Lean decoding and export, LFC, and runtime execution are route evidence rather
than semantic theorem coverage.

## Route

1. source
2. rmc
3. parser-json
4. decoded-dtr-ast
5. formal-witness
6. translated-lf-ast
7. lf-source
8. lfc
9. runtime

The tracked package contains thirteen files, nine hashed expected artifacts,
and runtime as the terminal stage.
