# Phase 2B2A Execution Preflight

## Status

The Phase-2B1 static audit, full build, direct Lean elaboration, and
artifact validation passed.

This preflight extracts executable parser and RMC contracts before
constructing semantic probe models. It does not execute a model and does
not modify production source.

## Production benchmark stage contract

Ordered stages:

- `source`
- `rmc`
- `parser-json`
- `decoded-dtr-ast`
- `formal-witness`
- `translated-lf-ast`
- `lf-source`
- `lfc`
- `runtime`

The complete `rmc` and `parser-json` stage objects are preserved in the
machine-readable JSON artifact.

## Java bridge wrappers

- `frontend/java-bridge/run-multistore-payload-from-zip.sh` (SHA-256 `7e0dae2270cfd08f1f8b9f993ae485dd424e9e82a975b89d9533b3f4ae44e2c0`)
- `frontend/java-bridge/run-multistore-from-zip.sh` (SHA-256 `1e2f8c497c3aef1e726a8e33ebd50e4cfaa339071142bcd8b18440e1a78a788a`)

Usage, Java invocation, classpath, exporter, parser, model, output, and ZIP
lines are recorded in the JSON artifact.

## CLI usage probes

- `wrapper-no-args:run-multistore-payload-from-zip.sh`: exit=2, timed_out=false
  - stdout: ``
  - stderr: `usage: run-multistore-from-zip.sh <artifact.zip> <input.rebeca> <output.json>`
- `wrapper-help:run-multistore-payload-from-zip.sh`: exit=2, timed_out=false
  - stdout: ``
  - stderr: `usage: run-multistore-from-zip.sh <artifact.zip> <input.rebeca> <output.json>`
- `wrapper-no-args:run-multistore-from-zip.sh`: exit=2, timed_out=false
  - stdout: ``
  - stderr: `usage: run-multistore-from-zip.sh <artifact.zip> <input.rebeca> <output.json>`
- `wrapper-help:run-multistore-from-zip.sh`: exit=2, timed_out=false
  - stdout: ``
  - stderr: `usage: run-multistore-from-zip.sh <artifact.zip> <input.rebeca> <output.json>`
- `rmc-no-args`: exit=0, timed_out=false
  - stdout: `Unexpected exception: Missing required option: s usage: rmc [options] --compactdtg Using this feature, compact DTG is generated on-the-fly from TTS. --debug Enables debug mode in result C++ files. --debug2 Enables debug level 2 mode in result C++ files. -e,--extension <value> Rebeca model extension (CORE_REBECA/TIMED_REBECA/PROBABILIS TIC_REBECA/PROBABILISTIC_TIME_REBECA ). Default is 'CORE_REBECA'. -h,--help Print this message. --nosafemode Disable checking for array index out of bound and acce`
  - stderr: `SLF4J: Failed to load class "org.slf4j.impl.StaticLoggerBinder". SLF4J: Defaulting to no-operation (NOP) logger implementation SLF4J: See http://www.slf4j.org/codes.html#StaticLoggerBinder for further details.`
- `rmc-help`: exit=0, timed_out=false
  - stdout: `Unexpected exception: Missing required option: s usage: rmc [options] --compactdtg Using this feature, compact DTG is generated on-the-fly from TTS. --debug Enables debug mode in result C++ files. --debug2 Enables debug level 2 mode in result C++ files. -e,--extension <value> Rebeca model extension (CORE_REBECA/TIMED_REBECA/PROBABILIS TIC_REBECA/PROBABILISTIC_TIME_REBECA ). Default is 'CORE_REBECA'. -h,--help Print this message. --nosafemode Disable checking for array index out of bound and acce`
  - stderr: `SLF4J: Failed to load class "org.slf4j.impl.StaticLoggerBinder". SLF4J: Defaulting to no-operation (NOP) logger implementation SLF4J: See http://www.slf4j.org/codes.html#StaticLoggerBinder for further details.`

Nonzero usage exits are evidence about the command contract, not tool
failures. No model was supplied.

## Official actor-priority examples

Candidate forms:

- `@priority("2")`
- `@priority(1)`
- `@priority(2)`
- `@priority(3)`
- `@priority(4)`
- `@priority(5)`
- `@priority(6)`
- `@priority(7)`
- `@priority(8)`

Source examples:

- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TimedRebecaPriority.rebeca:11` — `@priority(3)`
- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TimedRebecaPriority.rebeca:28` — `@priority(1)`
- `official-compiler:src/test/resources/org/rebecalang/compiler/modelcompiler/TimedRebecaPriority.rebeca:30` — `@priority("2")`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/Arithmetic_test.rebeca:30` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/Sender_and_Receiver.rebeca:10` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/Sender_and_Receiver.rebeca:17` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/env_example.rebeca:12` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/env_example.rebeca:18` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/env_example.rebeca:34` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/env_example.rebeca:39` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/env_example.rebeca:50` — `@priority(3)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/env_example.rebeca:55` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/hybrid.rebeca:10` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/if_else_example.rebeca:10` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/if_else_example.rebeca:16` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/if_else_example.rebeca:32` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/if_else_example.rebeca:37` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/if_else_example.rebeca:47` — `@priority(3)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/if_else_example.rebeca:52` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_and_switch_with_after.rebeca:7` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_and_switch_with_after.rebeca:22` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_and_switch_with_after.rebeca:30` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_and_switch_with_after.rebeca:31` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_and_switch_with_internal_after.rebeca:6` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_sw.rebeca:10` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_sw.rebeca:16` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_sw.rebeca:32` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_sw.rebeca:37` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_sw.rebeca:44` — `@priority(3)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/node_sw.rebeca:49` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:20` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:29` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:35` — `@priority(3)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:53` — `@priority(4)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:60` — `@priority(5)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:92` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:101` — `@priority(2)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:126` — `@priority(3)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:150` — `@priority(1)`
- `published-parser-artifact:ReLico-fmcad-2026-artifact-v1/benchmarks/phils.rebeca:151` — `@priority(2)`

Complete source contexts are preserved in the JSON artifact. Probe-model
construction must copy the official placement and argument form instead
of guessing from an isolated annotation token.

## Baseline model

The accepted `core--initialization--positive` source is the parser-control
baseline. Its main-block context and SHA-256 are preserved in the JSON
artifact.

## Readiness

Dynamic parser execution contract: **ready**

Official RMC execution contract: **ready**

Semantic model execution performed: **no**

Production source mutation required: **no**

## Next phase

Phase 2B2B will create external temporary probe models and execute the
actual Java parser/JSON bridge for:

1. no actor-priority annotation;
2. local message-server priority only;
3. nonempty actor-priority annotation;
4. a second nonempty actor-priority value;
5. each grammatically plausible explicit-empty form derived from the
   official syntax.

It will record parser exit status, diagnostics, JSON existence and content,
and whether any downstream decoded or LF artifact is produced. RMC
discriminating behavior remains a separate subsequent execution step.
