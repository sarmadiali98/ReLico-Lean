# Decision 0004: Trusted Java parser exporter

## Status

Accepted for vertical slice v0; extended by Decision 0005.

## Parser entry point

The frontend bridge uses the existing Rebeca compiler framework:

```text
RebecaModelCompiler.compileRebecaFile
```

It selects:

CompilerExtension.TIMED_REBECA
CoreVersion.CORE_2_1

Parsing and the existing Java semantic checker run before export.

Exporter

The exporter entry point is:

org.rebecalang.compiler.frontendbridge.RebecaV0JsonExporter

It traverses the parser-produced RebecaModel and emits bridge schema
version 1.

It does not invoke the previous Java LinguaFrancaCodeGenerator.
Translation to LF remains exclusively in Lean.

Accepted parser AST fragment

The exporter accepts:

exactly one reactive class;
exactly one main actor of that class;
exactly one integer state variable;
exactly one constructor;
exactly one message server;
assignments to the declared state variable;
integer literals;
references to the declared state variable;
delayed self-sends to the declared message server.

It rejects unsupported parser AST nodes instead of silently dropping
them.

Reproducible check

The command:

frontend/java-bridge/check-v0.sh <artifact.zip>

performs:

real .rebeca fixture
→ existing Timed Rebeca parser
→ Java parser AST
→ bridge JSON
→ Lean JSON decoder
→ Lean DTR AST
→ verified Lean translator
→ LF AST
→ LF/C++ source printer

The generated JSON is structurally compared with the checked v0 JSON
fixture.

Trust boundary

The following frontend components remain trusted:

the existing Java Timed Rebeca parser;
the existing Java semantic checker;
the Java AST-to-JSON exporter.

The versioned JSON decoder and the DTR-to-LF translator execute in Lean.
The previous Java LF generator is not part of this path.

Official LF/C++ validation

The reproducible bridge check also invokes the official lfc compiler
on V0Controller.lf.

The check succeeds only when:

the LF parser accepts the generated source;
CMake configuration succeeds;
generated C++ compilation succeeds;
the V0Controller executable is produced.

## Runtime execution validation

A second finite fixture validates actual execution:

```text
frontend/fixtures/v0-once.rebeca
```

Its constructor schedules one delayed self-message. The message server
updates the state and schedules no further action, allowing the
generated LF/C++ executable to terminate.

The command:

frontend/java-bridge/check-v0-runtime.sh <artifact.zip>

checks:

Timed Rebeca parsing
→ bridge export
→ Lean decoding
→ verified translation
→ LF/C++ rendering
→ lfc generation
→ C++ compilation
→ native execution
→ successful termination

This is an integration test, not a formal verification of the LF
compiler, C++ compiler, runtime, operating system, or hardware.

## Finite-store extension

Decision 0005 adds the generalized exporter:

```text
org.rebecalang.compiler.frontendbridge.RebecaStoreJsonExporter
```

The exporter accepts a finite nonempty list of integer state-variable
declarations. Assignment targets and variable references are validated
against the complete declaration list.

The reusable parser-to-native integration command is:

```text
frontend/java-bridge/check-store.sh <artifact.zip>
```

The schema-version-1 exporter and integration checks remain available
for regression and compatibility testing.
