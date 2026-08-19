import Relico.DTR.GeneralWellFormed
import Relico.Frontend.GeneralElaborator

set_option autoImplicit false

namespace Relico
namespace Frontend

open Lean

/-!
# The `general-v1` decoder

The top of the general frontend: JSON text in, a well-formed `DTR.GeneralModel`
out, and a `GeneralDiagnostic` on every failure path.

Four steps, in this order, because each one is what makes the next one's
question meaningful:

1. **Parse.** `Lean.Json.parse`, failing with `invalidJson`.
2. **Decode the schema.** `Lean.fromJson?` into `RawGeneralModel`, failing with
   `schemaDecodeFailed`. Everything past this point has the right *shape*.
3. **Check the envelope.** `family` and `schemaVersion`, failing with
   `unexpectedFamily` and `unsupportedSchemaVersion`. These two live here rather
   than in the elaborator because a document from a different producer should be
   refused before any of its content is interpreted — the elaborator's
   diagnostics all name a class or a message server, and there is no honest
   context string to give them for a document that was never ours to read.
4. **Elaborate, then gate on well-formedness.** `elaborateGeneralModel` builds
   the model; `DTR.GeneralModel.wellFormed` judges the assembled thing.

The two-layer split of step 4 is the one worth stating. The elaborator decides
everything answerable while looking at a single declaration — an empty
parameter name, a duplicate state variable, a statement kind outside the
fragment. `wellFormed` decides everything answerable only about the whole model
— that a binding names a declared known-rebec, that a send resolves to a real
message server. Neither layer re-asks the other's question, so no pair of
checks can disagree.

Compare `decodeGlobalMultiStorePayloadModelText`, whose steps are the same and
whose error type is `String`. The general reader carries a structured
diagnostic instead, so a test can assert *which* rule refused a document rather
than matching on prose.
-/

/--
Step 1: JSON text to a `Lean.Json` value.

The four sibling decoders build the string `"invalid JSON: " ++ message`. Here
the prefix comes from `GeneralDiagnosticReason.invalidJson.message` instead and
`detail` carries the parser's text alone, so `render` produces the same reading
(`general-v1: invalid JSON: ⟨parser text⟩ in document`) while a test can assert
the reason without depending on a single word of Lean's parser output.

`context` is the literal `"document"` on every decoder-level failure: there is
no class or message server to name yet, and an empty context would render as
though the failure had no location at all.
-/
def parseGeneralJson
    (text : String) :
    GeneralElab Lean.Json :=
  match Lean.Json.parse text with

  | .ok value =>
      .ok value

  | .error message =>
      .error
        (generalDiagnostic
          .invalidJson
          message
          "document"
          none)

/--
Step 2: a `Lean.Json` value to `RawGeneralModel`.

The type ascription on `Lean.fromJson?` is what selects the instance, and is
copied from the sibling decoders because the elaborator cannot infer the target
from the `Except` alone.

A failure here means the document is not a `general-v1` document at all: a
missing required field, or a field of the wrong JSON type. Note the ordering
consequence — this fires *before* the envelope check, so a document from another
producer that happens to lack `classes` is reported as a schema failure rather
than as an unexpected family. That is the honest report: we cannot read its
`family` field with any confidence if we could not read its shape.
-/
def rawGeneralModelOfJson
    (json : Lean.Json) :
    GeneralElab RawGeneralModel :=
  match
    (Lean.fromJson? json :
      Except String RawGeneralModel)
  with

  | .ok value =>
      .ok value

  | .error message =>
      .error
        (generalDiagnostic
          .schemaDecodeFailed
          message
          "document"
          none)

/--
Step 3a: the producer must be the general exporter.

Checked before the version, which reverses the sibling decoder's order
(`GlobalMultiStorePayloadDecoder` tests the version first). The reversal is
deliberate: a version number means nothing until the family is known, since
nothing obliges two families to number their schemas on the same clock. A
`general` document at version 2 is a reader we have not written; a `store`
document at version 1 is a different reader entirely, and saying "unsupported
version" about it would be actively misleading.

`detail` reports the family found, not the family expected. The expectation is
`generalBridgeFamily`, visible in this file and in the schema module; the value
found is the only part the reader of the message cannot already see.
-/
def requireGeneralFamily
    (raw : RawGeneralModel) :
    GeneralElab Unit :=
  if raw.family == generalBridgeFamily then
    .ok ()
  else
    .error
      (generalDiagnostic
        .unexpectedFamily
        raw.family
        "document"
        none)

/--
Step 3b: the schema version must be the one this reader was written against.

Equality, not `≤`. A lower version is a document whose fields may have carried
different meanings, and this reader has no migration for it; a higher version is
a document with fields it would silently ignore. Widening this to a range is a
decision to be made when a version 2 exists and its differences are known, not
in advance.
-/
def requireGeneralSchemaVersion
    (raw : RawGeneralModel) :
    GeneralElab Unit :=
  if raw.schemaVersion == generalBridgeSchemaVersion then
    .ok ()
  else
    .error
      (generalDiagnostic
        .unsupportedSchemaVersion
        (toString raw.schemaVersion)
        "document"
        none)

/--
Classify a well-formedness failure across the five clauses.

`DTR.GeneralModel.wellFormed` is a single `Bool`, so a bare `false` says only that
something is wrong somewhere. The five clauses are therefore re-tested
individually here,
in `wellFormed`'s own conjunct order (`GeneralWellFormed.lean:362-366`), so that
the diagnostic names the rule that actually refused the model.

The cost is one re-evaluation of the clauses, on the failure path only, since the
caller reaches this function only when `wellFormed` has already answered `false`.
The alternative — checking five clauses here and never calling `wellFormed` —
would put the definition of the gate in two places, and a later edit to
`wellFormed` would then change what the build proves without changing what the
frontend accepts. One definition, re-read for its explanation, is the cheaper
error.

`modelNotWellFormed` is the remainder, and is **unreachable** while `wellFormed`
is exactly the conjunction of these five clauses. It is here so that adding a
sixth conjunct without extending this function yields an honest "not well
formed" rather than a misattribution to one of the five. It should not be
deleted on the grounds that it cannot fire: its job is to start firing on the
day the module it mirrors changes.
-/
def classifyGeneralWellFormedness
    (model : DTR.GeneralModel) :
    GeneralDiagnosticReason :=
  if !model.bindingsMatchDeclarations then
    .bindingsMatchDeclarationsFailed
  else if !model.argumentsMatchConstructor then
    .argumentsMatchConstructorFailed
  else if !model.sendTargetsDeclared then
    .sendTargetsDeclaredFailed
  else if !model.sendsResolveToMessageServers then
    .sendsResolveToMessageServersFailed
  else if !model.namesUniqueAndValid then
    .namesUniqueAndValidFailed
  else
    .modelNotWellFormed

/--
Gate an elaborated model on well-formedness.

Separated from the classification above so that the *decision* is made by exactly
one call to `DTR.GeneralModel.wellFormed` and the *explanation* is computed only
when needed. The call is written in dot form, matching
`GlobalMultiStorePayloadDecoder`, because the clause definitions and the
conjunction both live in the `GeneralModel` namespace.
-/
def requireGeneralWellFormed
    (model : DTR.GeneralModel) :
    GeneralElab Unit :=
  if model.wellFormed then
    .ok ()
  else
    .error
      (generalDiagnostic
        (classifyGeneralWellFormedness model)
        ""
        "document"
        none)

/--
A `RawGeneralModel` to a well-formed `DTR.GeneralModel`.

Split out from the text reader, mirroring `decodeRawGlobalMultiStorePayloadModel`,
for two reasons. A test can build a raw model directly and exercise the envelope,
elaboration, and well-formedness rules without routing a string through
`Lean.Json`; and when one of those rules regresses, the failure is attributable
without first ruling out the parser.
-/
def decodeRawGeneralModel
    (raw : RawGeneralModel) :
    GeneralElab DTR.GeneralModel := do

  requireGeneralFamily raw
  requireGeneralSchemaVersion raw

  let model ←
    elaborateGeneralModel raw

  requireGeneralWellFormed model

  pure model

/--
The general frontend's entry point: `general-v1` text to a well-formed
`DTR.GeneralModel`, or the first diagnostic that refused it.

First, not all: the `Except` monad stops at the first failure, so a document with
two problems reports one of them. That is the same behaviour as every sibling
decoder and as the Java exporter, which throws on the first unsupported
construct. Collecting every diagnostic would be a different design — and a
better one for a user fixing a model by hand — but it would have to be the
design of the whole frontend rather than of this module alone, since the
elaborator's `mapM` is what discards the rest of a list after one element fails.

Nothing downstream of this function needs to re-check anything it checked: the
result is a model that satisfies `DTR.GeneralModel.wellFormed`, which is the
hypothesis the stage-D translation and the stage-F/G correspondence theorems are
written against.
-/
def decodeGeneralModelText
    (text : String) :
    GeneralElab DTR.GeneralModel := do

  let json ←
    parseGeneralJson text

  let raw ←
    rawGeneralModelOfJson json

  decodeRawGeneralModel raw


end Frontend
end Relico
