# ReLico Documentation

This index separates documentation for the current system from historical development records. Current scope and correctness claims should be read from the first two sections.

## Current Documentation

- [Project overview](../README.md)
- [Accepted General-family fragment](supported-fragment-general.md)
- [Verification and trusted boundary](trusted-boundary.md)
- [General-family correctness claims](claims/general-family-correctness.md)
- [Test and evidence model](../tests/README.md)
- [Evaluation catalog](../evaluation/README.md)
- [Application benchmarks](../benchmarks/README.md)
- [Examples and demonstration runs](../examples/README.md)
- [General frontend fixture contract](../frontend/fixtures/general/README.md)

## Architecture and Semantics

- [Accepted General-family fragment](supported-fragment-general.md)
- [Verification and trusted boundary](trusted-boundary.md)
- [`docs/decisions/`](decisions/) contains dated design decisions. These are historical decision records; later measurements may refine their context.

## Formal Verification

- [General-family correctness claims](claims/general-family-correctness.md)
- [Singleton v0 correctness milestone](claims/v0-correctness.md)
- [Finite-store correctness milestone](claims/finite-store-correctness.md)

The singleton and finite-store claim documents describe compatibility families, not the current General-family scope.

## Supported Fragment

- [Current General-family fragment](supported-fragment-general.md)
- [Original singleton vertical slice](supported-fragment.md), retained as a historical milestone

## Evaluation

- [Evaluation catalog](../evaluation/README.md)
- [Application benchmarks](../benchmarks/README.md)
- [Test catalog](../tests/README.md)
- [Examples](../examples/README.md)

The VMCAI 2027 evaluation suite is under active development and is not frozen for artifact submission.

## Developer Notes

- [Contributing](../CONTRIBUTING.md)
- [General frontend fixtures](../frontend/fixtures/general/README.md)

## Historical Development Notes

- `STAGE_*_DESIGN.md` and `STAGE_*_FINDINGS.md` record dated development stages.
- [`decisions/`](decisions/) contains dated design decisions.
- [`actor-priority/`](actor-priority/) records the phased actor-priority investigation and integration work.
- [Paper correction ledger](PAPER_CORRECTIONS.md) is a research ledger, not current product documentation.
- [Paper-fragment transcription](dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md) analyzes the paper fragment; it is not the active accepted-fragment definition.
- [`archive/`](archive/) contains superseded roadmaps, handoffs, and state records.

Historical documents may use old project names, paths, counts, or present-tense status statements. They are retained as records and are not authoritative for the current tool.
