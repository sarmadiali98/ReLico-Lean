# `general--traindoor-case-study--positive`

A **general**-family positive benchmark: the paper's RQ1 TrainDoor model — a `Controller` starts a `Train` and a `Door` together; the train reports its movement and the door closes over a 1-time-unit delay, while a `Checker` records a violation if the train moves before the door is closed. Five reactive classes, a `KeepAlive` heartbeat on a 100-time-unit loop.

## Provenance

- **Original source:** `examples.zip:ReLico-main/TrainDoor/TrainDoor.rebeca`, 101 lines, one of the paper's RQ1 verification benchmarks (the base member of the TrainDoor family; TrainDoor2 and TrainDoorFeedback are already in the suite from the corpus wave).
- **Original blocker:** the parameterless external-send target `Checker.trainEvt` — and, behind it, three more of the same boundary: `Checker.doorEvt`, `Train.move`, `Door.close`.
- **Adaptation:** four marker parameters, one per parameterless server that is the target of an external send; each send site passes `0` and no server body reads it. See [`ADAPTATION.md`](ADAPTATION.md).

## Stages

8 stages, terminal `runtime`: `source`, `rmc`, `parser-json`, `decoded-dtr-ast`, `translated-lf-ast`, `lf-source`, `lfc`, `runtime`, through the `--family general` arm.

## Evidence

- every pipeline stage exits 0, including the model checker;
- the generated LF is preserved and SHA-256-pinned at `expected/lf-source/TranslatedLFProgram.lf`;
- RMC reports `satisfied` for `Deadlock-Freedom and No Deadline Missed`.

## Keep-alive

The `KeepAlive` heartbeat recurs on a 100-time-unit delayed self-send, and the train/door race resolves on 1-time-unit delays. Logical time advances and the runtime terminates within its budget.
