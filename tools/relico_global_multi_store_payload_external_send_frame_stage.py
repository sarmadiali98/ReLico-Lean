#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from pathlib import Path

TARGET = "global-multi-actor-payload--external-send-frame--negative"

FORMAL_TEST = "Relico/Tests/GlobalMultiStorePayloadExternalSendFrame.lean"

STAGES = [
    "source",
    "rmc",
    "parser-json",
    "decoded-dtr-ast",
    "expected-boundary-stage",
    "diagnostics",
]

REQUIRED_NAMES = [
    "positive_source_sender_continuation_installed",
    "positive_source_sender_queue_is_unchanged",
    "positive_source_receiver_update_survives",
    "positive_target_sender_continuation_installed",
    "positive_sender_states_after_correspond",
    "positive_frame_transition_corresponds",
    "positive_frame_history_is_unique",
    "zero_delay_frame_attempt_succeeds",
    "zero_delay_target_frame_applies",
    "payload_evaluation_failure_performs_no_transition",
    "duplicate_collision_performs_no_transition",
    "self_resolution_performs_no_transition",
    "arbitrary_unrelated_actor_is_preserved",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(
        path.read_bytes()
    ).hexdigest()


def write_json(
    path: Path,
    value: dict,
) -> None:
    path.parent.mkdir(
        parents=True,
        exist_ok=True,
    )

    path.write_text(
        json.dumps(
            value,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def boundary(args):
    parser_model = json.loads(
        args.parser_json.read_text(
            encoding="utf-8"
        )
    )

    if (
        parser_model.get("family")
        != "global-multi-store-payload"
    ):
        raise RuntimeError(
            "parser_family_mismatch"
        )

    decoded = args.decoded.read_text(
        encoding="utf-8"
    )

    if not decoded.strip():
        raise RuntimeError(
            "decoded_dtr_ast_empty"
        )

    manifest = json.loads(
        args.manifest.read_text(
            encoding="utf-8"
        )
    )

    names = [
        (
            stage.get("name")
            or stage.get("stage")
        )
        for stage in manifest.get(
            "stages",
            [],
        )
        if isinstance(
            stage,
            dict,
        )
    ]

    if names != STAGES:
        raise RuntimeError(
            "manifest_stage_contract_mismatch"
        )

    formal_text = (
        args.repo
        / FORMAL_TEST
    ).read_text(
        encoding="utf-8"
    )

    missing = [
        name
        for name in REQUIRED_NAMES
        if name not in formal_text
    ]

    if missing:
        raise RuntimeError(
            "formal_obligations_missing:"
            + ",".join(missing)
        )

    with args.obligations.open(
        "r",
        encoding="utf-8",
        newline="",
    ) as handle:
        rows = list(
            csv.DictReader(
                handle,
                delimiter="\t",
            )
        )

    target_rows = [
        row
        for row in rows
        if row.get(
            "final_benchmark_id"
        )
        == TARGET
    ]

    if len(target_rows) != 27:
        raise RuntimeError(
            "obligation_count_mismatch"
        )

    if any(
        row.get("mapping_status")
        != "accepted"
        or row.get("evidence_role")
        != "source-capability"
        for row in target_rows
    ):
        raise RuntimeError(
            "obligation_contract_mismatch"
        )

    result = {
        "authoritative_module":
            FORMAL_TEST,
        "benchmark_id":
            TARGET,
        "boundary":
            "source-grounded-external-send-frame-transition-witness-absent",
        "decoded_dtr_ast_sha256":
            sha256(args.decoded),
        "expected_absence":
            True,
        "last_supported_stage":
            "decoded-dtr-ast",
        "parser_family":
            "global-multi-store-payload",
        "parser_json_sha256":
            sha256(args.parser_json),
        "required_frame_obligations":
            REQUIRED_NAMES,
        "schema_version":
            1,
        "source_capability_obligation_count":
            27,
        "status":
            "pass",
    }

    write_json(
        args.output,
        result,
    )

    print(
        "GLOBAL_MULTI_STORE_PAYLOAD_EXTERNAL_SEND_FRAME_BOUNDARY_OK"
    )


def diagnostics(args):
    value = json.loads(
        args.input.read_text(
            encoding="utf-8"
        )
    )

    if (
        value.get("benchmark_id")
        != TARGET
        or value.get("status")
        != "pass"
        or value.get("expected_absence")
        is not True
        or value.get("last_supported_stage")
        != "decoded-dtr-ast"
        or value.get("parser_family")
        != "global-multi-store-payload"
    ):
        raise RuntimeError(
            "boundary_input_mismatch"
        )

    write_json(
        args.output,
        {
            "benchmark_id":
                TARGET,
            "boundary":
                value["boundary"],
            "decoded_dtr_ast_succeeded":
                True,
            "expected_boundary_confirmed":
                True,
            "last_supported_stage":
                "decoded-dtr-ast",
            "legacy_multi_actor_parser_rejection_used":
                False,
            "parser_json_succeeded":
                True,
            "schema_version":
                1,
            "status":
                "pass",
        },
    )

    print(
        "GLOBAL_MULTI_STORE_PAYLOAD_EXTERNAL_SEND_FRAME_DIAGNOSTICS_OK"
    )


def main() -> int:
    parser = argparse.ArgumentParser()

    subs = parser.add_subparsers(
        dest="command",
        required=True,
    )

    first = subs.add_parser(
        "frame-boundary"
    )

    first.add_argument(
        "--benchmark-id",
        required=True,
    )
    first.add_argument(
        "--repo",
        type=Path,
        required=True,
    )
    first.add_argument(
        "--parser-json",
        type=Path,
        required=True,
    )
    first.add_argument(
        "--decoded",
        type=Path,
        required=True,
    )
    first.add_argument(
        "--manifest",
        type=Path,
        required=True,
    )
    first.add_argument(
        "--obligations",
        type=Path,
        required=True,
    )
    first.add_argument(
        "--output",
        type=Path,
        required=True,
    )

    second = subs.add_parser(
        "diagnostics"
    )

    second.add_argument(
        "--input",
        type=Path,
        required=True,
    )
    second.add_argument(
        "--output",
        type=Path,
        required=True,
    )

    args = parser.parse_args()

    try:
        if args.command == "frame-boundary":
            if args.benchmark_id != TARGET:
                raise RuntimeError(
                    "benchmark_id_mismatch"
                )

            boundary(args)

        elif args.command == "diagnostics":
            diagnostics(args)

        return 0

    except Exception as exc:
        print(
            "global-multi-store-payload-external-send-frame-stage: "
            + type(exc).__name__
            + ": "
            + str(exc),
            file=sys.stderr,
        )

        return 1


if __name__ == "__main__":
    raise SystemExit(main())
