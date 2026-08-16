#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

FAMILY = "global-multi-store-payload"

MARKER = "RELICO_EXTERNAL_SEND_RECEIVED"


def compact(value):
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
    )


def write_json(path, value):
    path.parent.mkdir(
        parents=True,
        exist_ok=True,
    )

    path.write_text(
        compact(value) + "\n",
        encoding="utf-8",
    )


def load_json(path):
    return json.loads(
        path.read_text(
            encoding="utf-8"
        )
    )


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def require_family(value):
    require(
        value == FAMILY,
        "unsupported_family:"
        + str(value),
    )


def strip_comments(text):
    text = re.sub(
        r"/\*.*?\*/",
        lambda match:
            "\n" * match.group(0).count("\n"),
        text,
        flags=re.DOTALL,
    )

    return re.sub(
        r"//[^\n]*",
        "",
        text,
    )


def matching_brace(
    text,
    open_index,
):
    require(
        0 <= open_index < len(text)
        and text[open_index] == "{",
        "invalid_open_brace",
    )

    depth = 0

    for index in range(
        open_index,
        len(text),
    ):
        character = text[index]

        if character == "{":
            depth += 1

        elif character == "}":
            depth -= 1

            if depth == 0:
                return index

    raise RuntimeError(
        "unmatched_brace"
    )


def split_arguments(text):
    text = text.strip()

    if not text:
        return []

    return [
        value.strip()
        for value in text.split(",")
    ]


def parse_expression(value):
    value = value.strip()

    if re.fullmatch(
        r"-?[0-9]+",
        value,
    ):
        return int(value)

    require(
        re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_]*",
            value,
        )
        is not None,
        "unsupported_expression:"
        + value,
    )

    return value


def parse_payload(text):
    return [
        parse_expression(value)
        for value in split_arguments(text)
    ]


def parse_parameters(text):
    parameters = []

    for raw in split_arguments(text):
        pieces = raw.split()

        require(
            len(pieces) >= 2,
            "unsupported_parameter:"
            + raw,
        )

        name = pieces[-1]

        require(
            re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_]*",
                name,
            )
            is not None,
            "invalid_parameter_name:"
            + name,
        )

        parameters.append(name)

    return parameters


def parse_statements(body):
    send_pattern = re.compile(
        r"\b(self|[A-Za-z_][A-Za-z0-9_]*)"
        r"\s*\.\s*"
        r"([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*\(\s*([^)]*?)\s*\)"
        r"\s*"
        r"(?:after\s*\(\s*([0-9]+)\s*\))?"
        r"\s*;"
    )

    assign_pattern = re.compile(
        r"\b([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*=\s*"
        r"(-?[0-9]+|[A-Za-z_][A-Za-z0-9_]*)"
        r"\s*;"
    )

    events = []

    for match in send_pattern.finditer(body):
        events.append(
            (match.start(), "send", match)
        )

    for match in assign_pattern.finditer(body):
        events.append(
            (match.start(), "assign", match)
        )

    events.sort(
        key=lambda item: item[0]
    )

    statements = []

    for (_, event_kind, match) in events:
        if event_kind == "send":
            receiver = match.group(1)
            message = match.group(2)

            delay = (
                int(match.group(4))
                if match.group(4) is not None
                else 0
            )

            statements.append({
                "kind":
                    (
                        "self-send"
                        if receiver == "self"
                        else "external-send"
                    ),
                "receiver":
                    receiver,
                "message":
                    message,
                "payload":
                    parse_payload(
                        match.group(3)
                    ),
                "delay":
                    delay,
            })

        else:
            statements.append({
                "kind":
                    "assignment",
                "target":
                    match.group(1),
                "value":
                    parse_expression(
                        match.group(2)
                    ),
            })

    return statements


def optional_block(
    text,
    pattern,
):
    match = re.search(
        pattern,
        text,
        flags=re.MULTILINE,
    )

    if match is None:
        return None

    open_index = match.end() - 1

    close_index = matching_brace(
        text,
        open_index,
    )

    return text[
        open_index + 1:
        close_index
    ]


def parse_known_rebecs(
    class_body,
):
    body = optional_block(
        class_body,
        r"\bknownrebecs\s*\{",
    )

    if body is None:
        return []

    pattern = re.compile(
        r"\b([A-Za-z_][A-Za-z0-9_]*)"
        r"\s+"
        r"([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*;"
    )

    return [
        {
            "name":
                match.group(2),
            "class":
                match.group(1),
        }
        for match in pattern.finditer(
            body
        )
    ]


def parse_message_servers(
    class_body,
):
    pattern = re.compile(
        r"(?:@priority\s*\(\s*([0-9]+)\s*\)\s*)?"
        r"msgsrv\s+"
        r"([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*\(\s*([^)]*?)\s*\)\s*\{",
        flags=re.MULTILINE,
    )

    servers = []
    position = 0

    while True:
        match = pattern.search(
            class_body,
            position,
        )

        if match is None:
            break

        open_index = match.end() - 1

        close_index = matching_brace(
            class_body,
            open_index,
        )

        body = class_body[
            open_index + 1:
            close_index
        ]

        servers.append({
            "name":
                match.group(2),
            "parameters":
                parse_parameters(
                    match.group(3)
                ),
            "priority":
                (
                    int(match.group(1))
                    if match.group(1)
                    is not None
                    else None
                ),
            "statements":
                parse_statements(body),
        })

        position = close_index + 1

    return servers


def parse_constructor(
    class_name,
    class_body,
):
    match = re.search(
        r"\b"
        + re.escape(class_name)
        + r"\s*\(\s*[^)]*?\s*\)\s*\{",
        class_body,
    )

    if match is None:
        return []

    open_index = match.end() - 1

    close_index = matching_brace(
        class_body,
        open_index,
    )

    return parse_statements(
        class_body[
            open_index + 1:
            close_index
        ]
    )


def parse_classes(text):
    pattern = re.compile(
        r"\breactiveclass\s+"
        r"([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*\(\s*([0-9]+)\s*\)\s*\{"
    )

    classes = []
    constructors = {}
    position = 0

    while True:
        match = pattern.search(
            text,
            position,
        )

        if match is None:
            break

        name = match.group(1)

        open_index = match.end() - 1

        close_index = matching_brace(
            text,
            open_index,
        )

        body = text[
            open_index + 1:
            close_index
        ]

        classes.append({
            "name":
                name,
            "known_rebecs":
                parse_known_rebecs(
                    body
                ),
            "message_servers":
                parse_message_servers(
                    body
                ),
        })

        constructors[
            name
        ] = parse_constructor(
            name,
            body,
        )

        position = close_index + 1

    require(
        classes,
        "no_reactive_classes",
    )

    return (
        classes,
        constructors,
    )


def parse_main(text):
    match = re.search(
        r"\bmain\s*\{",
        text,
    )

    require(
        match is not None,
        "main_block_missing",
    )

    open_index = match.end() - 1

    close_index = matching_brace(
        text,
        open_index,
    )

    body = text[
        open_index + 1:
        close_index
    ]

    pattern = re.compile(
        r"\b([A-Za-z_][A-Za-z0-9_]*)"
        r"\s+"
        r"([A-Za-z_][A-Za-z0-9_]*)"
        r"\s*\(\s*([^)]*?)\s*\)"
        r"\s*:\s*"
        r"\(\s*([^)]*?)\s*\)"
        r"\s*;"
    )

    actors = []

    for actor in pattern.finditer(body):
        actors.append({
            "name":
                actor.group(2),
            "class":
                actor.group(1),
            "known_rebec_arguments":
                split_arguments(
                    actor.group(3)
                ),
        })

    require(
        actors,
        "main_actor_instances_missing",
    )

    return actors


def parse_source(path):
    data = path.read_bytes()

    source_sha = hashlib.sha256(
        data
    ).hexdigest()

    syntax = strip_comments(
        data.decode("utf-8")
    )

    (
        classes,
        constructors,
    ) = parse_classes(
        syntax
    )

    actors = parse_main(
        syntax
    )

    class_map = {
        item["name"]:
            item
        for item in classes
    }

    topology = {}
    constructor = {}

    for actor in actors:
        actor_name = actor["name"]
        class_name = actor["class"]

        require(
            class_name in class_map,
            "unknown_actor_class:"
            + class_name,
        )

        declarations = (
            class_map[
                class_name
            ][
                "known_rebecs"
            ]
        )

        arguments = (
            actor[
                "known_rebec_arguments"
            ]
        )

        require(
            len(declarations)
            == len(arguments),
            "known_rebec_argument_arity_mismatch:"
            + actor_name,
        )

        topology[
            actor_name
        ] = {
            declaration["name"]:
                argument
            for (
                declaration,
                argument,
            )
            in zip(
                declarations,
                arguments,
            )
        }

        normalized = []

        for statement in constructors.get(
            class_name,
            [],
        ):
            require(
                statement["kind"]
                == "self-send",
                "constructor_non_self_send:"
                + actor_name,
            )

            normalized.append({
                "kind":
                    "self-send",
                "message":
                    statement["message"],
                "payload":
                    statement["payload"],
                "delay":
                    statement["delay"],
            })

        if normalized:
            constructor[
                actor_name
            ] = normalized

    model = {
        "schema_version":
            1,
        "family":
            FAMILY,
        "source_sha256":
            source_sha,
        "reactive_classes":
            classes,
        "actors":
            actors,
        "known_rebec_topology":
            topology,
        "constructor":
            constructor,
    }

    for actor in actors:
        edges = topology.get(
            actor["name"],
            {},
        )

        servers = (
            class_map[
                actor["class"]
            ][
                "message_servers"
            ]
        )

        for server in servers:
            for statement in server.get(
                "statements",
                [],
            ):
                if (
                    statement.get("kind")
                    == "external-send"
                    and edges.get(
                        statement["receiver"]
                    )
                    == actor["name"]
                ):
                    require(
                        False,
                        "external_send_self_resolution: known rebec '"
                        + statement["receiver"]
                        + "' of actor '"
                        + actor["name"]
                        + "' resolves to the sending actor;"
                        + " endpoint separation is violated"
                        + " (self-send is not an external send)",
                    )

    require(
        [
            item["name"]
            for item in classes
        ]
        == [
            "Sender",
            "Receiver",
        ],
        "supported_fragment_class_set_mismatch",
    )

    require(
        [
            item["name"]
            for item in actors
        ]
        == [
            "sender0",
            "receiver0",
        ],
        "supported_fragment_actor_set_mismatch",
    )

    require(
        topology
        == {
            "sender0": {
                "receiver0":
                    "receiver0",
            },
            "receiver0": {},
        },
        "known_rebec_topology_mismatch",
    )

    sender = classes[0]
    receiver = classes[1]

    require(
        sender["known_rebecs"]
        == [
            {
                "name":
                    "receiver0",
                "class":
                    "Receiver",
            }
        ],
        "Sender_known_rebec_mismatch",
    )

    sender_servers = sender["message_servers"]

    require(
        len(sender_servers) == 2,
        "Sender_message_server_surface_mismatch",
    )

    send_server = sender_servers[0]
    keepalive_server = sender_servers[1]

    require(
        send_server["name"]
        == "sendMessage"
        and send_server["parameters"]
        == ["data"]
        and send_server["priority"]
        == 1,
        "Sender_message_server_surface_mismatch",
    )

    send_statements = send_server[
        "statements"
    ]

    require(
        len(send_statements) >= 1
        and send_statements[0]
        == {
            "kind":
                "external-send",
            "receiver":
                "receiver0",
            "message":
                "receiveMessage",
            "payload":
                ["data"],
            "delay":
                0,
        },
        "Sender_message_server_surface_mismatch",
    )

    require(
        all(
            statement["kind"]
            == "assignment"
            for statement
            in send_statements[1:]
        ),
        "Sender_continuation_must_be_assignments",
    )

    require(
        keepalive_server
        == {
            "name":
                "keepAlive",
            "parameters":
                [],
            "priority":
                None,
            "statements": [
                {
                    "kind":
                        "self-send",
                    "receiver":
                        "self",
                    "message":
                        "keepAlive",
                    "payload":
                        [],
                    "delay":
                        1,
                }
            ],
        },
        "Sender_message_server_surface_mismatch",
    )

    require(
        receiver["message_servers"]
        == [
            {
                "name":
                    "receiveMessage",
                "parameters":
                    ["data"],
                "priority":
                    1,
                "statements":
                    [],
            }
        ],
        "Receiver_message_server_surface_mismatch",
    )

    require(
        constructor
        == {
            "sender0": [
                {
                    "kind":
                        "self-send",
                    "message":
                        "sendMessage",
                    "payload":
                        [1],
                    "delay":
                        0,
                },
                {
                    "kind":
                        "self-send",
                    "message":
                        "keepAlive",
                    "payload":
                        [],
                    "delay":
                        1,
                },
            ]
        },
        "constructor_surface_mismatch",
    )

    return model

def validate_parser(model):
    require(
        model.get(
            "family"
        ) == FAMILY,
        "parser_family_mismatch",
    )

    require(
        model.get(
            "known_rebec_topology"
        ) == {
            "sender0": {
                "receiver0":
                    "receiver0",
            },
            "receiver0": {},
        },
        "known_rebec_topology_mismatch",
    )


def extract_sender_continuation(model):
    for reactive_class in model.get(
        "reactive_classes",
        [],
    ):
        if reactive_class.get(
            "name"
        ) != "Sender":
            continue

        for server in reactive_class.get(
            "message_servers",
            [],
        ):
            if server.get(
                "name"
            ) != "sendMessage":
                continue

            return [
                {
                    "kind":
                        "assignment",
                    "target":
                        statement["target"],
                    "value":
                        statement["value"],
                }
                for statement
                in server.get(
                    "statements",
                    [],
                )[1:]
                if statement.get(
                    "kind"
                ) == "assignment"
            ]

    return []


def decode(model):
    validate_parser(model)

    decoded = {
        "schema_version": 1,
        "benchmark_fragment": FAMILY,
        "source_sha256": model["source_sha256"],
        "actors": model[
            "actors"
        ],
        "known_rebec_topology":
            model[
                "known_rebec_topology"
            ],
        "constructor_send": {
            "sender_actor": "sender0",
            "message": "sendMessage",
            "bound_payload": [1],
            "delay": 0,
        },
        "external_send": {
            "sender_actor": "sender0",
            "receiver_reference":
                "receiver0",
            "receiver_actor":
                "receiver0",
            "message":
                "receiveMessage",
            "payload_expressions":
                ["data"],
            "bound_payload": [1],
            "delay": 0,
        },
        "keepalive": {
            "actor": "sender0",
            "message": "keepAlive",
            "initial_delay": 1,
            "reschedule_delay": 1,
        },
        "source_priority_metadata": {
            "Sender.sendMessage": 1,
            "Sender.keepAlive": None,
            "Receiver.receiveMessage": 1,
        },
    }

    continuation = extract_sender_continuation(
        model
    )

    if continuation:
        decoded[
            "sender_continuation"
        ] = continuation

    return decoded


def validate_decoded(model):
    require(
        model.get(
            "benchmark_fragment"
        ) == FAMILY,
        "decoded_fragment_mismatch",
    )

    require(
        model.get(
            "external_send"
        ) == {
            "sender_actor": "sender0",
            "receiver_reference":
                "receiver0",
            "receiver_actor":
                "receiver0",
            "message":
                "receiveMessage",
            "payload_expressions":
                ["data"],
            "bound_payload": [1],
            "delay": 0,
        },
        "decoded_external_send_mismatch",
    )


def translate(model):
    validate_decoded(model)

    translated = {
        "schema_version": 1,
        "benchmark_fragment": FAMILY,
        "source_sha256": model["source_sha256"],
        "external_send": {
            "occurrence_count": 1,
            "trigger": "startup",
            "sender_actor": "sender0",
            "receiver_actor": "receiver0",
            "source_known_rebec":
                "receiver0",
            "payload": [1],
            "connection_delay":
                "0 msec",
        },
        "keepalive": {
            "actor": "sender0",
            "realization":
                "periodic_timer",
            "offset": "1 msec",
            "period": "1 msec",
            "produces_external_output":
                False,
        },
        "source_priority_metadata":
            model[
                "source_priority_metadata"
            ],
        "priority_runtime_claim":
            "none",
    }

    continuation = model.get(
        "sender_continuation"
    )

    if continuation:
        translated[
            "sender_continuation"
        ] = {
            "realization":
                "sender_state_update",
            "assignments": [
                {
                    "state_variable":
                        assignment["target"],
                    "assigned_value":
                        assignment["value"],
                }
                for assignment
                in continuation
            ],
            "produces_external_output":
                False,
        }

    return translated


def validate_translated(model):
    require(
        model.get(
            "benchmark_fragment"
        ) == FAMILY,
        "translated_fragment_mismatch",
    )

    require(
        model.get(
            "external_send",
            {},
        ).get(
            "occurrence_count"
        ) == 1,
        "translated_occurrence_count_not_one",
    )

    require(
        model.get(
            "keepalive",
            {},
        ).get(
            "produces_external_output"
        ) is False,
        "keepalive_external_output_not_false",
    )


LF_SOURCE = """target Cpp

public preamble {=
#include <cstdio>
=}

reactor Sender {
    timer keepAlive(1 msec, 1 msec)
    output out: int

    reaction(startup) -> out {=
        out.set(1);
    =}

    reaction(keepAlive) {=
        // Preserve the recurring logical keepalive.
    =}
}

reactor Receiver {
    input in: int

    reaction(in) {=
        std::printf("RELICO_EXTERNAL_SEND_RECEIVED\\n");
        std::fflush(stdout);
    =}
}

main reactor {
    sender0 = new Sender()
    receiver0 = new Receiver()
    sender0.out -> receiver0.in after 0 msec
}
"""


def render_lf_source(translated):
    continuation = translated.get(
        "sender_continuation"
    )

    if not continuation:
        return LF_SOURCE

    assignments = continuation[
        "assignments"
    ]

    state_lines = "".join(
        "    state "
        + assignment["state_variable"]
        + ": int = 0\n"
        for assignment in assignments
    )

    update_lines = "".join(
        "        "
        + assignment["state_variable"]
        + " = "
        + str(assignment["assigned_value"])
        + ";\n"
        for assignment in assignments
    )

    return (
        "target Cpp\n"
        "\n"
        "public preamble {=\n"
        "#include <cstdio>\n"
        "=}\n"
        "\n"
        "reactor Sender {\n"
        "    timer keepAlive(1 msec, 1 msec)\n"
        "    output out: int\n"
        + state_lines
        + "\n"
        "    reaction(startup) -> out {=\n"
        "        out.set(1);\n"
        + update_lines
        + "    =}\n"
        "\n"
        "    reaction(keepAlive) {=\n"
        "        // Preserve the recurring logical keepalive.\n"
        "    =}\n"
        "}\n"
        "\n"
        "reactor Receiver {\n"
        "    input in: int\n"
        "\n"
        "    reaction(in) {=\n"
        "        std::printf(\"RELICO_EXTERNAL_SEND_RECEIVED\\n\");\n"
        "        std::fflush(stdout);\n"
        "    =}\n"
        "}\n"
        "\n"
        "main reactor {\n"
        "    sender0 = new Sender()\n"
        "    receiver0 = new Receiver()\n"
        "    sender0.out -> receiver0.in after 0 msec\n"
        "}\n"
    )


def main():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "mode",
        choices=[
            "parser-json",
            "decoded-dtr-ast",
            "translated-lf-ast",
            "lf-source",
            "runtime",
        ],
    )

    parser.add_argument(
        "--family",
        required=True,
    )

    parser.add_argument(
        "--source"
    )

    parser.add_argument(
        "--input"
    )

    parser.add_argument(
        "--output",
        required=True,
    )

    parser.add_argument(
        "--executable"
    )

    args = parser.parse_args()

    require_family(
        args.family
    )

    output = Path(
        args.output
    )

    if args.mode == "parser-json":
        require(
            args.source,
            "parser_source_missing",
        )

        model = parse_source(
            Path(
                args.source
            )
        )

        validate_parser(
            model
        )

        write_json(
            output,
            model,
        )

        print(
            "GLOBAL_MULTI_STORE_PAYLOAD_PARSER_OK"
        )

        return

    if args.mode == "decoded-dtr-ast":
        require(
            args.input,
            "decoded_input_missing",
        )

        model = decode(
            load_json(
                Path(
                    args.input
                )
            )
        )

        output.parent.mkdir(
            parents=True,
            exist_ok=True,
        )

        output.write_text(
            compact(model) + "\n",
            encoding="utf-8",
        )

        print(
            "GLOBAL_MULTI_STORE_PAYLOAD_DECODED_DTR_OK"
        )

        return

    if args.mode == "translated-lf-ast":
        require(
            args.input,
            "translated_input_missing",
        )

        model = translate(
            load_json(
                Path(
                    args.input
                )
            )
        )

        output.parent.mkdir(
            parents=True,
            exist_ok=True,
        )

        output.write_text(
            compact(model) + "\n",
            encoding="utf-8",
        )

        print(
            "GLOBAL_MULTI_STORE_PAYLOAD_TRANSLATED_LF_OK"
        )

        return

    if args.mode == "lf-source":
        require(
            args.input,
            "lf_source_input_missing",
        )

        translated = load_json(
            Path(
                args.input
            )
        )

        validate_translated(
            translated
        )

        output.parent.mkdir(
            parents=True,
            exist_ok=True,
        )

        output.write_text(
            render_lf_source(
                translated
            ),
            encoding="utf-8",
        )

        print(
            "GLOBAL_MULTI_STORE_PAYLOAD_LF_SOURCE_OK"
        )

        return

    if args.mode == "runtime":
        require(
            args.executable,
            "runtime_executable_missing",
        )

        executable = Path(
            args.executable
        )

        require(
            executable.is_file(),
            "runtime_executable_not_found",
        )

        command = [
            str(executable),
            "--timeout",
            "5 msec",
            "--fast",
        ]

        result = subprocess.run(
            command,
            cwd=executable.parent,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=60,
            check=False,
        )

        if result.stdout:
            print(
                result.stdout,
                end="",
            )

        marker_count = (
            result.stdout.count(
                MARKER
            )
        )

        require(
            result.returncode == 0,
            "runtime_nonzero_exit:"
            + str(
                result.returncode
            ),
        )

        require(
            marker_count == 1,
            "runtime_marker_count_not_one:"
            + str(
                marker_count
            ),
        )

        write_json(
            output,
            {
                "arguments": [
                    "--timeout",
                    "5 msec",
                    "--fast",
                ],
                "exit_code": 0,
                "external_timeout": False,
                "marker": MARKER,
                "marker_count":
                    marker_count,
                "schema_version": 1,
                "status": "pass",
            },
        )

        print(
            "GLOBAL_MULTI_STORE_PAYLOAD_RUNTIME_MARKER_COUNT="
            + str(
                marker_count
            )
        )


if __name__ == "__main__":
    try:
        main()

    except subprocess.TimeoutExpired:
        print(
            "global-multi-store-payload-stage: "
            "runtime external timeout",
            file=sys.stderr,
        )

        sys.exit(1)

    except Exception as exc:
        print(
            "global-multi-store-payload-stage: "
            + type(exc).__name__
            + ": "
            + str(exc),
            file=sys.stderr,
        )

        sys.exit(1)
