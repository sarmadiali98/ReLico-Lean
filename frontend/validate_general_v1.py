#!/usr/bin/env python3
"""Structural validator for the ``general-v1`` parser-bridge schema.

This is the executable specification of what
``frontend/java-bridge/RebecaGeneralJsonExporter.java`` is allowed to emit.
It is written independently of that exporter, from the restriction list in
``docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md``, so that agreement
between the two is evidence rather than tautology.

It deliberately replaces a JSON Schema file. A schema document that nothing
executes is a second source of truth, and this project has already been bitten
several times by exactly that (a dead ``SCHEMA_VERSION`` constant, nine stale
narrative counters). Everything here runs on every gate.

What it checks, beyond key and type shape: that every cross-reference in the
document resolves. Binding order matches the declared known-rebec order, every
send names a message server its target class actually declares with a matching
arity, every variable read resolves to a state variable or a parameter or an
in-scope loop counter, and a known rebec is never read as a value. Those are
the properties that make the topology static, which is the whole reason the
frontend rejects anything at all.

Usage::

    python3 frontend/validate_general_v1.py <document.json> [...]

Exits non-zero and prints every violation found, rather than only the first,
so one run tells you everything that is wrong with an exporter change.
"""

from __future__ import annotations

import json
import pathlib
import sys

VALUE_TYPES = {"int", "boolean"}

BINARY_OPERATORS = {
    "+", "-", "*", "/", "%",
    "==", "!=", "<", "<=", ">", ">=",
    "&&", "||",
}

UNARY_OPERATORS = {"!", "-"}

STATEMENT_KEYS = {
    "assign": {"kind", "target", "value", "line"},
    "send": {
        "kind", "target", "targetClassName", "messageServer",
        "arguments", "after", "line",
    },
    "if": {"kind", "condition", "then", "else", "line"},
    "for": {"kind", "init", "condition", "update", "body", "line"},
    "declare": {"kind", "name", "type", "value", "line"},
}

EXPRESSION_KEYS = {
    "intLiteral": {"kind", "value", "line"},
    "boolLiteral": {"kind", "value", "line"},
    "variable": {"kind", "name", "line"},
    "binary": {"kind", "operator", "left", "right", "line"},
    "unary": {"kind", "operator", "operand", "line"},
}

# An instance constructor argument and an ``after`` delay are literals written
# without a line, because the exporter builds them from a different code path.
# The asymmetry is deliberate and is pinned here so it cannot drift silently.
BARE_LITERAL_KEYS = {
    "intLiteral": {"kind", "value"},
    "boolLiteral": {"kind", "value"},
}


class Report:
    """Collects violations so that one run reports all of them."""

    def __init__(self) -> None:
        self.violations: list[str] = []

    def fail(self, where: str, message: str) -> None:
        self.violations.append(where + ": " + message)

    def require(self, condition: bool, where: str, message: str) -> bool:
        if not condition:
            self.fail(where, message)

        return condition

    def keys(self, node: object, expected: set[str], where: str) -> bool:
        if not isinstance(node, dict):
            self.fail(where, "expected an object, found " + type(node).__name__)

            return False

        actual = set(node)

        if actual != expected:
            missing = sorted(expected - actual)
            extra = sorted(actual - expected)

            detail = []

            if missing:
                detail.append("missing " + ", ".join(missing))

            if extra:
                detail.append("unexpected " + ", ".join(extra))

            self.fail(where, "; ".join(detail))

            return False

        return True

    def line(self, node: dict, where: str) -> None:
        value = node.get("line")

        if value is None:
            return

        self.require(
            isinstance(value, int) and not isinstance(value, bool) and value >= 1,
            where,
            "line must be null or a positive integer, found " + repr(value),
        )

    def name(self, value: object, where: str) -> None:
        self.require(
            isinstance(value, str) and value.strip() == value and value != "",
            where,
            "expected a bare non-empty name, found " + repr(value),
        )


def validate(document: object, report: Report) -> None:
    if not report.keys(
        document,
        {"schemaVersion", "family", "classes", "instances"},
        "document",
    ):
        return

    report.require(
        document["schemaVersion"] == 1,
        "document",
        "schemaVersion must be 1, found " + repr(document["schemaVersion"]),
    )

    report.require(
        document["family"] == "general",
        "document",
        'family must be "general", found ' + repr(document["family"]),
    )

    classes = document["classes"]
    instances = document["instances"]

    if not isinstance(classes, list) or not isinstance(instances, list):
        report.fail("document", "classes and instances must both be arrays")

        return

    # R1. Fig. 4 writes ClassDecl+ Main, and an empty main has nothing to
    # translate, so both lists are non-empty.
    report.require(len(classes) >= 1, "document", "no reactive class (R1)")
    report.require(len(instances) >= 1, "document", "no instance")

    by_name: dict[str, dict] = {}

    for index, declaration in enumerate(classes):
        where = "classes[" + str(index) + "]"

        if not validate_class(declaration, report, where):
            continue

        if declaration["name"] in by_name:
            report.fail(where, "duplicate class " + declaration["name"])

        by_name[declaration["name"]] = declaration

    for declaration in list(by_name.values()):
        validate_class_references(declaration, by_name, report)

    seen: dict[str, dict] = {}

    for index, instance in enumerate(instances):
        where = "instances[" + str(index) + "]"

        if not validate_instance_shape(instance, report, where):
            continue

        if instance["name"] in seen:
            report.fail(where, "duplicate instance " + instance["name"])

        seen[instance["name"]] = instance

    for instance in list(seen.values()):
        validate_instance_references(instance, by_name, seen, report)


def validate_class(declaration: object, report: Report, where: str) -> bool:
    if not report.keys(
        declaration,
        {
            "name", "queueBound", "line", "knownRebecs",
            "stateVariables", "constructor", "messageServers",
        },
        where,
    ):
        return False

    report.name(declaration["name"], where + ".name")
    report.line(declaration, where)

    bound = declaration["queueBound"]

    # R7. Mandatory, and a bound below one cannot hold a message.
    report.require(
        isinstance(bound, int) and not isinstance(bound, bool) and bound >= 1,
        where + ".queueBound",
        "must be an integer of at least 1, found " + repr(bound),
    )

    for index, known in enumerate(declaration["knownRebecs"]):
        spot = where + ".knownRebecs[" + str(index) + "]"

        if report.keys(known, {"name", "className", "line"}, spot):
            report.name(known["name"], spot + ".name")
            report.name(known["className"], spot + ".className")
            report.line(known, spot)

    for index, variable in enumerate(declaration["stateVariables"]):
        spot = where + ".stateVariables[" + str(index) + "]"

        if report.keys(variable, {"name", "type", "line"}, spot):
            report.name(variable["name"], spot + ".name")
            report.line(variable, spot)
            report.require(
                variable["type"] in VALUE_TYPES,
                spot + ".type",
                "must be one of " + ", ".join(sorted(VALUE_TYPES))
                + ", found " + repr(variable["type"]),
            )

    # D1, D2, D3 all say a block may be absent, so emptiness is never an
    # error here; what is an error is a name colliding across the two
    # namespaces, because then a bare name in a body is ambiguous.
    members: dict[str, str] = {}

    for kind, entries in (
        ("known rebec", declaration["knownRebecs"]),
        ("state variable", declaration["stateVariables"]),
    ):
        for entry in entries:
            if not isinstance(entry, dict):
                continue

            name = entry.get("name")

            if name in members:
                report.fail(
                    where,
                    "member name " + repr(name) + " declared twice, as "
                    + members[name] + " and as " + kind,
                )

            members[name] = kind

    constructor = declaration["constructor"]

    if constructor is not None:
        spot = where + ".constructor"

        if report.keys(constructor, {"line", "parameters", "body"}, spot):
            report.line(constructor, spot)
            validate_parameters(constructor["parameters"], report, spot)

    servers: set[str] = set()

    for index, server in enumerate(declaration["messageServers"]):
        spot = where + ".messageServers[" + str(index) + "]"

        if not report.keys(
            server,
            {"name", "priority", "line", "parameters", "body"},
            spot,
        ):
            continue

        report.name(server["name"], spot + ".name")
        report.line(server, spot)

        if server["name"] in servers:
            report.fail(spot, "duplicate message server " + server["name"])

        servers.add(server["name"])

        priority = server["priority"]

        # R6. One integer literal, optional. Lower means earlier.
        if priority is not None:
            report.require(
                isinstance(priority, int)
                and not isinstance(priority, bool)
                and priority >= 0,
                spot + ".priority",
                "must be null or a non-negative integer, found "
                + repr(priority),
            )

        validate_parameters(server["parameters"], report, spot)

    return True


def validate_parameters(parameters: object, report: Report, where: str) -> None:
    if not isinstance(parameters, list):
        report.fail(where + ".parameters", "expected an array")

        return

    seen: set[str] = set()

    for index, parameter in enumerate(parameters):
        spot = where + ".parameters[" + str(index) + "]"

        if not report.keys(parameter, {"name", "type", "line"}, spot):
            continue

        report.name(parameter["name"], spot + ".name")
        report.line(parameter, spot)

        report.require(
            parameter["type"] in VALUE_TYPES,
            spot + ".type",
            "must be one of " + ", ".join(sorted(VALUE_TYPES))
            + ", found " + repr(parameter["type"]),
        )

        if parameter["name"] in seen:
            report.fail(spot, "duplicate parameter " + parameter["name"])

        seen.add(parameter["name"])


def validate_class_references(
    declaration: dict,
    by_name: dict,
    report: Report,
) -> None:
    """Bodies, in a scope built from the class and the enclosing signature."""
    where = "class " + str(declaration.get("name"))

    for index, known in enumerate(declaration["knownRebecs"]):
        if not isinstance(known, dict):
            continue

        # A known rebec must have an actor type: that is what makes the
        # binding resolvable in main, and therefore the topology static.
        report.require(
            known.get("className") in by_name,
            where + ".knownRebecs[" + str(index) + "]",
            "known rebec " + str(known.get("name")) + " has non-actor type "
            + str(known.get("className")),
        )

    state = {
        variable["name"]
        for variable in declaration["stateVariables"]
        if isinstance(variable, dict) and "name" in variable
    }

    rebecs = {
        known["name"]: known["className"]
        for known in declaration["knownRebecs"]
        if isinstance(known, dict) and "name" in known
    }

    constructor = declaration["constructor"]

    if constructor is not None and isinstance(constructor.get("body"), list):
        walk_statements(
            constructor["body"],
            Context(
                declaration,
                by_name,
                dict.fromkeys(state, True),
                rebecs,
                parameter_names(constructor),
                where + ".constructor",
            ),
            report,
        )

    for index, server in enumerate(declaration["messageServers"]):
        if not isinstance(server, dict) or not isinstance(server.get("body"), list):
            continue

        walk_statements(
            server["body"],
            Context(
                declaration,
                by_name,
                dict.fromkeys(state, True),
                rebecs,
                parameter_names(server),
                where + ".messageServers[" + str(index) + "]",
            ),
            report,
        )


def parameter_names(signature: dict) -> set[str]:
    parameters = signature.get("parameters")

    if not isinstance(parameters, list):
        return set()

    return {
        parameter["name"]
        for parameter in parameters
        if isinstance(parameter, dict) and "name" in parameter
    }


class Context:
    """The names a body may read, and the class it belongs to."""

    def __init__(
        self,
        declaration: dict,
        by_name: dict,
        state: dict,
        rebecs: dict,
        parameters: set,
        where: str,
    ) -> None:
        self.declaration = declaration
        self.by_name = by_name
        self.state = state
        self.rebecs = rebecs
        self.parameters = parameters
        self.locals: list[str] = []
        self.where = where

    def readable(self, name: str) -> bool:
        return (
            name in self.state
            or name in self.parameters
            or name in self.locals
        )

    def at(self, suffix: str) -> str:
        return self.where + suffix


def walk_statements(
    statements: object,
    context: Context,
    report: Report,
    inside: str = ".body",
) -> None:
    if not isinstance(statements, list):
        report.fail(context.at(inside), "expected an array of statements")

        return

    # D7 for bodies. A local declared inside a body leaves scope with the
    # body, so the depth is recorded on entry and restored on exit — the same
    # discipline the `for` rule below has always applied to its counter,
    # lifted to every body now that stage I admits declarations in them.
    depth = len(context.locals)

    for index, statement in enumerate(statements):
        walk_statement(
            statement,
            context,
            report,
            inside + "[" + str(index) + "]",
            declare_allowed=True,
        )

    del context.locals[depth:]


def walk_statement(
    statement: object,
    context: Context,
    report: Report,
    suffix: str,
    declare_allowed: bool,
) -> None:
    where = context.at(suffix)

    if not isinstance(statement, dict):
        report.fail(where, "expected a statement object")

        return

    kind = statement.get("kind")

    if kind not in STATEMENT_KEYS:
        report.fail(
            where,
            "unknown statement kind " + repr(kind) + "; R14 admits "
            + ", ".join(sorted(STATEMENT_KEYS)),
        )

        return

    if kind == "declare" and not declare_allowed:
        # R15 and D7. What remains refused is a declaration in a `for`
        # header's update slot — the one call site that still passes
        # `declare_allowed=False`, since an update is an expression slot.
        report.fail(where, "a declare in a for update (R15, D7)")

    if not report.keys(statement, STATEMENT_KEYS[kind], where):
        return

    report.line(statement, where)

    if kind == "assign":
        target = statement["target"]
        report.name(target, where + ".target")

        if target in context.rebecs:
            report.fail(
                where,
                "assignment to known rebec " + str(target)
                + " (R21: the topology is fixed by main)",
            )
        elif not context.readable(target):
            report.fail(where, "assignment to undeclared name " + str(target))

        walk_expression(statement["value"], context, report, suffix + ".value")

        return

    if kind == "declare":
        report.name(statement["name"], where + ".name")

        report.require(
            statement["type"] in VALUE_TYPES,
            where + ".type",
            "a loop counter must have a value type, found "
            + repr(statement["type"]),
        )

        walk_expression(statement["value"], context, report, suffix + ".value")

        context.locals.append(statement["name"])

        return

    if kind == "if":
        walk_expression(
            statement["condition"], context, report, suffix + ".condition"
        )

        # Branch bodies are separate bodies: each gets its own depth snapshot
        # inside walk_statements, so a local declared in one branch is gone
        # before the other branch or the enclosing body is walked.
        walk_statements(statement["then"], context, report, suffix + ".then")
        walk_statements(statement["else"], context, report, suffix + ".else")

        return

    if kind == "for":
        depth = len(context.locals)

        walk_statement(
            statement["init"], context, report, suffix + ".init",
            declare_allowed=True,
        )

        walk_expression(
            statement["condition"], context, report, suffix + ".condition"
        )

        walk_statement(
            statement["update"], context, report, suffix + ".update",
            declare_allowed=False,
        )

        walk_statements(statement["body"], context, report, suffix + ".body")

        # D7. The counter leaves scope at the end of the loop.
        del context.locals[depth:]

        return

    walk_send(statement, context, report, suffix)


def walk_send(
    statement: dict,
    context: Context,
    report: Report,
    suffix: str,
) -> None:
    where = context.at(suffix)

    target = statement["target"]
    target_class_name = statement["targetClassName"]

    if not isinstance(target, dict) or target.get("kind") not in {
        "self", "knownRebec",
    }:
        report.fail(
            where + ".target",
            "R18 admits self or a known rebec, found " + repr(target),
        )

        return

    if target["kind"] == "self":
        if not report.keys(target, {"kind"}, where + ".target"):
            return

        report.require(
            target_class_name == context.declaration.get("name"),
            where,
            "a self send whose targetClassName is "
            + str(target_class_name) + " rather than "
            + str(context.declaration.get("name")),
        )
    else:
        if not report.keys(target, {"kind", "name"}, where + ".target"):
            return

        declared = context.rebecs.get(target["name"])

        if declared is None:
            report.fail(
                where,
                "D6: a send to " + str(target["name"])
                + ", which is not a known rebec of "
                + str(context.declaration.get("name")),
            )

            return

        report.require(
            declared == target_class_name,
            where,
            "a send to known rebec " + str(target["name"]) + " of type "
            + str(declared) + " carrying targetClassName "
            + str(target_class_name),
        )

    receiver = context.by_name.get(target_class_name)

    if receiver is None:
        report.fail(where, "send to undeclared class " + str(target_class_name))

        return

    name = statement["messageServer"]
    report.name(name, where + ".messageServer")

    server = next(
        (
            candidate
            for candidate in receiver["messageServers"]
            if isinstance(candidate, dict) and candidate.get("name") == name
        ),
        None,
    )

    if server is None:
        report.fail(
            where,
            "a send of " + str(name) + ", which class "
            + str(target_class_name) + " does not declare",
        )

        return

    arguments = statement["arguments"]
    parameters = server.get("parameters") or []

    if not isinstance(arguments, list):
        report.fail(where + ".arguments", "expected an array")

        return

    if len(arguments) != len(parameters):
        report.fail(
            where,
            "a send of " + str(name) + " with " + str(len(arguments))
            + " arguments where " + str(len(parameters)) + " are declared",
        )

    for index, argument in enumerate(arguments):
        walk_expression(
            argument, context, report,
            suffix + ".arguments[" + str(index) + "]",
        )

    validate_after(statement["after"], report, where + ".after")


def validate_after(after: object, report: Report, where: str) -> None:
    """D9 and R19. Absent is null, never rewritten to zero."""
    if after is None:
        return

    if not report.keys(after, BARE_LITERAL_KEYS["intLiteral"], where):
        return

    report.require(
        after.get("kind") == "intLiteral",
        where,
        "an after delay must be an integer literal, found "
        + repr(after.get("kind")),
    )

    value = after.get("value")

    report.require(
        isinstance(value, int)
        and not isinstance(value, bool)
        and value >= 0,
        where,
        "an after delay must be a non-negative integer, found " + repr(value),
    )


def walk_expression(
    expression: object,
    context: Context,
    report: Report,
    suffix: str,
) -> None:
    where = context.at(suffix)

    if not isinstance(expression, dict):
        report.fail(where, "expected an expression object")

        return

    kind = expression.get("kind")

    if kind not in EXPRESSION_KEYS:
        report.fail(
            where,
            "unknown expression kind " + repr(kind) + "; D5 admits "
            + ", ".join(sorted(EXPRESSION_KEYS)),
        )

        return

    if not report.keys(expression, EXPRESSION_KEYS[kind], where):
        return

    report.line(expression, where)

    if kind == "intLiteral":
        value = expression["value"]

        report.require(
            isinstance(value, int)
            and not isinstance(value, bool)
            and value >= 0,
            where,
            "an integer literal must be non-negative, found " + repr(value)
            + " (write a negation with the unary minus)",
        )

        return

    if kind == "boolLiteral":
        report.require(
            isinstance(expression["value"], bool),
            where,
            "a boolean literal must be true or false, found "
            + repr(expression["value"]),
        )

        return

    if kind == "variable":
        name = expression["name"]
        report.name(name, where + ".name")

        if name in context.rebecs:
            report.fail(
                where,
                "a use of known rebec " + str(name)
                + " as a value (A1: a rebec reference is not a value)",
            )
        elif not context.readable(name):
            report.fail(where, "a read of undeclared name " + str(name))

        return

    if kind == "binary":
        report.require(
            expression["operator"] in BINARY_OPERATORS,
            where,
            "D5 admits " + " ".join(sorted(BINARY_OPERATORS)) + ", found "
            + repr(expression["operator"]),
        )

        walk_expression(expression["left"], context, report, suffix + ".left")
        walk_expression(expression["right"], context, report, suffix + ".right")

        return

    report.require(
        expression["operator"] in UNARY_OPERATORS,
        where,
        "D5 admits " + " ".join(sorted(UNARY_OPERATORS)) + ", found "
        + repr(expression["operator"]),
    )

    walk_expression(expression["operand"], context, report, suffix + ".operand")


def validate_instance_shape(instance: object, report: Report, where: str) -> bool:
    if not report.keys(
        instance,
        {"name", "className", "priority", "line", "bindings", "arguments"},
        where,
    ):
        return False

    report.name(instance["name"], where + ".name")
    report.name(instance["className"], where + ".className")
    report.line(instance, where)

    priority = instance["priority"]

    if priority is not None:
        report.require(
            isinstance(priority, int)
            and not isinstance(priority, bool)
            and priority >= 0,
            where + ".priority",
            "must be null or a non-negative integer, found " + repr(priority),
        )

    return True


def validate_instance_references(
    instance: dict,
    by_name: dict,
    instances: dict,
    report: Report,
) -> None:
    where = "instance " + str(instance["name"])

    declaration = by_name.get(instance["className"])

    if declaration is None:
        report.fail(
            where,
            "of undeclared reactive class " + str(instance["className"]),
        )

        return

    known = [
        entry
        for entry in declaration["knownRebecs"]
        if isinstance(entry, dict)
    ]

    bindings = instance["bindings"]

    if not isinstance(bindings, list):
        report.fail(where + ".bindings", "expected an array")

        return

    # R5. Positional, so order carries meaning: the nth binding belongs to the
    # nth known rebec. A reordered list would silently rewire the topology.
    if len(bindings) != len(known):
        report.fail(
            where,
            "binding " + str(len(bindings)) + " known rebecs where class "
            + str(instance["className"]) + " declares " + str(len(known)),
        )
    else:
        for index, binding in enumerate(bindings):
            spot = where + ".bindings[" + str(index) + "]"

            if not report.keys(
                binding, {"knownRebec", "instance", "className"}, spot
            ):
                continue

            report.require(
                binding["knownRebec"] == known[index].get("name"),
                spot,
                "out of order: names " + str(binding["knownRebec"])
                + " where the class declares "
                + str(known[index].get("name")) + " at that position",
            )

            bound = instances.get(binding["instance"])

            if bound is None:
                report.fail(
                    spot,
                    "bound to undeclared instance " + str(binding["instance"]),
                )

                continue

            report.require(
                bound["className"] == binding["className"],
                spot,
                "claims class " + str(binding["className"])
                + " but instance " + str(binding["instance"]) + " has class "
                + str(bound["className"]),
            )

            report.require(
                binding["className"] == known[index].get("className"),
                spot,
                "binds a " + str(binding["className"]) + " where known rebec "
                + str(known[index].get("name")) + " has type "
                + str(known[index].get("className")),
            )

    constructor = declaration["constructor"]
    parameters = [] if constructor is None else (constructor.get("parameters") or [])
    arguments = instance["arguments"]

    if not isinstance(arguments, list):
        report.fail(where + ".arguments", "expected an array")

        return

    if len(arguments) != len(parameters):
        report.fail(
            where,
            "passing " + str(len(arguments)) + " constructor arguments where "
            + str(instance["className"]) + " declares " + str(len(parameters)),
        )

        return

    for index, argument in enumerate(arguments):
        spot = where + ".arguments[" + str(index) + "]"
        parameter = parameters[index]

        if not isinstance(argument, dict):
            report.fail(spot, "expected a literal object")

            continue

        kind = argument.get("kind")

        if kind not in BARE_LITERAL_KEYS:
            report.fail(
                spot,
                "R4 admits a literal only, found " + repr(kind),
            )

            continue

        report.keys(argument, BARE_LITERAL_KEYS[kind], spot)

        # D8. The literal must match the declared parameter type, which is the
        # whole reason R4's IntLit is read as "literal" rather than "integer".
        expected = (
            "boolLiteral"
            if parameter.get("type") == "boolean"
            else "intLiteral"
        )

        report.require(
            kind == expected,
            spot,
            "a " + str(kind) + " where parameter "
            + str(parameter.get("name")) + " is declared "
            + str(parameter.get("type")),
        )


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(
            "usage: validate_general_v1.py <document.json> [...]",
            file=sys.stderr,
        )

        return 2

    failed = False

    for name in argv[1:]:
        path = pathlib.Path(name)

        try:
            document = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            print(path.name + ": unreadable: " + str(error))
            failed = True

            continue

        report = Report()
        validate(document, report)

        if report.violations:
            failed = True
            print(path.name + ": " + str(len(report.violations)) + " violation(s)")

            for violation in report.violations:
                print("  " + violation)
        else:
            print(path.name + ": general-v1 OK")

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
