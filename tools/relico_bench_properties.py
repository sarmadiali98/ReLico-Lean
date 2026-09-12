from __future__ import annotations

from pathlib import Path
from typing import Any, TypeVar
import re


PROPERTY_ID = re.compile(r"[a-z0-9][a-z0-9-]*\Z")
RMC_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
LOGICS = {"Assertion", "TCTL"}
EXPECTED_RESULTS = {"TRUE", "FALSE"}

ErrorType = TypeVar("ErrorType", bound=Exception)


def _raise(error_type: type[ErrorType], message: str) -> None:
    raise error_type(message)


def _strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//[^\n]*", "", text)


def _matching_brace(text: str, opening: int) -> int:
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return index
    return -1


def property_declarations(text: str) -> dict[str, list[str]]:
    """Conservatively enforce one property container and one named formula."""
    cleaned = _strip_comments(text).strip()
    header = re.match(r"property\s*\{", cleaned)
    if header is None:
        return {}
    opening = cleaned.find("{", header.start())
    closing = _matching_brace(cleaned, opening)
    if closing < 0 or cleaned[closing + 1 :].strip():
        return {}

    declarations: dict[str, list[str]] = {"Assertion": [], "TCTL": []}
    block_counts = {"Assertion": 0, "TCTL": 0}
    body = cleaned[opening + 1 : closing]
    depth = 0
    index = 0
    while index < len(body):
        if body[index] == "{":
            depth += 1
            index += 1
            continue
        if body[index] == "}":
            depth -= 1
            if depth < 0:
                return {}
            index += 1
            continue
        if depth == 0:
            match = re.match(r"(Assertion|TCTL)\s*\{", body[index:])
            if match is not None:
                logic = match.group(1)
                block_counts[logic] += 1
                block_opening = index + match.group(0).rfind("{")
                block_closing = _matching_brace(body, block_opening)
                if block_closing < 0:
                    return {}
                block = body[block_opening + 1 : block_closing]
                names = re.findall(r"(?m)^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:", block)
                declarations[logic].extend(names)
                index = block_closing + 1
                continue
        index += 1
    if any(count > 1 for count in block_counts.values()):
        return {}
    return declarations


def validate_properties(
    *,
    benchmark_id: str,
    benchmark_directory: Path,
    properties: object,
    error_type: type[ErrorType],
) -> list[dict[str, Any]]:
    if properties is None:
        return []
    if not isinstance(properties, list):
        _raise(error_type, f"{benchmark_id}: properties is not an array")

    validated: list[dict[str, Any]] = []
    property_ids: set[str] = set()
    rmc_names: set[str] = set()
    benchmark_root = benchmark_directory.resolve()

    for index, value in enumerate(properties):
        label = f"{benchmark_id}: property {index + 1}"
        if not isinstance(value, dict):
            _raise(error_type, f"{label} is not an object")
        required_fields = {
            "property_id", "logic", "rmc_name", "expected", "source", "required"
        }
        missing = required_fields - set(value)
        extra = set(value) - required_fields - {"description"}
        if missing:
            _raise(error_type, f"{label} is missing {', '.join(sorted(missing))}")
        if extra:
            _raise(error_type, f"{label} has unknown fields {', '.join(sorted(extra))}")

        property_id = value["property_id"]
        rmc_name = value["rmc_name"]
        logic = value["logic"]
        expected = value["expected"]
        source = value["source"]
        required = value["required"]
        description = value.get("description")

        if not isinstance(property_id, str) or PROPERTY_ID.fullmatch(property_id) is None:
            _raise(error_type, f"{label} has invalid property_id")
        if property_id in property_ids:
            _raise(error_type, f"{benchmark_id}: duplicate property_id {property_id}")
        property_ids.add(property_id)
        if not isinstance(rmc_name, str) or RMC_NAME.fullmatch(rmc_name) is None:
            _raise(error_type, f"{label} has invalid rmc_name")
        if rmc_name in rmc_names:
            _raise(error_type, f"{benchmark_id}: duplicate rmc_name {rmc_name}")
        rmc_names.add(rmc_name)
        if logic not in LOGICS:
            _raise(error_type, f"{label} has unsupported logic {logic!r}")
        if expected not in EXPECTED_RESULTS:
            _raise(error_type, f"{label} has unsupported expected result {expected!r}")
        if not isinstance(required, bool):
            _raise(error_type, f"{label} required flag is invalid")
        if description is not None and (not isinstance(description, str) or not description):
            _raise(error_type, f"{label} description is invalid")
        if not isinstance(source, str) or not source:
            _raise(error_type, f"{label} source is invalid")
        relative = Path(source)
        if (
            relative.is_absolute()
            or relative == Path(".")
            or ".." in relative.parts
            or not source.startswith("property/")
            or relative.suffix != ".property"
        ):
            _raise(error_type, f"{label} has unsafe property source {source!r}")
        source_path = (benchmark_directory / relative).resolve()
        if source_path.parent == benchmark_root or benchmark_root not in source_path.parents:
            _raise(error_type, f"{label} source escapes the benchmark directory")
        if not source_path.is_file():
            _raise(error_type, f"{label} property source is missing: {source}")

        declarations = property_declarations(source_path.read_text(encoding="utf-8"))
        expected_declarations = declarations.get(logic, [])
        other_logic = "TCTL" if logic == "Assertion" else "Assertion"
        if expected_declarations != [rmc_name] or declarations.get(other_logic):
            _raise(
                error_type,
                f"{label} must contain exactly one {logic} declaration named {rmc_name}",
            )
        validated.append(value)

    return validated
