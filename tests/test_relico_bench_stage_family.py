from __future__ import annotations

import argparse
import ast
import importlib.util
import sys
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]

STAGE_TOOL = (
    REPO
    / "tools"
    / "relico_bench_stage.py"
)


def load_stage_tool():
    specification = (
        importlib.util.spec_from_file_location(
            "relico_bench_stage_family_test",
            STAGE_TOOL,
        )
    )

    if (
        specification is None
        or specification.loader is None
    ):
        raise RuntimeError(
            "could not load stage tool"
        )

    module = importlib.util.module_from_spec(
        specification
    )

    sys.modules[specification.name] = module
    specification.loader.exec_module(module)

    return module


def command_parser(
    parser: argparse.ArgumentParser,
    command: str,
) -> argparse.ArgumentParser:
    actions = [
        action
        for action in parser._actions
        if isinstance(
            action,
            argparse._SubParsersAction,
        )
    ]

    if len(actions) != 1:
        raise AssertionError(
            "expected one subparser action"
        )

    return actions[0].choices[command]


def family_action(
    parser: argparse.ArgumentParser,
) -> argparse.Action:
    matches = [
        action
        for action in parser._actions
        if action.dest == "family"
    ]

    if len(matches) != 1:
        raise AssertionError(
            "expected one family action"
        )

    return matches[0]


def function_source(
    name: str,
) -> str:
    source = STAGE_TOOL.read_text(
        encoding="utf-8"
    )

    tree = ast.parse(source)

    matches = [
        node
        for node in tree.body
        if (
            isinstance(node, ast.FunctionDef)
            and node.name == name
        )
    ]

    if len(matches) != 1:
        raise AssertionError(
            "expected one function: " + name
        )

    text = ast.get_source_segment(
        source,
        matches[0],
    )

    if text is None:
        raise AssertionError(
            "could not recover function source"
        )

    return text


class FamilySelectorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.root_parser = (
            load_stage_tool().build_parser()
        )

    def test_parser_json_family_contract(
        self,
    ) -> None:
        action = family_action(
            command_parser(
                self.root_parser,
                "parser-json",
            )
        )

        self.assertEqual(
            action.default,
            "v0",
        )

        self.assertEqual(
            list(action.choices),
            [
                "v0",
                "multi-store-payload",
            ],
        )

    def test_lean_export_family_contract(
        self,
    ) -> None:
        action = family_action(
            command_parser(
                self.root_parser,
                "lean-export",
            )
        )

        self.assertEqual(
            action.default,
            "v0",
        )

        self.assertEqual(
            list(action.choices),
            [
                "v0",
                "multi-store-payload",
            ],
        )

    def test_parser_routes_are_present(
        self,
    ) -> None:
        source = function_source(
            "parser_json_stage"
        )

        self.assertIn(
            "run-from-zip.sh",
            source,
        )

        self.assertIn(
            (
                "run-multistore-payload-"
                "from-zip.sh"
            ),
            source,
        )

    def test_lean_exporter_assignments_are_present(
        self,
    ) -> None:
        source = function_source(
            "lean_export_stage"
        )

        self.assertIn(
            (
                "Relico/Benchmark/"
                "ArtifactExporter.lean"
            ),
            source,
        )

        self.assertIn(
            (
                "Relico/Benchmark/"
                "MultiStorePayload"
                "ArtifactExporter.lean"
            ),
            source,
        )

    def test_lean_command_uses_selected_exporter(
        self,
    ) -> None:
        source = function_source(
            "lean_export_stage"
        )

        self.assertEqual(
            source.count("str(exporter)"),
            1,
        )

        self.assertEqual(
            source.count(
                '"Relico/Benchmark/'
                'ArtifactExporter.lean"'
            ),
            1,
        )

        self.assertEqual(
            source.count(
                '"Relico/Benchmark/'
                'MultiStorePayload'
                'ArtifactExporter.lean"'
            ),
            1,
        )

    def test_family_is_declared_only_for_relevant_commands(
        self,
    ) -> None:
        source = STAGE_TOOL.read_text(
            encoding="utf-8"
        )

        self.assertEqual(
            source.count('"--family"'),
            2,
        )


if __name__ == "__main__":
    unittest.main()
