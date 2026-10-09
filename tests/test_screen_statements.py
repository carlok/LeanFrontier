from __future__ import annotations

import io
import pathlib
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import frontier_validate  # noqa: E402
import screen_statements  # noqa: E402

MODULE = """import LeanFrontier.Other
import Mathlib.Data.Nat.Basic

open Finset
namespace LeanFrontier.Toy

def double (n : Nat) : Nat := 2 * n

theorem double_eq (n : Nat) : double n = 2 * n := rfl

theorem plain (n : Nat) : n + 0 = n := by simp

end LeanFrontier.Toy
"""


class StatementScreenTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.path = pathlib.Path(self.temp.name) / "Toy.lean"
        self.path.write_text(MODULE, encoding="utf-8")
        self.code = frontier_validate.strip_comments(MODULE)
        self.goals = frontier_validate.statement_goals(self.path)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_each_goal_is_stated_in_its_context_with_the_modules_imports(self) -> None:
        source, spans = screen_statements.module_source(
            self.code, self.goals, ["LeanFrontier.Toy.double_eq", "LeanFrontier.Toy.plain"])
        self.assertTrue(source.startswith("import Mathlib\nimport LeanFrontier.Other\nimport Mathlib.Data.Nat.Basic\n"), source)
        self.assertNotIn("import LeanFrontier\n", source)
        lines = source.splitlines()
        for name, start, end in spans:
            block = lines[start - 1:end]
            self.assertEqual(block[0], "section")
            self.assertEqual(block[-1], "end")
            self.assertIn("set_option autoImplicit false", block)
            self.assertIn("namespace LeanFrontier.Toy", block)
            self.assertIn("  sorry", block)
        self.assertEqual([name for name, _, _ in spans], ["LeanFrontier.Toy.double_eq", "LeanFrontier.Toy.plain"])

    def test_errors_are_attributed_to_the_goal_whose_lines_they_fall_in(self) -> None:
        source, spans = screen_statements.module_source(
            self.code, self.goals, ["LeanFrontier.Toy.double_eq", "LeanFrontier.Toy.plain"])
        _, first_start, _ = spans[0]
        output = (f"/tmp/Toy.lean:{first_start + 4}:30: error(lean.unknownIdentifier): Unknown identifier `double`\n"
                  f"/tmp/Toy.lean:{first_start + 4}:31: error: a second error\n")
        errors = screen_statements.attribute_errors(output, spans)
        self.assertEqual(errors, {"LeanFrontier.Toy.double_eq": "Unknown identifier `double`"})

    def test_a_statement_naming_its_own_modules_definition_is_expected_to_fail(self) -> None:
        owned = screen_statements.own_names(self.code)
        self.assertEqual(owned, {"double"})
        self.assertTrue(screen_statements.names_own_definition(self.goals["LeanFrontier.Toy.double_eq"][0], owned))
        self.assertFalse(screen_statements.names_own_definition(self.goals["LeanFrontier.Toy.plain"][0], owned))

    def test_an_unexplained_failure_fails_the_screen(self) -> None:
        """The point of the screen: a failure not caused by the module's own
        definitions means the receiver misread or mis-contextualised it."""
        root = pathlib.Path(self.temp.name) / "repo"
        (root / "LeanFrontier").mkdir(parents=True)
        (root / "Submissions").mkdir()
        (root / "LeanFrontier" / "Toy.lean").write_text(MODULE, encoding="utf-8")
        (root / "Submissions" / "toy.json").write_text(
            '{"submission_id": "toy", "entrypoints": ["LeanFrontier.Toy.double_eq", "LeanFrontier.Toy.plain"]}',
            encoding="utf-8")

        class Result:
            returncode, stderr = 1, ""

            def __init__(self, stdout: str) -> None:
                self.stdout = stdout

        def fake_run(command, cwd, timeout):
            source = pathlib.Path(command[-1]).read_text(encoding="utf-8").splitlines()
            # Every statement fails: one for an expected reason, one not.
            lines = [i + 1 for i, line in enumerate(source) if line.startswith("example")]
            return Result("".join(f"/tmp/x.lean:{line}:8: error: boom\n" for line in lines))

        original = screen_statements.run
        screen_statements.run = fake_run
        try:
            report = screen_statements.screen(root, 10)
            printed = io.StringIO()
            with redirect_stdout(printed):
                exit_code = screen_statements.main(["--root", str(root)])
        finally:
            screen_statements.run = original
        outcomes = {name: item["outcome"] for name, item in report["results"].items()}
        self.assertEqual(outcomes, {"LeanFrontier.Toy.double_eq": "own definition",
                                    "LeanFrontier.Toy.plain": "other"})
        self.assertEqual(exit_code, 1)
        self.assertIn("::error::LeanFrontier.Toy.plain (toy) cannot be stated as written: boom", printed.getvalue())

    def test_every_declared_entrypoint_has_a_statement_to_screen(self) -> None:
        """Without Lean, on every pull request: each declared entrypoint's
        statement can be found. A submission whose statement the receiver cannot
        find was never probed or textually checked, so it should stop here."""
        claims = screen_statements.declared_entrypoints(ROOT)
        found = set()
        for path in (ROOT / "LeanFrontier").rglob("*.lean"):
            found |= set(frontier_validate.statement_goals(path)) & set(claims)
        self.assertEqual(sorted(set(claims) - found), [])


if __name__ == "__main__":
    unittest.main()
