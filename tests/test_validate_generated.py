from __future__ import annotations

import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class GeneratedOutputValidatorTests(unittest.TestCase):
    def test_validates_a_regenerated_umbrella_without_executing_lean(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary) / "base"
            candidate = Path(temporary) / "candidate"
            ignored = shutil.ignore_patterns(".git", ".lake", ".codegraph", "__pycache__")
            shutil.copytree(ROOT, base, ignore=ignored)
            umbrella = base / "LeanFrontier.lean"
            umbrella.write_text(umbrella.read_text(encoding="utf-8") + "\n", encoding="utf-8")
            shutil.copytree(base, candidate, ignore=ignored)
            subprocess.run(
                ["python3", str(ROOT / "tools" / "generate_umbrella.py"), "--root", str(candidate)],
                check=True,
            )
            subprocess.run(
                [
                    "python3",
                    str(ROOT / "tools" / "validate_generated.py"),
                    "--base",
                    str(base),
                    "--candidate",
                    str(candidate),
                ],
                check=True,
            )


class AccumulationSeriesGateTests(unittest.TestCase):
    """The gate cannot regenerate the series (shallow checkout), so it checks
    the one property that makes it trustworthy: rows are only ever appended."""

    ROW = "2026-09-25,{id},64,44,0.688,0.500,3,6,true,true\n"

    def setUp(self) -> None:
        import sys
        sys.path.insert(0, str(ROOT / "tools"))
        from generate_accumulation_series import HEADER
        from validate_generated import validate_accumulation
        self.validate = validate_accumulation
        self.header = HEADER
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name) / "base"
        self.candidate = Path(self.temporary.name) / "candidate"
        for root in (self.base, self.candidate):
            (root / "experiments").mkdir(parents=True)
            (root / "Submissions").mkdir()
            for claim in ("older", "newer"):
                (root / "Submissions" / f"{claim}.json").write_text("{}")
        self.published = self.header + self.ROW.format(id="older")
        (self.base / "experiments" / "accumulation.csv").write_text(self.published)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, text: str) -> None:
        (self.candidate / "experiments" / "accumulation.csv").write_text(text)

    def test_accepts_an_appended_row(self) -> None:
        self.write(self.published + self.ROW.format(id="newer"))
        self.validate(self.base, self.candidate)

    def test_rejects_a_rewritten_row(self) -> None:
        self.write(self.published.replace(",64,", ",65,") + self.ROW.format(id="newer"))
        with self.assertRaisesRegex(ValueError, "only gain rows"):
            self.validate(self.base, self.candidate)

    def test_rejects_a_row_for_a_submission_that_does_not_exist(self) -> None:
        self.write(self.published + self.ROW.format(id="invented"))
        with self.assertRaisesRegex(ValueError, "unknown or repeated"):
            self.validate(self.base, self.candidate)

    def test_rejects_a_repeated_submission(self) -> None:
        self.write(self.published + self.ROW.format(id="older"))
        with self.assertRaisesRegex(ValueError, "unknown or repeated"):
            self.validate(self.base, self.candidate)

    def test_rejects_a_malformed_row(self) -> None:
        self.write(self.published + "2026-09-25,newer,64\n")
        with self.assertRaisesRegex(ValueError, "malformed"):
            self.validate(self.base, self.candidate)


if __name__ == "__main__":
    unittest.main()
