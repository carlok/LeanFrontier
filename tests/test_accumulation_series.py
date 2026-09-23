from __future__ import annotations

import csv
import pathlib
import re
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import generate_accumulation_series as series  # noqa: E402

SERIES = ROOT / "experiments" / "accumulation.csv"


def data_rows() -> list[dict[str, str]]:
    lines = [line for line in SERIES.read_text(encoding="utf-8").splitlines() if not line.startswith("#")]
    return list(csv.DictReader(lines))


class AccumulationSeriesTests(unittest.TestCase):
    """The series replaces a suspended experiment, so it has to be reproducible."""

    def test_the_committed_series_is_current(self) -> None:
        result = subprocess.run([sys.executable, str(ROOT / "tools" / "generate_accumulation_series.py"), "--root", str(ROOT), "--check"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_one_row_per_accepted_submission(self) -> None:
        rows = data_rows()
        claims = {path.stem for path in (ROOT / "Submissions").glob("*.json")}
        self.assertEqual({row["submission_id"] for row in rows}, claims)
        self.assertEqual(len(rows), len(claims), "a submission is counted once")

    def test_the_last_row_describes_the_corpus_as_it_stands(self) -> None:
        modules = {
            "LeanFrontier." + path.relative_to(ROOT / "LeanFrontier").with_suffix("").as_posix().replace("/", ".")
            for path in (ROOT / "LeanFrontier").rglob("*.lean")
        }
        edges = [
            (name, target)
            for path in (ROOT / "LeanFrontier").rglob("*.lean")
            for name in ["LeanFrontier." + path.relative_to(ROOT / "LeanFrontier").with_suffix("").as_posix().replace("/", ".")]
            for target in re.findall(r"^import (LeanFrontier\S*)", path.read_text(encoding="utf-8"), re.MULTILINE)
            if target in modules
        ]
        last = data_rows()[-1]
        self.assertEqual(int(last["modules"]), len(modules))
        self.assertEqual(int(last["edges"]), len(edges))

    def test_the_corpus_only_grows(self) -> None:
        counts = [int(row["modules"]) for row in data_rows()]
        self.assertEqual(counts, sorted(counts), "add-only history should never lose a module")

    def test_the_add_only_boundary_is_marked(self) -> None:
        for row in data_rows():
            expected = row["date"] >= "2026-09-22"
            self.assertEqual(row["add_only_rule"] == "true", expected, row["submission_id"])

    def test_history_is_read_from_each_commit_not_from_today(self) -> None:
        """Reconstructing from today's files would let a later edit rewrite earlier rows."""
        source = (ROOT / "tools" / "generate_accumulation_series.py").read_text(encoding="utf-8")
        self.assertIn("ls-tree", source)
        self.assertIn("cat-file", source)

    def test_depth_handles_a_chain(self) -> None:
        sources = {
            "LeanFrontier.A": "",
            "LeanFrontier.B": "import LeanFrontier.A\n",
            "LeanFrontier.C": "import LeanFrontier.B\n",
        }
        self.assertEqual(series.depth_of(sources, series.edges_of(sources)), 3)


if __name__ == "__main__":
    unittest.main()
