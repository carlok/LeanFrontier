from __future__ import annotations

import csv
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import generate_accumulation_series as series  # noqa: E402

GENERATOR = ROOT / "tools" / "generate_accumulation_series.py"


def parse(text: str) -> list[dict[str, str]]:
    return list(csv.DictReader(line for line in text.splitlines() if not line.startswith("#")))


class SyntheticHistory(unittest.TestCase):
    """The logic, on a repository built for the test.

    The committed series is post-merge generated output, like the catalogue and
    the ledger: on the pull request that adds a submission it is stale by
    construction. So its correctness is tested here, on a history whose answer
    is known, and not by asserting the real file is current.
    """

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temp.name)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")

    def tearDown(self) -> None:
        self.temp.cleanup()

    def git(self, *args: str, date: str | None = None) -> str:
        env = None
        if date:
            import os
            env = dict(os.environ, GIT_AUTHOR_DATE=f"{date}T12:00:00", GIT_COMMITTER_DATE=f"{date}T12:00:00")
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True, text=True, env=env).stdout

    def accept(self, submission: str, modules: dict[str, str], date: str) -> None:
        (self.root / "Submissions").mkdir(exist_ok=True)
        (self.root / "Submissions" / f"{submission}.json").write_text("{}\n")
        for path, source in modules.items():
            target = self.root / "LeanFrontier" / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source)
        self.git("add", "-A")
        self.git("commit", "-qm", submission, date=date)

    def generate(self) -> list[dict[str, str]]:
        return parse(series.render(self.root))

    def test_rows_follow_acceptance_with_the_corpus_at_each_step(self) -> None:
        self.accept("a", {"A.lean": "theorem a : True := trivial\n"}, "2026-09-01")
        self.accept("b", {"B.lean": "import LeanFrontier.A\n"}, "2026-09-03")
        self.accept("c", {"C.lean": "import LeanFrontier.B\n"}, "2026-09-23")
        rows = self.generate()
        self.assertEqual([row["submission_id"] for row in rows], ["a", "b", "c"])
        self.assertEqual([row["modules"] for row in rows], ["1", "2", "3"])
        self.assertEqual([row["edges"] for row in rows], ["0", "1", "2"])
        self.assertEqual([row["max_depth"] for row in rows], ["1", "2", "3"])
        self.assertEqual([row["imports_recent"] for row in rows], ["false", "true", "false"])
        self.assertEqual([row["add_only_rule"] for row in rows], ["false", "false", "true"])

    def test_a_submission_merged_from_a_stale_branch_sees_the_corpus_it_joined(self) -> None:
        """Rows describe the default branch at acceptance, not the submission's branch.

        The first version read the commit that added the claim, which sits on
        the submission's own branch and can lack modules merged meanwhile; the
        module count went backwards.
        """
        self.accept("a", {"A.lean": ""}, "2026-09-01")
        self.git("switch", "-qc", "topic")
        self.accept("late", {"Late.lean": "import LeanFrontier.A\n"}, "2026-09-02")
        self.git("switch", "-q", "main")
        self.accept("b", {"B.lean": ""}, "2026-09-03")
        self.git("merge", "-q", "--no-ff", "-m", "merge late", "topic")
        rows = self.generate()
        self.assertEqual([row["submission_id"] for row in rows], ["a", "b", "late"])
        self.assertEqual([row["modules"] for row in rows], ["1", "2", "3"])

    def test_generating_twice_changes_nothing(self) -> None:
        self.accept("a", {"A.lean": ""}, "2026-09-01")
        command = [sys.executable, str(GENERATOR), "--root", str(self.root)]
        self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
        first = (self.root / "experiments" / "accumulation.csv").read_text()
        self.assertEqual(subprocess.run(command + ["--check"], capture_output=True).returncode, 0)
        self.assertEqual((self.root / "experiments" / "accumulation.csv").read_text(), first)

    def test_a_shallow_clone_is_refused_rather_than_truncated(self) -> None:
        for day in ("2026-09-01", "2026-09-02", "2026-09-03"):
            self.accept(f"s{day[-1]}", {f"M{day[-1]}.lean": ""}, day)
        clone = pathlib.Path(self.temp.name) / "shallow"
        subprocess.run(["git", "clone", "-q", "--depth", "1", f"file://{self.root}", str(clone)], check=True, capture_output=True)
        result = subprocess.run([sys.executable, str(GENERATOR), "--root", str(clone)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("shallow", result.stdout)
        self.assertFalse((clone / "experiments" / "accumulation.csv").exists())

    def test_depth_on_a_chain(self) -> None:
        sources = {"LeanFrontier.A": "", "LeanFrontier.B": "import LeanFrontier.A\n", "LeanFrontier.C": "import LeanFrontier.B\n"}
        self.assertEqual(series.depth_of(sources, series.edges_of(sources)), 3)


class CommittedSeries(unittest.TestCase):
    """Properties the committed file keeps even when it is stale."""

    def setUp(self) -> None:
        self.rows = parse((ROOT / "experiments" / "accumulation.csv").read_text(encoding="utf-8"))

    def test_every_row_names_an_accepted_submission(self) -> None:
        claims = {path.stem for path in (ROOT / "Submissions").glob("*.json")}
        self.assertTrue({row["submission_id"] for row in self.rows} <= claims)

    def test_the_corpus_only_grows(self) -> None:
        counts = [int(row["modules"]) for row in self.rows]
        self.assertEqual(counts, sorted(counts))

    def test_the_add_only_boundary_is_marked(self) -> None:
        for row in self.rows:
            self.assertEqual(row["add_only_rule"] == "true", row["date"] >= "2026-09-22", row["submission_id"])


if __name__ == "__main__":
    unittest.main()
