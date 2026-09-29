from __future__ import annotations

import gzip
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import export_dataset  # noqa: E402


class ExportOnSyntheticHistory(unittest.TestCase):
    """A history whose records are known, as for the accumulation series."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temp.name)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")

    def tearDown(self) -> None:
        self.temp.cleanup()

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True, text=True).stdout

    def commit(self, message: str, files: dict[str, str]) -> None:
        for path, text in files.items():
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-qm", message)

    def claim(self, submission: str) -> dict[str, str]:
        return {f"Submissions/{submission}.json": json.dumps({"submission_id": submission}) + "\n"}

    def test_records_join_claim_modules_imports_and_observation(self) -> None:
        self.commit("a", {**self.claim("a"), "LeanFrontier/A.lean": "theorem a : True := trivial\n"})
        # Maintenance between two submissions must not be attributed to either.
        self.commit("maintenance", {"LeanFrontier/A.lean": "-- tidied\ntheorem a : True := trivial\n"})
        self.commit("b", {**self.claim("b"), "LeanFrontier/B.lean": "import LeanFrontier.A\nimport Mathlib\n"})
        # Before the add-only rule a submission could extend an existing module.
        self.commit("c", {**self.claim("c"), "LeanFrontier/B.lean": "import LeanFrontier.A\nimport Mathlib\n-- more\n"})
        observation = {"submission_id": "b", "accepted_revision": "x", "report": {"protocol_version": "0.1", "observed": {"entrypoints": {}}}}
        self.commit("observe b", {"receiver-observations/b/x.json": json.dumps(observation)})

        records = {record["submission_id"]: record for record in export_dataset.records(self.root)}
        self.assertEqual(list(records), ["a", "b", "c"])
        self.assertEqual(records["a"]["modules"], ["LeanFrontier.A"])
        self.assertEqual(records["b"]["modules"], ["LeanFrontier.B"])
        self.assertEqual(records["b"]["extended"], [])
        self.assertEqual(records["b"]["imports"], {"LeanFrontier.B": ["LeanFrontier.A"]})
        self.assertEqual(records["c"]["modules"], [])
        self.assertEqual(records["c"]["extended"], ["LeanFrontier.B"])
        self.assertEqual(records["b"]["claim"], {"submission_id": "b"})
        self.assertEqual(records["b"]["observation"]["accepted_revision"], "x")
        self.assertIsNone(records["a"]["observation"])

    def test_the_export_is_byte_for_byte_reproducible(self) -> None:
        self.commit("a", {**self.claim("a"), "LeanFrontier/A.lean": ""})
        first = export_dataset.render(self.root)
        self.assertEqual(first, export_dataset.render(self.root))
        lines = gzip.decompress(first).decode().splitlines()
        self.assertEqual(json.loads(lines[0])["record_version"], export_dataset.RECORD_VERSION)


class ExportOnTheCorpus(unittest.TestCase):
    def test_one_record_per_claim(self) -> None:
        if subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--is-shallow-repository"],
                          capture_output=True, text=True).stdout.strip() == "true":
            self.skipTest("shallow clone")
        records = export_dataset.records(ROOT)
        claims = {path.stem for path in (ROOT / "Submissions").glob("*.json")}
        self.assertEqual({record["submission_id"] for record in records}, claims)


if __name__ == "__main__":
    unittest.main()
