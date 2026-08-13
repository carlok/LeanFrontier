from __future__ import annotations

import io
import json
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import score_award  # noqa: E402
import build_award_input  # noqa: E402


def entry(identifier: str, *, alias: bool = False, generated: bool = False, restatement: bool = False) -> dict[str, object]:
    return {
        "format_version": "0.1",
        "submission_id": identifier,
        "lean_source_bytes": 4096,
        "entrypoints": [f"LeanFrontier.Test.{identifier}.first", f"LeanFrontier.Test.{identifier}.second"],
        "declarations": [
            {"name": f"LeanFrontier.Test.{identifier}.shared", "kind": "definition", "statement_sha256": f"shared-{identifier}", "type_dependencies": [], "alias": alias, "generated": generated, "restatement": restatement},
            {"name": f"LeanFrontier.Test.{identifier}.first", "kind": "theorem", "statement_sha256": f"first-{identifier}", "type_dependencies": [f"LeanFrontier.Test.{identifier}.shared"]},
            {"name": f"LeanFrontier.Test.{identifier}.second", "kind": "theorem", "statement_sha256": f"second-{identifier}", "type_dependencies": [f"LeanFrontier.Test.{identifier}.shared"]},
        ],
    }


class AwardScoreTests(unittest.TestCase):
    def run_score(self, *payloads: dict[str, object]) -> dict[str, object]:
        with tempfile.TemporaryDirectory() as directory:
            paths: list[str] = []
            for index, payload in enumerate(payloads):
                path = Path(directory) / f"{index}.json"
                path.write_text(json.dumps(payload), encoding="utf-8")
                paths.append(str(path))
            output = io.StringIO()
            with redirect_stdout(output):
                status = score_award.main(["--closing-revision", "abc123", *sum((["--input", path] for path in paths), [])])
        self.assertEqual(status, 0)
        return json.loads(output.getvalue())

    def test_scores_reuse_and_depth(self) -> None:
        report = self.run_score(entry("layered"))
        result = report["ranked_results"][0]
        self.assertEqual(result["components"]["type_level_depth"]["raw_edges"], 2)
        self.assertEqual(result["components"]["interface_reuse"]["reused_interfaces"], ["LeanFrontier.Test.layered.shared"])
        self.assertGreater(result["score"], 0)

    def test_committed_fixture_is_a_dry_run_input(self) -> None:
        fixture = ROOT / "tests" / "fixtures" / "award" / "layered.json"
        report = self.run_score(json.loads(fixture.read_text(encoding="utf-8")))
        self.assertEqual(report["ranked_results"][0]["submission_id"], "award-fixture")

    def test_excludes_alias_and_generated_padding(self) -> None:
        report = self.run_score(entry("alias", alias=True), entry("generated", generated=True), entry("restatement", restatement=True))
        for result in report["ranked_results"]:
            self.assertEqual(result["components"]["interface_reuse"]["reused_interfaces"], [])
            self.assertIn(result["exclusions"][0]["reason"], {"alias", "generated", "restatement"})

    def test_equal_scores_use_deterministic_tie_break(self) -> None:
        first = self.run_score(entry("one"), entry("two"))
        second = self.run_score(entry("one"), entry("two"))
        self.assertEqual(first["ranked_results"], second["ranked_results"])

    def test_rejects_malformed_artifact(self) -> None:
        with self.assertRaises(SystemExit):
            score_award.main(["--closing-revision", "abc", "--input", str(ROOT / "tests" / "missing.json")])

    def test_builds_input_from_new_receiver_observation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            observation = Path(directory) / "observation.json"
            output = Path(directory) / "input.json"
            observation.write_text(json.dumps({
                "observation_version": "0.1",
                "submission_id": "fixture",
                "accepted_revision": "merge",
                "report": {"accepted": True, "observed": {
                    "lean_source_bytes": 4096,
                    "entrypoints": {"LeanFrontier.Test.fixture.first": entry("fixture")["declarations"][1]},
                    "audited_declarations": {item["name"]: item for item in entry("fixture")["declarations"]},
                }},
            }), encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                status = build_award_input.main(["--observation", str(observation), "--json-out", str(output)])
            self.assertEqual(status, 0)
            self.assertEqual(json.loads(output.read_text())["submission_id"], "fixture")


if __name__ == "__main__":
    unittest.main()
