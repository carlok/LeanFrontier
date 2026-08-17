from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RUN_INTEGRATION = os.environ.get("LEANFRONTIER_INTEGRATION") == "1"
ACTIVE_MATHLIB_REVISION = json.loads((ROOT / "policy" / "mathlib-release.json").read_text())["mathlib_revision"]


@unittest.skipUnless(RUN_INTEGRATION, "set LEANFRONTIER_INTEGRATION=1 to run Lean receiver integration tests")
class ReceiverIntegrationTests(unittest.TestCase):
    """Full receiver tests; they require the pinned Mathlib cache and take minutes."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="leanfrontier-integration-")
        self.candidate = Path(self.temp.name) / "candidate"
        self.base = Path(self.temp.name) / "base"
        ignored = shutil.ignore_patterns(".git", ".lake", ".frontier", "__pycache__")
        shutil.copytree(ROOT, self.candidate, ignore=ignored)
        shutil.copytree(ROOT, self.base, ignore=ignored)
        (self.candidate / ".lake").mkdir()
        (self.candidate / ".lake" / "packages").symlink_to(ROOT / ".lake" / "packages", target_is_directory=True)
        (self.base / "LeanFrontier" / "Algebra" / "Binomial.lean").unlink()
        (self.base / "Submissions" / "bootstrap-binomial.json").unlink()

    def tearDown(self) -> None:
        self.temp.cleanup()

    def claim(self, entrypoint: str) -> None:
        (self.candidate / "Submissions" / "bootstrap-binomial.json").write_text(
            json.dumps(
                {
                    "protocol_version": "0.1",
                    "submission_id": "bootstrap-binomial",
                    "producer": {"type": "other", "model": None, "agent": "integration-test"},
                    "origin_mode": "target_driven",
                    "statement_origin": "machine",
                    "proof_origin": "machine",
                    "entrypoints": [entrypoint],
                    "base_mathlib_revision": ACTIVE_MATHLIB_REVISION,
                    "source_context": None,
                }
            )
        )

    def validate(self) -> dict[str, object]:
        report = self.candidate / ".frontier" / "report.json"
        result = subprocess.run(
            [str(ROOT / "tools" / "validate-submission"), "--base-dir", str(self.base), "--candidate-dir", str(self.candidate), "--json-out", str(report)],
            text=True,
            capture_output=True,
            timeout=480,
            check=False,
        )
        self.assertTrue(report.exists(), result.stderr + result.stdout)
        payload = json.loads(report.read_text())
        self.assertEqual(result.returncode == 0, payload["accepted"])
        return payload

    def test_valid_bundle_exercises_build_axioms_and_mathlib_comparison(self) -> None:
        payload = self.validate()
        self.assertTrue(payload["accepted"])
        observed = payload["observed"]
        self.assertEqual(observed["build"], "pass")
        self.assertEqual(observed["entrypoints"]["LeanFrontier.Algebra.add_add_sq"]["axioms"], ["propext"])
        self.assertEqual(observed["mathlib_exact_matches"], 0)

    def test_unimported_subject_module_is_built_by_the_library_glob(self) -> None:
        source = self.candidate / "LeanFrontier" / "Geometry" / "BuildProbe.lean"
        source.write_text(
            "import Mathlib.Tactic\n\n"
            "namespace LeanFrontier.Geometry\n"
            "theorem build_probe : (1 : Nat) + 1 = 2 := by norm_num\n"
            "end LeanFrontier.Geometry\n"
        )
        result = subprocess.run(["lake", "build"], cwd=self.candidate, text=True, capture_output=True, timeout=300, check=False)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertTrue((self.candidate / ".lake" / "build" / "lib" / "lean" / "LeanFrontier" / "Geometry" / "BuildProbe.olean").exists())

    def test_baseline_probe_rejects_existing_easy_result(self) -> None:
        source = self.candidate / "LeanFrontier" / "Algebra" / "Binomial.lean"
        source.write_text(
            "import Mathlib.Algebra.Group.Nat.Defs\n\n"
            "namespace LeanFrontier.Algebra\n"
            "theorem add_zero_and_one (n : Nat) : n + 0 = n ∧ (1 : Nat) = 1 := by simp\n"
            "end LeanFrontier.Algebra\n"
        )
        self.claim("LeanFrontier.Algebra.add_zero_and_one")
        payload = self.validate()
        self.assertFalse(payload["accepted"])
        self.assertIn("TRIVIAL_BASELINE_RESULT", {item["code"] for item in payload["diagnostics"]})

    def test_mathlib_duplicate_is_rejected(self) -> None:
        source = self.candidate / "LeanFrontier" / "Algebra" / "Binomial.lean"
        source.write_text(
            "import Mathlib.Algebra.Group.Nat.Defs\n\n"
            "namespace LeanFrontier.Algebra\n"
            "theorem nat_add_comm_copy (a b : Nat) : a + b = b + a := Nat.add_comm a b\n"
            "end LeanFrontier.Algebra\n"
        )
        self.claim("LeanFrontier.Algebra.nat_add_comm_copy")
        payload = self.validate()
        self.assertFalse(payload["accepted"])
        self.assertIn("DUPLICATE_STATEMENT", {item["code"] for item in payload["diagnostics"]})

    def test_native_audit_reports_an_unauthorized_compiled_axiom(self) -> None:
        source = self.candidate / "LeanFrontier" / "Experimental" / "AuditOnly.lean"
        source.write_text(
            "namespace LeanFrontier.Experimental\n"
            "axiom integrationOnlyAxiom : False\n"
            "theorem integrationOnlyTheorem : False := integrationOnlyAxiom\n"
            "end LeanFrontier.Experimental\n"
        )
        subprocess.run(["lake", "build", "frontier-audit", "LeanFrontier.Experimental.AuditOnly"], cwd=self.candidate, check=True, timeout=300)
        output = subprocess.run(
            ["lake", "exe", "frontier-audit", "--", "LeanFrontier.Experimental.AuditOnly"],
            cwd=self.candidate,
            text=True,
            capture_output=True,
            check=True,
            timeout=120,
        ).stdout
        rows = [json.loads(line) for line in output.splitlines()]
        theorem = next(row for row in rows if row["name"] == "LeanFrontier.Experimental.integrationOnlyTheorem")
        self.assertIn("LeanFrontier.Experimental.integrationOnlyAxiom", theorem["axioms"])


if __name__ == "__main__":
    unittest.main()
