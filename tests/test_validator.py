from __future__ import annotations

import json
import io
import hashlib
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import frontier_validate  # noqa: E402


ACTIVE_MATHLIB_REVISION = frontier_validate.load_release_policy()["mathlib_revision"]


def metadata(identifier: str = "valid-bundle") -> str:
    return json.dumps(
        {
            "protocol_version": "0.1",
            "submission_id": identifier,
            "producer": {"type": "llm", "model": "test-model", "agent": "test-agent"},
            "origin_mode": "target_driven",
            "statement_origin": "machine",
            "proof_origin": "machine",
            "entrypoints": ["LeanFrontier.Algebra.new_result"],
            "base_mathlib_revision": ACTIVE_MATHLIB_REVISION,
            "source_context": None,
        }
    )


class ValidatorPreflightTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name) / "base"
        self.candidate = Path(self.temp.name) / "candidate"
        for root in (self.base, self.candidate):
            (root / "LeanFrontier" / "Algebra").mkdir(parents=True)
            (root / "Submissions").mkdir()
            (root / "LeanFrontier" / "Algebra" / "Existing.lean").write_text("namespace LeanFrontier.Algebra\nend LeanFrontier.Algebra\n")
        (self.candidate / "LeanFrontier" / "Algebra" / "New.lean").write_text(
            "namespace LeanFrontier.Algebra\n"
            "theorem new_result (n : Nat) : n ^ 2 + 2 * n + 1 = (n + 1) ^ 2 := by omega\n"
            "end LeanFrontier.Algebra\n"
        )
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(metadata())

    def tearDown(self) -> None:
        self.temp.cleanup()

    def validate(self) -> tuple[int, dict[str, object]]:
        output = io.StringIO()
        with redirect_stdout(output):
            status = frontier_validate.main(["--base-dir", str(self.base), "--candidate-dir", str(self.candidate), "--preflight-only"])
        return status, json.loads(output.getvalue())

    def assert_rejected(self, expected_code: str) -> None:
        status, report = self.validate()
        self.assertEqual(status, 1)
        codes = {item["code"] for item in report["diagnostics"]}  # type: ignore[index]
        self.assertIn(expected_code, codes)

    def test_valid_theorem(self) -> None:
        status, report = self.validate()
        self.assertEqual(status, 0)
        self.assertTrue(report["accepted"])

    def test_sorry_is_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text("theorem new_result : True := by sorry\n")
        self.assert_rejected("SORRY_DETECTED")

    def test_custom_axiom_is_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text("axiom bad : False\ntheorem new_result : True := True.intro\n")
        self.assert_rejected("UNAUTHORIZED_AXIOM")

    def test_unauthorized_path_is_rejected(self) -> None:
        (self.candidate / "README.md").write_text("payload")
        self.assert_rejected("PATH_POLICY_VIOLATION")

    def test_malformed_metadata_is_rejected(self) -> None:
        (self.candidate / "Submissions" / "valid-bundle.json").write_text("{")
        self.assert_rejected("SCHEMA_INVALID")

    def test_inactive_mathlib_revision_is_rejected(self) -> None:
        record = json.loads(metadata())
        record["base_mathlib_revision"] = "v0.0.0"
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(json.dumps(record))
        self.assert_rejected("SCHEMA_INVALID")

    def test_exact_duplicate_is_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text(
            "theorem new_result (n : Nat) : n = n := rfl\n"
            "theorem another_result (n : Nat) : n = n := rfl\n"
        )
        self.assert_rejected("DUPLICATE_STATEMENT")

    def test_propositional_noise_is_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text("theorem new_result (P : Prop) : P → P := id\n")
        self.assert_rejected("TRIVIAL_BASELINE_RESULT")

    def test_permuted_family_is_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text(
            "theorem new_result (n : Nat) : n + 1 = 1 + n := by omega\n"
            "theorem swapped_result (n : Nat) : n + 2 = 2 + n := by omega\n"
            "theorem enumerated_result (n : Nat) : n + 3 = 3 + n := by omega\n"
        )
        self.assert_rejected("DEGENERATE_THEOREM_FAMILY")

    def test_oversized_submission_is_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text("-- " + "x" * 52000)
        self.assert_rejected("RESOURCE_LIMIT_EXCEEDED")

    def test_public_audit_observation_uses_digest_not_raw_expression(self) -> None:
        canonical = "normalized elaborated expression"
        observation = frontier_validate.public_finding(
            {
                "name": "LeanFrontier.Algebra.new_result",
                "kind": "theorem",
                "axioms": ["propext"],
                "type_canonical": canonical,
            }
        )
        self.assertNotIn("type_canonical", observation)
        self.assertEqual(observation["statement_sha256"], hashlib.sha256(canonical.encode()).hexdigest())

    def test_public_audit_observation_preserves_only_type_dependencies(self) -> None:
        observation = frontier_validate.public_finding(
            {
                "name": "LeanFrontier.Algebra.new_result",
                "kind": "theorem",
                "axioms": [],
                "type_canonical": "canonical",
                "type_dependencies": ["Nat.add", "LeanFrontier.Algebra.shared", 3],
            }
        )
        self.assertEqual(observation["type_dependencies"], ["LeanFrontier.Algebra.shared", "Nat.add"])

    def test_prose_mentioning_a_trust_escape_is_not_a_rejection(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text(
            "/-- Proved without any extra axiom, and with no `sorry` left behind.\n"
            "The `elab` machinery is deliberately unused. -/\n"
            "theorem new_result (n : Nat) : n ^ 2 + 2 * n + 1 = (n + 1) ^ 2 := by omega\n"
            "-- no unsafe or macro tricks here either\n"
        )
        status, report = self.validate()
        self.assertEqual(status, 0, report["diagnostics"])
        self.assertTrue(report["accepted"])

    def test_a_trust_escape_after_a_comment_is_still_rejected(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text(
            "/- an ordinary block comment -/\n"
            "axiom bad : False\n"
            "theorem new_result : True := True.intro\n"
        )
        self.assert_rejected("UNAUTHORIZED_AXIOM")

    def test_nested_block_comments_do_not_leak_code(self) -> None:
        source = "/- outer /- inner -/ still comment: axiom -/\ntheorem t : Nat := 0\n"
        self.assertNotIn("axiom", frontier_validate.strip_comments(source))
        self.assertIn("theorem t", frontier_validate.strip_comments(source))

    def test_audit_imports_every_module_in_the_tree(self) -> None:
        """Not just the changed ones, and not via the umbrella."""
        modules = frontier_validate.modules_for(
            self.candidate, ["LeanFrontier/Algebra/New.lean", "Submissions/valid-bundle.json"]
        )
        self.assertIn("LeanFrontier.Algebra.New", modules)
        self.assertIn("LeanFrontier.Algebra.Existing", modules)
        self.assertEqual(len(modules), len(set(modules)))

    def test_audit_module_list_does_not_depend_on_the_umbrella(self) -> None:
        """A module merged but not yet in the generated umbrella is still audited."""
        recent = self.candidate / "LeanFrontier" / "Combinatorics"
        recent.mkdir(parents=True)
        (recent / "JustMerged.lean").write_text("namespace LeanFrontier.X\nend LeanFrontier.X\n")
        (self.candidate / "LeanFrontier.lean").write_text("import LeanFrontier.Algebra.Existing\n")
        modules = frontier_validate.modules_for(self.candidate, [])
        self.assertIn("LeanFrontier.Combinatorics.JustMerged", modules)

    def test_accepted_entrypoints_are_read_from_the_base_tree(self) -> None:
        (self.base / "Submissions" / "earlier.json").write_text(
            json.dumps({"submission_id": "earlier", "entrypoints": ["LeanFrontier.Old.kept"]})
        )
        (self.base / "Submissions" / "broken.json").write_text("{ not json")
        accepted = frontier_validate.accepted_entrypoints(self.base)
        self.assertEqual(accepted, {"LeanFrontier.Old.kept"})

    def test_a_submission_removing_an_accepted_entrypoint_is_a_regression(self) -> None:
        accepted = {"LeanFrontier.Old.kept", "LeanFrontier.Old.dropped"}
        findings = {"LeanFrontier.Old.kept": {}, "LeanFrontier.New.added": {}}
        self.assertEqual(
            frontier_validate.corpus_regressions(accepted, findings),
            ["LeanFrontier.Old.dropped"],
        )

    def test_an_untouched_corpus_reports_no_regression(self) -> None:
        accepted = {"LeanFrontier.Old.kept"}
        findings = {"LeanFrontier.Old.kept": {}, "LeanFrontier.New.added": {}}
        self.assertEqual(frontier_validate.corpus_regressions(accepted, findings), [])

    def test_award_source_facts_mark_direct_aliases(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text("namespace LeanFrontier.Algebra\ndef alias := Existing\nend LeanFrontier.Algebra\n")
        facts = frontier_validate.declared_public_facts(self.candidate, ["LeanFrontier/Algebra/New.lean"])
        self.assertTrue(facts["LeanFrontier.Algebra.alias"]["alias"])


if __name__ == "__main__":
    unittest.main()
