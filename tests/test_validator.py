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


class PreflightHarness:
    """Base and candidate trees plus the calls every preflight test makes.

    Kept apart from the test cases so a second suite can reuse the fixture
    without also re-running the first suite's assertions.
    """

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


class ValidatorPreflightTests(PreflightHarness, unittest.TestCase):
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

    def test_family_split_across_submissions_is_rejected(self) -> None:
        """Two members accepted earlier plus one now still make a family of three."""
        accepted = (
            "theorem earlier_one (n : Nat) : n + 1 = 1 + n := by omega\n"
            "theorem earlier_two (n : Nat) : n + 2 = 2 + n := by omega\n"
        )
        for root in (self.base, self.candidate):
            (root / "LeanFrontier" / "Algebra" / "Existing.lean").write_text(accepted)
        (self.candidate / "LeanFrontier" / "Algebra" / "New.lean").write_text(
            "theorem new_result (n : Nat) : n + 3 = 3 + n := by omega\n"
        )
        self.assert_rejected("DEGENERATE_THEOREM_FAMILY")

    def test_family_below_the_threshold_across_submissions_is_accepted(self) -> None:
        accepted = "theorem earlier_one (n : Nat) : n + 1 = 1 + n := by omega\n"
        for root in (self.base, self.candidate):
            (root / "LeanFrontier" / "Algebra" / "Existing.lean").write_text(accepted)
        (self.candidate / "LeanFrontier" / "Algebra" / "New.lean").write_text(
            "theorem new_result (n : Nat) : n + 2 = 2 + n := by omega\n"
        )
        status, report = self.validate()
        self.assertEqual(status, 0, report["diagnostics"])

    def test_the_family_threshold_comes_from_policy(self) -> None:
        """The value was hardcoded as 3 while policy advertised a knob."""
        self.assertEqual(frontier_validate.load_json(frontier_validate.DEFAULT_TRIVIALITY)["family_threshold"], 3)
        source = (ROOT / "tools" / "frontier_validate.py").read_text()
        self.assertIn('triviality["family_threshold"]', source)

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

    def test_an_entrypoint_directly_under_the_prefix_is_rejected(self) -> None:
        """`LeanFrontier.foo` becomes a root-namespace name once the prefix is removed."""
        record = json.loads(metadata())
        record["entrypoints"] = ["LeanFrontier.new_result"]
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(json.dumps(record))
        self.assert_rejected("SCHEMA_INVALID")

    def test_every_accepted_entrypoint_already_carries_a_namespace(self) -> None:
        """The rule is enforceable because the corpus never needed the exception."""
        for path in sorted((ROOT / "Submissions").glob("*.json")):
            for entrypoint in json.loads(path.read_text())["entrypoints"]:
                self.assertRegex(entrypoint, frontier_validate.ENTRYPOINT_RE, path.name)

    def test_only_the_submissions_own_modules_are_rechecked(self) -> None:
        """Imported modules were rechecked when they were admitted."""
        submitted = frontier_validate.submitted_modules(
            ["LeanFrontier/Algebra/New.lean", "Submissions/valid-bundle.json"]
        )
        self.assertEqual(submitted, ["LeanFrontier.Algebra.New"])
        audited = frontier_validate.modules_for(self.candidate, [])
        self.assertIn("LeanFrontier.Algebra.Existing", audited)
        self.assertNotIn("LeanFrontier.Algebra.Existing", submitted)

    def test_a_failing_kernel_recheck_is_a_rejection(self) -> None:
        calls: list[list[str]] = []

        class Result:
            returncode = 1
            stderr = "kernel rejected declaration"
            stdout = ""

        original = frontier_validate.run
        frontier_validate.run = lambda cmd, cwd, timeout: (calls.append(cmd), Result())[1]
        try:
            report = frontier_validate.Report()
            frontier_validate.kernel_recheck(
                self.candidate, ["LeanFrontier.Algebra.New"],
                {"kernel_recheck_timeout_seconds": 180}, report,
            )
        finally:
            frontier_validate.run = original
        self.assertEqual(calls[0], ["lake", "env", "leanchecker", "LeanFrontier.Algebra.New"])
        self.assertFalse(report.accepted)
        self.assertEqual(report.diagnostics[0].code, "KERNEL_RECHECK_FAILED")

    def test_the_ignore_set_follows_the_repository_gitignore(self) -> None:
        """A submitter running the receiver in a working tree should see what CI sees."""
        derived = frontier_validate.ignored_names(ROOT)
        for noise in (".DS_Store", "coverage.xml", ".coverage"):
            self.assertIn(noise, derived, f"{noise} is in .gitignore but the receiver still walks it")
        self.assertTrue(frontier_validate.ALWAYS_IGNORED <= derived)

    def test_the_ignore_set_comes_from_the_trusted_tree(self) -> None:
        """A candidate that could widen it could hide files from the receiver."""
        (self.candidate / ".gitignore").write_text("LeanFrontier/\nSubmissions/\n")
        changed, _ = frontier_validate.changed_paths(self.base, self.candidate)
        self.assertIn("Submissions/valid-bundle.json", changed)
        self.assertIn("LeanFrontier/Algebra/New.lean", changed)

    def test_base_cases_are_not_a_family(self) -> None:
        """Whitespace collapses before numerals, so `lucas 0` keeps its literal."""
        zero = frontier_validate.normalized_statement(" : lucas 0 = 2")
        one = frontier_validate.normalized_statement(" : lucas 1 = 1")
        self.assertNotEqual(zero, one)
        shifted_one = frontier_validate.normalized_statement("(n : Nat) : n + 1 = 1 + n")
        shifted_two = frontier_validate.normalized_statement("(n : Nat) : n + 2 = 2 + n")
        self.assertEqual(shifted_one, shifted_two)

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

    def test_a_regression_message_states_the_total_it_elides(self) -> None:
        """Naming five of six sends a submitter back to fix the wrong number."""
        many = [f"LeanFrontier.Old.gone{n}" for n in range(7)]
        message = frontier_validate.regression_message(many)
        self.assertTrue(message.startswith("7 accepted entrypoints"), message)
        self.assertIn("and 2 more", message)
        self.assertIn("gone0", message)
        self.assertNotIn("gone6", message)

    def test_a_short_regression_message_elides_nothing(self) -> None:
        message = frontier_validate.regression_message(["LeanFrontier.Old.gone"])
        self.assertEqual(message, "1 accepted entrypoints are no longer present: [\'LeanFrontier.Old.gone\']")
        self.assertNotIn("more", message)

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


class LauncherArmClaimTests(PreflightHarness, unittest.TestCase):
    """The field the whole A/B depends on must survive the receiver."""

    def with_arm(self, value: object) -> None:
        claim = json.loads(metadata())
        claim["launcher_arm"] = value
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(json.dumps(claim))

    def test_an_arm_is_accepted(self) -> None:
        for arm in ("A", "B", None):
            with self.subTest(arm=arm):
                self.with_arm(arm)
                status, report = self.validate()
                self.assertEqual(status, 0, report)

    def test_an_unrecognised_arm_is_rejected(self) -> None:
        self.with_arm("C")
        self.assert_rejected("SCHEMA_INVALID")

    def test_an_invented_field_is_still_rejected(self) -> None:
        """Permitting one optional key must not open the record to any key."""
        claim = json.loads(metadata())
        claim["smuggled"] = "value"
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(json.dumps(claim))
        self.assert_rejected("SCHEMA_INVALID")


CONJECTURE_MODULE = (
    "namespace LeanFrontier.Algebra\n"
    "/-- Stated, not proved. -/\n"
    "def collatz_bounded : Prop := ∀ n : Nat, 0 < n → ∃ k, k ≥ n\n"
    "end LeanFrontier.Algebra\n"
)


def conjecture_metadata(identifier: str = "valid-bundle", entrypoints: list[str] | None = None, agent: str = "test-agent") -> str:
    record = json.loads(metadata(identifier))
    record["producer"]["agent"] = agent
    record["entrypoints"] = entrypoints or ["LeanFrontier.Algebra.collatz_bounded"]
    return json.dumps(record)


class ConjectureParsingTests(unittest.TestCase):
    """A conjecture is `def NAME : Prop := P`; it asserts nothing and needs no sorry."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.path = Path(self.temp.name) / "Module.lean"

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_a_prop_valued_definition_is_a_conjecture(self) -> None:
        self.path.write_text(CONJECTURE_MODULE)
        self.assertEqual(frontier_validate.declared_conjectures(self.path), {"collatz_bounded"})

    def test_an_ordinary_definition_is_not_a_conjecture(self) -> None:
        self.path.write_text("def double (n : Nat) : Nat := 2 * n\n")
        self.assertEqual(frontier_validate.declared_conjectures(self.path), set())

    def test_prose_mentioning_prop_is_not_a_conjecture(self) -> None:
        self.path.write_text("/-- We could def foo : Prop := True here, but do not. -/\ntheorem t : True := trivial\n")
        self.assertEqual(frontier_validate.declared_conjectures(self.path), set())

    def test_a_conjecture_is_counted_as_a_stated_proposition(self) -> None:
        """Otherwise a sweep of near-identical conjectures evades family detection."""
        self.path.write_text(CONJECTURE_MODULE)
        names = {name for name, _ in frontier_validate.declared_statements(self.path)}
        self.assertIn("collatz_bounded", names)
        body = dict(frontier_validate.declared_statements(self.path))["collatz_bounded"]
        # Shaped like a theorem's body so one probe and one normalizer serve both.
        self.assertTrue(body.startswith(": "), body)


class ConjectureQuotaTests(PreflightHarness, unittest.TestCase):
    """Stating is nearly free and proving is hard, so the cheap act is tied to
    the expensive one."""

    def landed(self, root: Path, identifier: str, source: str, entrypoints: list[str], agent: str = "test-agent") -> None:
        (root / "LeanFrontier" / "Algebra" / f"{identifier}.lean").write_text(source)
        (root / "Submissions" / f"{identifier}.json").write_text(
            conjecture_metadata(identifier, entrypoints, agent))

    def propose_conjecture(self) -> None:
        (self.candidate / "LeanFrontier" / "Algebra" / "New.lean").write_text(CONJECTURE_MODULE)
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(conjecture_metadata())

    def test_a_producer_with_no_accepted_theorem_may_state_none(self) -> None:
        self.propose_conjecture()
        self.assert_rejected("CONJECTURE_QUOTA_EXCEEDED")

    def test_one_accepted_theorem_allows_one_conjecture(self) -> None:
        source = "namespace LeanFrontier.Algebra\ntheorem landed (n : Nat) : n = n := rfl\nend LeanFrontier.Algebra\n"
        for root in (self.base, self.candidate):
            self.landed(root, "earlier", source, ["LeanFrontier.Algebra.landed"])
        self.propose_conjecture()
        status, report = self.validate()
        self.assertEqual(status, 0, report)

    def test_an_unresolved_conjecture_consumes_the_allowance(self) -> None:
        theorem = "namespace LeanFrontier.Algebra\ntheorem landed (n : Nat) : n = n := rfl\nend LeanFrontier.Algebra\n"
        held = "namespace LeanFrontier.Algebra\ndef already_open : Prop := ∀ n : Nat, n = n\nend LeanFrontier.Algebra\n"
        for root in (self.base, self.candidate):
            self.landed(root, "earlier", theorem, ["LeanFrontier.Algebra.landed"])
            self.landed(root, "held", held, ["LeanFrontier.Algebra.already_open"])
        self.propose_conjecture()
        self.assert_rejected("CONJECTURE_QUOTA_EXCEEDED")

    def test_resolving_a_conjecture_returns_the_allowance(self) -> None:
        """The contract's resolution shape is `theorem name : ConjectureName := ...`."""
        theorem = "namespace LeanFrontier.Algebra\ntheorem landed (n : Nat) : n = n := rfl\nend LeanFrontier.Algebra\n"
        held = "namespace LeanFrontier.Algebra\ndef already_open : Prop := ∀ n : Nat, n = n\nend LeanFrontier.Algebra\n"
        proof = "namespace LeanFrontier.Algebra\ntheorem already_open_holds : already_open := fun _ => rfl\nend LeanFrontier.Algebra\n"
        for root in (self.base, self.candidate):
            self.landed(root, "earlier", theorem, ["LeanFrontier.Algebra.landed"])
            self.landed(root, "held", held, ["LeanFrontier.Algebra.already_open"])
            self.landed(root, "resolution", proof, ["LeanFrontier.Algebra.already_open_holds"])
        self.propose_conjecture()
        status, report = self.validate()
        self.assertEqual(status, 0, report)

    def test_an_undeclared_conjecture_still_counts(self) -> None:
        """Otherwise the quota and both probes are opt-in.

        A conjecture that is not named in `entrypoints` still lands in the
        corpus and is still importable by later submissions, so a producer
        who simply omits it would face no quota and no probing.
        """
        module = (
            "namespace LeanFrontier.Algebra\n"
            "def quietly_stated : Prop := \u2200 n : Nat, n = n\n"
            "theorem declared (n : Nat) : n + 0 = n := rfl\n"
            "end LeanFrontier.Algebra\n"
        )
        (self.candidate / "LeanFrontier" / "Algebra" / "New.lean").write_text(module)
        claim = json.loads(conjecture_metadata())
        claim["entrypoints"] = ["LeanFrontier.Algebra.declared"]
        (self.candidate / "Submissions" / "valid-bundle.json").write_text(json.dumps(claim))
        self.assert_rejected("CONJECTURE_QUOTA_EXCEEDED")

    def test_the_quota_is_per_producer(self) -> None:
        theorem = "namespace LeanFrontier.Algebra\ntheorem landed (n : Nat) : n = n := rfl\nend LeanFrontier.Algebra\n"
        for root in (self.base, self.candidate):
            self.landed(root, "earlier", theorem, ["LeanFrontier.Algebra.landed"], agent="someone-else")
        self.propose_conjecture()
        self.assert_rejected("CONJECTURE_QUOTA_EXCEEDED")
