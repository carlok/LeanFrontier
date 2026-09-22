from __future__ import annotations

import json
import io
import hashlib
import os
import signal
import subprocess
import time
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

    def test_code_that_runs_on_import_or_build_is_rejected(self) -> None:
        """Consumers build LeanFrontier from source and import it, so both run code.

        An `initialize` block ran arbitrary IO in any file that merely imported
        its module, and passed every earlier check.
        """
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        theorem = "theorem new_result (n : Nat) : n ^ 2 + 2 * n + 1 = (n + 1) ^ 2 := by omega\n"
        for payload in (
            'initialize do\n  IO.FS.writeFile "x" "y"\n',
            "builtin_initialize pure ()\n",
            "@[init initFn] opaque hook : Nat\n",
            "attribute [init initFn] hook\n",
            '@[extern "c_fn"] opaque native : Nat → Nat\n',
            "@[implemented_by other] def fast : Nat := 0\n",
            'run_cmd Lean.logInfo "x"\n',
            "run_elab pure ()\n",
            "run_meta pure ()\n",
            "simproc reduceFoo (foo _) := fun _ => pure .continue\n",
            "dsimproc reduceBar (bar _) := fun _ => pure .continue\n",
            "macro_rules | `(tactic| trivial) => `(tactic| rfl)\n",
            "elab_rules : tactic | `(tactic| trivial) => pure ()\n",
            "declare_syntax_cat payload\n",
        ):
            with self.subTest(payload=payload.splitlines()[0]):
                path.write_text(payload + theorem)
                self.assert_rejected("SECURITY_POLICY_VIOLATION")

    def test_ordinary_names_near_the_banned_words_are_accepted(self) -> None:
        path = self.candidate / "LeanFrontier" / "Algebra" / "New.lean"
        path.write_text(
            "namespace LeanFrontier.Algebra\n"
            "def initialSegment (n : Nat) : Nat := n\n"
            "def externalAngle (n : Nat) : Nat := n\n"
            "theorem new_result (n : Nat) : initialSegment n + externalAngle n = 2 * n := by\n"
            "  simp [initialSegment, externalAngle]; omega\n"
            "end LeanFrontier.Algebra\n"
        )
        status, report = self.validate()
        self.assertEqual(status, 0, report["diagnostics"])

    def test_an_existing_module_cannot_be_modified(self) -> None:
        """Only names of accepted results were protected, not their meaning.

        Redefining something an accepted theorem depends on kept its name
        compiling while changing what it says. Edits go through maintenance.
        """
        existing = self.candidate / "LeanFrontier" / "Algebra" / "Existing.lean"
        existing.write_text(existing.read_text() + "-- a harmless-looking edit\n")
        status, report = self.validate()
        self.assertEqual(status, 1)
        paths = {item.get("path") for item in report["diagnostics"] if item["code"] == "PATH_POLICY_VIOLATION"}  # type: ignore[union-attr]
        self.assertIn("LeanFrontier/Algebra/Existing.lean", paths)

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

    def test_a_failed_build_reports_the_lean_errors(self) -> None:
        """Lake prints elaboration errors on stdout and only a summary on stderr."""

        class Result:
            returncode = 1
            stdout = (
                "✖ [2/3] Building LeanFrontier.Algebra.New (1.4s)\n"
                "trace: .> LEAN_PATH=/candidate/.lake/build/lib/lean lean /candidate/LeanFrontier/Algebra/New.lean\n"
                "error: LeanFrontier/Algebra/New.lean:1:21: Type mismatch\n"
                "error: Lean exited with code 1\n"
            )
            stderr = "error: build failed\n"

        original = frontier_validate.run
        frontier_validate.run = lambda cmd, cwd, timeout: Result()
        try:
            report = frontier_validate.Report()
            frontier_validate.lean_audit(
                None, self.candidate, [], [], {}, {}, {"build_timeout_seconds": 300}, {}, {}, set(), report,
            )
        finally:
            frontier_validate.run = original
        self.assertEqual(report.diagnostics[0].code, "BUILD_FAILED")
        message = report.diagnostics[0].message
        self.assertIn("New.lean:1:21: Type mismatch", message)
        self.assertIn("error: build failed", message)
        self.assertNotIn("LEAN_PATH", message)

    def test_a_failed_build_reports_the_submitters_error_from_real_lake_output(self) -> None:
        """Real `lake build` output for tests/fixtures/receiver/BrokenFixture.lean.

        The error sits mid-stream: other modules keep building after it, and
        v4.34.0 linter warnings in untouched modules follow. A plain tail of
        the output lost the error entirely; the report must carry it, and
        nothing about files the submission did not change.
        """
        fixtures = ROOT / "tests" / "fixtures" / "receiver"

        class Result:
            returncode = 1
            stdout = (fixtures / "broken-build.stdout").read_text(encoding="utf-8")
            stderr = (fixtures / "broken-build.stderr").read_text(encoding="utf-8")

        self.assertNotIn("BrokenFixture.lean:7:64", Result.stdout[-2000:], "fixture no longer shows the tail problem")
        original = frontier_validate.run
        frontier_validate.run = lambda cmd, cwd, timeout: Result()
        try:
            report = frontier_validate.Report()
            frontier_validate.lean_audit(
                None, self.candidate, [], ["LeanFrontier.Algebra.BrokenFixture"], {}, {},
                {"build_timeout_seconds": 300}, {}, {}, set(), report,
            )
        finally:
            frontier_validate.run = original
        message = report.diagnostics[0].message
        self.assertEqual(report.diagnostics[0].code, "BUILD_FAILED")
        self.assertIn("error: LeanFrontier/Algebra/BrokenFixture.lean:7:64: unsolved goals", message)
        self.assertIn("⊢ a * b * 2 + a ^ 2 + b ^ 2 = a ^ 2 + b ^ 2", message)
        self.assertIn("The `ring` tactic failed to close the goal", message)
        self.assertIn("error: build failed", message)
        for noise in ("Furstenberg", "✔", "LEAN_PATH"):
            self.assertNotIn(noise, message)
        self.assertLessEqual(len(message), frontier_validate.DIAGNOSTIC_LIMIT)

    def test_a_deprecated_api_in_the_submission_is_rejected(self) -> None:
        """A deprecation is a warning today and an error after a later Mathlib upgrade.

        Every one admitted became a future break in the upgrade audit; eleven
        had to be fixed by hand in #224.
        """
        calls: list[list[str]] = []

        class Result:
            returncode = 0
            stdout = (
                "✔ [2530/2541] Built LeanFrontier.NumberTheory.SternDiatomic (2.4s)\n"
                "⚠ [2531/2541] Built LeanFrontier.Algebra.New (1.2s)\n"
                "warning: LeanFrontier/Algebra/New.lean:3:40: `if_pos` has been deprecated: Use `ite_eq_left` instead\n"
                "warning: LeanFrontier/Algebra/New.lean:1:0: 'Mathlib.Data.Real.Basic' has been deprecated: please replace this import by\n"
                "\n"
                "import Mathlib.Basic.Real.Basic\n"
                "warning: LeanFrontier/Algebra/New.lean:9:2: this tactic is never executed\n"
                "warning: LeanFrontier/Topology/Furstenberg.lean:162:25: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\n"
            )
            stderr = ""

        original = frontier_validate.run
        frontier_validate.run = lambda cmd, cwd, timeout: (calls.append(cmd), Result())[1]
        try:
            report = frontier_validate.Report()
            frontier_validate.lean_audit(
                None, self.candidate, [], ["LeanFrontier.Algebra.New"], {}, {},
                {"build_timeout_seconds": 300, "kernel_recheck_timeout_seconds": 180}, {}, {}, set(), report,
            )
        finally:
            frontier_validate.run = original
        self.assertEqual([item.code for item in report.diagnostics], ["DEPRECATED_API"])
        message = report.diagnostics[0].message
        self.assertIn("`if_pos` has been deprecated: Use `ite_eq_left` instead", message)
        self.assertIn("import Mathlib.Basic.Real.Basic", message)
        self.assertNotIn("never executed", message, "only deprecations are rejected, not style lints")
        self.assertNotIn("Furstenberg", message, "another module's deprecation is not the submitter's to fix")
        self.assertEqual(calls, [["lake", "build"]], "a rejected build stops before the kernel recheck")

    def test_deprecations_elsewhere_do_not_reject_a_submission(self) -> None:
        fixtures = ROOT / "tests" / "fixtures" / "receiver"

        class Result:
            returncode = 0
            stdout = (fixtures / "broken-build.stdout").read_text(encoding="utf-8")
            stderr = ""

        self.assertIn("has been deprecated", Result.stdout)
        self.assertEqual(frontier_validate.deprecations(Result(), {"LeanFrontier/Algebra/New.lean"}), [])

    def test_undeclared_conjectures_reach_the_probes(self) -> None:
        """The probes need the submitted *modules* to find `def X : Prop := ...`.

        `lean_audit` reused the name `submitted` for the declaration names it
        compares against Mathlib, and handed those to the probes, which then
        found no conjecture to probe in either direction.
        """
        module = "LeanFrontier.Algebra.New"
        finding = {
            "name": "LeanFrontier.Algebra.new_result", "kind": "theorem", "axioms": [],
            "normalized_term_bytes": 10, "type_canonical": "00", "type_hint": "h",
        }

        class Result:
            returncode = 0
            stdout = json.dumps(finding) + "\n"
            stderr = ""

        seen: dict[str, object] = {}
        saved = {name: getattr(frontier_validate, name) for name in ("run", "mathlib_duplicates", "baseline_probes", "downstream_smoke")}
        frontier_validate.run = lambda cmd, cwd, timeout: Result()
        frontier_validate.mathlib_duplicates = lambda hints, release, report: set()
        frontier_validate.baseline_probes = lambda candidate, modules, submitted, *rest: seen.setdefault("submitted", submitted)
        frontier_validate.downstream_smoke = lambda *args: None
        try:
            report = frontier_validate.Report()
            frontier_validate.lean_audit(
                None, self.candidate, [module], [module], {}, {"entrypoints": ["LeanFrontier.Algebra.new_result"]},
                {"build_timeout_seconds": 300, "kernel_recheck_timeout_seconds": 180, "validation_timeout_seconds": 600,
                 "max_normalized_term_bytes": 65536},
                {"allowed_axioms": [], "always_reject": []}, {}, set(), report,
            )
        finally:
            for name, value in saved.items():
                setattr(frontier_validate, name, value)
        self.assertEqual(report.diagnostics, [])
        self.assertEqual(list(seen.get("submitted", [])), [module])

    def test_a_pathological_build_is_capped(self) -> None:

        class Result:
            returncode = 1
            stdout = "".join(
                f"error: LeanFrontier/Algebra/New.lean:{line}:0: unknown identifier 'x{line}'\n" for line in range(1, 20001)
            )
            stderr = "error: build failed\n"

        message = frontier_validate.lean_errors(Result(), {"LeanFrontier/Algebra/New.lean"})
        self.assertLessEqual(len(message), frontier_validate.DIAGNOSTIC_LIMIT)
        self.assertTrue(message.startswith("error: LeanFrontier/Algebra/New.lean:1:0:"), "the first error is the likeliest cause")
        self.assertIn("elided", message)

    def test_errors_elsewhere_are_kept_when_the_submitters_files_have_none(self) -> None:
        """Editing an existing module can break a module the submission did not touch."""

        class Result:
            returncode = 1
            stdout = (
                "warning: LeanFrontier/Topology/Furstenberg.lean:97:2: Try this: letI\n"
                "error: LeanFrontier/NumberTheory/MarkovTree.lean:12:4: unknown constant 'MarkovEquation.jump_pos'\n"
            )
            stderr = "error: build failed\n"

        message = frontier_validate.lean_errors(Result(), {"LeanFrontier/NumberTheory/MarkovEquation.lean"})
        self.assertIn("MarkovTree.lean:12:4: unknown constant", message)
        self.assertNotIn("Furstenberg", message)

    def test_a_failed_smoke_test_reports_the_lean_errors(self) -> None:

        class Result:
            returncode = 1
            stdout = "Client.lean:3:7: error: unknown identifier 'LeanFrontier.Algebra.new_result'\n"
            stderr = ""

        original = frontier_validate.run
        frontier_validate.run = lambda cmd, cwd, timeout: Result()
        try:
            report = frontier_validate.Report()
            frontier_validate.downstream_smoke(
                self.candidate, ["LeanFrontier.Algebra.New"], ["LeanFrontier.Algebra.new_result"], report,
            )
        finally:
            frontier_validate.run = original
        self.assertIn("unknown identifier", report.diagnostics[0].message)

    def test_a_timed_out_command_leaves_no_orphaned_grandchild(self) -> None:
        """A probe is `lake env lean`: killing only `lake` left `lean` running under PID 1.

        Orphans accumulated across probes and exhausted memory on a small host.
        """
        pidfile = self.candidate / "grandchild.pid"
        with self.assertRaises(subprocess.TimeoutExpired):
            frontier_validate.run(["sh", "-c", f"sleep 60 & echo $! > {pidfile}; wait"], self.candidate, 1)
        grandchild = int(pidfile.read_text())
        deadline = time.time() + 5
        while time.time() < deadline:
            try:
                os.kill(grandchild, 0)
            except ProcessLookupError:
                return
            time.sleep(0.1)
        os.kill(grandchild, signal.SIGKILL)
        self.fail("the timed-out command's grandchild survived")

    def test_probe_runs_are_timed_and_timeouts_counted(self) -> None:
        outcomes = iter([subprocess.TimeoutExpired(["lake"], 10), 1, 0])

        class Result:
            stdout = stderr = ""

            def __init__(self, code: int) -> None:
                self.returncode = code

        def fake_run(cmd, cwd, timeout):
            outcome = next(outcomes)
            if isinstance(outcome, Exception):
                raise outcome
            return Result(outcome)

        original = frontier_validate.run
        frontier_validate.run = fake_run
        try:
            runs: list[dict[str, object]] = []
            proved = frontier_validate.probe_goal(
                self.candidate, self.candidate / "probe.lean", ": True",
                {"baseline_probes": ["simp", "omega", "decide"], "probe_timeout_seconds": 10}, runs,
            )
        finally:
            frontier_validate.run = original
        self.assertEqual(proved, "decide")
        self.assertEqual([item["tactic"] for item in runs], ["simp", "omega", "decide"])
        self.assertEqual([item["outcome"] for item in runs], ["timeout", "failed", "closed"])
        self.assertTrue(all(isinstance(item["seconds"], float) for item in runs))

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
