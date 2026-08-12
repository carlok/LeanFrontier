from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = (ROOT / ".github" / "workflows" / "validate-submission.yml").read_text()
SYNC_WORKFLOW = (ROOT / ".github" / "workflows" / "sync-umbrella.yml").read_text()
CATALOGUE_WORKFLOW = (ROOT / ".github" / "workflows" / "sync-catalogue.yml").read_text()
DOCKERFILE = (ROOT / "tools" / "Dockerfile.validator").read_text()
LAKEFILE = (ROOT / "lakefile.toml").read_text()


class WorkflowContractTests(unittest.TestCase):
    """Static checks for properties GitHub Actions cannot exercise locally."""

    def test_pr_receiver_uses_separate_trusted_and_candidate_checkouts(self) -> None:
        self.assertIn("pull_request:", WORKFLOW)
        self.assertIn("github.event.pull_request.base.sha", WORKFLOW)
        self.assertIn("github.event.pull_request.head.sha", WORKFLOW)
        self.assertIn("path: trusted", WORKFLOW)
        self.assertIn("path: candidate", WORKFLOW)
        self.assertEqual(WORKFLOW.count("persist-credentials: false"), 2)

    def test_receiver_has_restricted_formal_execution_and_report(self) -> None:
        for required in (
            "--network none",
            "--read-only",
            "--cap-drop ALL",
            "no-new-privileges",
            "--memory 2g",
            "lake exe cache get",
            "preflight-report.json",
            "report-output/report.json",
            '-v "$GITHUB_WORKSPACE/candidate:/candidate:ro"',
            '-v "$GITHUB_WORKSPACE/candidate/.lake:/candidate/.lake"',
            '-v "$GITHUB_WORKSPACE/report-output:/report-output"',
            'chmod 0777 "$GITHUB_WORKSPACE/report-output"',
        ):
            self.assertIn(required, WORKFLOW)

    def test_receiver_image_installs_the_pinned_toolchain_via_its_shared_elan_volume(self) -> None:
        self.assertIn("FROM debian:bookworm-slim", DOCKERFILE)
        self.assertIn("elan-init.sh", DOCKERFILE)
        self.assertIn("--retry 5 --retry-all-errors", DOCKERFILE)
        self.assertIn("--default-toolchain none", DOCKERFILE)
        self.assertIn("/usr/local/bin/lake", DOCKERFILE)
        self.assertIn('ELAN_HOME=/elan', DOCKERFILE)
        self.assertIn('-v "$GITHUB_WORKSPACE/elan:/elan"', WORKFLOW)
        self.assertIn('-v "$GITHUB_WORKSPACE/elan:/elan:ro"', WORKFLOW)
        self.assertIn("sh -c 'lake update && lake exe cache get'", WORKFLOW)
        self.assertIn("for attempt in 1 2 3", WORKFLOW)
        self.assertNotIn("sh -lc 'lake update", WORKFLOW)
        self.assertNotIn("leanprover/lean4", DOCKERFILE)

    def test_all_subject_modules_build_and_the_umbrella_is_trusted_post_merge_output(self) -> None:
        self.assertIn('globs = ["LeanFrontier.+"]', LAKEFILE)
        self.assertIn("LeanFrontier/**/*.lean", SYNC_WORKFLOW)
        self.assertIn("contents: write", SYNC_WORKFLOW)
        self.assertIn("tools/generate_umbrella.py", SYNC_WORKFLOW)

    def test_receiver_uses_a_pinned_mathlib_fingerprint_index(self) -> None:
        validator = (ROOT / "tools" / "frontier_validate.py").read_text()
        self.assertIn("mathlib-fingerprints-v4.33.0-rc1.json", validator)
        self.assertIn("Mathlib fingerprint index does not match the pinned revision", validator)
        self.assertNotIn('"--all", match_arg, "Mathlib"', validator)

    def test_receiver_smoke_tests_downstream_imports(self) -> None:
        validator = (ROOT / "tools" / "frontier_validate.py").read_text()
        self.assertIn("def downstream_smoke", validator)
        self.assertIn('SCRATCH = Path("/tmp/leanfrontier")', validator)
        self.assertIn('report.observations["downstream_import_smoke"] = "pass"', validator)

    def test_catalogue_is_trusted_post_merge_output(self) -> None:
        self.assertIn("LeanFrontier/**/*.lean", CATALOGUE_WORKFLOW)
        self.assertIn("Submissions/**/*.json", CATALOGUE_WORKFLOW)
        self.assertIn("tools/generate_catalogue.py", CATALOGUE_WORKFLOW)
        self.assertIn("contents: write", CATALOGUE_WORKFLOW)

    def test_trusted_generators_are_serialized(self) -> None:
        for workflow in (SYNC_WORKFLOW, CATALOGUE_WORKFLOW):
            self.assertIn("group: trusted-generated-main", workflow)
            self.assertIn("cancel-in-progress: false", workflow)


if __name__ == "__main__":
    unittest.main()
