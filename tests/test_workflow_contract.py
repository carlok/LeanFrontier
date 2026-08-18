from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = (ROOT / ".github" / "workflows" / "validate-submission.yml").read_text()
SYNC_WORKFLOW = (ROOT / ".github" / "workflows" / "sync-umbrella.yml").read_text()
CATALOGUE_WORKFLOW = (ROOT / ".github" / "workflows" / "sync-catalogue.yml").read_text()
OBSERVATION_WORKFLOW = (ROOT / ".github" / "workflows" / "record-observation.yml").read_text()
PAGES_WORKFLOW = (ROOT / ".github" / "workflows" / "deploy-pages.yml").read_text()
UPGRADE_WORKFLOW = (ROOT / ".github" / "workflows" / "mathlib-upgrade.yml").read_text()
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
        self.assertGreaterEqual(WORKFLOW.count("persist-credentials: false"), 2)

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
        self.assertIn('globs = ["LeanFrontier", "LeanFrontier.+"]', LAKEFILE)
        self.assertIn("LeanFrontier/**/*.lean", SYNC_WORKFLOW)
        self.assertIn("contents: write", SYNC_WORKFLOW)
        self.assertIn("tools/generate_umbrella.py", SYNC_WORKFLOW)
        umbrella = (ROOT / "LeanFrontier.lean").read_text()
        self.assertLess(umbrella.index("import LeanFrontier"), umbrella.index("/-!"))

    def test_receiver_uses_the_active_mathlib_fingerprint_index(self) -> None:
        validator = (ROOT / "tools" / "frontier_validate.py").read_text()
        self.assertIn("load_release_policy", validator)
        self.assertIn("fingerprint_index", validator)
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
        self.assertIn("receiver-observations/**/*.json", CATALOGUE_WORKFLOW)

    def test_accepted_receiver_reports_are_persisted_only_after_merge(self) -> None:
        for required in (
            "push:",
            "branches: [main]",
            "actions: write",
            "tools/persist_observation.py",
            "receiver-artifact/report-output/report.json",
            "receiver-observations",
        ):
            self.assertIn(required, OBSERVATION_WORKFLOW)

    def test_observations_are_written_without_a_fork_trigger(self) -> None:
        """`pull_request_target` reads fork code in a trusted context; a merge to main does not."""
        self.assertNotIn("pull_request_target:", OBSERVATION_WORKFLOW)
        self.assertNotIn("allow-unsafe-pr-checkout", OBSERVATION_WORKFLOW)
        self.assertNotIn("github.event.pull_request.", OBSERVATION_WORKFLOW)
        # Revisions come from the merge commit's own parents.
        self.assertIn('base="$(git rev-parse "$merge^1")"', OBSERVATION_WORKFLOW)
        self.assertIn('head="$(git rev-parse --verify --quiet "$merge^2"', OBSERVATION_WORKFLOW)

    def test_observation_checkout_keeps_the_merge_parent_and_fails_loudly(self) -> None:
        """A shallow checkout cannot resolve `<merge>^1`, and process substitution hides it."""
        self.assertIn("fetch-depth: 2", OBSERVATION_WORKFLOW)
        self.assertIn('git rev-parse --verify --quiet "$merge^1" > /dev/null', OBSERVATION_WORKFLOW)

    def test_post_merge_writer_runs_trusted_code_on_merged_data(self) -> None:
        """`pull_request_target` carries a write token: never execute the merged tree."""
        self.assertIn("ref: ${{ steps.submission.outputs.base }}", OBSERVATION_WORKFLOW)
        self.assertIn("path: .trusted-receiver", OBSERVATION_WORKFLOW)
        self.assertIn(".trusted-receiver/tools/persist_observation.py", OBSERVATION_WORKFLOW)
        self.assertIn(".trusted-receiver/tools/generate_catalogue.py --root .", OBSERVATION_WORKFLOW)
        self.assertNotIn("python3 tools/persist_observation.py", OBSERVATION_WORKFLOW)
        self.assertNotIn("run: python3 tools/generate_catalogue.py", OBSERVATION_WORKFLOW)

    def test_post_merge_writer_refuses_a_submission_touching_trusted_paths(self) -> None:
        self.assertIn("Refuse to record if the merge touched trusted infrastructure", OBSERVATION_WORKFLOW)
        for guarded in (".github", "tools", "policy", "schema", "lakefile.toml", "lean-toolchain"):
            self.assertIn(guarded, OBSERVATION_WORKFLOW)

    def test_every_generator_may_dispatch_the_checks_it_depends_on(self) -> None:
        """Opening the protected pull request is useless without dispatching its checks."""
        for workflow in (SYNC_WORKFLOW, CATALOGUE_WORKFLOW, OBSERVATION_WORKFLOW):
            self.assertIn("actions: write", workflow)

    def test_trusted_generators_open_protected_maintenance_prs(self) -> None:
        for workflow in (SYNC_WORKFLOW, CATALOGUE_WORKFLOW, OBSERVATION_WORKFLOW):
            self.assertIn("automation/generated/", workflow)
            self.assertIn("gh pr create", workflow)
            self.assertIn("gh workflow run validate-submission.yml", workflow)
            self.assertIn("gh pr merge", workflow)
            self.assertNotIn("git push\n", workflow)

    def test_owner_maintenance_prs_have_a_separate_validation_path(self) -> None:
        self.assertIn("validate-maintenance:", WORKFLOW)
        self.assertIn("startsWith(github.event.pull_request.head.ref, 'maintenance/')", WORKFLOW)
        self.assertIn("github.event.pull_request.author_association == 'OWNER'", WORKFLOW)
        self.assertIn("github.event.pull_request.user.login == 'github-actions[bot]'", WORKFLOW)

    def test_a_branch_name_alone_never_skips_the_ordinary_receiver(self) -> None:
        """Head refs are submitter-controlled: each exemption must also pin the author."""
        for required in (
            "!(startsWith(github.event.pull_request.head.ref, 'automation/generated/') &&",
            "!(startsWith(github.event.pull_request.head.ref, 'maintenance/') &&",
        ):
            self.assertIn(required, WORKFLOW)
        self.assertNotIn(
            "!startsWith(github.event.pull_request.head.ref, 'maintenance/')", WORKFLOW
        )
        self.assertNotIn(
            "!startsWith(github.event.pull_request.head.ref, 'automation/generated/')", WORKFLOW
        )

    def test_generated_output_validation_does_not_execute_candidate_code(self) -> None:
        validator = (ROOT / "tools" / "validate_generated.py").read_text()
        self.assertIn('allowed(path)', validator)
        self.assertIn('generate_umbrella.py', validator)
        self.assertIn('generate_catalogue.py', validator)
        self.assertNotIn('lake build', validator)

    def test_ordinary_receiver_never_runs_for_manual_generated_validation(self) -> None:
        self.assertIn("github.event_name == 'pull_request' &&", WORKFLOW)

    def test_pages_deployment_includes_catalogue_and_field_notes(self) -> None:
        for required in (
            "docs/website/**",
            "docs/catalogue/**",
            "mkdir -p _site/catalogue",
            "cp -R docs/website/. _site/",
            "cp -R docs/catalogue/. _site/catalogue/",
            "path: _site",
        ):
            self.assertIn(required, PAGES_WORKFLOW)

    def test_deployed_site_uses_project_root_navigation(self) -> None:
        homepage = (ROOT / "docs" / "website" / "index.html").read_text()
        notes = (ROOT / "docs" / "website" / "notes" / "field-note-01.html").read_text()
        catalogue_generator = (ROOT / "tools" / "generate_catalogue.py").read_text()
        self.assertIn('href="catalogue/"', homepage)
        self.assertNotIn('href="../catalogue/"', homepage)
        self.assertIn('href="../catalogue/"', notes)
        self.assertIn('<a href=\\"../\\">LeanFrontier</a>', catalogue_generator)

    def test_trusted_generators_are_serialized(self) -> None:
        for workflow in (SYNC_WORKFLOW, CATALOGUE_WORKFLOW):
            self.assertIn("group: trusted-generated-main", workflow)
            self.assertIn("cancel-in-progress: false", workflow)

    def test_mathlib_upgrader_uses_only_trusted_tagged_release_inputs(self) -> None:
        for required in (
            "schedule:",
            "workflow_dispatch:",
            "leanprover-community/mathlib4",
            "prerelease == false",
            "draft == false",
            "maintenance/mathlib-upgrade-",
            "--network none",
            "--read-only",
            "tools/update_mathlib_release.py",
            "tools/audit_mathlib_upgrade.py",
            "gh pr merge \"$pr\" --auto --merge",
        ):
            self.assertIn(required, UPGRADE_WORKFLOW)
        self.assertNotIn("/pulls", UPGRADE_WORKFLOW)

    def test_mathlib_upgrade_has_a_required_gate_and_a_trusted_path_policy(self) -> None:
        test_workflow = (ROOT / ".github" / "workflows" / "test.yml").read_text()
        validator = (ROOT / "tools" / "validate_mathlib_upgrade.py").read_text()
        self.assertIn("mathlib-upgrade:", test_workflow)
        self.assertIn("maintenance/mathlib-upgrade-", test_workflow)
        self.assertIn('ACTOR: ${{ github.actor }}', test_workflow)
        self.assertIn('"$ACTOR" == "github-actions[bot]"', test_workflow)
        self.assertIn("validate_mathlib_upgrade.py", WORKFLOW)
        self.assertIn("Mathlib upgrade changes forbidden paths", validator)


if __name__ == "__main__":
    unittest.main()
