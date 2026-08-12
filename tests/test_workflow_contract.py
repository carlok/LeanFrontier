from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = (ROOT / ".github" / "workflows" / "validate-submission.yml").read_text()


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
            "candidate/.frontier/report.json",
        ):
            self.assertIn(required, WORKFLOW)


if __name__ == "__main__":
    unittest.main()
