from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

ADVISORY_URL = "https://github.com/carlok/LeanFrontier/security/advisories/new"

REQUIRED_ROOT_FILES = (
    "CODE_OF_CONDUCT.md",
    "CONTRIBUTING.md",
    "SECURITY.md",
    "AGENT.md",
    "LICENSE",
    "README.md",
)

REQUIRED_GITHUB_FILES = (
    ".github/PULL_REQUEST_TEMPLATE.md",
    ".github/dependabot.yml",
    ".github/ISSUE_TEMPLATE/config.yml",
)


class CommunityFileTests(unittest.TestCase):
    def test_required_community_files_exist(self) -> None:
        missing = [path for path in (*REQUIRED_ROOT_FILES, *REQUIRED_GITHUB_FILES)
                   if not (ROOT / path).is_file()]
        self.assertEqual(missing, [])

    def test_security_policy_links_private_reporting(self) -> None:
        security = (ROOT / "SECURITY.md").read_text(encoding="utf-8")
        self.assertIn(ADVISORY_URL, security)
        self.assertIn("do not", security.lower())

    def test_issue_template_config_points_at_security_advisory(self) -> None:
        config = (ROOT / ".github/ISSUE_TEMPLATE/config.yml").read_text(encoding="utf-8")
        self.assertIn(ADVISORY_URL, config)
        self.assertIn("blank_issues_enabled: false", config)

    def test_contributing_readme_and_security_cross_link(self) -> None:
        readme = (ROOT / "README.md").read_text(encoding="utf-8")
        contributing = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
        security = (ROOT / "SECURITY.md").read_text(encoding="utf-8")
        self.assertIn("SECURITY.md", readme)
        self.assertIn("CONTRIBUTING.md", readme)
        self.assertIn("SECURITY.md", contributing)
        self.assertIn("README.md", contributing)
        self.assertIn("CONTRIBUTING.md", security)
        self.assertIn("README.md", security)

    def test_code_of_conduct_names_enforcement_contact(self) -> None:
        conduct = (ROOT / "CODE_OF_CONDUCT.md").read_text(encoding="utf-8")
        self.assertIn("carlo.perassi@gmail.com", conduct)
        self.assertIn("carlok", conduct)


if __name__ == "__main__":
    unittest.main()