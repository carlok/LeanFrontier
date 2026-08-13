from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class AgentPromptTests(unittest.TestCase):
    def test_launcher_points_to_canonical_protocol_and_local_receiver(self) -> None:
        prompt = (ROOT / "prompts" / "TRY-LEANFRONTIER.md").read_text(encoding="utf-8")
        for required in (
            "CONTRACT.md",
            "SUBMITTER.md",
            "./tools/validate-submission --base-ref origin/main",
            "Submissions/<submission-id>.json",
            '"accepted": true',
        ):
            self.assertIn(required, prompt)

    def test_readme_and_site_expose_the_raw_launcher_url(self) -> None:
        url = "https://raw.githubusercontent.com/carlok/LeanFrontier/main/prompts/TRY-LEANFRONTIER.md"
        self.assertIn(url, (ROOT / "README.md").read_text(encoding="utf-8"))
        self.assertIn(url, (ROOT / "docs" / "website" / "index.html").read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
