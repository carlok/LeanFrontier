"""The launcher A/B is only interpretable if the arms differ in one place.

Anything else that drifts between the two files becomes a second, unrecorded
treatment. See PREREGISTRATION.md.
"""

import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CONTROL = ROOT / "prompts" / "TRY-LEANFRONTIER.md"
EXTENSION = ROOT / "prompts" / "TRY-LEANFRONTIER-EXTEND.md"

# The paragraph the experiment varies, plus the title line that names the arm.
CONTROL_BLOCK = """Start from current `main` in a fork or branch. Inspect the existing library and
catalogue before choosing a subject: prefer an uncovered area or a genuine
extension over a near duplicate."""

EXTENSION_BLOCK = """Start from current `main` in a fork or branch. Read the catalogue and choose an
accepted submission to build on. Import its module and prove something that
depends on it: a generalization, a consequence, or a result that needs it as a
lemma. A near duplicate is still a near duplicate and will be rejected."""


class LauncherArms(unittest.TestCase):
    def setUp(self) -> None:
        self.control = CONTROL.read_text()
        self.extension = EXTENSION.read_text()

    def test_each_arm_carries_its_own_block(self) -> None:
        self.assertIn(CONTROL_BLOCK, self.control)
        self.assertIn(EXTENSION_BLOCK, self.extension)
        self.assertNotIn(EXTENSION_BLOCK, self.control)
        self.assertNotIn(CONTROL_BLOCK, self.extension)

    def test_arms_are_otherwise_identical(self) -> None:
        """Normalise away the varied block and the title, then compare words.

        Comparison is word-level, not byte-level: the two blocks are different
        lengths, so the sentence following them rewraps. Line breaks are not a
        treatment. Any difference in the words themselves is.
        """
        control = self.control.replace(CONTROL_BLOCK, "<BLOCK>").replace(
            "# Try LeanFrontier with an agent", "<TITLE>", 1)
        extension = self.extension.replace(EXTENSION_BLOCK, "<BLOCK>").replace(
            "# Try LeanFrontier with an agent (extension arm)", "<TITLE>", 1)
        self.assertEqual(control.split(), extension.split())

    def test_preregistration_names_both_arms(self) -> None:
        prereg = (ROOT / "PREREGISTRATION.md").read_text()
        self.assertIn("TRY-LEANFRONTIER.md", prereg)
        self.assertIn("TRY-LEANFRONTIER-EXTEND.md", prereg)

    def test_assignment_ledger_has_the_expected_columns(self) -> None:
        rows = [l for l in (ROOT / "experiments" / "launcher-ab.csv")
                .read_text().splitlines() if l and not l.startswith("#")]
        self.assertEqual(rows[0], "submission_id,arm,assigned_utc")
        for row in rows[1:]:
            self.assertIn(row.split(",")[1], {"A", "B", "unassigned"})


if __name__ == "__main__":
    unittest.main()
