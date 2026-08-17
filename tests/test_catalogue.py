from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generate_catalogue", ROOT / "tools" / "generate_catalogue.py"
)
assert SPEC is not None and SPEC.loader is not None
catalogue = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = catalogue
SPEC.loader.exec_module(catalogue)


class CatalogueTests(unittest.TestCase):
    def test_only_declared_entrypoints_are_catalogued(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "LeanFrontier").mkdir()
            (root / "Submissions").mkdir()
            (root / "LeanFrontier" / "Toy.lean").write_text(
                """namespace LeanFrontier.Toy

/-- The public theorem. -/
theorem listed : True := trivial

/-- An implementation helper, deliberately not an entrypoint. -/
theorem helper : True := trivial
""",
                encoding="utf-8",
            )
            (root / "Submissions" / "toy.json").write_text(
                json.dumps(
                    {
                        "submission_id": "toy",
                        "producer": {"agent": "test-agent"},
                        "origin_mode": "mathlib_extension",
                        "entrypoints": ["LeanFrontier.Toy.listed"],
                    }
                ),
                encoding="utf-8",
            )

            rendered = catalogue.render(root)

        self.assertIn("LeanFrontier.Toy.listed", rendered)
        self.assertNotIn("LeanFrontier.Toy.helper", rendered)
        self.assertIn("The public theorem.", rendered)

    def test_prose_containing_theorem_does_not_swallow_the_next_declaration(self) -> None:
        """`finditer` does not overlap: a match inside prose hides the real one."""
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "LeanFrontier").mkdir()
            (root / "Submissions").mkdir()
            (root / "LeanFrontier" / "Toy.lean").write_text(
                """/-!
# A module whose prose mentions declarations

Nicomachus's theorem is the companion statement for cubes.
-/

namespace LeanFrontier.Toy

/-- The first public theorem. -/
theorem first : True := trivial

/-- The second public theorem. -/
theorem second : True := trivial
""",
                encoding="utf-8",
            )
            (root / "Submissions" / "toy.json").write_text(
                json.dumps(
                    {
                        "submission_id": "toy",
                        "producer": {"agent": "test-agent"},
                        "origin_mode": "mathlib_extension",
                        "entrypoints": ["LeanFrontier.Toy.first", "LeanFrontier.Toy.second"],
                    }
                ),
                encoding="utf-8",
            )

            rendered = catalogue.render(root)

        self.assertIn("LeanFrontier.Toy.first", rendered)
        self.assertIn("LeanFrontier.Toy.second", rendered)
        self.assertIn("The first public theorem.", rendered)


if __name__ == "__main__":
    unittest.main()
