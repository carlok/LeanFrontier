from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
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

    def test_corpus_shape_reports_both_measures(self) -> None:
        """An import is one line and gameable; a statement mentioning a constant is not."""
        shape = catalogue.corpus_shape(ROOT)
        self.assertGreater(len(shape["modules"]), 0)
        self.assertIn(
            ("LeanFrontier.NumberTheory.FordCircle", "LeanFrontier.NumberTheory.Mediant"),
            shape["edges"],
        )
        self.assertIn("LeanFrontier.Mediant.crossDet", shape["shared"])
        self.assertGreaterEqual(len(shape["shared"][ "LeanFrontier.Mediant.crossDet"]), 2)

    def test_the_graph_input_is_a_function_of_the_corpus(self) -> None:
        """The catalogue is committed; a layout input that wandered would diff every run."""
        shape = catalogue.corpus_shape(ROOT)
        groups = catalogue.components(shape["modules"], shape["edges"])
        self.assertEqual(groups, catalogue.components(shape["modules"], shape["edges"]))
        self.assertEqual(sorted(m for g in groups for m in g), sorted(shape["modules"]))
        sources = [catalogue.dot_source(g, shape["edges"]) for g in groups if len(g) > 1]
        self.assertEqual(sum(s.count(" -> ") for s in sources), len(shape["edges"]))
        self.assertEqual(sum(s.count("[label=") for s in sources),
                         sum(len(g) for g in groups if len(g) > 1))

    def test_checking_compares_the_graph_not_its_drawing(self) -> None:
        """A different Graphviz on the checking machine must not fail a current catalogue."""
        shape = catalogue.corpus_shape(ROOT)
        undrawn = catalogue.graph_section(shape, drawn=False)
        self.assertNotIn("<svg", undrawn)
        redrawn = undrawn.replace('"></div>', '"><svg>any layout at all</svg></div>')
        self.assertEqual(catalogue.comparable(redrawn), catalogue.comparable(undrawn))
        # But the graph itself changing is a change.
        edges = [edge for edge in shape["edges"] if "Mediant" not in edge[1]]
        fewer = catalogue.graph_section({**shape, "edges": edges}, drawn=False)
        self.assertNotEqual(catalogue.comparable(fewer), catalogue.comparable(undrawn))

    def test_the_committed_catalogue_checks_without_graphviz(self) -> None:
        """The generated-output gate checks the catalogue and has no Graphviz."""
        result = subprocess.run(
            [sys.executable, str(ROOT / "tools" / "generate_catalogue.py"), "--check"],
            capture_output=True, text=True, env={"PATH": ""},
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    @unittest.skipIf(shutil.which("dot") is None, "Graphviz is not installed")
    def test_each_connected_group_is_drawn_once(self) -> None:
        shape = catalogue.corpus_shape(ROOT)
        drawn = catalogue.graph_section(shape)
        groups = [g for g in catalogue.components(shape["modules"], shape["edges"]) if len(g) > 1]
        self.assertEqual(drawn.count("<svg"), len(groups))
        self.assertNotIn(' id="', drawn)

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
