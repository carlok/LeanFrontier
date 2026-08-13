from __future__ import annotations

import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class GeneratedOutputValidatorTests(unittest.TestCase):
    def test_validates_a_regenerated_umbrella_without_executing_lean(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary) / "base"
            candidate = Path(temporary) / "candidate"
            ignored = shutil.ignore_patterns(".git", ".lake", "__pycache__")
            shutil.copytree(ROOT, base, ignore=ignored)
            shutil.copytree(base, candidate, ignore=ignored)
            subprocess.run(
                ["python3", str(ROOT / "tools" / "generate_umbrella.py"), "--root", str(candidate)],
                check=True,
            )
            subprocess.run(
                [
                    "python3",
                    str(ROOT / "tools" / "validate_generated.py"),
                    "--base",
                    str(base),
                    "--candidate",
                    str(candidate),
                ],
                check=True,
            )


if __name__ == "__main__":
    unittest.main()
