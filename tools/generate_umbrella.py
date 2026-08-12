#!/usr/bin/env python3
"""Generate the exhaustive LeanFrontier umbrella import module."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
HEADER = """/-!
# LeanFrontier

The umbrella module for the public LeanFrontier library.

This file is generated from the subject modules below `LeanFrontier/`. Do not
edit it in an ordinary submission.
-/
"""


def module_name(path: Path, source_root: Path) -> str:
    relative = path.relative_to(source_root).with_suffix("")
    parts = (source_root.name, *relative.parts)
    if not all(IDENTIFIER.fullmatch(part) for part in parts):
        raise ValueError(f"invalid Lean module path: {path.relative_to(source_root.parent)}")
    return ".".join(parts)


def render(root: Path) -> str:
    source_root = root / "LeanFrontier"
    modules = sorted(module_name(path, source_root) for path in source_root.rglob("*.lean"))
    imports = "".join(f"\nimport {module}" for module in modules)
    return f"{HEADER}{imports}\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true", help="fail if the umbrella is stale")
    args = parser.parse_args()
    destination = args.root / "LeanFrontier.lean"
    expected = render(args.root)
    existing = destination.read_text(encoding="utf-8") if destination.exists() else ""
    if existing == expected:
        return 0
    if args.check:
        print(f"{destination} is stale; run tools/generate_umbrella.py")
        return 1
    destination.write_text(expected, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
