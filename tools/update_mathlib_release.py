#!/usr/bin/env python3
"""Apply a selected official Lean/Mathlib release pair to trusted package pins."""

from __future__ import annotations

import argparse
from pathlib import Path

from mathlib_release import ROOT, load_release_policy, write_release_policy


def replace_exact(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(old) != 1:
        raise RuntimeError(f"expected exactly one active revision in {path}")
    path.write_text(text.replace(old, new), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-revision", required=True)
    parser.add_argument("--lean-toolchain", required=True)
    args = parser.parse_args(argv)
    previous = load_release_policy()
    current_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if current_toolchain != previous["lean_toolchain"]:
        raise RuntimeError("lean-toolchain does not match the active release policy")
    current_revision = previous["mathlib_revision"]
    lakefile = ROOT / "lakefile.toml"
    if lakefile.read_text(encoding="utf-8").count(f'rev = "{current_revision}"') != 1:
        raise RuntimeError("lakefile.toml does not match the active release policy")
    replace_exact(ROOT / "lean-toolchain", current_toolchain, args.lean_toolchain)
    replace_exact(lakefile, f'rev = "{current_revision}"', f'rev = "{args.mathlib_revision}"')
    write_release_policy(
        ROOT / "policy" / "mathlib-release.json",
        mathlib_revision=args.mathlib_revision,
        lean_toolchain=args.lean_toolchain,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
