#!/usr/bin/env python3
"""Validate the narrow file-level contract for a trusted Mathlib upgrade PR."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from mathlib_release import load_release_policy


STATIC_PATHS = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "policy/mathlib-release.json"}


def files(root: Path) -> dict[str, bytes]:
    return {path.relative_to(root).as_posix(): path.read_bytes() for path in root.rglob("*") if path.is_file() and ".git" not in path.parts}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args(argv)
    before, after = files(args.base), files(args.candidate)
    changed = {path for path in set(before) | set(after) if before.get(path) != after.get(path)}
    release = load_release_policy(args.candidate / "policy" / "mathlib-release.json")
    index = f"policy/{release['fingerprint_index']}"
    audit = f"policy/mathlib-upgrades/{release['mathlib_revision']}.json"
    previous = load_release_policy(args.base / "policy" / "mathlib-release.json")
    old_index = f"policy/{previous['fingerprint_index']}"
    allowed = STATIC_PATHS | {index, audit, old_index}
    if changed - allowed:
        raise ValueError(f"Mathlib upgrade changes forbidden paths: {sorted(changed - allowed)}")
    if not {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "policy/mathlib-release.json", index, audit}.issubset(changed):
        raise ValueError("Mathlib upgrade is missing required generated changes")
    if old_index != index and old_index in after:
        raise ValueError("the replaced Mathlib fingerprint index must not remain in Git")
    payload = json.loads((args.candidate / audit).read_text(encoding="utf-8"))
    if payload.get("mathlib_revision") != release["mathlib_revision"] or payload.get("accepted") is not True or payload.get("code") != "ACCEPTED" or payload.get("collisions"):
        raise ValueError("Mathlib upgrade audit report is not an accepted collision-free result")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
