#!/usr/bin/env python3
"""Read and update LeanFrontier's active, tagged Mathlib release policy."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_POLICY = ROOT / "policy" / "mathlib-release.json"
REQUIRED_KEYS = {"policy_version", "source_release_tag", "lean_toolchain", "mathlib_revision", "fingerprint_index"}
REVISION_RE = re.compile(r"^v\d+\.\d+\.\d+(?:-[0-9A-Za-z.]+)?$")
TOOLCHAIN_RE = re.compile(r"^leanprover/lean4:v\d+\.\d+\.\d+(?:-[0-9A-Za-z.]+)?$")
INDEX_RE = re.compile(r"^mathlib-fingerprints-v\d+\.\d+\.\d+(?:-[0-9A-Za-z.]+)?\.json$")


class ReleasePolicyError(ValueError):
    """The active release policy is malformed or inconsistent."""


def load_release_policy(path: Path = DEFAULT_POLICY) -> dict[str, str]:
    try:
        value: Any = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReleasePolicyError(f"cannot read Mathlib release policy: {error}") from error
    if not isinstance(value, dict) or set(value) != REQUIRED_KEYS:
        raise ReleasePolicyError("Mathlib release policy keys are invalid")
    if value.get("policy_version") != "0.1":
        raise ReleasePolicyError("Mathlib release policy version is unsupported")
    fields = ("source_release_tag", "mathlib_revision", "lean_toolchain", "fingerprint_index")
    if any(not isinstance(value.get(field), str) for field in fields):
        raise ReleasePolicyError("Mathlib release policy values must be strings")
    if value["source_release_tag"] != value["mathlib_revision"] or not REVISION_RE.fullmatch(value["mathlib_revision"]):
        raise ReleasePolicyError("Mathlib release policy must use one official tagged revision")
    if not TOOLCHAIN_RE.fullmatch(value["lean_toolchain"]):
        raise ReleasePolicyError("Mathlib release policy has an invalid Lean toolchain")
    expected = f"mathlib-fingerprints-{value['mathlib_revision']}.json"
    if value["fingerprint_index"] != expected or not INDEX_RE.fullmatch(value["fingerprint_index"]):
        raise ReleasePolicyError("Mathlib release policy has an inconsistent fingerprint index name")
    return {key: value[key] for key in REQUIRED_KEYS}


def write_release_policy(path: Path, *, mathlib_revision: str, lean_toolchain: str) -> dict[str, str]:
    policy = {
        "policy_version": "0.1",
        "source_release_tag": mathlib_revision,
        "lean_toolchain": lean_toolchain,
        "mathlib_revision": mathlib_revision,
        "fingerprint_index": f"mathlib-fingerprints-{mathlib_revision}.json",
    }
    # Validate before writing so the maintenance updater cannot create a partial policy.
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(policy, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    try:
        load_release_policy(temporary)
        temporary.replace(path)
    finally:
        if temporary.exists():
            temporary.unlink()
    return policy
