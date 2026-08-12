#!/usr/bin/env python3
"""Build the trusted exact-theorem fingerprint index for the pinned Mathlib."""

from __future__ import annotations

import hashlib
import json
import subprocess
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "policy" / "mathlib-fingerprints-v4.33.0-rc1.json"
MATHLIB_REVISION = "v4.33.0-rc1"


def main() -> int:
    process = subprocess.Popen(
        ["lake", "exe", "frontier-audit", "--", "--all", "Mathlib"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdout is not None
    fingerprints: dict[str, set[str]] = defaultdict(set)
    for line in process.stdout:
        item = json.loads(line)
        hint = item.get("type_hint")
        canonical = item.get("type_canonical")
        if item.get("kind") != "theorem" or not isinstance(hint, str) or not isinstance(canonical, str):
            raise RuntimeError("frontier-audit emitted an invalid Mathlib theorem row")
        fingerprints[hint].add(hashlib.sha256(canonical.encode("utf-8")).hexdigest())
    stderr = process.stderr.read() if process.stderr is not None else ""
    if process.wait() != 0:
        raise RuntimeError(stderr.strip() or "frontier-audit could not scan Mathlib")
    payload = {
        "format_version": 1,
        "mathlib_revision": MATHLIB_REVISION,
        "fingerprints_by_type_hint": {hint: sorted(values) for hint, values in sorted(fingerprints.items())},
    }
    DESTINATION.write_text(json.dumps(payload, separators=(",", ":"), sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
