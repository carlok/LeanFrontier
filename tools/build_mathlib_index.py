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
        ["lake", "exe", "frontier-audit", "--", "--all", "--fingerprints", "Mathlib"],
        cwd=ROOT,
        text=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdout is not None
    fingerprints: dict[str, set[str]] = defaultdict(set)
    while header := process.stdout.readline():
        kind, separator, payload = header.rstrip(b"\n").decode("ascii").partition("\t")
        hint, separator2, size_text = payload.partition("\t")
        if kind != "theorem" or not separator or not separator2 or not hint or not size_text:
            raise RuntimeError("frontier-audit emitted an invalid Mathlib theorem row")
        canonical = process.stdout.read(int(size_text))
        if len(canonical) != int(size_text):
            raise RuntimeError("frontier-audit ended inside a Mathlib theorem row")
        fingerprints[hint].add(hashlib.sha256(canonical.hex().encode("ascii")).hexdigest())
    stderr = process.stderr.read().decode("utf-8", errors="replace") if process.stderr is not None else ""
    if process.wait() != 0:
        detail = stderr.strip()
        raise RuntimeError(f"frontier-audit exited with status {process.returncode}" + (f": {detail}" if detail else ""))
    payload = {
        "format_version": 1,
        "mathlib_revision": MATHLIB_REVISION,
        "fingerprints_by_type_hint": {hint: sorted(values) for hint, values in sorted(fingerprints.items())},
    }
    DESTINATION.write_text(json.dumps(payload, separators=(",", ":"), sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
