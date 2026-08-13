#!/usr/bin/env python3
"""Validate a trusted generated-output maintenance candidate without executing it."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def files(root: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for path in root.rglob("*"):
        if not path.is_file() or ".git" in path.parts or ".lake" in path.parts:
            continue
        result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def allowed(path: str) -> bool:
    return path in {"LeanFrontier.lean", "docs/catalogue/index.html"} or (
        path.startswith("receiver-observations/") and path.endswith(".json")
    )


def validate_observation(path: Path, root: Path) -> None:
    record = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(record, dict) or record.get("observation_version") != "0.1":
        raise ValueError(f"invalid observation {path}")
    submission_id = record.get("submission_id")
    if not isinstance(submission_id, str):
        raise ValueError(f"observation has no submission id: {path}")
    claim = json.loads((root / "Submissions" / f"{submission_id}.json").read_text(encoding="utf-8"))
    report = record.get("report")
    if not isinstance(report, dict) or report.get("accepted") is not True:
        raise ValueError(f"observation is not an accepted receiver report: {path}")
    entrypoints = report.get("observed", {}).get("entrypoints", {})
    if set(claim.get("entrypoints", [])) != set(entrypoints):
        raise ValueError(f"observation entrypoints mismatch immutable claim: {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    base_files = files(args.base)
    candidate_files = files(args.candidate)
    paths = {path for path in base_files.keys() | candidate_files.keys() if base_files.get(path) != candidate_files.get(path)}
    if not paths or any(not allowed(path) for path in paths):
        raise SystemExit(f"unexpected generated-output paths: {sorted(paths)}")
    if "LeanFrontier.lean" in paths:
        subprocess.run(["python3", str(ROOT / "generate_umbrella.py"), "--root", str(args.candidate), "--check"], check=True)
    if "docs/catalogue/index.html" in paths:
        subprocess.run(["python3", str(ROOT / "generate_catalogue.py"), "--root", str(args.candidate), "--check"], check=True)
    for relative in paths:
        if relative.startswith("receiver-observations/"):
            validate_observation(args.candidate / relative, args.candidate)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
