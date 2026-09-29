#!/usr/bin/env python3
"""Validate a trusted generated-output maintenance candidate without executing it."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import date
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
    return path in {
        "LeanFrontier.lean",
        "docs/catalogue/index.html",
        "experiments/launcher-ab.csv",
        "experiments/accumulation.csv",
        "experiments/rejections.csv",
    } or (
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


def validate_accumulation(base: Path, candidate: Path) -> None:
    """The series can only grow: rows already published never change.

    It cannot be regenerated here, because it is computed from the default
    branch's full history and this checkout is shallow. What can be checked is
    the property that makes it trustworthy: each row describes a commit that is
    already on main, so a writer only ever appends.
    """
    from generate_accumulation_series import DESTINATION, HEADER

    before_path = base / DESTINATION
    before = before_path.read_text(encoding="utf-8") if before_path.exists() else HEADER
    after = (candidate / DESTINATION).read_text(encoding="utf-8")
    if not after.startswith(before) or not after.startswith(HEADER):
        raise ValueError("accumulation series may only gain rows; an existing row or its header changed")
    published = {line.split(",")[1] for line in before[len(HEADER):].splitlines()}
    for line in after[len(before):].splitlines():
        fields = line.split(",")
        if len(fields) != 11:
            raise ValueError(f"malformed accumulation row: {line!r}")
        day, submission, modules, edges, per_module, connected, in_degree, depth, recent, add_only, stated = fields
        date.fromisoformat(day)
        if submission in published or not (candidate / "Submissions" / f"{submission}.json").is_file():
            raise ValueError(f"accumulation row for an unknown or repeated submission: {submission}")
        published.add(submission)
        for number in (modules, edges, in_degree, depth):
            int(number)
        for number in (per_module, connected):
            float(number)
        if recent not in {"true", "false"} or add_only not in {"true", "false"} or stated not in {"true", "false", "unknown"}:
            raise ValueError(f"malformed accumulation row: {line!r}")


def validate_rejections(base: Path, candidate: Path) -> None:
    """Weekly aggregates are recorded once, after the week ends, and never
    rewritten: the reports behind them expire, so this file is the only copy."""
    from collect_rejections import DESTINATION, HEADER

    before_path = base / DESTINATION
    before = before_path.read_text(encoding="utf-8") if before_path.exists() else HEADER
    after = (candidate / DESTINATION).read_text(encoding="utf-8")
    if not after.startswith(before) or not after.startswith(HEADER):
        raise ValueError("rejection aggregates may only gain rows; an existing row or its header changed")
    weeks = {line.split(",", 1)[0] for line in before[len(HEADER):].splitlines()}
    latest = max(weeks, default="")
    seen: set[tuple[str, str]] = set()
    for line in after[len(before):].splitlines():
        fields = line.split(",")
        if len(fields) != 3:
            raise ValueError(f"malformed rejection row: {line!r}")
        week, code, runs = fields
        day = date.fromisoformat(week)
        if day.weekday() != 0 or week <= latest:
            raise ValueError(f"rejection row for a week that is not a new Monday: {line!r}")
        if not code.replace("_", "").isalpha() or not code.isupper() or (week, code) in seen:
            raise ValueError(f"malformed or repeated rejection code: {line!r}")
        if int(runs) < 1:
            raise ValueError(f"rejection row with no runs: {line!r}")
        seen.add((week, code))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    base_files = files(args.base)
    candidate_files = files(args.candidate)
    paths = {path for path in base_files.keys() | candidate_files.keys() if base_files.get(path) != candidate_files.get(path)}
    # Name only what is actually disallowed. Listing every changed path when
    # one is unexpected sends the reader looking at the innocent ones.
    unexpected = sorted(path for path in paths if not allowed(path))
    if not paths:
        raise SystemExit("generated-output pull request changes nothing")
    if unexpected:
        raise SystemExit(f"unexpected generated-output paths: {unexpected}")
    if "LeanFrontier.lean" in paths:
        subprocess.run(["python3", str(ROOT / "tools" / "generate_umbrella.py"), "--root", str(args.candidate), "--check"], check=True)
    if "docs/catalogue/index.html" in paths:
        subprocess.run(["python3", str(ROOT / "tools" / "generate_catalogue.py"), "--root", str(args.candidate), "--check"], check=True)
    if "experiments/launcher-ab.csv" in paths:
        subprocess.run(["python3", str(ROOT / "tools" / "generate_experiment_ledger.py"), "--root", str(args.candidate), "--check"], check=True)
    if "experiments/accumulation.csv" in paths:
        validate_accumulation(args.base, args.candidate)
    if "experiments/rejections.csv" in paths:
        validate_rejections(args.base, args.candidate)
    for relative in paths:
        if relative.startswith("receiver-observations/"):
            validate_observation(args.candidate / relative, args.candidate)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
