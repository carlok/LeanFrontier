#!/usr/bin/env python3
"""Persist one accepted receiver report without modifying its producer claim."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--submission", type=Path, required=True)
    parser.add_argument("--accepted-revision", required=True)
    parser.add_argument("--candidate-revision", required=True)
    parser.add_argument("--trusted-receiver-revision", required=True)
    parser.add_argument("--validation-run", required=True)
    parser.add_argument("--observed-at", required=True)
    parser.add_argument("--output-root", type=Path, default=Path("receiver-observations"))
    args = parser.parse_args()

    report = load_json(args.report)
    submission = load_json(args.submission)
    if not isinstance(report, dict) or report.get("accepted") is not True:
        raise SystemExit("receiver report is not accepted")
    if not isinstance(submission, dict) or not isinstance(submission.get("submission_id"), str):
        raise SystemExit("submission record has no valid submission_id")
    observed = report.get("observed")
    if not isinstance(observed, dict) or not isinstance(observed.get("entrypoints"), dict):
        raise SystemExit("receiver report has no valid entrypoint observations")
    entrypoints = submission.get("entrypoints")
    if not isinstance(entrypoints, list) or set(entrypoints) != set(observed["entrypoints"]):
        raise SystemExit("receiver entrypoints do not match the immutable submission claim")

    payload = {
        "observation_version": "0.1",
        "submission_id": submission["submission_id"],
        "accepted_revision": args.accepted_revision,
        "validated_candidate_revision": args.candidate_revision,
        "trusted_receiver_revision": args.trusted_receiver_revision,
        "validation_run": args.validation_run,
        "observed_at": args.observed_at,
        "report": report,
    }
    destination = args.output_root / submission["submission_id"] / f"{args.accepted_revision}.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if destination.exists() and destination.read_text(encoding="utf-8") != encoded:
        raise SystemExit(f"refusing to rewrite observation at {destination}")
    destination.write_text(encoded, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
