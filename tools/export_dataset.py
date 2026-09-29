#!/usr/bin/env python3
"""Export the accepted corpus as one JSON record per submission.

The catalogue is for reading and the accumulation series is for counting; this
is for anyone who wants to analyse the corpus without cloning the repository
and walking its history. Each record joins what the submitter claimed, what the
receiver observed, and where the submission sits in the corpus:

- the claim, exactly as submitted (`Submissions/<id>.json`);
- the commit on the default branch at which it was accepted, and its date;
- the modules that merge added, with their internal imports, and any existing
  modules it changed (allowed until the add-only rule of 22 September 2026);
- the receiver observation, if one was recorded.

The walk over history is the accumulation series' own, so the two artifacts
agree on which commit accepted which submission. Output is deterministic:
records in order of acceptance, keys sorted, gzip without a timestamp, so the
same commit always yields the same bytes and a release asset can be verified by
regenerating it. See docs/dataset.md for the record schema.
"""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path
from typing import Any

from generate_accumulation_series import IMPORT_RE, ROOT, ShallowHistory, modules_at, run, submission_commits

RECORD_VERSION = 1


def observations(root: Path) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for path in sorted((root / "receiver-observations").glob("*/*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        submission = record.get("submission_id")
        if not isinstance(submission, str):
            continue
        report = record.get("report", {})
        result[submission] = {
            "accepted_revision": record.get("accepted_revision"),
            "observed_at": record.get("observed_at"),
            "validation_run": record.get("validation_run"),
            "trusted_receiver_revision": record.get("trusted_receiver_revision"),
            "validated_candidate_revision": record.get("validated_candidate_revision"),
            "protocol_version": report.get("protocol_version"),
            "duration_seconds": report.get("duration_seconds"),
            "observed": report.get("observed", {}),
        }
    return result


def has_parent(commit: str, root: Path) -> bool:
    return bool(run(["rev-list", "--parents", "-n", "1", commit], root).split()[1:])


def records(root: Path) -> list[dict[str, Any]]:
    if run(["rev-parse", "--is-shallow-repository"], root).strip() == "true":
        raise ShallowHistory(f"{root} is a shallow clone; fetch full history (git fetch --unshallow) first")
    observed = observations(root)
    result: list[dict[str, Any]] = []
    last_commit = ""
    added: set[str] = set()
    extended: set[str] = set()
    sources: dict[str, str] = {}
    for commit, day, submission in submission_commits(root):
        if commit != last_commit:
            # Against the merge's own first parent, not the previous
            # submission: maintenance commits land in between and change
            # modules no submission touched.
            sources = modules_at(commit, root)
            before = modules_at(f"{commit}^1", root) if has_parent(commit, root) else {}
            added = set(sources) - set(before)
            extended = {name for name in before if name in sources and sources[name] != before[name]}
            last_commit = commit
        claim_text = run(["show", f"{commit}:Submissions/{submission}.json"], root)
        known = set(sources)
        result.append({
            "record_version": RECORD_VERSION,
            "submission_id": submission,
            "accepted": {"commit": commit, "date": day},
            "claim": json.loads(claim_text),
            "modules": sorted(added),
            "extended": sorted(extended),
            "imports": {
                module: sorted(target for target in IMPORT_RE.findall(sources[module]) if target in known)
                for module in sorted(added)
            },
            "observation": observed.get(submission),
        })
    return result


def render(root: Path) -> bytes:
    lines = "".join(json.dumps(record, sort_keys=True, ensure_ascii=False) + "\n" for record in records(root))
    # filename="" and mtime=0: the gzip header then carries nothing that varies.
    return gzip.compress(lines.encode("utf-8"), mtime=0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path, required=True, help="where to write the .jsonl.gz")
    args = parser.parse_args()
    try:
        data = render(args.root)
    except ShallowHistory as error:
        print(error)
        return 2
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
