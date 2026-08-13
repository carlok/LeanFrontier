#!/usr/bin/env python3
"""Extract a sealed award-scoring input from one accepted receiver observation."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--observation", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args(argv)
    payload = load_json(args.observation)
    if not isinstance(payload, dict) or payload.get("observation_version") != "0.1":
        raise SystemExit("invalid receiver observation")
    report = payload.get("report")
    if not isinstance(report, dict) or report.get("accepted") is not True:
        raise SystemExit("receiver observation is not accepted")
    observed = report.get("observed")
    if not isinstance(observed, dict):
        raise SystemExit("receiver observation lacks facts")
    declarations = observed.get("audited_declarations")
    entrypoints = observed.get("entrypoints")
    if not isinstance(declarations, dict) or not isinstance(entrypoints, dict):
        raise SystemExit("receiver observation predates award audit facts")
    if not isinstance(observed.get("lean_source_bytes"), int):
        raise SystemExit("receiver observation lacks source size")
    records = {name: item for name, item in declarations.items() if isinstance(name, str) and isinstance(item, dict)}
    records.update({name: item for name, item in entrypoints.items() if isinstance(name, str) and isinstance(item, dict)})
    output = {
        "format_version": "0.1",
        "submission_id": payload.get("submission_id"),
        "accepted_revision": payload.get("accepted_revision"),
        "lean_source_bytes": observed["lean_source_bytes"],
        "entrypoints": sorted(entrypoints),
        "declarations": [records[name] for name in sorted(records)],
    }
    encoded = json.dumps(output, indent=2, sort_keys=True) + "\n"
    print(encoded, end="")
    if args.json_out:
        args.json_out.write_text(encoded, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
