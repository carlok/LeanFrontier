#!/usr/bin/env python3
"""Check that the receiver can state every accepted entrypoint as it is written.

The receiver reads statements from source text and probes them in a context it
rebuilds (`frontier_validate.statement_goals`). Four bugs in that reading were
found in one week of October 2026, each silent: a misread statement is simply
probed as something else, or not at all. This screen states every accepted
entrypoint with `sorry`, one Lean file per module, in exactly that context.

A statement may fail to state for an expected reason: it names a definition of
its own module, which the receiver's probe deliberately cannot see. Any other
failure means the reading or the context is wrong, and the screen fails.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

from frontier_validate import IMPORT_RE, run, statement_goals, strip_comments
from mathlib_release import ROOT

LEAN_ERROR_RE = re.compile(r"^\S+?:(?P<line>\d+):\d+: error(?:\([^)]*\))?: (?P<message>.*)$", re.MULTILINE)
DEFINITION_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:noncomputable|private|protected|partial|unsafe)[ \t]+)*"
    r"(?:def|abbrev|structure|inductive|class|instance|opaque)[ \t]+([^\s(:{\[]+)",
    re.MULTILINE)
IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def declared_entrypoints(root: Path) -> dict[str, str]:
    """Entrypoint -> submission id, from every accepted claim."""
    found: dict[str, str] = {}
    for path in sorted((root / "Submissions").glob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        for entrypoint in record.get("entrypoints", []):
            found[entrypoint] = record.get("submission_id", path.stem)
    return found


def own_names(code: str) -> set[str]:
    """Last components of the names this module defines."""
    return {name.rsplit(".", 1)[-1] for name in DEFINITION_RE.findall(code)}


def names_own_definition(statement: str, owned: set[str]) -> bool:
    """Whether a statement mentions something its own module defines. Such a
    statement cannot be stated from the baseline by design."""
    return bool(owned & {token for part in IDENTIFIER_RE.findall(statement) for token in part.split(".")})


def module_source(code: str, goals: dict[str, tuple[str, tuple[str, str]]], wanted: list[str]) -> tuple[str, list[tuple[str, int, int]]]:
    """One Lean file stating each wanted goal with `sorry`, and the line span of each."""
    imports = [f"import {module}" for module in IMPORT_RE.findall(code) if module != "Mathlib"]
    lines = ["import Mathlib", *imports, ""]
    spans: list[tuple[str, int, int]] = []
    for name in wanted:
        body, (header, footer) = goals[name]
        context = [line for line in header.splitlines() if not line.startswith("import ")]
        start = len(lines) + 1
        lines += ["section", *context, f"example {body.strip()} := by", "  sorry", *footer.splitlines(), "end"]
        spans.append((name, start, len(lines)))
    return "\n".join(lines) + "\n", spans


def attribute_errors(output: str, spans: list[tuple[str, int, int]]) -> dict[str, str]:
    """First Lean error inside each goal's span."""
    errors: dict[str, str] = {}
    for match in LEAN_ERROR_RE.finditer(output):
        line = int(match.group("line"))
        for name, start, end in spans:
            if start <= line <= end:
                errors.setdefault(name, match.group("message").strip()[:300])
    return errors


def screen(root: Path, timeout: int) -> dict[str, object]:
    claims = declared_entrypoints(root)
    results: dict[str, dict[str, str]] = {}
    with tempfile.TemporaryDirectory(prefix="screen-statements-") as scratch:
        for path in sorted((root / "LeanFrontier").rglob("*.lean")):
            goals = statement_goals(path)
            wanted = sorted(name for name in goals if name in claims)
            if not wanted:
                continue
            code = strip_comments(path.read_text(encoding="utf-8"))
            source, spans = module_source(code, goals, wanted)
            probe = Path(scratch) / f"{path.stem}.lean"
            probe.write_text(source, encoding="utf-8")
            result = run(["lake", "env", "lean", "-DmaxErrors=100000", str(probe)], root, timeout)
            errors = attribute_errors(f"{result.stdout}\n{result.stderr}", spans)
            owned = own_names(code)
            for name in wanted:
                if name not in errors:
                    outcome = "stated"
                elif names_own_definition(goals[name][0], owned):
                    outcome = "own definition"
                else:
                    outcome = "other"
                results[name] = {"submission": claims[name], "outcome": outcome, **({"error": errors[name]} if name in errors else {})}
    counts = {outcome: sum(item["outcome"] == outcome for item in results.values())
              for outcome in ("stated", "own definition", "other")}
    return {"entrypoints": len(claims), "screened": len(results),
            "unmatched": sorted(set(claims) - set(results)), "counts": counts, "results": results}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--timeout", type=int, default=1200, help="seconds per module")
    args = parser.parse_args(argv)
    report = screen(args.root, args.timeout)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    counts = report["counts"]
    print(f"{report['screened']} of {report['entrypoints']} entrypoints screened: "
          f"{counts['stated']} stated, {counts['own definition']} name their own module's definitions, "
          f"{counts['other']} other")
    failed = False
    for name, item in sorted(report["results"].items()):
        if item["outcome"] == "other":
            print(f"::error::{name} ({item['submission']}) cannot be stated as written: {item['error']}")
            failed = True
    for name in report["unmatched"]:
        print(f"::error::{name} is declared but its statement was not found")
        failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
