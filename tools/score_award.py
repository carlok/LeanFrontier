#!/usr/bin/env python3
"""Score accepted LeanFrontier award entries without executing submitted code.

Inputs are trusted, normalized audit facts produced by the receiver.  The
script has no network access and deliberately does not read candidate sources.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / "policy" / "award-scoring-v0.1.json"
FORMAT_VERSION = "0.1"


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def script_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def fail(message: str) -> ValueError:
    return ValueError(f"invalid award input: {message}")


def score_one(payload: Any, policy: dict[str, Any], closing_revision: str) -> dict[str, Any]:
    if not isinstance(payload, dict) or payload.get("format_version") != FORMAT_VERSION:
        raise fail("format_version must be '0.1'")
    submission_id = payload.get("submission_id")
    entrypoints = payload.get("entrypoints")
    declarations = payload.get("declarations")
    source_bytes = payload.get("lean_source_bytes")
    if not isinstance(submission_id, str) or not submission_id:
        raise fail("submission_id must be a nonempty string")
    if not isinstance(entrypoints, list) or not entrypoints or any(not isinstance(name, str) for name in entrypoints):
        raise fail("entrypoints must be a nonempty string list")
    if not isinstance(declarations, list) or not isinstance(source_bytes, int) or source_bytes < 0:
        raise fail("declarations and lean_source_bytes are required")

    all_nodes: dict[str, dict[str, Any]] = {}
    exclusions: list[dict[str, str]] = []
    fingerprints: set[str] = set()
    for item in declarations:
        if not isinstance(item, dict) or not isinstance(item.get("name"), str):
            raise fail("each declaration needs a name")
        name = item["name"]
        if name in all_nodes:
            raise fail(f"duplicate declaration name {name}")
        if not name.startswith("LeanFrontier."):
            raise fail(f"declaration outside LeanFrontier: {name}")
        dependencies = item.get("type_dependencies", [])
        if not isinstance(dependencies, list) or any(not isinstance(dep, str) for dep in dependencies):
            raise fail(f"type_dependencies must be strings for {name}")
        all_nodes[name] = item

    qualifying: dict[str, dict[str, Any]] = {}
    for name, item in sorted(all_nodes.items()):
        reason: str | None = None
        if item.get("kind") not in policy["eligible_kinds"]:
            reason = "ineligible_kind"
        else:
            for flag in policy["excluded_flags"]:
                if item.get(flag) is True:
                    reason = flag
                    break
        fingerprint = item.get("statement_sha256")
        if reason is None and isinstance(fingerprint, str):
            if fingerprint in fingerprints:
                reason = "alpha_equivalent"
            else:
                fingerprints.add(fingerprint)
        if reason is None:
            qualifying[name] = item
        else:
            exclusions.append({"name": name, "reason": reason})

    missing = sorted(set(entrypoints) - set(all_nodes))
    if missing:
        raise fail(f"entrypoints absent from declarations: {missing}")

    def depth(name: str, visiting: set[str]) -> int:
        if name in visiting:
            return 0
        children = [dep for dep in all_nodes[name]["type_dependencies"] if dep in qualifying]
        if not children:
            return 1
        return 1 + max(depth(child, visiting | {name}) for child in children)

    raw_depth = max(depth(name, set()) for name in entrypoints)
    reused = sorted(
        name for name in qualifying
        if name not in entrypoints and sum(name in all_nodes[entrypoint]["type_dependencies"] for entrypoint in entrypoints) >= 2
    )
    source_kib = max(source_bytes / 1024, policy["efficiency_minimum_kib"])
    depth_score = policy["depth_weight"] * min(raw_depth, policy["depth_edge_cap"]) / policy["depth_edge_cap"]
    reuse_score = policy["reuse_weight"] * min(len(reused), policy["reuse_interface_cap"]) / policy["reuse_interface_cap"]
    efficiency_ratio = len(qualifying) / source_kib
    efficiency_score = policy["efficiency_weight"] * min(efficiency_ratio, policy["efficiency_nodes_per_kib_cap"]) / policy["efficiency_nodes_per_kib_cap"]
    total = round(depth_score + reuse_score + efficiency_score, 6)
    return {
        "submission_id": submission_id,
        "score": total,
        "components": {
            "type_level_depth": {"raw_edges": raw_depth, "score": round(depth_score, 6)},
            "interface_reuse": {"reused_interfaces": reused, "score": round(reuse_score, 6)},
            "interface_efficiency": {"qualifying_nodes": len(qualifying), "source_kib": round(source_kib, 6), "nodes_per_kib": round(efficiency_ratio, 6), "score": round(efficiency_score, 6)},
        },
        "exclusions": exclusions,
        "tie_break_key": hashlib.sha256(f"{closing_revision}\0{submission_id}".encode()).hexdigest(),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--closing-revision", required=True)
    parser.add_argument("--input", type=Path, action="append", required=True, dest="inputs")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args(argv)
    policy = load_json(POLICY_PATH)
    if not isinstance(policy, dict) or policy.get("format_version") != FORMAT_VERSION:
        raise SystemExit("invalid award scoring policy")
    try:
        results = [score_one(load_json(path), policy, args.closing_revision) for path in args.inputs]
    except (OSError, json.JSONDecodeError, ValueError) as error:
        raise SystemExit(str(error))
    results.sort(key=lambda result: (-result["score"], result["tie_break_key"], result["submission_id"]))
    output = {
        "format_version": FORMAT_VERSION,
        "scorer_sha256": script_sha256(),
        "policy_sha256": hashlib.sha256(POLICY_PATH.read_bytes()).hexdigest(),
        "closing_revision": args.closing_revision,
        "ranked_results": results,
    }
    encoded = json.dumps(output, indent=2, sort_keys=True) + "\n"
    print(encoded, end="")
    if args.json_out:
        args.json_out.write_text(encoded, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
