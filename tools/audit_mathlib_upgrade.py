#!/usr/bin/env python3
"""Audit the accepted corpus against the active Mathlib fingerprint index."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from mathlib_release import ROOT, load_release_policy


def accepted_entrypoints(root: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for path in sorted((root / "Submissions").glob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        for entrypoint in record.get("entrypoints", []):
            if isinstance(entrypoint, str):
                result[entrypoint] = path.stem
    return result


def load_index(root: Path, release: dict[str, str]) -> dict[str, set[str]]:
    index = json.loads((root / "policy" / release["fingerprint_index"]).read_text(encoding="utf-8"))
    if index.get("format_version") != 1 or index.get("mathlib_revision") != release["mathlib_revision"]:
        raise ValueError("Mathlib fingerprint index does not match the active release policy")
    entries = index.get("fingerprints_by_type_hint")
    if not isinstance(entries, dict):
        raise ValueError("Mathlib fingerprint index has invalid entries")
    return {hint: set(values) for hint, values in entries.items() if isinstance(hint, str) and isinstance(values, list) and all(isinstance(value, str) for value in values)}


def resolved_mathlib_commit(root: Path) -> str:
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest.get("packages", []):
        if isinstance(package, dict) and package.get("name") == "mathlib" and isinstance(package.get("rev"), str):
            return package["rev"]
    raise ValueError("lake-manifest.json does not contain a resolved Mathlib commit")


def fingerprint(item: dict[str, Any]) -> str | None:
    canonical = item.get("type_canonical")
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest() if isinstance(canonical, str) else None


def find_collisions(entrypoints: dict[str, str], findings: dict[str, dict[str, Any]], index: dict[str, set[str]]) -> list[dict[str, str]]:
    collisions: list[dict[str, str]] = []
    for name, submission_id in sorted(entrypoints.items()):
        finding = findings.get(name)
        if finding is None:
            raise ValueError(f"accepted entrypoint is absent from the Lean audit: {name}")
        digest = fingerprint(finding)
        hint = finding.get("type_hint")
        if not isinstance(hint, str) or digest is None:
            raise ValueError(f"Lean audit emitted invalid fingerprint data for {name}")
        if digest in index.get(hint, set()):
            collisions.append({"submission_id": submission_id, "entrypoint": name, "statement_sha256": digest})
    return collisions


def run(command: list[str], *, cwd: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=timeout, check=False)


def corpus_modules(root: Path) -> list[str]:
    """Every subject module, as Lean module names."""
    return sorted(
        path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
        for path in (root / "LeanFrontier").rglob("*.lean")
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    release = load_release_policy(root / "policy" / "mathlib-release.json")
    result: dict[str, Any] = {
        "format_version": 1,
        "source_release_tag": release["source_release_tag"],
        "lean_toolchain": release["lean_toolchain"],
        "mathlib_revision": release["mathlib_revision"],
        "accepted": False,
        "code": "BUILD_FAILED",
        "kernel_recheck": "not reached",
        "collisions": [],
    }
    try:
        entrypoints = accepted_entrypoints(root)
        build = run(["lake", "build"], cwd=root, timeout=480)
        if build.returncode:
            raise RuntimeError(build.stderr.strip()[-2000:] or "lake build failed")
        for module in corpus_modules(root):
            recheck = run(["lake", "env", "leanchecker", module], cwd=root, timeout=300)
            if recheck.returncode:
                raise RuntimeError(
                    (recheck.stderr.strip() or recheck.stdout.strip())[-2000:]
                    or f"leanchecker rejected {module} after the upgrade"
                )
        audit = run(["lake", "exe", "frontier-audit", "--", "LeanFrontier"], cwd=root, timeout=240)
        if audit.returncode:
            raise RuntimeError(audit.stderr.strip()[-2000:] or "frontier-audit failed")
        findings = {item["name"]: item for line in audit.stdout.splitlines() if isinstance(item := json.loads(line), dict) and isinstance(item.get("name"), str)}
        index_path = root / "policy" / release["fingerprint_index"]
        collisions = find_collisions(entrypoints, findings, load_index(root, release))
        with tempfile.TemporaryDirectory(prefix="leanfrontier-upgrade-client-") as directory:
            client = Path(directory) / "Client.lean"
            client.write_text("import LeanFrontier\n\n" + "\n".join(f"#check {name}" for name in sorted(entrypoints)) + "\n", encoding="utf-8")
            smoke = run(["lake", "env", "lean", str(client)], cwd=root, timeout=120)
            if smoke.returncode:
                raise RuntimeError(smoke.stderr.strip()[-2000:] or "downstream entrypoint smoke test failed")
        result.update({
            "mathlib_commit": resolved_mathlib_commit(root),
            "fingerprint_index": release["fingerprint_index"],
            "fingerprint_index_sha256": hashlib.sha256(index_path.read_bytes()).hexdigest(),
            "entrypoint_count": len(entrypoints),
            "downstream_import_smoke": "pass",
            "kernel_recheck": "pass",
            "collisions": collisions,
            "accepted": not collisions,
            "code": "MATHLIB_UPSTREAM_COLLISION" if collisions else "ACCEPTED",
        })
    except (OSError, ValueError, json.JSONDecodeError, RuntimeError, subprocess.TimeoutExpired) as error:
        result["error"] = str(error)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
