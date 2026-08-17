from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import audit_mathlib_upgrade  # noqa: E402
from mathlib_release import ReleasePolicyError, load_release_policy, write_release_policy  # noqa: E402
import validate_mathlib_upgrade  # noqa: E402


class MathlibReleasePolicyTests(unittest.TestCase):
    def test_current_policy_selects_its_exact_index_name(self) -> None:
        policy = load_release_policy()
        self.assertEqual(policy["fingerprint_index"], f"mathlib-fingerprints-{policy['mathlib_revision']}.json")
        self.assertTrue((ROOT / "policy" / policy["fingerprint_index"]).is_file())

    def test_rejects_mismatched_release_tag(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "release.json"
            path.write_text(json.dumps({
                "policy_version": "0.1", "source_release_tag": "v1.2.3", "mathlib_revision": "v1.2.4",
                "lean_toolchain": "leanprover/lean4:v1.2.3", "fingerprint_index": "mathlib-fingerprints-v1.2.4.json",
            }))
            with self.assertRaises(ReleasePolicyError):
                load_release_policy(path)

    def test_write_policy_is_self_consistent(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "release.json"
            write_release_policy(path, mathlib_revision="v9.8.7", lean_toolchain="leanprover/lean4:v9.8.7")
            self.assertEqual(load_release_policy(path)["fingerprint_index"], "mathlib-fingerprints-v9.8.7.json")


class MathlibCollisionTests(unittest.TestCase):
    def test_new_mathlib_exact_match_blocks_upgrade(self) -> None:
        entrypoints = {"LeanFrontier.Example.result": "example-submission"}
        findings = {"LeanFrontier.Example.result": {"type_hint": "hint", "type_canonical": "canonical"}}
        digest = audit_mathlib_upgrade.fingerprint(findings["LeanFrontier.Example.result"])
        collisions = audit_mathlib_upgrade.find_collisions(entrypoints, findings, {"hint": {digest}})
        self.assertEqual(collisions[0]["submission_id"], "example-submission")
        self.assertEqual(collisions[0]["entrypoint"], "LeanFrontier.Example.result")

    def test_missing_audited_entrypoint_is_an_error(self) -> None:
        with self.assertRaises(ValueError):
            audit_mathlib_upgrade.find_collisions({"LeanFrontier.Missing": "submission"}, {}, {})


class MathlibUpgradePathTests(unittest.TestCase):
    def write_tree(self, root: Path, *, revision: str, index: str, accepted: bool = True) -> None:
        (root / "policy" / "mathlib-upgrades").mkdir(parents=True)
        (root / "lean-toolchain").write_text(f"leanprover/lean4:{revision}\n")
        (root / "lakefile.toml").write_text(f'rev = "{revision}"\n')
        (root / "lake-manifest.json").write_text("{}\n")
        (root / "policy" / "mathlib-release.json").write_text(json.dumps({
            "policy_version": "0.1", "source_release_tag": revision, "mathlib_revision": revision,
            "lean_toolchain": f"leanprover/lean4:{revision}", "fingerprint_index": index,
        }))
        (root / "policy" / index).write_text("{}\n")
        (root / "policy" / "mathlib-upgrades" / f"{revision}.json").write_text(json.dumps({
            "mathlib_revision": revision, "accepted": accepted,
            "code": "ACCEPTED" if accepted else "MATHLIB_UPSTREAM_COLLISION", "collisions": [] if accepted else [{}],
        }))

    def test_upgrade_path_accepts_only_the_replaced_index_and_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, candidate = Path(directory) / "base", Path(directory) / "candidate"
            self.write_tree(base, revision="v1.0.0", index="mathlib-fingerprints-v1.0.0.json")
            self.write_tree(candidate, revision="v1.0.1", index="mathlib-fingerprints-v1.0.1.json")
            (candidate / "lake-manifest.json").write_text('{"mathlib":"new"}\n')
            (candidate / "policy" / "mathlib-upgrades" / "v1.0.0.json").write_bytes(
                (base / "policy" / "mathlib-upgrades" / "v1.0.0.json").read_bytes()
            )
            self.assertEqual(validate_mathlib_upgrade.main(["--base", str(base), "--candidate", str(candidate)]), 0)

    def test_upgrade_path_rejects_collision_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, candidate = Path(directory) / "base", Path(directory) / "candidate"
            self.write_tree(base, revision="v1.0.0", index="mathlib-fingerprints-v1.0.0.json")
            self.write_tree(candidate, revision="v1.0.1", index="mathlib-fingerprints-v1.0.1.json", accepted=False)
            (candidate / "lake-manifest.json").write_text('{"mathlib":"new"}\n')
            (candidate / "policy" / "mathlib-upgrades" / "v1.0.0.json").write_bytes(
                (base / "policy" / "mathlib-upgrades" / "v1.0.0.json").read_bytes()
            )
            with self.assertRaises(ValueError):
                validate_mathlib_upgrade.main(["--base", str(base), "--candidate", str(candidate)])
