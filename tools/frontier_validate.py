#!/usr/bin/env python3
"""Deterministic validator for one LeanFrontier submission bundle.

This module deliberately has no third-party dependencies. It is invoked by the
local wrapper and by the GitHub receiver using a trusted checkout of this file.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import tempfile
import time
import hashlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from mathlib_release import DEFAULT_POLICY as DEFAULT_MATHLIB_RELEASE, ReleasePolicyError, load_release_policy


ROOT = Path(__file__).resolve().parents[1]
SCRATCH = Path("/tmp/leanfrontier")
DEFAULT_LIMITS = ROOT / "policy" / "limits.json"
DEFAULT_AXIOMS = ROOT / "policy" / "axioms.json"
DEFAULT_TRIVIALITY = ROOT / "policy" / "triviality.json"
DEFAULT_CONJECTURE = ROOT / "policy" / "conjecture.json"
SUBMISSION_RE = re.compile(r"^Submissions/([a-z0-9][a-z0-9-]{2,63})\.json$")
# At least two components after the ownership prefix: one mathematical
# namespace and the declaration itself. `LeanFrontier.tentMap` would land in the
# root namespace once the prefix is removed, and leaves the next submission in
# the same area no name to use.
ENTRYPOINT_RE = re.compile(r"^LeanFrontier(?:\.[A-Za-z_][A-Za-z0-9_']*){2,}$")
FORBIDDEN_SECURITY = re.compile(
    r"\b(?:unsafe|run_tac|elab|macro|syntax)\b|#(?:eval|print|reduce|check|guard)", re.MULTILINE
)
SORRY_RE = re.compile(r"\b(?:sorry|sorryAx)\b")
AXIOM_RE = re.compile(r"\baxiom\b")
DECL_RE = re.compile(
    r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b(?P<body>.*?)(?=\s*:=)", re.DOTALL
)
# A conjecture is `def NAME : Prop := <proposition>`. The right-hand side runs
# until the next thing that can start a top-level declaration; an extraction
# that gets this wrong yields an unusable probe, which is reported as
# inconclusive rather than as a rejection.
CONJECTURE_RE = re.compile(
    r"^[ \t]*def[ \t]+([A-Za-z_][A-Za-z0-9_']*)[ \t]*:[ \t]*Prop[ \t]*:=(?P<body>.*?)"
    r"(?=^[ \t]*(?:@\[|theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|namespace|end|open|section|variable)\b|\Z)",
    re.DOTALL | re.M,
)
# `theorem c_holds : ConjectureName := ...` is how the contract says a
# conjecture is resolved, so resolution is detectable from the source text.
RESOLUTION_RE = re.compile(
    r"^[ \t]*theorem[ \t]+[A-Za-z_][A-Za-z0-9_']*[ \t]*:[ \t]*([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:=",
    re.M,
)
DECLARATION_RE = re.compile(r"\b(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)\b")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
PUBLIC_DECLARATION_RE = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_']*)\b")
DIRECT_ALIAS_RE = re.compile(r"^\s*(?:def|abbrev)\s+[A-Za-z_][A-Za-z0-9_']*\s*:=\s*[A-Za-z_][A-Za-z0-9_.']*\s*$")


@dataclass
class Diagnostic:
    code: str
    message: str
    path: str | None = None

    def json(self) -> dict[str, str]:
        result = {"code": self.code, "message": self.message}
        if self.path:
            result["path"] = self.path
        return result


@dataclass
class Report:
    started_at: float = field(default_factory=time.time)
    diagnostics: list[Diagnostic] = field(default_factory=list)
    observations: dict[str, Any] = field(default_factory=dict)

    def reject(self, code: str, message: str, path: str | None = None) -> None:
        self.diagnostics.append(Diagnostic(code, message, path))

    @property
    def accepted(self) -> bool:
        return not self.diagnostics

    def json(self) -> dict[str, Any]:
        return {
            "protocol_version": "0.1",
            "accepted": self.accepted,
            "diagnostics": [item.json() for item in self.diagnostics],
            "observed": self.observations,
            "duration_seconds": round(time.time() - self.started_at, 3),
        }


def load_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


ALWAYS_IGNORED = frozenset({".git", ".lake", ".frontier", "__pycache__"})


def ignored_names(trusted: Path | None) -> frozenset[str]:
    """Names the repository itself declares uninteresting, plus the always-ignored.

    A submitter following README instructions runs the receiver in a working
    tree, where `.DS_Store` and the `coverage.xml` the documented test command
    writes would otherwise be reported as path policy violations — findings CI
    never produces, since it validates a clean checkout. Reading `.gitignore`
    keeps one source of truth instead of a second hardcoded list that drifts.

    Read from the trusted tree, never the candidate: a submission that could
    extend this set could hide files from the receiver. Only plain names are
    honoured; globs and negations are left to git.
    """
    if trusted is None:
        return ALWAYS_IGNORED
    try:
        lines = (trusted / ".gitignore").read_text(encoding="utf-8").splitlines()
    except OSError:
        return ALWAYS_IGNORED
    plain = {
        entry.rstrip("/")
        for line in lines
        if (entry := line.strip()) and not entry.startswith(("#", "!"))
        and not any(character in entry for character in "*?[]/")
    }
    plain |= {
        entry.rstrip("/")
        for line in lines
        if (entry := line.strip()) and entry.endswith("/") and entry.count("/") == 1
        and not any(character in entry for character in "*?[]!#")
    }
    return ALWAYS_IGNORED | frozenset(plain)


def tree_files(root: Path, ignored: frozenset[str] = ALWAYS_IGNORED) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for directory, names, files in os.walk(root, followlinks=False):
        names[:] = [name for name in names if name not in ignored]
        directory_path = Path(directory)
        for name in files:
            if name in ignored:
                continue
            path = directory_path / name
            relative = path.relative_to(root).as_posix()
            result[relative] = path
    return result


def content_changed(left: Path | None, right: Path | None) -> bool:
    if left is None or right is None:
        return True
    if left.is_symlink() or right.is_symlink():
        return True
    return left.read_bytes() != right.read_bytes()


def changed_paths(base: Path | None, candidate: Path) -> tuple[dict[str, Path | None], dict[str, Path]]:
    ignored = ignored_names(base)
    before = tree_files(base, ignored) if base else {}
    after = tree_files(candidate, ignored)
    changed = {
        name: after.get(name)
        for name in sorted(set(before) | set(after))
        if content_changed(before.get(name), after.get(name))
    }
    return changed, before


def is_allowed_path(path: str) -> bool:
    return path.startswith("LeanFrontier/") or SUBMISSION_RE.fullmatch(path) is not None


def line_count(path: Path) -> int:
    try:
        return path.read_text(encoding="utf-8").count("\n") + 1
    except UnicodeDecodeError:
        return 0


def validate_metadata(record: Any, submission_id: str, limits: dict[str, Any], mathlib_release: dict[str, str], report: Report, path: str) -> None:
    if not isinstance(record, dict):
        report.reject("SCHEMA_INVALID", "submission record must be a JSON object", path)
        return
    required = {
        "protocol_version", "submission_id", "producer", "origin_mode", "statement_origin",
        "proof_origin", "entrypoints", "base_mathlib_revision", "source_context",
    }
    # Optional keys are enumerated here rather than inferred: an unrecognised
    # key stays a rejection, so a producer cannot smuggle metadata past the
    # receiver by inventing a field name.
    optional = {"launcher_arm"}
    unknown = set(record) - required - optional
    missing = required - set(record)
    if missing or unknown:
        report.reject("SCHEMA_INVALID", f"record keys mismatch; missing={sorted(missing)}, unknown={sorted(unknown)}", path)
    arm = record.get("launcher_arm")
    if "launcher_arm" in record and arm not in {"A", "B", None}:
        report.reject("SCHEMA_INVALID", f"launcher_arm must be \"A\", \"B\" or null, not {arm!r}", path)
    if record.get("protocol_version") != "0.1":
        report.reject("SCHEMA_INVALID", "protocol_version must be '0.1'", path)
    if record.get("submission_id") != submission_id:
        report.reject("SCHEMA_INVALID", "submission_id must match the file name", path)
    producer = record.get("producer")
    if not isinstance(producer, dict) or set(producer) != {"type", "model", "agent"}:
        report.reject("SCHEMA_INVALID", "producer requires exactly type, model, and agent", path)
    elif producer.get("type") not in {"llm", "autonomous_agent", "hybrid", "other"}:
        report.reject("SCHEMA_INVALID", "producer.type is invalid", path)
    if record.get("origin_mode") not in {"mathlib_extension", "target_driven", "autonomous_discovery"}:
        report.reject("SCHEMA_INVALID", "origin_mode is invalid", path)
    for key in ("statement_origin", "proof_origin"):
        if record.get(key) not in {"machine", "human", "mixed", "unknown"}:
            report.reject("SCHEMA_INVALID", f"{key} is invalid", path)
    entrypoints = record.get("entrypoints")
    if not isinstance(entrypoints, list) or not entrypoints or len(entrypoints) > limits["max_public_entrypoints"]:
        report.reject("SCHEMA_INVALID", "entrypoints must be a nonempty bounded list", path)
    elif len(entrypoints) != len(set(entrypoints)) or any(not isinstance(item, str) or not ENTRYPOINT_RE.fullmatch(item) for item in entrypoints):
        report.reject(
            "SCHEMA_INVALID",
            "entrypoints must be unique names of the form LeanFrontier.<Namespace>.<declaration>",
            path,
        )
    elif any(len(item) > limits["max_identifier_length"] for item in entrypoints):
        report.reject(
            "SCHEMA_INVALID",
            f"an entrypoint name exceeds {limits['max_identifier_length']} characters",
            path,
        )
    if record.get("base_mathlib_revision") != mathlib_release["mathlib_revision"]:
        report.reject("SCHEMA_INVALID", "base_mathlib_revision must match the pinned revision", path)
    context = record.get("source_context")
    if context is not None and (not isinstance(context, str) or len(context) > 4096):
        report.reject("SCHEMA_INVALID", "source_context must be null or a short string", path)


def strip_comments(source: str) -> str:
    """Blank Lean comments, keeping offsets, before the source-policy scans.

    A module docstring that merely mentions `axiom` or `sorry` is prose, not a
    trust escape, and the kernel audit is what actually decides the axiom
    closure. Nested `/- -/` is Lean's rule; `--` runs to end of line.
    """
    result: list[str] = []
    depth = 0
    index = 0
    while index < len(source):
        character = source[index]
        if depth:
            if source.startswith("/-", index):
                depth += 1
                result.append("  ")
                index += 2
                continue
            if source.startswith("-/", index):
                depth -= 1
                result.append("  ")
                index += 2
                continue
            result.append("\n" if character == "\n" else " ")
            index += 1
            continue
        if source.startswith("/-", index):
            depth = 1
            result.append("  ")
            index += 2
            continue
        if source.startswith("--", index):
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            result.append(" " * (end - index))
            index = end
            continue
        result.append(character)
        index += 1
    return "".join(result)


def normalized_statement(text: str) -> str:
    """Literal skeleton of a statement, used by the family detector.

    Whitespace is removed before numerals are, so a numeral written against an
    identifier keeps its identity: `lucas 0 = 2` normalizes to `lucas0=#`, not
    `lucas#=#`. Base cases of a recursion therefore do not collapse into one
    family with each other, while `n + 1 = 1 + n` and `n + 2 = 2 + n` still do.
    That is the behaviour we want and it is easy to break by reordering these
    two substitutions, so `test_base_cases_are_not_a_family` pins it.
    """
    text = re.sub(r"--.*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"\s+", "", text)
    text = re.sub(r"\b(?:theorem|lemma)[A-Za-z_][A-Za-z0-9_']*", "", text)
    text = re.sub(r"\([A-Za-z_][A-Za-z0-9_']*:[^)]+\)", "(_)", text)
    text = re.sub(r"\b\d+\b", "#", text)
    return text


def proposition_shape(statement: str) -> str:
    """Cheap deterministic canonicalization for the intentionally limited v1 fragment."""
    compact = normalized_statement(statement)
    # Bound variables are semantically irrelevant to the v1 family detector.
    compact = re.sub(r"\b[A-Z][A-Za-z0-9_']*\b", "P", compact)
    for connective in ("∧", "∨"):
        if connective in compact:
            pieces = [piece.strip("()") for piece in compact.split(connective)]
            compact = connective.join(sorted(pieces))
    return compact.replace("True", "⊤").replace("False", "⊥")


def declared_statements(path: Path) -> list[tuple[str, str]]:
    """Every stated proposition in a module, theorem or conjecture.

    A conjecture's body is rendered as `: <proposition>` so it has the same
    shape as a theorem's, which lets one probe, one skeleton normalizer and one
    family counter serve both. A sweep of near-identical conjectures is a
    degenerate family for the same reason a sweep of theorems is.
    """
    try:
        source = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    # Prose that happens to contain `theorem` is not a declaration.
    code = strip_comments(source)
    found = [(match.group(1), match.group("body")) for match in DECL_RE.finditer(code)]
    found += [(match.group(1), ": " + match.group("body").strip())
              for match in CONJECTURE_RE.finditer(code)]
    return found


def declared_conjectures(path: Path) -> set[str]:
    try:
        source = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return set()
    return {match.group(1) for match in CONJECTURE_RE.finditer(strip_comments(source))}


def entrypoint_kinds(candidate: Path, modules: list[str], entrypoints: list[str]) -> dict[str, str]:
    """Textual kind per entrypoint, for checks that run before the Lean audit."""
    conjectures: set[str] = set()
    for module in modules:
        path = candidate / (module.replace(".", "/") + ".lean")
        if path.exists():
            conjectures |= declared_conjectures(path)
    return {
        entrypoint: "conjecture" if entrypoint.rsplit(".", 1)[-1] in conjectures else "theorem"
        for entrypoint in entrypoints
    }


def static_preflight(base: Path | None, candidate: Path, limits: dict[str, Any], mathlib_release: dict[str, str], triviality: dict[str, Any], report: Report) -> tuple[dict[str, Path | None], dict[str, Any] | None]:
    changed, before = changed_paths(base, candidate)
    corpus = corpus_skeletons(base)
    report.observations["changed_files"] = sorted(changed)
    if len(changed) > limits["max_changed_files"]:
        report.reject("RESOURCE_LIMIT_EXCEEDED", "too many changed files")
    changed_bytes = 0
    lean_bytes = 0
    added_lines = 0
    declarations = 0
    metadata: dict[str, Any] | None = None
    submission_paths: list[tuple[str, str]] = []
    seen_shapes: dict[str, str] = {}
    skeleton_counts: dict[str, int] = {}
    for relative, path in changed.items():
        if not is_allowed_path(relative):
            report.reject("PATH_POLICY_VIOLATION", "ordinary submissions may only change LeanFrontier/ and one submission record", relative)
        if path is None:
            report.reject("PATH_POLICY_VIOLATION", "ordinary submissions may not delete files", relative)
            continue
        if path.is_symlink():
            report.reject("SECURITY_POLICY_VIOLATION", "symlinks are not permitted", relative)
            continue
        size = path.stat().st_size
        changed_bytes += size
        if size > limits["max_individual_file_bytes"]:
            report.reject("RESOURCE_LIMIT_EXCEEDED", "individual file exceeds policy limit", relative)
        if relative.endswith(".lean"):
            lean_bytes += size
            added_lines += line_count(path)
            try:
                source = path.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                report.reject("SECURITY_POLICY_VIOLATION", "Lean source must be UTF-8 text", relative)
                continue
            code = strip_comments(source)
            if SORRY_RE.search(code):
                report.reject("SORRY_DETECTED", "sorry or sorryAx is prohibited", relative)
            if AXIOM_RE.search(code):
                report.reject("UNAUTHORIZED_AXIOM", "axiom declarations are prohibited", relative)
            if FORBIDDEN_SECURITY.search(code):
                report.reject("SECURITY_POLICY_VIOLATION", "metaprogramming or command execution is prohibited in submissions", relative)
            declarations += len(DECLARATION_RE.findall(code))
            for _, statement in declared_statements(path):
                shape = proposition_shape(statement)
                skeleton_counts[normalized_statement(statement)] = skeleton_counts.get(normalized_statement(statement), 0) + 1
                if shape in seen_shapes:
                    report.reject("DUPLICATE_STATEMENT", f"same normalized statement as {seen_shapes[shape]}", relative)
                else:
                    seen_shapes[shape] = relative
                if re.search(r"\bTrue\b|\bFalse\b", statement) or re.search(r"\b([A-Za-z_][A-Za-z0-9_']*)\s*→\s*\1\b", statement):
                    report.reject("TRIVIAL_BASELINE_RESULT", "statement has an obvious tautological collapse", relative)
        match = SUBMISSION_RE.fullmatch(relative)
        if match:
            submission_paths.append((relative, match.group(1)))
            if relative in before:
                report.reject("PATH_POLICY_VIOLATION", "submission claim must be newly added", relative)
            try:
                parsed = load_json(path)
            except (OSError, json.JSONDecodeError) as error:
                report.reject("SCHEMA_INVALID", f"invalid JSON: {error}", relative)
            else:
                validate_metadata(parsed, match.group(1), limits, mathlib_release, report, relative)
                metadata = parsed if isinstance(parsed, dict) else None
    if len(submission_paths) != 1:
        report.reject("SCHEMA_INVALID", "exactly one newly added Submissions/<id>.json record is required")
    if changed_bytes > limits["max_total_changed_bytes"] or lean_bytes > limits["max_lean_source_bytes"] or added_lines > limits["max_added_lines"]:
        report.reject("RESOURCE_LIMIT_EXCEEDED", "submission exceeds aggregate byte or line limits")
    if declarations > limits["max_declarations"]:
        report.reject("RESOURCE_LIMIT_EXCEEDED", "submission exceeds the declaration limit")
    threshold = triviality["family_threshold"]
    for skeleton, count in skeleton_counts.items():
        accepted = corpus.get(skeleton, 0)
        if count + accepted >= threshold:
            already = f", {accepted} of them already accepted" if accepted else ""
            report.reject(
                "DEGENERATE_THEOREM_FAMILY",
                f"{count + accepted} declarations share one literal-normalized skeleton{already}",
            )
    report.observations.update({"changed_bytes": changed_bytes, "lean_source_bytes": lean_bytes, "added_lines": added_lines, "new_declarations": declarations})
    return changed, metadata


def corpus_skeletons(base: Path | None) -> dict[str, int]:
    """Literal-normalized statement skeletons already in the accepted corpus.

    The family detector counted only within one submission, so a producer could
    land two members of a permuted family now and the rest later: the counter
    reset each time and the threshold never fired. Exact-digest duplicate
    detection does not cover the gap either, since family members differ by
    construction. Counting candidates against the corpus closes it.
    """
    result: dict[str, int] = {}
    if base is None:
        return result
    for path in sorted((base / "LeanFrontier").rglob("*.lean")):
        for _, statement in declared_statements(path):
            skeleton = normalized_statement(statement)
            result[skeleton] = result.get(skeleton, 0) + 1
    return result


def accepted_entrypoints(base: Path | None) -> set[str]:
    """Entrypoints every already-merged submission record declares.

    An ordinary submission may modify source below `LeanFrontier/`, including a
    module that somebody else's accepted submission owns. Nothing else in the
    receiver notices when that removes a result the corpus already promised.
    """
    result: set[str] = set()
    if base is None:
        return result
    for path in sorted((base / "Submissions").glob("*.json")):
        try:
            record = load_json(path)
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(record, dict):
            result.update(item for item in record.get("entrypoints", []) if isinstance(item, str))
    return result


def corpus_regressions(accepted: set[str], findings: dict[str, Any]) -> list[str]:
    """Accepted entrypoints the candidate no longer exposes."""
    return sorted(accepted - set(findings))


def regression_message(regressions: list[str], shown: int = 5) -> str:
    """Name a few, but always state the total.

    A submitter who fixes only the names printed would otherwise resubmit and
    fail again on the ones elided.
    """
    head = regressions[:shown]
    remainder = len(regressions) - len(head)
    elided = f", and {remainder} more" if remainder else ""
    return f"{len(regressions)} accepted entrypoints are no longer present: {head}{elided}"


def submitted_modules(paths: Iterable[str]) -> list[str]:
    """Only the subject modules this submission adds or changes."""
    return sorted(
        path[:-5].replace("/", ".")
        for path in paths
        if path.startswith("LeanFrontier/") and path.endswith(".lean")
    )


def modules_for(candidate: Path, paths: Iterable[str]) -> list[str]:
    """Every subject module in the tree, not only the ones this submission touched.

    The duplicate and corpus-regression comparisons need the accepted corpus in
    the audit environment. Reading it from the umbrella looked equivalent and is
    not: the umbrella is post-merge generated output that arrives in its own
    later pull request, so a submission validated between a merge and that sync
    sees a corpus missing whatever landed most recently, and is rejected for
    removing declarations it never touched. Walking the tree has no such window.
    """
    modules = {
        path.relative_to(candidate).with_suffix("").as_posix().replace("/", ".")
        for path in sorted((candidate / "LeanFrontier").rglob("*.lean"))
    }
    modules.update(
        path[:-5].replace("/", ".")
        for path in paths
        if path.startswith("LeanFrontier/") and path.endswith(".lean")
    )
    return sorted(modules) or ["LeanFrontier"]


def declared_public_facts(candidate: Path, paths: Iterable[str]) -> dict[str, dict[str, bool]]:
    """Best-effort source ownership map for audit facts, limited to changed files.

    The receiver has already rejected generated syntax and submission changes are
    bounded.  Keeping this small parser here means an imported older module can
    never be counted as part of a new submission's award interface.
    """
    facts: dict[str, dict[str, bool]] = {}
    for relative in paths:
        if not relative.startswith("LeanFrontier/") or not relative.endswith(".lean"):
            continue
        namespace: list[str] = []
        for line in (candidate / relative).read_text(encoding="utf-8").splitlines():
            if match := NAMESPACE_RE.match(line):
                namespace.append(match.group(1))
                continue
            if END_RE.match(line):
                if namespace:
                    namespace.pop()
                continue
            if match := PUBLIC_DECLARATION_RE.match(line):
                prefix = ".".join(namespace)
                name = f"{prefix}.{match.group(1)}" if prefix else match.group(1)
                facts[name] = {
                    "generated": name.rsplit(".", 1)[-1].startswith("_"),
                    "alias": bool(DIRECT_ALIAS_RE.match(line)),
                    "restatement": False,
                }
    return facts


def run(command: list[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=timeout, check=False)


def parse_audit(output: str) -> dict[str, Any]:
    findings: dict[str, Any] = {}
    for line in output.splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict) and isinstance(item.get("name"), str):
            findings[item["name"]] = item
    return findings


def canonical_digest(item: dict[str, Any]) -> str | None:
    canonical = item.get("type_canonical")
    if not isinstance(canonical, str):
        return None
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def public_finding(item: dict[str, Any] | None) -> dict[str, Any] | None:
    if item is None:
        return None
    dependencies = item.get("type_dependencies", [])
    return {
        "name": item.get("name"),
        "kind": item.get("kind"),
        "axioms": item.get("axioms", []),
        "statement_sha256": canonical_digest(item),
        "type_dependencies": sorted(item for item in dependencies if isinstance(item, str)),
    }


def mathlib_duplicates(hints: set[str], mathlib_release: dict[str, str], report: Report) -> set[str] | None:
    """Look up exact Mathlib theorem fingerprints in the trusted pinned index.

    The index is generated by ``tools/build_mathlib_index.py`` from the same
    Lean-native canonical forms as candidate findings. Keeping this expensive
    whole-Mathlib traversal out of the PR path makes the v1 validation timeout
    enforceable without treating an inconclusive comparison as acceptance.
    """
    try:
        index = load_json(ROOT / "policy" / mathlib_release["fingerprint_index"])
        if index.get("format_version") != 1 or index.get("mathlib_revision") != mathlib_release["mathlib_revision"]:
            raise ValueError("Mathlib fingerprint index does not match the pinned revision")
        entries = index.get("fingerprints_by_type_hint")
        if not isinstance(entries, dict):
            raise ValueError("Mathlib fingerprint index has invalid entries")
        matches: set[str] = set()
        for hint in hints:
            values = entries.get(hint, [])
            if not isinstance(values, list) or any(not isinstance(value, str) for value in values):
                raise ValueError(f"Mathlib fingerprint index has invalid entry for hint {hint}")
            matches.update(values)
        report.observations["mathlib_exact_matches"] = len(matches)
        return matches
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        report.reject("BUILD_FAILED", f"Mathlib duplicate comparison failed: {error}")
        return None


def entrypoint_bodies(candidate: Path, modules: list[str], entrypoints: list[str]) -> dict[str, str]:
    wanted = {entrypoint.rsplit(".", 1)[-1]: entrypoint for entrypoint in entrypoints}
    found: dict[str, str] = {}
    for module in modules:
        path = candidate / (module.replace(".", "/") + ".lean")
        if path.exists():
            for name, body in declared_statements(path):
                if name in wanted:
                    found[wanted[name]] = body
    return found


def producer_signature(claim: dict[str, Any]) -> str:
    """Stable identity for quota accounting.

    The agent names the harness that produced the submission, which is the unit
    a quota should bind; the model is the fallback when no agent is recorded.
    """
    producer = claim.get("producer") or {}
    for key in ("agent", "model"):
        value = producer.get(key)
        if isinstance(value, str) and value.strip():
            return f"{key}:{value.strip()}"
    return "unrecorded"


def corpus_conjecture_state(base: Path | None) -> tuple[dict[str, int], dict[str, int]]:
    """Per producer: accepted theorems, and conjectures still unresolved.

    Resolution is read from the source rather than from an audit of the base
    tree: the contract requires a proving submission to add
    `theorem name : ConjectureName := ...`, so the shape is textual by
    construction.
    """
    theorems: dict[str, int] = {}
    unresolved: dict[str, int] = {}
    if base is None:
        return theorems, unresolved

    resolved: set[str] = set()
    for path in sorted((base / "LeanFrontier").rglob("*.lean")):
        try:
            code = strip_comments(path.read_text(encoding="utf-8"))
        except UnicodeDecodeError:
            continue
        for match in RESOLUTION_RE.finditer(code):
            resolved.add(match.group(1).rsplit(".", 1)[-1])

    conjecture_names: set[str] = set()
    for path in sorted((base / "LeanFrontier").rglob("*.lean")):
        conjecture_names |= declared_conjectures(path)

    for path in sorted((base / "Submissions").glob("*.json")):
        try:
            claim = load_json(path)
        except (OSError, ValueError):
            continue
        who = producer_signature(claim)
        for entrypoint in claim.get("entrypoints", []) or []:
            if not isinstance(entrypoint, str):
                continue
            short = entrypoint.rsplit(".", 1)[-1]
            if short in conjecture_names:
                if short not in resolved:
                    unresolved[who] = unresolved.get(who, 0) + 1
            else:
                theorems[who] = theorems.get(who, 0) + 1
    return theorems, unresolved


def submitted_conjectures(candidate: Path, modules: list[str]) -> dict[str, str]:
    """Every conjecture the submission adds, keyed by name, with its body.

    Deliberately not limited to declared entrypoints. A conjecture that is not
    an entrypoint still lands in the corpus and is still importable, so binding
    the quota and the probes to the claim would make both opt-in: a producer
    could add any number of unprobed conjectures simply by not naming them.
    """
    found: dict[str, str] = {}
    for module in modules:
        path = candidate / (module.replace(".", "/") + ".lean")
        if not path.exists():
            continue
        conjectures = declared_conjectures(path)
        for name, body in declared_statements(path):
            if name in conjectures:
                found[name] = body
    return found


def conjecture_quota(base: Path | None, candidate: Path, modules: list[str], entrypoints: list[str], claim: dict[str, Any], policy: dict[str, Any], report: Report) -> None:
    proposed = len(submitted_conjectures(candidate, modules))
    if not proposed:
        return
    theorems, unresolved = corpus_conjecture_state(base)
    who = producer_signature(claim)
    allowance = theorems.get(who, 0) * policy["unresolved_per_accepted_theorem"]
    held = unresolved.get(who, 0)
    report.observations["conjecture_quota"] = {
        "producer": who, "accepted_theorems": theorems.get(who, 0),
        "unresolved": held, "allowance": allowance, "proposed": proposed,
    }
    if held + proposed > allowance:
        report.reject(
            "CONJECTURE_QUOTA_EXCEEDED",
            f"{who} holds {held} unresolved conjectures and proposes {proposed}, "
            f"against an allowance of {allowance} from {theorems.get(who, 0)} accepted theorems")


def probe_goal(candidate: Path, probe_file: Path, goal: str, triviality: dict[str, Any]) -> str | None:
    """First bounded tactic that closes `goal` from the baseline, if any."""
    for tactic in triviality["baseline_probes"]:
        probe_file.write_text(
            "import Mathlib\nimport LeanFrontier\n\n" f"example {goal} := by\n  {tactic}\n",
            encoding="utf-8")
        try:
            result = run(["lake", "env", "lean", str(probe_file)], candidate, triviality["probe_timeout_seconds"])
        except (OSError, subprocess.TimeoutExpired):
            continue
        if result.returncode == 0:
            return tactic
    return None


def baseline_probes(candidate: Path, modules: list[str], submitted: list[str], entrypoints: list[str], triviality: dict[str, Any], report: Report) -> None:
    """Try bounded tactics without importing a changed candidate module.

    A reference to a newly introduced definition makes the probe inconclusive,
    never a rejection.

    A theorem is probed in one direction: proving it from the baseline alone
    means it was already known. A conjecture is probed in both. Proving it
    means it is not a conjecture but a theorem the producer did not attempt,
    and refuting it means the corpus would be carrying a target that cannot be
    hit. Both directions reuse the same bounded tactic list.
    """
    probe_file = SCRATCH / "baseline_probe.lean"
    probe_file.parent.mkdir(parents=True, exist_ok=True)
    kinds = entrypoint_kinds(candidate, modules, entrypoints)
    goals = dict(entrypoint_bodies(candidate, modules, entrypoints))
    # Undeclared conjectures are probed on the same terms as declared ones,
    # but only in the modules this submission touched: the corpus's existing
    # conjectures were probed when they landed and are not re-probed here.
    for name, body in submitted_conjectures(candidate, submitted).items():
        goals.setdefault(name, body)
        kinds.setdefault(name, "conjecture")
    outcomes: dict[str, str] = {}
    for entrypoint, body in goals.items():
        conjecture = kinds.get(entrypoint) == "conjecture"
        proved = probe_goal(candidate, probe_file, body, triviality)
        if proved:
            outcomes[entrypoint] = proved
            if conjecture:
                report.reject("CONJECTURE_PROVABLE", f"baseline-only probe '{proved}' proved conjecture {entrypoint}; it is a theorem, not a conjecture")
            else:
                report.reject("TRIVIAL_BASELINE_RESULT", f"baseline-only probe '{proved}' proved {entrypoint}")
            continue
        if conjecture:
            # `body` is `: P`, so the negation goal is `: ¬(P)`.
            refuted = probe_goal(candidate, probe_file, f": ¬({body.lstrip()[1:].strip()})", triviality)
            if refuted:
                outcomes[entrypoint] = f"refuted by {refuted}"
                report.reject("CONJECTURE_REFUTED", f"baseline-only probe '{refuted}' proved the negation of {entrypoint}")
                continue
        outcomes.setdefault(entrypoint, "inconclusive")
    report.observations["baseline_triviality_probes"] = outcomes


def downstream_smoke(candidate: Path, modules: list[str], entrypoints: list[str], report: Report) -> None:
    """Check that a clean consumer module can import and name the public API."""
    client = SCRATCH / "downstream" / "Client.lean"
    client.parent.mkdir(parents=True, exist_ok=True)
    imports = "\n".join(f"import {module}" for module in sorted(set(modules)))
    checks = "\n".join(f"#check {entrypoint}" for entrypoint in entrypoints)
    client.write_text(f"{imports}\n\n{checks}\n", encoding="utf-8")
    try:
        result = run(["lake", "env", "lean", str(client)], candidate, 30)
    except (OSError, subprocess.TimeoutExpired) as error:
        report.reject("BUILD_FAILED", f"downstream import smoke test did not complete: {error}")
        return
    if result.returncode:
        report.reject("BUILD_FAILED", result.stderr.strip()[-2000:] or "downstream import smoke test failed")
        return
    report.observations["downstream_import_smoke"] = "pass"


def kernel_recheck(candidate: Path, modules: list[str], limits: dict[str, Any], report: Report) -> None:
    """Replay the submitted modules through the kernel with `leanchecker`.

    `lake build` and the axiom audit both trust the elaborated environment that
    the build produced. `leanchecker` re-checks those declarations against the
    kernel from their compiled form, so a proof accepted through an elaborator
    bug does not reach the corpus on the elaborator's word alone. Imported
    modules are trusted here: each was rechecked when it was admitted.
    """
    for module in modules:
        try:
            result = run(["lake", "env", "leanchecker", module], candidate, limits["kernel_recheck_timeout_seconds"])
        except (OSError, subprocess.TimeoutExpired) as error:
            report.reject("KERNEL_RECHECK_FAILED", f"leanchecker did not complete for {module}: {error}")
            return
        if result.returncode:
            detail = (result.stderr.strip() or result.stdout.strip())[-2000:]
            report.reject("KERNEL_RECHECK_FAILED", detail or f"leanchecker rejected {module}")
            return
    report.observations["kernel_recheck"] = "pass"


def lean_audit(base: Path | None, candidate: Path, modules: list[str], submitted: list[str], declared_facts: dict[str, dict[str, bool]], metadata: dict[str, Any], limits: dict[str, Any], axioms: dict[str, Any], mathlib_release: dict[str, str], accepted: set[str], report: Report) -> None:
    try:
        build = run(["lake", "build"], candidate, limits["build_timeout_seconds"])
    except (OSError, subprocess.TimeoutExpired) as error:
        report.reject("BUILD_FAILED", f"Lake build did not complete: {error}")
        return
    if build.returncode:
        report.reject("BUILD_FAILED", build.stderr.strip()[-2000:] or build.stdout.strip()[-2000:])
        return
    kernel_recheck(candidate, submitted, limits, report)
    if not report.accepted:
        return
    try:
        audit = run(["lake", "exe", "frontier-audit", "--", *modules], candidate, limits["validation_timeout_seconds"] - limits["build_timeout_seconds"])
    except (OSError, subprocess.TimeoutExpired) as error:
        report.reject("BUILD_FAILED", f"Lean audit did not complete: {error}")
        return
    if audit.returncode:
        report.reject("BUILD_FAILED", audit.stderr.strip()[-2000:] or audit.stdout.strip()[-2000:])
        return
    findings = parse_audit(audit.stdout)
    # The umbrella is imported, so every accepted declaration should be visible
    # here. Any that is not, this submission removed, renamed, or overwrote.
    regressions = corpus_regressions(accepted, findings)
    if regressions:
        report.reject("CORPUS_REGRESSION", regression_message(regressions))
    report.observations["corpus_entrypoints_checked"] = len(accepted)
    entrypoints = metadata.get("entrypoints", [])
    # Findings now span the accepted corpus as well, so the Mathlib comparison
    # is kept to declarations this submission actually introduces.
    submitted = set(declared_facts) | set(entrypoints)
    candidate_hints = {
        item.get("type_hint")
        for name, item in findings.items()
        if name in submitted and isinstance(item.get("type_hint"), str)
    }
    baseline_fingerprints = mathlib_duplicates(candidate_hints, mathlib_release, report)
    for entrypoint in entrypoints:
        finding = findings.get(entrypoint)
        if finding is None:
            report.reject("BUILD_FAILED", f"declared entrypoint was not found by the Lean audit: {entrypoint}")
            continue
        if finding.get("kind") not in {"theorem", "conjecture"}:
            report.reject("SCHEMA_INVALID", f"entrypoint is neither a theorem nor a conjecture: {entrypoint}")
        term_bytes = finding.get("normalized_term_bytes")
        if not isinstance(term_bytes, int) or term_bytes > limits["max_normalized_term_bytes"]:
            report.reject("RESOURCE_LIMIT_EXCEEDED", f"{entrypoint} exceeds the normalized-term limit")
        used_axioms = set(finding.get("axioms", []))
        # `always_reject` is not merely the complement of `allowed_axioms`: an
        # axiom named there stays prohibited even if someone later permits it.
        prohibited = (used_axioms - set(axioms["allowed_axioms"])) | (
            used_axioms & set(axioms["always_reject"]))
        if prohibited:
            report.reject("UNAUTHORIZED_AXIOM", f"{entrypoint} depends on prohibited axioms: {sorted(prohibited)}")
        fingerprint = canonical_digest(finding)
        same_corpus = [name for name, item in findings.items() if name != entrypoint and canonical_digest(item) == fingerprint]
        if same_corpus:
            report.reject("DUPLICATE_STATEMENT", f"{entrypoint} duplicates LeanFrontier declaration {sorted(same_corpus)[0]}")
        if baseline_fingerprints is not None and fingerprint in baseline_fingerprints:
            report.reject("DUPLICATE_STATEMENT", f"{entrypoint} has an exact elaborated statement already in Mathlib")
    if report.accepted:
        baseline_probes(candidate, modules, submitted, entrypoints, load_json(DEFAULT_TRIVIALITY), report)
    if report.accepted:
        downstream_smoke(candidate, modules, entrypoints, report)
    report.observations["build"] = "pass"
    report.observations["entrypoints"] = {name: public_finding(findings.get(name)) for name in entrypoints}
    audited_declarations: dict[str, dict[str, Any] | None] = {}
    for name, facts in sorted(declared_facts.items()):
        finding = public_finding(findings.get(name))
        if finding is not None:
            finding.update(facts)
        audited_declarations[name] = finding
    report.observations["audited_declarations"] = audited_declarations


def export_git_ref(ref: str, destination: Path) -> None:
    process = subprocess.run(["git", "archive", ref], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if process.returncode:
        raise RuntimeError(process.stderr.decode().strip())
    unpack = subprocess.run(["tar", "-x", "-C", str(destination)], input=process.stdout, check=False)
    if unpack.returncode:
        raise RuntimeError("unable to materialize base Git reference")


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--base-dir", type=Path, help="trusted baseline tree")
    source.add_argument("--base-ref", help="Git ref used as the trusted baseline")
    parser.add_argument("--candidate-dir", type=Path, default=Path.cwd(), help="candidate tree (default: current directory)")
    parser.add_argument("--json-out", type=Path, help="write the structured receiver report here")
    parser.add_argument("--preflight-only", action="store_true", help="do not run Lake or Lean")
    parser.add_argument("--bootstrap", action="store_true", help="validate the initial seed without a baseline tree")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    candidate = args.candidate_dir.resolve()
    report = Report()
    if not candidate.is_dir():
        report.reject("PATH_POLICY_VIOLATION", "candidate directory does not exist")
    limits = load_json(DEFAULT_LIMITS)
    axioms = load_json(DEFAULT_AXIOMS)
    triviality = load_json(DEFAULT_TRIVIALITY)
    try:
        mathlib_release = load_release_policy(DEFAULT_MATHLIB_RELEASE)
    except ReleasePolicyError as error:
        report.reject("BUILD_FAILED", str(error))
        mathlib_release = None
    base: Path | None = args.base_dir.resolve() if args.base_dir else None
    temporary: tempfile.TemporaryDirectory[str] | None = None
    try:
        if args.base_ref:
            temporary = tempfile.TemporaryDirectory(prefix="leanfrontier-base-")
            base = Path(temporary.name)
            try:
                export_git_ref(args.base_ref, base)
            except RuntimeError as error:
                report.reject("PATH_POLICY_VIOLATION", f"cannot export base ref {args.base_ref}: {error}")
        if base is None and not args.bootstrap:
            report.reject("PATH_POLICY_VIOLATION", "provide --base-dir or --base-ref (or use --bootstrap only for the initial seed)")
        changed, metadata = static_preflight(base, candidate, limits, mathlib_release or {"mathlib_revision": ""}, triviality, report)
        if report.accepted and metadata is not None:
            # Textual, so it runs with the other cheap checks rather than after
            # a Mathlib build the submission was never going to survive.
            conjecture_quota(
                base, candidate, submitted_modules(changed),
                [e for e in metadata.get("entrypoints", []) if isinstance(e, str)],
                metadata, load_json(DEFAULT_CONJECTURE), report)
        if report.accepted and not args.preflight_only:
            if metadata is None:
                report.reject("SCHEMA_INVALID", "no valid metadata record was available for audit")
            else:
                lean_audit(base, candidate, modules_for(candidate, changed), submitted_modules(changed), declared_public_facts(candidate, changed), metadata, limits, axioms, mathlib_release or {}, accepted_entrypoints(base), report)
    finally:
        if temporary:
            temporary.cleanup()
    payload = report.json()
    print(json.dumps(payload, indent=2, sort_keys=True))
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0 if report.accepted else 1
