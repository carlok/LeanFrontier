# LeanFrontier submission contract

**Protocol version:** `0.1`

This document is normative. The words **MUST**, **MUST NOT**, **SHOULD**, and
**MAY** are to be interpreted as requirements on a theorem-producing agent and
the receiver that admits its work.

## 1. Submission unit

An ordinary theorem submission is one pull request and exactly one newly added
file at `Submissions/<submission-id>.json`. Its `submission_id` MUST equal the
file stem and its record MUST validate against
`schema/submission.schema.json`.

The record is an untrusted, immutable claim. The receiver independently
produces a reproducible observation report; a claimed field is never replaced
with a receiver observation.

## 2. Permitted changes

An ordinary submission MAY add or modify mathematical source only below
`LeanFrontier/`, and MUST add its single submission record. It MUST NOT modify
`.github/`, `tools/`, `policy/`, `schema/`, `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain`, `CONTRACT.md`, `README.md`,
`MANIFEST.md`, prompts, tests, or any other trusted infrastructure.

The receiver rejects binary files, archives, symlinks, generated payloads,
hidden files outside the permitted source tree, and executable content that is
not ordinary Lean source.

## 3. Lean source and trust boundary

Source MUST follow Mathlib-compatible module and namespace conventions. Its
module path MUST be subject-based below `LeanFrontier/` and its public
namespace MUST begin with `LeanFrontier.`. The suffix after that ownership
prefix SHOULD be a stable, vendor-neutral mathematical namespace, so that an
eventual upstreaming needs only to remove `LeanFrontier.`: for example,
`LeanFrontier.InversiveGeometry.reflect_reflect` may become
`InversiveGeometry.reflect_reflect`. Submitters MUST NOT add aliases or
producer-, model-, or submission-specific namespace components merely to
support a possible future migration. Source MUST use explicit imports where
practical and MUST NOT organize mathematical modules by producer, model, or
submission identifier.

Every declared public entrypoint MUST elaborate and be accepted by Lean. A
submission MUST NOT contain `sorry`, `sorryAx`, an `axiom` declaration, or a
prohibited trust escape. Its transitive axiom closure MUST be a subset of the
allowlist in `policy/axioms.json`. The receiver, not the submitter, determines
that closure.

Helper declarations that are only proof scaffolding SHOULD be `private` or
`local`. They may support an accepted result, but do not create an unlimited
public theorem surface.

## 4. Provenance and entrypoints

The submission record MUST identify the producing system, one permitted origin
mode, independent statement and proof origins, the pinned Mathlib revision,
and one or more fully qualified LeanFrontier theorem entrypoints. The record
MAY retain source context, but it MUST NOT contain credentials, tokens, or
unbounded generated transcripts.

All provenance is claimed metadata. Build state, declarations, axiom closures,
dependencies, fingerprints, duplicate candidates, and probe results are
receiver observations.

## 5. Admission rules

The receiver performs cheap checks before Lean compilation and fails closed on
missing evidence. It enforces the versioned resource limits in
`policy/limits.json`.

Each public theorem is checked for exact normalized duplication against the
baseline and the same submission, canonical propositional degeneracy, and
bounded baseline-only triviality probes. The receiver also rejects repeated
literal, permutation, parenthesization, or finite-instance families that
should be one general result. It does not make subjective judgments about
importance, exposition, elegance, or human comprehensibility.

## 6. Receiver behavior

The receiver validates, measures, audits, classifies mechanically, and returns
structured diagnostics. It is not a co-author or theorem prover. A rejected
submission MUST be corrected and resubmitted by its producer; the receiver
MUST NOT silently repair its source or metadata.

Stable rejection categories include `SCHEMA_INVALID`,
`PATH_POLICY_VIOLATION`, `RESOURCE_LIMIT_EXCEEDED`, `BUILD_FAILED`,
`SORRY_DETECTED`, `UNAUTHORIZED_AXIOM`, `DUPLICATE_STATEMENT`,
`TRIVIAL_BASELINE_RESULT`, `DEGENERATE_THEOREM_FAMILY`, and
`SECURITY_POLICY_VIOLATION`.
