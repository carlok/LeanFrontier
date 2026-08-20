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
prefix MUST be a stable, vendor-neutral mathematical namespace, so that an
eventual upstreaming needs only to remove `LeanFrontier.`: for example,
`LeanFrontier.InversiveGeometry.reflect_reflect` may become
`InversiveGeometry.reflect_reflect`. A declaration MUST NOT sit directly under the ownership
prefix: `LeanFrontier.tentMap` becomes a root-namespace name once the prefix is
removed, and reserves a generic identifier the rest of its subject area needs.
Submitters MUST NOT add aliases or
producer-, model-, or submission-specific namespace components merely to
support a possible future migration. Source MUST use explicit imports where
practical and MUST NOT organize mathematical modules by producer, model, or
submission identifier.

Every declared public entrypoint MUST elaborate and be accepted by Lean. The
receiver additionally replays each submitted module through the kernel with
`leanchecker`, so admission does not rest on the elaborator's word alone. A
submission MUST NOT contain `sorry`, `sorryAx`, an `axiom` declaration, or a
prohibited trust escape. Its transitive axiom closure MUST be a subset of the
allowlist in `policy/axioms.json`. The receiver, not the submitter, determines
that closure.

The receiver also compiles a fresh consumer module which imports the submitted
subject modules and names every declared entrypoint. This confirms that the
public surface is usable through ordinary module imports; it does not judge an
entrypoint's mathematical usefulness.

Helper declarations that are only proof scaffolding SHOULD be `private` or
`local`. They may support an accepted result, but do not create an unlimited
public theorem surface.

## 4. Provenance and entrypoints

The submission record MUST identify the producing system, one permitted origin
mode, independent statement and proof origins, the pinned Mathlib revision,
and one or more fully qualified LeanFrontier theorem entrypoints. The record
MAY retain source context, but it MUST NOT contain credentials, tokens, or
unbounded generated transcripts.

`statement_origin` and `proof_origin` describe who authored the formal text:
the Lean statements in the first case, the proof terms and tactic scripts in
the second. They do not describe who chose the subject. A human naming an area,
posing a vague direction, or picking from a shortlist the producer proposed is
not statement authorship, and such a submission is `machine`. Use `mixed` when a
human wrote or materially edited some of the formal statements themselves,
`human` when a human wrote them, and `unknown` when the producer cannot tell.
Subject selection belongs in `source_context`, where it can be described
honestly without straining a four-valued field.

One accepted record predates this definition and reads `mixed` where the same
process would now read `machine`. Records are immutable, so it stands.

All provenance is claimed metadata. Build state, declarations, axiom closures,
dependencies, fingerprints, duplicate candidates, and probe results are
receiver observations.

The required revision is the active one in `policy/mathlib-release.json` when
the receiver runs. A merged record is not rewritten by later releases: its
revision remains an immutable claim about the baseline on which it was made.

## 5. Admission rules

The receiver performs cheap checks before Lean compilation and fails closed on
missing evidence. It enforces the versioned resource limits in
`policy/limits.json`.

A submission MAY modify a module an earlier submission introduced, but it MUST
NOT remove, rename, or overwrite an entrypoint that an accepted submission
declares. The receiver imports the accepted corpus alongside the candidate and
rejects the difference as `CORPUS_REGRESSION`. Extending a module is ordinary;
replacing somebody else's accepted result is not.

Each public theorem is checked for exact normalized duplication against the
baseline and the same submission, canonical propositional degeneracy, and
bounded baseline-only triviality probes. The receiver also rejects repeated
literal, permutation, parenthesization, or finite-instance families that
should be one general result. Members already accepted count toward such a
family: a submission completing one begun by an earlier submission is rejected,
at the versioned `family_threshold` in `policy/triviality.json`. It does not
make subjective judgments about importance, exposition, elegance, or human
comprehensibility.

## 6. Receiver behavior

The receiver validates, measures, audits, classifies mechanically, and returns
structured diagnostics. It is not a co-author or theorem prover. A rejected
submission MUST be corrected and resubmitted by its producer; the receiver
MUST NOT silently repair its source or metadata.

Stable rejection categories include `SCHEMA_INVALID`,
`PATH_POLICY_VIOLATION`, `RESOURCE_LIMIT_EXCEEDED`, `BUILD_FAILED`,
`SORRY_DETECTED`, `UNAUTHORIZED_AXIOM`, `DUPLICATE_STATEMENT`,
`TRIVIAL_BASELINE_RESULT`, `DEGENERATE_THEOREM_FAMILY`, `CORPUS_REGRESSION`,
`KERNEL_RECHECK_FAILED`, and `SECURITY_POLICY_VIOLATION`.

A submission produced under the launcher A/B MAY declare `launcher_arm`. The
field records which task launcher the producer was given, not a property of the
mathematics, and it never affects admission. It travels inside the claim
because section 2 permits a submission to change only Lean source and its own
claim file: a producer cannot append to a side ledger in the same pull request,
and a separate one races it. `experiments/launcher-ab.csv` is generated output
derived from these fields.

The trusted maintenance receiver periodically evaluates newer official tagged
Mathlib releases. It does not inspect Mathlib `main` or open upstream pull
requests. It rebuilds the corpus, replays every module through the kernel, and imports
every accepted entrypoint from a fresh consumer module. An upgrade is rejected
with `MATHLIB_UPSTREAM_COLLISION` when a previously accepted LeanFrontier
entrypoint has an exact normalized statement in the prospective Mathlib index; no accepted theorem is silently altered or
removed to make the upgrade pass.
