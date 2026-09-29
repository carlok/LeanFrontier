# The LeanFrontier dataset

One JSON record per accepted submission, in order of acceptance, gzipped:
`leanfrontier-corpus-<version>.jsonl.gz`. It joins what the submitter claimed,
what the receiver observed, and where the submission sits in the corpus, so the
corpus can be analysed without cloning the repository and walking its history.

It is generated from the repository by `tools/export_dataset.py`, which needs a
full clone (it refuses a shallow one):

```
python3 tools/export_dataset.py --output leanfrontier-corpus.jsonl.gz
```

The output is deterministic: records in order of acceptance, keys sorted, gzip
without a timestamp. The same commit always yields the same bytes, so a
released file can be checked by regenerating it at the tagged commit.

## Record, version 1

| Field | Meaning |
|---|---|
| `record_version` | `1`. Bumped when a field changes meaning or is removed. |
| `submission_id` | The claim's identifier, also its file name under `Submissions/`. |
| `accepted.commit` | The commit on the default branch at which the claim first appeared: the merge that accepted it. |
| `accepted.date` | That commit's author date, `YYYY-MM-DD`. |
| `claim` | The claim exactly as submitted: producer, origin mode, statement and proof origin, entrypoints, Mathlib base revision, `source_context`. Schema: `schema/submission.schema.json`. |
| `modules` | Corpus modules the accepting merge added, compared with that merge's first parent. |
| `extended` | Existing modules the merge changed. Non-empty only before 22 September 2026, when ordinary submissions became add-only. |
| `imports` | For each added module, the corpus modules it imports. Mathlib imports are omitted. |
| `observation` | The receiver's record of the accepted run, or `null` (one submission, `bootstrap-binomial`, predates observations). |
| `observation.accepted_revision` | The merge commit the observation was recorded for. |
| `observation.validated_candidate_revision` | The exact pull-request head the receiver validated. |
| `observation.trusted_receiver_revision` | The receiver code that ran. |
| `observation.validation_run` | The GitHub Actions run, for the full log. |
| `observation.observed_at`, `.duration_seconds`, `.protocol_version` | When, how long, which protocol. |
| `observation.observed.entrypoints` | Per public theorem: `kind`, `axioms` (the full axiom closure), `statement_sha256` (digest of the normalized statement), `type_dependencies` (constants its statement mentions). |
| `observation.observed.*` | The rest of the receiver's measurements: build and kernel re-check outcome, baseline triviality probes and their runs, exact Mathlib matches, corpus entrypoints re-checked, new declarations, lines and bytes changed. |

`claim.entrypoints` is what the submitter declared; `observation.observed.entrypoints`
is what the receiver verified. They are equal for every record; the gate on generated
output (`tools/validate_generated.py`) refuses an observation whose
entrypoints differ from the claim's.

## What it is not

- **Not the source.** Statements appear as digests and dependency lists. The
  Lean source is in the repository at `accepted.commit`.
- **Not rejections.** Only accepted submissions have records. Rejected runs are
  summarised separately, by diagnostic code, without source or submitter.
- **Not a judgement of interest.** The receiver checks validity, novelty against
  Mathlib and the corpus, and triviality by bounded tactics; nothing here says a
  result is important.

## Releases and citation

A release is a git tag `corpus-<version>` with the generated file attached as a
release asset. Cite the tag. The data inherits the repository's licence
(Apache-2.0).
