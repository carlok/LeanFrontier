# Adopting the receiver

How to put LeanFrontier's admission protocol in front of another Lean
repository. Read [`threat-model.md`](threat-model.md) first: it says what the
receiver guarantees and what it does not, and this guide assumes you want the
first and accept the second.

The receiver is not a package. It is a set of files you copy and adapt, in
layers. The first layer is the whole protocol; the rest are conveniences that
LeanFrontier grew because of the volume it receives.

## Layer 1: the receiver

This is what decides whether a pull request is admitted.

| Copy | What it is |
|---|---|
| `tools/frontier_validate.py`, `tools/validate-submission` | The validator and its entry point. Preflight (paths, claim, source policy, limits) and formal checks (build, kernel re-check, axioms, duplicates, triviality probes, corpus regression). |
| `tools/FrontierAudit.lean` and the `frontier-audit` `[[lean_exe]]` in `lakefile.toml` | The Lean side: declaration kinds, axiom closures, normalized statements and their digests. |
| `tools/Dockerfile.validator` | The image candidate code runs in. |
| `policy/axioms.json`, `limits.json`, `triviality.json`, `conjecture.json` | What the receiver enforces. `limits.json` also sets the container's memory and disk, through the workflow. |
| `policy/mathlib-release.json` and its `mathlib-fingerprints-*.json` | The pinned Mathlib and the index of its statements that duplicates are checked against. Build yours with `tools/build_mathlib_index.py` (workflow `build-mathlib-index.yml`). |
| `schema/submission.schema.json` | The claim a submission carries. |
| `.github/workflows/validate-submission.yml` | Runs trusted base code against the candidate in the restricted container. |
| `CONTRACT.md` | The rules, for submitters. Adapt the wording; keep the diagnostic codes, which the tests tie to the code. |

**Change:** the library root (`LeanFrontier` appears in paths, the umbrella
module and the source policy), the pinned Mathlib and its index, the limits,
and the axiom allowlist if yours differs.

**Repository settings the protocol depends on:** a ruleset on the default
branch requiring the `validate` check with strict up-to-date branches, and no
bypass actors. Without "up to date", a branch is validated against a base that
is not the one it merges into.

## Layer 2: a durable record

`record-observation.yml`, `tools/persist_observation.py` and
`tools/validate_generated.py`. After each accepted merge, trusted code on the
default branch writes the receiver's report into `receiver-observations/` and
opens a pull request for it. The gate on generated output checks such pull
requests without running candidate code. This is what makes the corpus
auditable after the workflow artifacts expire.

It needs a **GitHub App** (variable `APP_CLIENT_ID`, secret `APP_PRIVATE_KEY`):
pull requests opened with `GITHUB_TOKEN` do not trigger workflows, so their
checks never run. The client ID is not secret; `actions/create-github-app-token`
v3 deprecates its `app-id` input in favour of `client-id`.

## Layer 3: conveniences

Take these only if you need them.

- **Auto-merge** (`auto-merge.yml`, `policy/auto_merge_allowlist.json`): merges
  after the receiver accepts the exact head, for listed authors only.
- **Generated views**: `generate_umbrella.py`, `generate_catalogue.py` (needs
  Graphviz), `generate_accumulation_series.py`, `collect_rejections.py`,
  `export_dataset.py`.
- **Mathlib upgrades** (`mathlib-upgrade.yml` with `update_mathlib_release.py`,
  `audit_mathlib_upgrade.py`, `validate_mathlib_upgrade.py`): a scheduled job
  that re-audits the whole corpus against a new release and opens a PR.
- **A merge queue** (`maintainer-merge-queue.yml`): with strict up-to-date
  checks every merge makes the other pull requests stale; the queue updates,
  re-validates and merges them one at a time, and never overrides a check.

## What running it taught us

Each of these cost a day or more. None is about proofs.

1. **A checker must print its verdict.** A report written inside a container
   and never copied out turns a clear rejection into "exit code 1".
2. **Size limits by measurement, and again as the corpus grows.** After a
   Mathlib upgrade every module rebuilds and is re-checked. Limits chosen when
   the corpus had 33 modules were guesses at 95; one of them (memory) turned out
   to be the one that failed.
3. **`leanchecker <Module>` checks every module whose name starts with
   `<Module>`, in parallel.** A module that is also a folder's name is checked
   with all its children, and memory scales with them. Give the container room,
   or check each module exactly once.
4. **A silent failure is usually a kill.** Report the exit status; SIGKILL in a
   memory-limited container means memory.
5. **`gh pr checks` exits 1 when a check has failed.** Under `pipefail`,
   `gh pr checks | grep -q fail` therefore never matches. Capture the output,
   then search it.
6. **App installation tokens last an hour** and cannot be renewed inside a
   step. Long waits must stop and say what is left.
7. **An App without `workflows` permission cannot push workflow files.** Keep
   it that way; it only means a maintainer updates fork branches by hand after
   a workflow change lands.
8. **Diagnostics are read literally, by agents.** "Exceeds the normalized-term
   limit" sent one producer to shrink a proof five times; the limit measured the
   statement. Say which thing is measured, how big it is, and what to change.
9. **Anything countable will be aimed at.** Publish a measure that cannot be
   gamed cheaply beside the one that can: statements that mention earlier work,
   not only imports of it.
