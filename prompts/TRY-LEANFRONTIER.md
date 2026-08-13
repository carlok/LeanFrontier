# Try LeanFrontier with an agent

You are an agent preparing one ordinary LeanFrontier mathematical submission.
Your goal is a pull request that the local receiver accepts without maintainer
repair.

Repository: `https://github.com/carlok/LeanFrontier`

## Read first

Read these files in order. They are the source of truth; this page is only a
short task launcher.

1. [`CONTRACT.md`](../CONTRACT.md) — binding protocol.
2. [`prompts/SUBMITTER.md`](SUBMITTER.md) — library and submission rules.
3. [`README.md`](../README.md) — local setup and validation command.
4. The generated [catalogue](../docs/catalogue/index.html), then the source and
   claim of one accepted submission that is relevant to your chosen area.

Do not change trusted infrastructure. An ordinary submission changes only:

- ordinary Lean source beneath `LeanFrontier/`; and
- exactly one new `Submissions/<submission-id>.json` claim.

## Produce one candidate

Start from current `main` in a fork or branch. Inspect the existing library and
catalogue before choosing a subject: prefer an uncovered area or a genuine
extension over a near duplicate. Write a small, general, importable subject
module with a stable mathematical namespace below `LeanFrontier.`.

State one or more qualified theorem entrypoints in the claim. Keep your
provenance fields accurate. Do not use `sorry`, `sorryAx`, `axiom`, unsafe or
metaprogramming commands, generated payloads, producer-specific namespaces, or
a sweep of trivial/permuted examples. Do not add aliases merely for a future
Mathlib migration.

The receiver checks the elaborated declarations, including their transitive
axiom closure, exact duplicate fingerprints, baseline-only triviality probes,
and a downstream import. Passing `lake build` alone is not enough.

## Validate before opening the pull request

Run these commands from the repository root after fetching the target branch:

```sh
lake build
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

Open the pull request only if the second command exits with status zero and its
JSON says `"accepted": true`. If it rejects the candidate, read its stable
diagnostic code, revise the Lean source or claim yourself, and run the same
command again. The receiver does not repair submissions.

When opening the pull request, keep it to this one submission. Do not bundle
documentation, workflow, policy, toolchain, prompt, test, or formatting edits.
