# Notes for agents changing this repository

This file is for **coding agents and contributors** who edit LeanFrontier itself
(receiver, policies, workflows, generated corpus tooling, or documentation).
For a **mathematical submission** task, use
[`prompts/TRY-LEANFRONTIER.md`](prompts/TRY-LEANFRONTIER.md) (and
[`prompts/SUBMITTER.md`](prompts/SUBMITTER.md)) instead. Humans may also use
[CONTRIBUTING.md](CONTRIBUTING.md).

## Project overview

LeanFrontier is a Lean 4 library of machine-checked mathematics on Mathlib, with
a mechanical **receiver** that decides whether a pull request is admissible.
Trusted paths (`.github/`, `tools/`, `policy/`, `schema/`, Lake config, and
related automation) are maintainer work on `maintenance/<topic>` branches. See
[CONTRACT.md](CONTRACT.md), [README.md](README.md), and
[docs/threat-model.md](docs/threat-model.md).

## Setup

Install the pinned Lean toolchain (via `elan`), Lake, and Python 3 for the fast
test suite:

```bash
lake update
lake exe cache get   # strongly recommended before lake build
lake build
python3 -m pip install --disable-pip-version-check -r requirements-dev.txt
```

Ordinary theorem submissions do not require building the whole corpus locally;
maintainer and receiver changes often do.

## Before each commit

Run the Python suite and coverage (**50% branch-aware floor** on selected
`tools/` modules — see [`.coveragerc`](.coveragerc)):

```bash
python3 -m coverage run -m unittest discover -s tests -v
python3 -m coverage report
```

**Always try to increase test coverage** when you add or change behaviour. Do
not lower the coverage floor to make CI green — add tests instead.

Run **`lake build`** (or the narrower build your change needs) before pushing
when you touch Lean sources or receiver build paths.

**Never commit** API keys, tokens, app private keys, personal access tokens,
or machine-specific paths, hostnames, or usernames. Keep docs and comments
**general**.

Before opening a maintenance pull request, re-read
[AGENT.md](AGENT.md) (this file), [SECURITY.md](SECURITY.md), and the relevant
workflow under [`.github/workflows/`](.github/workflows/).

## Mathematical submissions

Do not use this file as the submission guide. Follow
[`prompts/TRY-LEANFRONTIER.md`](prompts/TRY-LEANFRONTIER.md), validate with:

```bash
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

and open a pull request only when the report shows `"accepted": true`.

## Conduct and templates

Follow [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md). For security reports, follow
[SECURITY.md](SECURITY.md) — do not open a public issue. Use the GitHub issue
and pull request templates for other work.