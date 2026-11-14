# Handoff for the next agent

Use this after the public-repo normalization work on branch
`cursor/normalize-public-repo-standard-7be1` (or its merge result).

## Verification checklist

Run each command from the repository root. Expected outcomes are stated so you
can diff without trusting the prior agent's prose.

| Claim | Command | Expected output (substrings) |
|-------|---------|------------------------------|
| Community files present | `python3 -m unittest tests.test_community -v` | `OK` on all tests |
| Full Python CI suite | `python3 -m pip install -q -r requirements-dev.txt && python3 -m coverage run -m unittest discover -s tests -v && python3 -m coverage report` | All tests `OK`; total coverage **≥ 50%**; exit code `0` |
| Advisory URL in policy | `grep -F 'github.com/carlok/LeanFrontier/security/advisories/new' SECURITY.md .github/ISSUE_TEMPLATE/config.yml` | Both files print a matching line |
| Blank issues disabled | `grep 'blank_issues_enabled: false' .github/ISSUE_TEMPLATE/config.yml` | One matching line |
| CoC enforcement email | `grep -F 'carlo.perassi@gmail.com' CODE_OF_CONDUCT.md` | One matching line |
| Lean toolchain (optional) | `command -v lake && lake --version` | `lake` path and version text |
| Lean build (optional, slow without cache) | `lake exe cache get && lake build` | Ends with successful build summary; may take tens of minutes first time |

Private vulnerability reporting enablement is **not** verifiable from the repo.
Owner manual step (see PR body): `gh api -X PUT repos/carlok/LeanFrontier/private-vulnerability-reporting`.

## Prioritized TODOs

### P0 — Confirm GitHub private reporting (owner)

**Acceptance:** Repository **Settings → Security → Private vulnerability
reporting** shows enabled, and the advisory URL opens a report form without 404.

### P1 — Post-merge hygiene

**Acceptance:** `main` contains `SECURITY.md`, `AGENT.md`, `.github/dependabot.yml`,
`.github/PULL_REQUEST_TEMPLATE.md`, updated `config.yml`, and `tests/test_community.py`;
`python3 -m unittest discover -s tests` passes on `main`.

### P2 — Dependabot noise

**Acceptance:** First weekly Dependabot PRs only touch `github-actions` pins or
`requirements-dev.txt`; no Lake/Mathlib ecosystem entries (unsupported).

### P3 — Site copy

**Acceptance:** If `docs/website/` pages duplicate contact guidance, they match
`SUPPORT.md` / `SECURITY.md` (no “email the maintainer” for security).

## Starter prompt

```text
You are working on carlok/LeanFrontier after public-repo normalization.

1. Read AGENT.md, CONTRIBUTING.md, SECURITY.md, and docs/TODO-handoff.md.
2. Run the verification table in TODO-handoff.md; paste raw command output for any failure.
3. If P0 private reporting is still disabled, document the exact gh api or UI step for @carlok only — do not merge on that alone.
4. Keep Apache-2.0; no secrets; coverage floor 50% must not drop.
5. Open a maintenance PR on maintenance/<topic> if you change receiver/workflows; otherwise follow ordinary submission rules.
```