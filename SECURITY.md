# Security policy

## Supported versions

Security fixes are considered for:

- the `main` branch of this repository; and
- the latest [release tag](https://github.com/carlok/LeanFrontier/tags) (currently
  `v0.3.0`).

Older tags and forks are best-effort only.

## Reporting

Report vulnerabilities **only** through GitHub's [private vulnerability
reporting](https://github.com/carlok/LeanFrontier/security/advisories/new): open
the repository **Security** tab and choose **Report a vulnerability** (or use
that link directly).

Please **do not** open a public GitHub issue, discussion, or pull request for a
security report. Please **do not** report security issues by email.

For how the project thinks about trust boundaries, see
[docs/threat-model.md](docs/threat-model.md).

## What counts as a vulnerability here

**Critical: the receiver accepts work it should reject**, or **merged corpus
content that does not match what the kernel checked** — for example a
submission without `sorry` that nonetheless depends on disallowed axioms, a
bypass of duplicate or triviality checks, or a regression that removes an
accepted theorem without a deliberate protocol change.

**High: trust or isolation failures in maintainer infrastructure** — for
example unexpected network access, write access, or privilege escalation in CI
validation containers; unsafe execution of untrusted submission code outside the
documented sandbox; or leakage of credentials from workflows.

**Also wanted: deterministic disagreements** between the local
`./tools/validate-submission` command and the GitHub Actions receiver on the
same commit, when reproduction steps and reports are included.

**Not a security report:** ordinary receiver rejections with documented codes;
slowness or resource use within published limits; mathematical incorrectness in
already-merged content that passed the stated checks (treat that as ordinary
research risk, not a defect in the reporting channel).

## What to expect

Maintainer: [@carlok](https://github.com/carlok). Reports are reviewed when
capacity allows. **There is no SLA**, no guaranteed response time, and no
commitment to public disclosure on a fixed schedule. The private advisory thread
is the only channel; do not follow up by email.

See also [CONTRIBUTING.md](CONTRIBUTING.md) and [README.md](README.md).