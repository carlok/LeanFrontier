# Contributing to LeanFrontier

LeanFrontier accepts compliant contributions regardless of whether their
producer is a person, an AI system, or a collaboration between them. The
receiver evaluates the submitted Lean source and immutable provenance claim;
it does not assign validity by producer identity.

## Mathematical submissions

Read [CONTRACT.md](CONTRACT.md) and
[the submitter guide](prompts/SUBMITTER.md) first. An ordinary submission is
one pull request containing only:

- Lean sources under `LeanFrontier/`; and
- exactly one new `Submissions/<submission-id>.json` claim.

Run the local receiver before opening the pull request:

    ./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json

The receiver reports acceptance or stable diagnostic codes; it does not repair
submissions. Correct a rejected submission in a new commit and run the same
command again.

For ideas on what to formalize next, see the non-normative
[contribution directions](docs/CONTRIBUTION-DIRECTIONS.md). The contract
remains authoritative.

### How many pull requests at once

There is no limit on open submission pull requests and no cadence rule, so
don't hold accepted work back in a queue. Only conjectures have a quota
(`policy/conjecture.json`). The practical constraints are mechanical:

- Keep each contribution on its own branch and in its own pull request,
  preferably in its own new module, so that independent work never conflicts.
- `main` requires branches to be up to date. Every merge, including the
  automated follow-ups, leaves other open pull requests behind; update the
  branch and let the checks run again.
- Each claim pins the active Mathlib revision from
  `policy/mathlib-release.json`. If the project upgrades before a claim
  merges, bump `base_mathlib_revision` and revalidate.

Substantive extensions that build on accepted results are especially
welcome.

## Proposing documentation

A pull request that changes only Markdown under `docs/` needs no claim and no
Lean source. The receiver accepts it as a documentation proposal and skips the
build entirely; a maintainer then reads it and merges it. `docs/catalogue/` is
generated and `docs/website/` is published, so neither can be changed this way.

## Questions and project maintenance

Use GitHub issues for questions, protocol proposals, and non-sensitive bug
reports. Changes to receiver infrastructure, policies, site presentation, and
generated corpus material are maintainer work rather than ordinary
submissions. Open a pull request from a branch named `maintenance/<topic>` for
such work.

For a conduct concern, do not publish sensitive details. Open a minimal issue
asking the maintainer for a private contact channel.
