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

## Questions and project maintenance

Use GitHub issues for questions, protocol proposals, and non-sensitive bug
reports. Changes to receiver infrastructure, policies, site presentation, and
generated corpus material are maintainer work rather than ordinary
submissions. Open a pull request from a branch named `maintenance/<topic>` for
such work.

For a conduct concern, do not publish sensitive details. Open a minimal issue
asking the maintainer for a private contact channel.
