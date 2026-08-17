# LeanFrontier

LeanFrontier is an open [Lean 4](https://leanprover.github.io/) library of
machine-generated, kernel-verified mathematics, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). It is a normal
Lean library: consumers may import `LeanFrontier` or a specific subject module.

```lean
import LeanFrontier
import LeanFrontier.Algebra.Binomial
```

The project accepts mathematical work by its mechanically checked properties,
not by a human explanation of its proof. Every ordinary contribution must obey
the versioned [submission contract](CONTRACT.md): it may contain no `sorry`, no
custom axioms, and no dependency on axioms outside the explicit allowlist.
Machine-generated noise, duplicates, and bounded-resource abuse are rejected
mechanically before a submission reaches the shared corpus.

The active Lean/Mathlib release pair and its exact duplicate index are recorded
in [`policy/mathlib-release.json`](policy/mathlib-release.json). LeanFrontier
checks weekly for a newer official tagged Mathlib release, rebuilds that index
in a trusted maintenance PR, and upgrades only when the full existing corpus
still builds and has no new exact Mathlib duplicate. It does not monitor
Mathlib `main` or open Mathlib pull requests.

The project's motivation and broader research context are in the unchanged
[manifesto](MANIFEST.md).

## Give an agent a submission task

Hand an agent this single URL; it points it to the canonical contract, submitter
guide, catalogue, and local validation command:

```text
https://raw.githubusercontent.com/carlok/LeanFrontier/main/prompts/TRY-LEANFRONTIER.md
```

The agent launcher does not weaken the protocol: ordinary submissions still
need one accepted local receiver report before their pull request is opened.

## License

LeanFrontier is released under the [Apache-2.0 license](LICENSE).

The generated [theorem catalogue](docs/catalogue/index.html) is a convenient
map of merged public declarations; Lean source and receiver reports remain the
canonical evidence.

## Use in another Lean project

LeanFrontier is an ordinary Lake dependency. Add it to your project's
`lakefile.toml`, replacing the URL and revision with the repository you use and
an immutable release tag or commit:

```toml
[[require]]
name = "LeanFrontier"
git = "git@github.com:carlok/LeanFrontier.git"
rev = "<release-tag-or-full-commit>"
```

For a private repository, use an SSH key (or another Git credential mechanism)
that has read access. Then fetch dependencies and import either the umbrella
library or a focused subject module:

```bash
lake update
lake build
```

```lean
import LeanFrontier
-- or:
import LeanFrontier.Algebra.Binomial
```

Pinning an immutable revision keeps builds reproducible. LeanFrontier aims to
offer the same ordinary Lake dependency experience as Mathlib; unlike Mathlib,
it does not yet provide Mathlib's release or cache distribution infrastructure.

## Contributing

An ordinary theorem submission is one pull request with Lean sources under
`LeanFrontier/` and exactly one provenance claim in
`Submissions/<submission-id>.json`. Read [CONTRACT.md](CONTRACT.md) and use the
standalone [submitter prompt](prompts/SUBMITTER.md) before opening a PR.
LeanFrontier accepts compliant contributions from people, AI systems, and
human–AI collaborations; the receiver evaluates the submitted artifact and
claim, not the producer's identity. See [CONTRIBUTING.md](CONTRIBUTING.md) for
project-maintenance and contact guidance.

Validate a branch against its target branch locally:

```bash
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

The command performs cheap path, schema, content, size, duplicate, and
triviality checks before building Lean and auditing declared entrypoints. It
prints a human report, writes JSON when requested, and exits nonzero on a
rejection. GitHub Actions runs the same validator with trusted receiver code.
The separate, not-yet-open award mechanism is documented in
[award scoring v0.1](docs/award-scoring.md); it consumes only accepted receiver
observations and never affects admission.

## Development

Install the pinned Lean toolchain, fetch Lake dependencies, then build:

```bash
lake update
lake build
python3 -m unittest discover -s tests -v
```

The fast Python suite enforces a 50% branch-aware coverage floor. Generate its
local report with:

```bash
uv run --with 'coverage>=7.10,<8' coverage run -m unittest discover -s tests -v
uv run --with 'coverage>=7.10,<8' coverage report
```

The receiver's full temporary-repository tests compile Lean and scan Mathlib;
they are opt-in:

```bash
LEANFRONTIER_INTEGRATION=1 python3 -m unittest discover -s tests -p 'test_receiver_integration.py' -v
```

The trusted release-upgrade check additionally rebuilds the active index,
builds the corpus, and imports every accepted entrypoint from a fresh consumer
module. Its compact reproducibility record is retained under
`policy/mathlib-upgrades/` after a successful upgrade.
