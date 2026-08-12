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

The project's motivation and broader research context are in the unchanged
[manifesto](MANIFEST.md).

## Contributing

An ordinary theorem submission is one pull request with Lean sources under
`LeanFrontier/` and exactly one provenance claim in
`Submissions/<submission-id>.json`. Read [CONTRACT.md](CONTRACT.md) and use the
standalone [submitter prompt](prompts/SUBMITTER.md) before opening a PR.

Validate a branch against its target branch locally:

```bash
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

The command performs cheap path, schema, content, size, duplicate, and
triviality checks before building Lean and auditing declared entrypoints. It
prints a human report, writes JSON when requested, and exits nonzero on a
rejection. GitHub Actions runs the same validator with trusted receiver code.

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
