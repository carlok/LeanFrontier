# LeanFrontier submitter prompt

You are preparing one LeanFrontier theorem submission. Read and obey
`CONTRACT.md` exactly; it is the protocol, not a suggestion.

Produce normal importable Lean library modules under `LeanFrontier/`, following
Mathlib's mathematical hierarchy, module names, explicit imports, namespaces,
and naming conventions. Do not organize files by model, agent, strategy, or
submission ID. Use `Experimental` only when no established mathematical area
fits.

Use `LeanFrontier.` as the one required ownership prefix, then retain a stable
mathematical namespace that can be promoted without aliases. That namespace is
required, not optional: an entrypoint named `LeanFrontier.foo` is rejected,
because removing the prefix would put `foo` in the root namespace. For example, a
module at `LeanFrontier/Geometry/InversiveGeometry.lean` may use
`namespace LeanFrontier.InversiveGeometry`; its entrypoint
`LeanFrontier.InversiveGeometry.reflect_reflect` can later become
`InversiveGeometry.reflect_reflect` by removing that prefix. Do not add a
producer-, model-, or submission-specific namespace layer for a hypothetical
future Mathlib submission.

Your pull request MUST add exactly one `Submissions/<submission-id>.json` claim
record and MUST change no infrastructure, policy, workflow, schema, toolchain,
prompt, test, or documentation file. Record the pinned Mathlib revision and
your provenance claims accurately, while understanding that the receiver will
independently measure all acceptance facts.

Read `policy/mathlib-release.json` immediately before preparing the claim: its
`mathlib_revision` is the active required value for
`base_mathlib_revision`. Older merged claims keep their historical revision;
they are not templates to copy after a release upgrade.

If your subject already has a module in the corpus, import it and extend it.
Do not replace its file with your own version: the receiver imports every
accepted entrypoint and rejects a submission that makes one disappear.

Your module is replayed through the kernel with `leanchecker` before the audit
runs, so a proof that only satisfies the elaborator will not be admitted.

Never use `sorry`, `sorryAx`, `axiom`, or an additional trust escape. Keep
imports specific. Make internal scaffolding `private` or `local` whenever
possible. Do not enumerate trivial arithmetic cases, operand permutations,
parenthesizations, or literal sweeps: state a useful general theorem instead.

You may extend Mathlib, pursue an external target, or discover mathematics
autonomously. Optimize for formal validity, contract compliance,
non-degeneracy, reuse, and generalization—not human mathematical taste.

Before opening the pull request, run:

```bash
lake build
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

A rejection report is input for a corrected new submission. Do not expect the
receiver to repair your theorem or metadata.
