# Threat model

LeanFrontier admits mathematics by mechanical check rather than by human
review. This document says what that buys, what it does not, and what went
wrong in practice. It is written for someone deciding whether to trust the
corpus, or considering the same arrangement for their own project.

The short version: the kernel settles whether a theorem is true, and almost
every problem found so far was about something else.

## What the receiver guarantees

For every accepted submission, mechanically, with the evidence kept in
`receiver-observations/`:

- **The theorems are proved.** Every submitted module is replayed through the
  Lean kernel with `leanchecker`, so admission does not rest on the elaborator
  alone.
- **The axioms are the ordinary ones.** `propext`, `Classical.choice`,
  `Quot.sound`, and nothing else (`policy/axioms.json`); `sorry` and `sorryAx`
  are rejected outright, in the source and in the axiom closure.
- **Nothing accepted disappears.** Every entrypoint of every earlier submission
  is re-audited on every later one, so a submission cannot remove or rename a
  result the corpus already promised (`CORPUS_REGRESSION`).
- **It is not already known.** Each public statement is fingerprinted and
  compared against a pinned Mathlib index and the rest of the corpus.
- **It is not trivial.** Bounded tactics (`rfl`, `simp`, `norm_num`, `tauto`,
  `omega`, `decide`, ten seconds each) are run against the statement from the
  baseline alone. A conjecture is probed in both directions: provable or
  refutable, it is not a conjecture.
- **It builds clean.** Deprecated Mathlib lemmas in the submission's own files
  are rejected, because a deprecation is a warning now and an error after the
  next upgrade.
- **It is importable.** A fresh consumer module imports the corpus and names
  every declared entrypoint.

## What it does not guarantee

- **That the mathematics is interesting.** The project says so in its
  manifesto. Triviality checks are mechanical, not editorial.
- **That the prose is honest.** Docstrings, module comments and the claim's
  `source_context` are read by no check. A misleading name over a correct
  theorem passes everything above.
- **That the provenance is true.** A claim states its producer and model. The
  receiver records that; it cannot verify it.
- **That a statement says what a reader assumes.** `theorem euler_conjecture`
  can be about anything. The catalogue publishes statement digests so the
  formal content, not the name, is what is cited.

## Attacks and failure modes found in practice

Each of these was found here, in a live repository, not in a design review.

### Code that runs when a module is imported

A Lean `initialize` block runs ordinary code — file writes, process spawns —
whenever its module is imported. It is not metaprogramming, so the old ban on
`elab`/`macro`/`unsafe` did not touch it. A two-file experiment confirmed it:
the module passed every check, built cleanly, and wrote a file the moment
another file said `import`. Consumers of LeanFrontier build it from source and
import it, so this was code execution on their machines.

**Now rejected:** `initialize`, `builtin_initialize`, `run_cmd`, `run_elab`,
`run_meta`, `simproc`, `dsimproc`, `macro_rules`, `elab_rules`,
`declare_syntax_cat`, and the `extern`, `implemented_by` and `init` attributes.
(#216)

### Meaning drift under a stable name

A submission could edit an existing module, and the corpus check compared
accepted entrypoints **by name**. Redefining a definition that an accepted
theorem depends on would leave that theorem compiling, under its own name, while
changing what it says. A statement digest would not catch it either: the change
is in a definition's body, not in the statement.

**Now rejected:** ordinary submissions may only add files. Extending an accepted
module means importing it from a new one; editing one is maintenance work, done
by a maintainer in the open. (#216)

### Deprecation debt

Deprecated lemmas are warnings under the pinned Mathlib and errors after a later
one. Every admitted use is a future failure of the upgrade audit, at a moment
when nobody remembers the submission. Thirteen had accumulated, two of them in a
module merged an hour earlier.

**Now rejected** as `DEPRECATED_API` in the submission's own files, quoting the
replacement Lean names. The upgrade audit separately reports deprecations the
corpus acquires from a new release, without blocking the upgrade. (#239)

### A check that silently did not run

A conjecture that the claim did not list as an entrypoint was never probed, in
either direction, for its whole existence as a feature. An internal variable
holding the module list had been reused for declaration names, so the probe
looked for conjectures in "modules" named like declarations and found none. The
quota check still counted them, which is what made it invisible.

Nothing was admitted through it: the corpus held no conjectures until the first
one arrived, and that arrival is what exposed the gap, through probe timings
added for an unrelated reason. **Lesson:** a check that cannot fail loudly needs
telemetry, or it is indistinguishable from a check that is not there. (#241,
telemetry from #201)

### Resource exhaustion through orphaned processes

Each probe runs `lake`, which starts `lean`. A timeout killed only `lake`, and
the `lean` beneath it was re-parented and kept running. On a small host the
orphans accumulated until memory and swap ran out. Reported by a contributor
running the receiver on their own server.

**Now:** every command runs in its own process group, and the group is killed on
timeout. (#201)

### A rejection that blamed the submitter for the maintainer's merges

The receiver compares the candidate tree with the base tree. A branch opened
before other submissions merged is missing their files, so it was rejected for
"deleting" and "editing" them: one PR drew ten path violations, including
deleting another contributor's module, for commits it simply did not have.
Not an attack, but a report that sends a contributor chasing faults that are not
theirs, which costs trust in every other diagnostic.

**Now:** staleness is read from the commit graph and reported as one
`BRANCH_BEHIND` diagnostic. (#254)

## Trust boundaries

- **Validator code is never the candidate's.** The workflow checks out the
  trusted base revision and the candidate side by side; every check runs the
  base's code, with policy read from the base.
- **Candidate code runs only in a restricted container:** `--network none`,
  `--read-only`, `--cap-drop ALL`, `--security-opt no-new-privileges`,
  `--memory 2g`, `--cpus 2`, `--pids-limit 512`, with a size-limited `tmpfs`.
- **No workflow that holds secrets reads the candidate.** Nothing uses
  `pull_request_target`. The generators and the merge path run on `push` or
  `workflow_run`, executing code from the default branch.
- **A branch name grants nothing.** Exemptions require both a branch prefix and
  a trusted author; a submitter naming their branch `maintenance/` is validated
  as an ordinary submission.
- **Auto-merge is narrow.** It fires only after the receiver accepts the exact
  commit, only for authors in `policy/auto_merge_allowlist.json`, and never on a
  `maintenance/` branch. A moved head cancels it.
- **Documentation proposals carry no code.** A PR of Markdown under `docs/` is
  accepted without a build, and excludes `docs/catalogue/` (generated) and
  `docs/website/` (published under the project's name). A person still merges
  it. (#291)

## What remains unguarded

Stated plainly, because an unstated residual risk is the dangerous kind.

- **Prose.** Nothing reads docstrings or `source_context`. The maintainer's
  glance before merging is the only check, which is the main reason the external
  contributor is not on the auto-merge allowlist.
- **Maintenance changes.** A `maintenance/` pull request bypasses the receiver
  entirely, including edits to the corpus. The discipline is to prove
  equivalence by hand — a whole-corpus audit before and after, showing identical
  statements, kinds and axioms — and to say so in the pull request.
- **Upstream.** The pinned Mathlib, its download cache, the Lean toolchain and
  GitHub Actions are all trusted. A compromised dependency compromises the
  corpus. The upgrade path pins an exact release and rebuilds the duplicate
  index, which narrows this but does not close it.
- **One producer's taste.** Most recent work comes from a single external
  producer. Nothing mechanical detects a corpus drifting into one agent's
  interests.

## If you are adopting this

Copy `tools/frontier_validate.py`, `policy/*.json`,
`schema/submission.schema.json` and the three workflows, then change: the
repository and app identities, the allowlist, the pinned release, and the
limits. Read `CONTRACT.md` for the rules those files enforce.

The part worth taking is not the code. It is the position that admission can be
mechanical if, and only if, the mechanical checks cover what actually goes
wrong — and that the list of what goes wrong is only learned by running the
thing in the open and writing down each failure.
