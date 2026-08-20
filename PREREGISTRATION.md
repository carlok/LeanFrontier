# Pre-registration: does the launcher suppress accumulation?

Registered 20 August 2026, before any submission was assigned to an arm.

## Why this document exists

The claim under test is the manifesto's: that machine-generated mathematics,
admitted without human taste, accumulates into reusable internal theory. That
is a claim about the import graph. Fixing the threshold after seeing the data
would make any outcome arguable, so the threshold is fixed here, first.

## What is already known

Measured 20 August 2026 (see `carlok/lean-corpus-density`):

- LeanFrontier at 24 modules has 4 internal import edges, 0.17 per module.
- Tau Ceti at 24 modules had 22, 0.92 per module, and its density rises
  monotonically to 1.55 by 2314 modules. Machine-generated mathematics does
  accumulate there.
- Tau Ceti is directed by human-written roadmaps. A roadmap specifies a
  dependency graph in advance, so it does not settle whether accumulation
  happens without one.
- LeanFrontier's own launcher tells producers to "prefer an uncovered area",
  which points away from the corpus. The observed sparsity may therefore be an
  artifact of the instruction rather than a property of machine mathematics.

That last point is what this experiment separates.

## Hypothesis

Producers instructed to extend the existing corpus will form import edges at a
higher rate than producers given the current launcher.

## Design

Two arms, differing in exactly one paragraph of the task launcher:

- **A (control)** — `prompts/TRY-LEANFRONTIER.md`, unchanged.
- **B (extension)** — `prompts/TRY-LEANFRONTIER-EXTEND.md`, which directs the
  producer to read the catalogue, pick an accepted submission, and prove
  something depending on it.

Every other instruction, and the receiver itself, is identical across arms. A
test asserts the two files differ only in the designated block.

Assignment is made by the maintainer when a producer is invited, alternating
between arms, and recorded in `experiments/launcher-ab.csv` at the time of
assignment rather than at merge. Submissions not assigned to an arm — walk-ins
who found the repository themselves — are recorded as unassigned and excluded.

## Metric

Internal import edges whose **source** is a module belonging to that arm's
submissions: what the producer did, not what was later done to them. Counted
per module. Edges into modules from either arm count equally; the corpus is
shared.

Secondary, reported but not used for the decision: edges per declaration,
maximum in-degree, and whether any module reaches depth 3.

## Decision rule

Stop at **18 accepted submissions per arm**. At that size, with arm A held at
its observed 0.17 edges per module and α = 0.05 one-sided:

| arm B reaches | vs control | power at 18/arm |
|---|---|---|
| 0.92 (Tau Ceti's rate) | 5.5× | 0.93 |
| 0.70 | 4.2× | 0.82 |
| 0.50 | 3.0× | 0.39 |
| 0.40 | 2.4× | 0.16 |

- **Arm B significantly above arm A** (conditional binomial, one-sided,
  α = 0.05): the sparsity was an instruction artifact. The launcher is fixed
  and the manifesto's claim survives this test.
- **No significant difference**: an effect of 4× or larger is ruled out at 82%
  power. This is *not* a finding of no effect. Effects below 3× need 34+ per
  arm and 2.4× needs 65+, which this project cannot reach at its current rate.
  That outcome will be reported as "no effect larger than ~4x", never as "no
  accumulation".

Either way the numbers are published, including a null.

## What would falsify the hypothesis

Arm B producing edges at or below arm A's rate. That would mean producers
directly instructed to build on machine-generated results still do not, which
is evidence against the manifesto's claim and not merely absence of evidence.

## Known limitations, recorded in advance

- Both launcher files are public, so an arm B producer can read arm A and vice
  versa. Assignment cannot be enforced, only recorded.
- Arm B measures compliance as much as capability: a producer told to import
  something will import something. This is why the secondary metrics —
  depth 3, in-degree above 1, cross-producer reuse — matter for interpreting a
  positive result. A one-import-and-stop pattern is compliance, not
  accumulation.
- Assignment alternates rather than being randomised, and the maintainer knows
  the arm when inviting. Recruitment is not blind.
- 18 per arm is 36 submissions against a corpus that took 23 to date.

---

## Amendment, 20 August 2026

Recorded before any submission carried an arm: `experiments/launcher-ab.csv`
held no assignments when this was written. Amending a pre-registration before
data exists is ordinary; amending it after the first arm-B submission is what
would void it.

**Producer.** A loop client running headless agents replaces the many-human
recruitment above. It alternates arms, rotates model families, and holds at
most one open pull request at a time.

The trade, stated plainly. Heterogeneous humans piloting different agents carry
noise that a single controlled process does not, so this is a cleaner
comparison and a faster path to the stopping point. It is also narrower: the
result describes what those model families do under two prompts, not what
machine producers do in general. Rotating families recovers part of that, not
all of it.

**Assignment.** Moves from invitation time to generation time, and is recorded
in the submission claim's `launcher_arm` field rather than a hand-kept ledger.
A producer cannot write to a side ledger — section 2 of the contract permits a
submission to change only Lean source and its own claim — so the assignment now
travels atomically with the submission it describes.

**Secondary metrics.** Cross-producer reuse is dropped: it is undefined with
one producer. Depth of at least 3 and in-degree above 1 are retained, and carry
more weight than before, because they remain the only way to separate "imported
one thing because instructed to" from "built a stack".

**Conjectures.** Permitted in both arms. Restricting them to arm B would
confound the treatment with a second change. Edges arising from conjecture
imports are reported as a separate series, so a positive result can be checked
for whether it is ordinary accumulation or producers chasing a target that was
handed to them.

**Unchanged.** The hypothesis, the primary metric, the stopping point of 18
accepted submissions per arm, the power table, and the commitment to report a
null as "no effect larger than ~4x" rather than "no accumulation".

**Added limitation.** A single producer means the experiment can no longer
distinguish a prompt effect from an interaction between the prompt and one
generator's habits. If arm B succeeds, the honest claim is that this
instruction changes what these models do, and replication with a different
producer becomes the obvious follow-up rather than an optional extra.
