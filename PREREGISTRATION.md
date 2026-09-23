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

## Deviation, 22 September 2026

Recorded after data exists: three accepted submissions carry an arm (A: 2,
B: 1), all landed on or before 20 August. This is not an amendment to the
design. It records receiver changes made for security and maintenance reasons
between then and now, so that the analysis can account for them. The
hypothesis, the primary metric, the stopping point and the decision rule are
unchanged.

The receiver is still identical across arms, as the design requires. Five
changes landed:

- **#193**: a rejected build now reports the Lean errors in the submitter's own
  files instead of only `error: build failed`. This changes the feedback a
  producer iterates on, not what is admitted.
- **#201**: a timed-out probe no longer leaves `lean` running, and each probe's
  outcome and time are recorded. This changes resources and observations, not
  admission.
- **#216**: ordinary submissions may only **add** files, and code that runs at
  build or import time is rejected.
- **#239**: deprecation warnings in the submission's own files are rejected as
  `DEPRECATED_API`.
- **#241**: a conjecture the claim does not list as an entrypoint is now probed
  in both directions, as the contract always required. It was silently skipped
  before. None of the three arm-tagged submissions is a conjecture.

**The add-only rule interacts with the primary metric.** Before #216, a
submission could extend an accepted module by editing it, which creates no
import edge. Now it must add a module that imports the one it extends, which
creates an edge by construction. The metric can therefore rise for reasons that
have nothing to do with the launcher, and plausibly more in arm B, whose
paragraph asks for exactly that kind of extension. Of the corpus's accepted
submissions before the change, one (#169, unassigned) extended a module by
editing it.

To keep this separable, the analysis will:

- report the primary metric separately for arm-tagged submissions accepted
  before and after 22 September 2026;
- count, for each arm, the edges whose target is a module the same submission
  could previously have edited instead: an accepted module extended rather than
  merely used.

If the two periods disagree, the pre-change submissions are the cleaner test of
the hypothesis. The post-change result will be reported as conditional on the
add-only rule.

The deprecation rule can reject submissions that would have been accepted
before. It applies identically to both arms and counts toward neither arm's
stopping point until a corrected resubmission is accepted.

## Suspension and replacement, 23 September 2026

**The A/B test is suspended.** It has three arm-tagged accepted submissions of
the thirty-six it requires: two in arm A (`padovan-sequence-sum`,
`thue-morse-prouhet-power-sums`) and one in arm B
(`stern-brocot-coprime-enumeration`). All three were accepted on 20 August 2026,
the day the amendment above was written. No submission has carried a
`launcher_arm` in the 34 days since, because the loop client that assigned arms
has not run since then.

Meanwhile the corpus grew from 23 accepted submissions to 58. The 55 untagged
submissions were produced outside the experiment, mostly by a single external
producer who was never assigned an arm. Any comparison between two and one
tagged submissions, inside a corpus fifty-five sixths of which is untagged,
would be arithmetic rather than evidence. **No arm comparison will be reported.**

The design above is left intact rather than deleted. The arms, the metric, the
decision rule and the power table stand as registered, and the test may be
revived if two independent producers are ever running at once. Reviving it
requires a new dated section here, stating the date from which submissions count;
nothing accepted before that date may be counted toward an arm.

### What replaces it, registered now

An **observational accumulation series** over the whole corpus, with no arms, no
treatment and no control. It cannot support a causal claim about the launcher,
and no causal claim will be made from it.

**Measured, per accepted submission, in order of acceptance:** internal import
edges; modules; edges per module; the share of modules importing at least one
other corpus module; maximum in-degree; maximum depth of the import graph; and
the share of submissions importing a module accepted within the preceding seven
days.

**Reported** as a dated series in `experiments/accumulation.csv`, generated by
trusted post-merge code from the corpus itself, so it can be recomputed from any
commit by anyone.

**The reference points** are the ones already recorded above: LeanFrontier at 24
modules had 4 internal edges, 0.17 per module; the comparison corpus had 0.92 per
module at the same size and 1.55 at 2314 modules. At 58 modules LeanFrontier has
36 internal edges, 0.62 per module.

**Three things this series cannot do, stated before it is read:**

1. It cannot separate the producer from the protocol. One external producer
   accounts for most recent submissions, so the series describes what that
   producer did as much as what the corpus affords.
2. From 22 September 2026 the add-only rule forces an import edge for any
   submission that extends an accepted module, since editing that module is no
   longer permitted. Edges after that date are therefore partly an artefact of
   the rule. The series is reported split at that date, and the pre-rule period
   is the cleaner one.
3. A rising ratio is consistent with accumulation and also with a producer
   working through one connected subject area. Maximum depth and in-degree are
   reported for exactly this reason: a deep graph is harder to produce by
   staying in one neighbourhood than a wide one.

**Committed in advance:** the series is published whatever it shows, including a
flat or falling ratio, and including the case where it rises only after
22 September and so is attributable to the rule rather than to the producers.
