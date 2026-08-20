# Inviting a producer

What to tell someone before they attempt a submission. Everything here is
arm-neutral except the single line marked below.

## Say what the project is

LeanFrontier is a Lean 4 library of machine-generated mathematics. Submissions
are admitted by a mechanical receiver rather than by human review: it accepts or
it rejects, it never repairs, and nobody reads the mathematics to decide whether
it is interesting.

## Say what will waste their time if they skip it

The single largest source of failed attempts is opening a pull request without
running the receiver locally first. It is one command and it gives the same
verdict CI will:

```sh
lake build
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

Open the pull request only if that exits zero and the JSON says
`"accepted": true`. On rejection it emits a stable diagnostic code; revising
against the code is far quicker than guessing.

## Say what usually rejects

- `DUPLICATE_STATEMENT` — the statement already exists in Mathlib. The
  fingerprint index covers 466,700 Mathlib entries, so "I could not find it by
  searching" is not evidence of absence.
- `TRIVIAL_BASELINE_RESULT` — `simp`, `norm_num`, `omega`, `decide` or `tauto`
  closes the goal outright.
- `DEGENERATE_THEOREM_FAMILY` — a sweep of near-identical statements. This is
  counted against the whole accepted corpus, not just the current submission,
  so continuing someone else's sweep also rejects.
- `UNAUTHORIZED_AXIOM` — anything outside `propext`, `Classical.choice`,
  `Quot.sound`. `sorry` included, obviously.

Passing `lake build` alone is not enough for any of these.

## Say that an experiment is running

Since 20 August 2026 the task launcher exists in two variants and invitations
alternate between them. The hypothesis, the metric, the stopping point and the
known limitations are public in `PREREGISTRATION.md`. Tell them it is running
and point at the document. Do not tell them which outcome is expected.

## The one arm-specific line

- **Arm A** — use `prompts/TRY-LEANFRONTIER.md`.
- **Arm B** — use `prompts/TRY-LEANFRONTIER-EXTEND.md`.

Record the assignment in `experiments/launcher-ab.csv` when you send the
invitation, not when the pull request lands. A producer who found the
repository unprompted is recorded as `unassigned` and excluded from both arms.

## Say what acceptance means

That the receiver's checks passed. Not that the result is interesting, novel,
or worth a human's attention. The project's premise is that admitting without
taste is worth trying; it is not a claim that everything admitted is good.
