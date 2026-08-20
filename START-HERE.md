# Start here

For a person who wants to make a submission. The agent-facing instructions are
in [`prompts/TRY-LEANFRONTIER.md`](prompts/TRY-LEANFRONTIER.md); this page is
about what *you* do.

The short version: set the repository up once, hand your agent one prompt, wait
about a quarter of an hour, check the receiver accepted it, open the pull
request.

## 1. Set up, once

```bash
git clone https://github.com/carlok/LeanFrontier.git
cd LeanFrontier
lake exe cache get
lake build
```

Do this before you involve an agent. `lake exe cache get` downloads a prebuilt
Mathlib, which is several gigabytes, and `lake build` then compiles the corpus
on top of it. It takes a while the first time and almost no time afterwards. An
agent that starts before this finishes will spend its run waiting on a compiler
instead of doing mathematics.

You need [elan](https://github.com/leanprover/elan). The toolchain version is
pinned in `lean-toolchain` and elan will pick it up; do not install Lean
separately.

## 2. Give your agent the task

Open your agent in the repository directory and give it this URL as the prompt:

```text
https://raw.githubusercontent.com/carlok/LeanFrontier/main/prompts/TRY-LEANFRONTIER.md
```

That file points it at the contract, the submitter guide, the catalogue and the
validation command. You do not need to explain the project to it, and you
should not tell it what to prove — choosing the subject is part of what the
project is measuring.

If you have been assigned to the extension arm of the running experiment, use
[`prompts/TRY-LEANFRONTIER-EXTEND.md`](prompts/TRY-LEANFRONTIER-EXTEND.md)
instead. Whoever invited you will say which.

## 3. Wait

Fifteen to twenty minutes is normal. The agent reads the catalogue, picks a
subject, writes a module, and iterates against the compiler. Most of the time
it looks like nothing is happening because it is waiting on `lake build`.

## 4. Check the receiver accepted it

The agent is instructed to run this itself. Run it again yourself; it is cheap
and it is the whole gate.

```bash
lake build
./tools/validate-submission --base-ref origin/main --json-out .frontier/report.json
```

Open a pull request **only** if that exits zero and the JSON says
`"accepted": true`. Anything else is a rejection, and CI will reach the same
verdict a few minutes later without your having to wait for it.

## 5. Open the pull request

One submission per pull request: Lean sources under `LeanFrontier/` and exactly
one `Submissions/<id>.json`. No documentation, workflow, policy or formatting
edits alongside it — those paths are refused.

Your pull request will wait for a maintainer rather than merging itself. That
is deliberate for a new contributor and says nothing about the work.

## If it is rejected

Read the stable code in the report and fix against the code. Four account for
most failures:

| Code | What it means |
|---|---|
| `DUPLICATE_STATEMENT` | The statement is already in Mathlib. The index holds 466,700 entries, so "I searched and did not find it" is not evidence of absence. |
| `TRIVIAL_BASELINE_RESULT` | `simp`, `norm_num`, `omega`, `decide` or `tauto` closes it outright. |
| `DEGENERATE_THEOREM_FAMILY` | A sweep of near-identical statements. Counted across the whole corpus, so continuing someone else's sweep also rejects. |
| `UNAUTHORIZED_AXIOM` | Anything beyond `propext`, `Classical.choice`, `Quot.sound`. `sorry` included. |

Passing `lake build` is not enough for any of these. The receiver never repairs
a submission; it rejects and tells you why.

## Things that surprise people

**Nobody reads the mathematics.** Acceptance means the checks passed. It is not
a judgement that the result is interesting, and the receiver is deliberately
incapable of making one.

**You can state a conjecture.** A definition whose type is `Prop` asserts
nothing, needs no `sorry`, and passes the kernel unchanged:

```lean
def collatz_bounded : Prop := ∀ n : ℕ, 0 < n → ∃ k, iterate n k = 1
```

It becomes a target another producer can aim at. Two catches: you may hold only
one unresolved conjecture per theorem you have landed, so land a theorem first;
and *any* parameterless `def foo : Prop := ...` counts as a conjecture whether
you meant it that way or not. Give it arguments if you meant an abbreviation.

**There is a running experiment**, on the wording of the task launcher. The
hypothesis, the metric and the stopping point are public in
[`PREREGISTRATION.md`](PREREGISTRATION.md). You will be told which arm you are
in; you will not be told which way it is expected to go.

**Some of this is new.** Auto-merge, conjectures and the arm field all landed on
20 August 2026, and the first end-to-end submission completed the same day. If
something behaves strangely it is likelier a bug here than a mistake of yours.
Say so and it will be looked at.
