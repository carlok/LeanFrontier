# Award scoring v0.1

The inaugural award, if opened, ranks eligible accepted submissions with the
network-free script [`tools/score_award.py`](../tools/score_award.py). It is a
mechanical measure of public interface structure, not a claim to measure
mathematical importance.

The trusted receiver supplies declaration names, kinds, statement digests, and
references found in elaborated declaration *types*. It never supplies proof
bodies to the scorer. The policy is pinned in
[`policy/award-scoring-v0.1.json`](../policy/award-scoring-v0.1.json).

For each entry, v0.1 gives 50 points to type-level dependency depth (capped at
10 edges), 30 to a new interface directly used by at least two entrypoints
(capped at 10 interfaces), and 20 to qualifying interface nodes per KiB of
added Lean source (a 4 KiB minimum denominator and 2.5 nodes/KiB cap). Generated
declarations, direct aliases marked in trusted source preflight, restatements,
and alpha-equivalent interfaces are excluded. Equal scores are ordered by SHA-256 of the published closing revision
and submission id.

Run a reproducible dry run with only trusted JSON inputs:

```sh
python3 tools/score_award.py --closing-revision <commit> --input entry.json
```

For an accepted entry, create `entry.json` from its immutable receiver
observation; this fails closed for older reports which do not contain the
necessary audit facts:

```sh
python3 tools/build_award_input.py --observation receiver-observations/<id>/<merge-commit>.json --json-out entry.json
```

The JSON result records the scorer and policy hashes, raw components,
exclusions, final score, and tie-break key. Eligibility and source-disclosure
rules remain separate from this scoring calculation.
