import LeanFrontier.Analysis.SlopeMinorant

/-!
# How the greatest step bounded minorant responds to its constraint set

`LeanFrontier.BoundedSlope.minorant a b L s hs` is the greatest sequence with increments
bounded by `a` upward and `b` downward lying below the ceiling `L` at the indices of `s`.
The module that introduced it characterises it against a fixed `s`. This one asks what
happens as `s` and `L` vary, and records the two facts that follow from the infimum form
alone.

## Main statements

* `LeanFrontier.BoundedSlope.slack_nonneg` - the slack budget is never negative for
  nonnegative rates.
* `LeanFrontier.BoundedSlope.minorant_anti_constraints` - imposing the ceiling at more
  indices can only lower the minorant.
* `LeanFrontier.BoundedSlope.inf_ceiling_le_minorant` - the minorant never falls below the
  least constrained ceiling value, at any index.

## Implementation notes

Both proofs go through `Finset.le_inf'` and `Finset.inf'_le` and use no property of
`slack` beyond nonnegativity, so they hold for the infimum of any nonnegative displacement
family. Antitonicity in `s` is the discrete counterpart of the observation that a Lipschitz
envelope decreases as its constraint set grows.
-/

namespace LeanFrontier.BoundedSlope

variable {a b : ℝ} {L : ℕ → ℝ} {s t : Finset ℕ}

/-- The slack budget between two indices is nonnegative when both rates are. -/
theorem slack_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : ℕ) : 0 ≤ slack a b i j :=
  add_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) (mul_nonneg hb (Nat.cast_nonneg _))

/-- Constraining the ceiling at more indices can only lower the greatest minorant. -/
theorem minorant_anti_constraints (hst : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty) (i : ℕ) :
    minorant a b L t ht i ≤ minorant a b L s hs i :=
  Finset.le_inf' hs _ fun _j hj => Finset.inf'_le _ (hst hj)

/-- At every index the minorant stays at or above the least constrained ceiling value. -/
theorem inf_ceiling_le_minorant (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : s.Nonempty) (i : ℕ) :
    s.inf' hs L ≤ minorant a b L s hs i :=
  Finset.le_inf' hs _ fun j hj =>
    le_trans (Finset.inf'_le _ hj) (le_add_of_nonneg_right (slack_nonneg ha hb i j))

end LeanFrontier.BoundedSlope
