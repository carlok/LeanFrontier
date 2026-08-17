import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Sums of powers of the first natural numbers

Two classical closed forms for sums over the initial segment of `ℕ`.

The first `n` odd numbers are `1, 3, 5, ..., 2n - 1`; their sum is `n²`. This is
the identity that makes the square numbers figurate: the `n`-th square is a sum
of `n` consecutive odd numbers.

Nicomachus's theorem is the companion statement for cubes: the sum of the first
`n` cubes is the square of the sum of the first `n` natural numbers,

`(∑ i < n, i)² = ∑ i < n, i³`.

## Main statements

* `LeanFrontier.PowerSums.sum_odd_eq_sq` - the first `n` odd numbers sum to `n²`.
* `LeanFrontier.PowerSums.sum_cubes_eq_sum_sq` - Nicomachus's theorem.

## Implementation notes

Both statements are about `ℕ` and are proved by induction with the arithmetic
steps discharged by `ring`, except for the one place where `n - 1` appears
inside the induction step for the cube identity, which is handled by the
elementary `Nat` subtraction lemmas. No division by a non-constant occurs, so
the identities are stated with no side conditions.
-/

namespace LeanFrontier.PowerSums

/-- The first `n` odd natural numbers sum to `n²`. -/
theorem sum_odd_eq_sq (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

/-- `n * (n - 1) * n + n² = n³`, the arithmetic heart of the Nicomachus
induction step. Kept private: it is proof scaffolding, not a public result. -/
private lemma mul_pred_mul_add_sq (n : ℕ) : n * (n - 1) * n + n ^ 2 = n ^ 3 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have h : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    calc
      n * (n - 1) * n + n ^ 2 = n ^ 2 * (n - 1) + n ^ 2 := by ring
      _ = n ^ 2 * (n - 1) + n ^ 2 * 1 := by rw [mul_one]
      _ = n ^ 2 * ((n - 1) + 1) := by rw [← mul_add]
      _ = n ^ 2 * n := by rw [h]
      _ = n ^ 3 := by ring

/-- Nicomachus's theorem: the sum of the first `n` cubes equals the square of the
sum of the first `n` natural numbers. -/
theorem sum_cubes_eq_sum_sq (n : ℕ) :
    (∑ i ∈ Finset.range n, i) ^ 2 = ∑ i ∈ Finset.range n, i ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [← ih]
      have hS : 2 * (∑ i ∈ Finset.range n, i) * n + n ^ 2 = n ^ 3 := by
        have hsum2 : (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := Finset.sum_range_id_mul_two n
        calc
          2 * (∑ i ∈ Finset.range n, i) * n + n ^ 2
              = (∑ i ∈ Finset.range n, i) * 2 * n + n ^ 2 := by ring
          _ = n * (n - 1) * n + n ^ 2 := by rw [hsum2]
          _ = n ^ 3 := mul_pred_mul_add_sq n
      calc
        ((∑ i ∈ Finset.range n, i) + n) ^ 2
            = (∑ i ∈ Finset.range n, i) ^ 2 + 2 * (∑ i ∈ Finset.range n, i) * n + n ^ 2 := by ring
        _ = (∑ i ∈ Finset.range n, i) ^ 2 + (2 * (∑ i ∈ Finset.range n, i) * n + n ^ 2) := by ring
        _ = (∑ i ∈ Finset.range n, i) ^ 2 + n ^ 3 := by rw [hS]

end LeanFrontier.PowerSums
