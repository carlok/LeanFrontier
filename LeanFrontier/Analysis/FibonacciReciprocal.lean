import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The reciprocal Fibonacci series converges

The sum of the reciprocals of the Fibonacci numbers,
`1/1 + 1/1 + 1/2 + 1/3 + 1/5 + 1/8 + ...`, converges; its value is the reciprocal Fibonacci
constant `ψ ≈ 3.3598856...`. Convergence is by comparison with a geometric series: the
Fibonacci numbers grow at least like `(3/2) ^ n`, so the reciprocals are eventually dominated
by `(2/3) ^ n`.

## Main statements

* `LeanFrontier.Nat.three_pow_le_two_pow_mul_fib` - the exponential growth bound
  `3 ^ n ≤ 2 ^ n * fib (n + 3)` in natural number arithmetic.
* `LeanFrontier.Nat.inv_fib_add_three_le` - the resulting geometric domination
  `(fib (n + 3) : ℝ)⁻¹ ≤ (2 / 3) ^ n`.
* `LeanFrontier.Nat.summable_inv_fib` - the series `∑ (fib n)⁻¹` converges.
* `LeanFrontier.Nat.tsum_inv_fib_le` - the crude explicit bound `∑' n, (fib n)⁻¹ ≤ 5`.

## Implementation notes

The growth bound is stated multiplicatively as `3 ^ n ≤ 2 ^ n * fib (n + 3)` so that it lives
in `ℕ` with no division or real exponentiation; it is exactly `(3 / 2) ^ n ≤ fib (n + 3)`
cleared of denominators. Its induction step reduces, via the defining recurrence, to
`fib (n + 1) ≤ fib (n + 2)`, and the offset `3` is the smallest for which this
ratio-three-halves bound holds at every index.

Because `fib 0 = 0`, the term at `n = 0` of the series is `(0 : ℝ)⁻¹ = 0` by the Lean
convention, so summing over all of `ℕ` is harmless; the comparison argument shifts the index
by three with `summable_nat_add_iff` and compares with `∑ (2/3) ^ n`. The bound `5` in
`tsum_inv_fib_le` is the head `1/1 + 1/1` plus the geometric tail bound
`∑ (2/3) ^ n = 3`; it is deliberately crude, and sharpening it toward `ψ` is left out of
scope. The irrationality of `ψ` (André-Jeannin) is far beyond this module.
-/

namespace LeanFrontier.Nat

/-- Exponential growth of the Fibonacci numbers, in `ℕ`: `3 ^ n ≤ 2 ^ n * fib (n + 3)`,
i.e. `fib (n + 3)` dominates `(3 / 2) ^ n`. -/
theorem three_pow_le_two_pow_mul_fib : ∀ n : ℕ, 3 ^ n ≤ 2 ^ n * Nat.fib (n + 3)
  | 0 => by decide
  | n + 1 => by
    have ih := three_pow_le_two_pow_mul_fib n
    have h1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have h3 : Nat.fib (n + 1) ≤ Nat.fib (n + 2) := Nat.fib_le_fib_succ
    have key : 3 * Nat.fib (n + 3) ≤ 2 * Nat.fib (n + 4) := by omega
    calc 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≤ 3 * (2 ^ n * Nat.fib (n + 3)) := Nat.mul_le_mul le_rfl ih
      _ = 2 ^ n * (3 * Nat.fib (n + 3)) := by ring
      _ ≤ 2 ^ n * (2 * Nat.fib (n + 4)) := Nat.mul_le_mul le_rfl key
      _ = 2 ^ (n + 1) * Nat.fib (n + 4) := by ring

/-- The reciprocal Fibonacci numbers are dominated by the geometric sequence `(2 / 3) ^ n`
after shifting the index by three. -/
theorem inv_fib_add_three_le (n : ℕ) : ((Nat.fib (n + 3) : ℝ))⁻¹ ≤ (2 / 3) ^ n := by
  have hfib : (0 : ℝ) < Nat.fib (n + 3) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have h : (3 : ℝ) ^ n ≤ 2 ^ n * Nat.fib (n + 3) := by
    exact_mod_cast three_pow_le_two_pow_mul_fib n
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have key : (1 : ℝ) ≤ (2 / 3) ^ n * Nat.fib (n + 3) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ h3, one_mul]
    exact h
  calc ((Nat.fib (n + 3) : ℝ))⁻¹ = ((Nat.fib (n + 3) : ℝ))⁻¹ * 1 := (mul_one _).symm
    _ ≤ ((Nat.fib (n + 3) : ℝ))⁻¹ * ((2 / 3) ^ n * Nat.fib (n + 3)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 / 3) ^ n * (((Nat.fib (n + 3) : ℝ))⁻¹ * Nat.fib (n + 3)) := by ring
    _ = (2 / 3) ^ n := by rw [inv_mul_cancel₀ hfib.ne', mul_one]

/-- The reciprocal Fibonacci series converges. The term at `n = 0` is `(0 : ℝ)⁻¹ = 0`, so
summing over all indices is harmless. -/
theorem summable_inv_fib : Summable fun n : ℕ => ((Nat.fib n : ℝ))⁻¹ := by
  rw [← summable_nat_add_iff 3]
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => inv_fib_add_three_le n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- A crude explicit bound on the reciprocal Fibonacci constant: the head `1/1 + 1/1`
plus the geometric tail bound `∑ (2/3) ^ n = 3`. The true value is `ψ ≈ 3.36`. -/
theorem tsum_inv_fib_le : ∑' n : ℕ, ((Nat.fib n : ℝ))⁻¹ ≤ 5 := by
  have hs := summable_inv_fib
  have hshift : Summable fun n : ℕ => ((Nat.fib (n + 3) : ℝ))⁻¹ :=
    (summable_nat_add_iff 3).mpr hs
  have hgeo : Summable fun n : ℕ => ((2 : ℝ) / 3) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsplit := hs.sum_add_tsum_nat_add 3
  have hle : ∑' n : ℕ, ((Nat.fib (n + 3) : ℝ))⁻¹ ≤ ∑' n : ℕ, ((2 : ℝ) / 3) ^ n :=
    hshift.tsum_le_tsum (fun n => inv_fib_add_three_le n) hgeo
  have hgeosum : ∑' n : ℕ, ((2 : ℝ) / 3) ^ n = 3 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hhead : (∑ i ∈ Finset.range 3, ((Nat.fib i : ℝ))⁻¹) = 2 := by
    norm_num [Finset.sum_range_succ, Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  linarith [hsplit, hle]

/-- The growth bound at `n = 10`: `3 ^ 10 = 59049` against `2 ^ 10 * fib 13 = 1024 * 233`. -/
example : 3 ^ 10 ≤ 2 ^ 10 * Nat.fib 13 := by decide

end LeanFrontier.Nat
