import LeanFrontier.Combinatorics.FiniteVariance
import Mathlib.Tactic

/-!
# Laguerre-Samuelson inequality for finite families

For a finite family of real numbers, no single value can lie arbitrarily far from the mean
relative to the family's variance.  In division-free form, if `x ∈ s` and `n = |s|`, then

`(n * f x - ∑ y ∈ s, f y)^2 ≤
  (n - 1) * (n * ∑ y ∈ s, (f y)^2 - (∑ y ∈ s, f y)^2)`.

After dividing by `n^2`, this is the classical Laguerre-Samuelson inequality
`(f x - mean)^2 ≤ (n - 1) * variance`.

The proof removes `x` from the family and applies the accepted pairwise-variance identity to
the remaining values.  The nonnegativity of their total pairwise squared difference is exactly
the Cauchy-Schwarz remainder needed for the sharp factor `n - 1`.
-/

open scoped BigOperators

namespace LeanFrontier.Finset

/-- **Laguerre-Samuelson inequality**, in a division-free finite-family form.

For any member `x` of a finite real family `s`, its squared deviation from the mean is at
most `|s| - 1` times the population variance.  The displayed form avoids division and remains
meaningful for the singleton case. -/
theorem laguerre_samuelson {ι : Type*} (s : Finset ι) (f : ι → ℝ) {x : ι} (hx : x ∈ s) :
    ((s.card : ℝ) * f x - ∑ y ∈ s, f y) ^ 2 ≤
      ((s.card : ℝ) - 1) *
        ((s.card : ℝ) * ∑ y ∈ s, f y ^ 2 - (∑ y ∈ s, f y) ^ 2) := by
  classical
  let t : Finset ι := s.erase x

  have hpair := sum_pairwise_sq_sub t f
  have hnonneg : 0 ≤ ∑ a ∈ t, ∑ b ∈ t, (f a - f b) ^ 2 := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    exact sq_nonneg _

  have htvar :
      0 ≤ (t.card : ℝ) * ∑ y ∈ t, f y ^ 2 - (∑ y ∈ t, f y) ^ 2 := by
    rw [hpair] at hnonneg
    nlinarith

  have hxt : x ∉ t := by
    simp [t]

  have hinsert : insert x t = s := by
    simp [t, hx]

  have hcardNat : s.card = t.card + 1 := by
    rw [← hinsert, Finset.card_insert_of_notMem hxt]

  have hcard : (s.card : ℝ) = (t.card : ℝ) + 1 := by
    exact_mod_cast hcardNat

  have hsum : (∑ y ∈ s, f y) = f x + ∑ y ∈ t, f y := by
    rw [← hinsert, Finset.sum_insert hxt]

  have hsq : (∑ y ∈ s, f y ^ 2) = f x ^ 2 + ∑ y ∈ t, f y ^ 2 := by
    rw [← hinsert, Finset.sum_insert hxt]

  have hscaled :
      0 ≤ ((t.card : ℝ) + 1) *
        ((t.card : ℝ) * ∑ y ∈ t, f y ^ 2 - (∑ y ∈ t, f y) ^ 2) :=
    mul_nonneg (by positivity) htvar

  rw [hcard, hsum, hsq]
  nlinarith

end LeanFrontier.Finset
