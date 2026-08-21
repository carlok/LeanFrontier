import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite variance identities

An algebraic identity expressing the total pairwise squared difference of a
finite family through its first and second moments.
-/

open scoped BigOperators

namespace LeanFrontier.Finset

variable {ι R : Type*} [CommRing R]

/-- The total squared difference over all ordered pairs in a finite family is
twice its unnormalized variance. -/
theorem sum_pairwise_sq_sub (s : Finset ι) (f : ι → R) :
    ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
      2 * (s.card : R) * ∑ x ∈ s, f x ^ 2 - 2 * (∑ x ∈ s, f x) ^ 2 := by
  calc
    ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
        ∑ x ∈ s, ∑ y ∈ s, (f x ^ 2 - 2 * f x * f y + f y ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = 2 * (s.card : R) * ∑ x ∈ s, f x ^ 2 - 2 * (∑ x ∈ s, f x) ^ 2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      have hcross :
          (∑ x ∈ s, ∑ y ∈ s, 2 * f x * f y) =
            2 * (∑ x ∈ s, f x) * (∑ y ∈ s, f y) := by
        calc
          (∑ x ∈ s, ∑ y ∈ s, 2 * f x * f y) =
              ∑ x ∈ s, (2 * f x) * (∑ y ∈ s, f y) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (Finset.mul_sum s f (2 * f x)).symm
          _ = (∑ x ∈ s, 2 * f x) * (∑ y ∈ s, f y) :=
            (Finset.sum_mul s (fun x ↦ 2 * f x) (∑ y ∈ s, f y)).symm
          _ = 2 * (∑ x ∈ s, f x) * (∑ y ∈ s, f y) := by
            congr 1
            exact (Finset.mul_sum s f 2).symm
      rw [hcross]
      ring

end LeanFrontier.Finset
