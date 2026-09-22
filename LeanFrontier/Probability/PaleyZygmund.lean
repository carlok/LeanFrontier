import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# A finite weighted Paley-Zygmund inequality

This module develops a finite weighted form of the Paley-Zygmund inequality, a standard
second-moment lower bound in probability theory.

For nonnegative weights summing to one and a nonnegative observable `X`, the theorem bounds the
weight of the superlevel set
`{i | θ * E[X] < X i}`
from below in terms of the first and second weighted moments.

The proof follows the classical argument:

1. split the first moment at the threshold `θ * E[X]`;
2. bound the contribution below threshold by `θ * E[X]`;
3. apply weighted Cauchy-Schwarz on the superlevel set.

The formulation is deliberately finite and algebraic. It can be specialized to finite
probability mass functions without introducing measure-theoretic coercions into the core
inequality, while still providing the standard second-moment method as a reusable theorem.
-/

open scoped BigOperators

namespace LeanFrontier.FiniteProbability

variable {ι : Type*}

/-- **Finite weighted Paley-Zygmund inequality.**

Let `w` be nonnegative weights on a finite set `s` with total weight one, and let `X` be
nonnegative on `s`. For `0 ≤ θ ≤ 1`, the square of
`(1 - θ) * E[X]` is at most the weight of the strict superlevel set
`{i ∈ s | θ * E[X] < X i}` times the second weighted moment.

Equivalently, whenever the second moment is positive, division yields the usual lower bound
for the probability of exceeding a fraction `θ` of the mean. -/
theorem paleyZygmund
    (s : Finset ι) (w X : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hX : ∀ i ∈ s, 0 ≤ X i)
    (hnorm : ∑ i ∈ s, w i = 1)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((1 - θ) * ∑ i ∈ s, w i * X i) ^ 2 ≤
      (∑ i ∈ s.filter (fun i => θ * (∑ j ∈ s, w j * X j) < X i), w i) *
        ∑ i ∈ s, w i * X i ^ 2 := by
  classical
  let m : ℝ := ∑ i ∈ s, w i * X i
  let A : Finset ι := s.filter fun i => θ * m < X i
  let B : Finset ι := s.filter fun i => X i ≤ θ * m

  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hX i hi)

  have htheta_m0 : 0 ≤ θ * m := mul_nonneg hθ0 hm0

  have hmassB : (∑ i ∈ B, w i) ≤ 1 := by
    rw [← hnorm]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro i his hiB
      exact hw i his

  have hbelow :
      (∑ i ∈ B, w i * X i) ≤ θ * m := by
    calc
      (∑ i ∈ B, w i * X i)
          ≤ ∑ i ∈ B, w i * (θ * m) := by
              apply Finset.sum_le_sum
              intro i hi
              have hiS : i ∈ s := (Finset.mem_filter.mp hi).1
              have hiX : X i ≤ θ * m := (Finset.mem_filter.mp hi).2
              exact mul_le_mul_of_nonneg_left hiX (hw i hiS)
      _ = (∑ i ∈ B, w i) * (θ * m) := by
            rw [Finset.sum_mul]
      _ = (θ * m) * ∑ i ∈ B, w i := by ring
      _ ≤ (θ * m) * 1 := mul_le_mul_of_nonneg_left hmassB htheta_m0
      _ = θ * m := by ring

  have hsplit :
      m = (∑ i ∈ A, w i * X i) + ∑ i ∈ B, w i * X i := by
    have h :=
      (Finset.sum_filter_add_sum_filter_not s
        (fun i => θ * m < X i) (fun i => w i * X i)).symm
    simpa [m, A, B, not_lt] using h

  have hlower :
      (1 - θ) * m ≤ ∑ i ∈ A, w i * X i := by
    linarith

  have hlower0 : 0 ≤ (1 - θ) * m :=
    mul_nonneg (sub_nonneg.mpr hθ1) hm0

  have hsumA0 : 0 ≤ ∑ i ∈ A, w i * X i := by
    apply Finset.sum_nonneg
    intro i hi
    have hiS : i ∈ s := (Finset.mem_filter.mp hi).1
    exact mul_nonneg (hw i hiS) (hX i hiS)

  have hsquare :
      ((1 - θ) * m) ^ 2 ≤ (∑ i ∈ A, w i * X i) ^ 2 := by
    nlinarith

  have hcs :
      (∑ i ∈ A, w i * X i) ^ 2 ≤
        (∑ i ∈ A, w i) * ∑ i ∈ A, w i * X i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i hi
      exact hw i ((Finset.mem_filter.mp hi).1)
    · intro i hi
      exact mul_nonneg (hw i ((Finset.mem_filter.mp hi).1)) (sq_nonneg (X i))
    · intro i hi
      ring_nf
      exact le_rfl

  have hmassA0 : 0 ≤ ∑ i ∈ A, w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact hw i ((Finset.mem_filter.mp hi).1)

  have hsecond :
      (∑ i ∈ A, w i * X i ^ 2) ≤ ∑ i ∈ s, w i * X i ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro i his hiA
      exact mul_nonneg (hw i his) (sq_nonneg (X i))

  have hfinal :
      ((1 - θ) * m) ^ 2 ≤
        (∑ i ∈ A, w i) * ∑ i ∈ s, w i * X i ^ 2 := by
    exact hsquare.trans <| hcs.trans <|
      mul_le_mul_of_nonneg_left hsecond hmassA0

  simpa [m, A] using hfinal

end LeanFrontier.FiniteProbability
