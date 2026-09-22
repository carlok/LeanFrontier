import LeanFrontier.Probability.PaleyZygmund
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Paley-Zygmund inequality for finite probability mass functions

The accepted finite weighted Paley-Zygmund theorem is algebraic: it works with explicit
nonnegative weights whose total is one.  This module connects that reusable core to Mathlib's
actual probability-mass-function interface.

For a real-valued nonnegative observable on a finite PMF, the result is stated in the standard
probabilistic form

`((1 - θ) * E[X])² / E[X²] ≤ P(X > θ * E[X])`

whenever the second moment is positive.

The proof does not reprove Paley-Zygmund.  It identifies PMF expectations and event probability
with the finite weighted sums used by `LeanFrontier.FiniteProbability.paleyZygmund`, then
divides the accepted product inequality by the positive second moment.
-/

open scoped BigOperators
open MeasureTheory

namespace LeanFrontier.ProbabilityTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Paley-Zygmund inequality for a finite probability mass function.**

If `X` is nonnegative, `0 ≤ θ ≤ 1`, and the second moment is positive, then the
probability that `X` exceeds `θ` times its expectation is at least
`((1 - θ) E[X])² / E[X²]`.

This is the standard probability-facing specialization of
`LeanFrontier.FiniteProbability.paleyZygmund`. -/
theorem pmf_paleyZygmund (p : PMF α) (X : α → ℝ)
    (hX : ∀ i, 0 ≤ X i)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsecond : 0 < ∫ i, X i ^ 2 ∂p.toMeasure) :
    (((1 - θ) * ∫ i, X i ∂p.toMeasure) ^ 2) /
        (∫ i, X i ^ 2 ∂p.toMeasure) ≤
      (p.toMeasure {i | θ * (∫ j, X j ∂p.toMeasure) < X i}).toReal := by
  classical

  have hsumENN : ∑ i : α, p i = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe

  have hnorm : ∑ i : α, (p i).toReal = 1 := by
    calc
      (∑ i : α, (p i).toReal) = ENNReal.toReal (∑ i : α, p i) := by
        symm
        simpa using
          (ENNReal.toReal_sum (s := Finset.univ) (f := fun i : α => p i)
            (fun i _ => p.apply_ne_top i))
      _ = 1 := by simp [hsumENN]

  have hmean :
      (∫ i, X i ∂p.toMeasure) = ∑ i : α, (p i).toReal * X i := by
    simpa [smul_eq_mul] using (PMF.integral_eq_sum p X)

  have hsecondMoment :
      (∫ i, X i ^ 2 ∂p.toMeasure) =
        ∑ i : α, (p i).toReal * X i ^ 2 := by
    simpa [smul_eq_mul] using (PMF.integral_eq_sum p (fun i => X i ^ 2))

  let m : ℝ := ∑ i : α, (p i).toReal * X i
  let A : Finset α := Finset.univ.filter fun i => θ * m < X i

  have hmass :
      (p.toMeasure {i | θ * m < X i}).toReal =
        ∑ i ∈ A, (p i).toReal := by
    have hset : {i | θ * m < X i} = (A : Set α) := by
      ext i
      simp [A]
    rw [hset, p.toMeasure_apply_finset A]
    simpa using
      (ENNReal.toReal_sum (s := A) (f := fun i : α => p i)
        (fun i _ => p.apply_ne_top i))

  have hcore :=
    LeanFrontier.FiniteProbability.paleyZygmund
      (s := Finset.univ) (w := fun i : α => (p i).toReal) (X := X)
      (fun i _ => ENNReal.toReal_nonneg)
      (fun i _ => hX i)
      hnorm hθ0 hθ1

  have hproduct :
      ((1 - θ) * m) ^ 2 ≤
        (∑ i ∈ A, (p i).toReal) *
          ∑ i : α, (p i).toReal * X i ^ 2 := by
    simpa [m, A] using hcore

  have hproduct' :
      ((1 - θ) * ∫ i, X i ∂p.toMeasure) ^ 2 ≤
        (p.toMeasure {i | θ * (∫ j, X j ∂p.toMeasure) < X i}).toReal *
          (∫ i, X i ^ 2 ∂p.toMeasure) := by
    rw [hmean, hsecondMoment]
    change ((1 - θ) * m) ^ 2 ≤
      (p.toMeasure {i | θ * m < X i}).toReal *
        (∑ i : α, (p i).toReal * X i ^ 2)
    rw [hmass]
    exact hproduct

  exact (div_le_iff₀ hsecond).2 hproduct'

end LeanFrontier.ProbabilityTheory
