import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Paley-Zygmund inequality on probability spaces

This module proves the classical Paley-Zygmund inequality for an arbitrary probability measure.
Unlike the finite weighted and finite-PMF formulations, the proof uses Mathlib's genuine
measure-theoretic and `L²` infrastructure.

The analytic core is Cauchy-Schwarz in the Hilbert space `L²(μ)`: pairing the random variable
with the indicator of a measurable event gives

`(∫_A X)² ≤ μ(A) * ∫ X²`.

The Paley-Zygmund estimate then follows by taking
`A = {ω | θ * E[X] < X ω}`, splitting the expectation across `A` and its complement,
and bounding the complement contribution by `θ * E[X]`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LeanFrontier.ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem setIntegral_sq_le_measureReal_mul_integral_sq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX2 : MemLp X 2 μ) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω in A, X ω ∂μ) ^ 2 ≤ μ.real A * ∫ ω, X ω ^ 2 ∂μ := by
  let f : Lp ℝ 2 μ := hX2.toLp X
  have hfcoe : (f : Ω → ℝ) =ᵐ[μ] X := by
    simpa [f] using hX2.coeFn_toLp

  have hμA : μ A ≠ ∞ := by finiteness
  let u : Lp ℝ 2 μ := indicatorConstLp 2 hA hμA (1 : ℝ)

  have huf : inner ℝ u f = ∫ ω in A, X ω ∂μ := by
    calc
      inner ℝ u f = ∫ ω in A, f ω ∂μ := by
        simpa [u] using (L2.inner_indicatorConstLp_one (μ := μ) hA hμA f)
      _ = ∫ ω in A, X ω ∂μ :=
        setIntegral_congr_ae hA (hfcoe.mono fun _ h _ => h)

  have hfu : inner ℝ f u = ∫ ω in A, X ω ∂μ := by
    rw [real_inner_comm]
    exact huf

  have huu : inner ℝ u u = μ.real A := by
    simpa [u] using
      (L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
        (μ := μ) hA hA hμA hμA)

  have hff : inner ℝ f f = ∫ ω, X ω ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfcoe] with ω hω
    rw [hω]
    simp [sq]

  have hcs := inner_mul_inner_self_le (𝕜 := ℝ) u f
  rw [huf, hfu, huu, hff] at hcs
  have habs :
      ‖∫ ω in A, X ω ∂μ‖ * ‖∫ ω in A, X ω ∂μ‖ =
        (∫ ω in A, X ω ∂μ) ^ 2 := by
    rw [Real.norm_eq_abs, ← abs_mul, abs_mul_self, pow_two]
  calc
    (∫ ω in A, X ω ∂μ) ^ 2 =
        ‖∫ ω in A, X ω ∂μ‖ * ‖∫ ω in A, X ω ∂μ‖ := habs.symm
    _ ≤ μ.real A * ∫ ω, X ω ^ 2 ∂μ := by
      simpa using hcs

/-- **Paley-Zygmund inequality on an arbitrary probability space.**

Let `X` be a measurable nonnegative real random variable with finite second moment. For
`0 ≤ θ ≤ 1`, if `E[X²]` is positive, then

`((1 - θ) * E[X])² / E[X²] ≤ P(X > θ * E[X])`.

The probability on the right is represented by `μ.real`, the real-valued measure of the
strict superlevel event. -/
theorem paleyZygmund (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (hXnonneg : ∀ ω, 0 ≤ X ω)
    (hX2 : MemLp X 2 μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsecond : 0 < ∫ ω, X ω ^ 2 ∂μ) :
    (((1 - θ) * ∫ ω, X ω ∂μ) ^ 2) / (∫ ω, X ω ^ 2 ∂μ) ≤
      μ.real {ω | θ * (∫ x, X x ∂μ) < X ω} := by
  let m : ℝ := ∫ ω, X ω ∂μ
  let A : Set Ω := {ω | θ * m < X ω}

  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_const hXmeas

  have hX1 : MemLp X 1 μ :=
    hX2.mono_exponent (by norm_num)
  have hXint : Integrable X μ :=
    memLp_one_iff_integrable.mp hX1

  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact integral_nonneg hXnonneg

  have htheta_m0 : 0 ≤ θ * m :=
    mul_nonneg hθ0 hm0

  have hbelow : (∫ ω in Aᶜ, X ω ∂μ) ≤ θ * m := by
    calc
      (∫ ω in Aᶜ, X ω ∂μ) ≤ ∫ _ in Aᶜ, θ * m ∂μ := by
        apply setIntegral_mono_on hXint.integrableOn (integrable_const _).integrableOn hA.compl
        intro ω hω
        have hnot : ¬ θ * m < X ω := by
          simpa [A] using hω
        exact le_of_not_gt hnot
      _ = μ.real Aᶜ * (θ * m) := by
        rw [setIntegral_const]
        simp [smul_eq_mul]
      _ ≤ 1 * (θ * m) :=
        mul_le_mul_of_nonneg_right measureReal_le_one htheta_m0
      _ = θ * m := one_mul _

  have hsplit :
      (∫ ω in A, X ω ∂μ) + ∫ ω in Aᶜ, X ω ∂μ = m := by
    simpa [m] using (integral_add_compl hA hXint)

  have hlower :
      (1 - θ) * m ≤ ∫ ω in A, X ω ∂μ := by
    linarith

  have hleft0 : 0 ≤ (1 - θ) * m :=
    mul_nonneg (sub_nonneg.mpr hθ1) hm0

  have hset0 : 0 ≤ ∫ ω in A, X ω ∂μ :=
    setIntegral_nonneg hA (fun ω _ => hXnonneg ω)

  have hsquare :
      ((1 - θ) * m) ^ 2 ≤ (∫ ω in A, X ω ∂μ) ^ 2 := by
    nlinarith

  have hcauchy :
      (∫ ω in A, X ω ∂μ) ^ 2 ≤ μ.real A * ∫ ω, X ω ^ 2 ∂μ :=
    setIntegral_sq_le_measureReal_mul_integral_sq hX2 hA

  have hproduct :
      ((1 - θ) * m) ^ 2 ≤ μ.real A * ∫ ω, X ω ^ 2 ∂μ :=
    hsquare.trans hcauchy

  have hdiv :
      (((1 - θ) * m) ^ 2) / (∫ ω, X ω ^ 2 ∂μ) ≤ μ.real A :=
    (div_le_iff₀ hsecond).2 hproduct

  simpa [m, A] using hdiv

end LeanFrontier.ProbabilityTheory
