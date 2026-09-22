import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Cantelli's inequality

This module proves Cantelli's inequality, the sharp one-sided analogue of Chebyshev's inequality.

For a square-integrable real random variable `X` on a probability space and `a > 0`,

`P(X - E[X] ≥ a) ≤ Var(X) / (Var(X) + a²)`.

Mathlib already contains the two-sided Chebyshev inequality.  The proof here uses the classical
optimized-shift argument: apply Markov's inequality to the normalized square
`((X - E[X] + t) / (a + t))²` with `t = Var(X) / a`.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace LeanFrontier.ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cantelli's inequality (one-sided Chebyshev inequality).**

For a square-integrable real random variable `X` and `a > 0`, the upper-tail probability
is bounded by

`P(X - E[X] ≥ a) ≤ Var(X) / (Var(X) + a²)`.

This is sharper than applying the ordinary two-sided Chebyshev inequality to the same event. -/
theorem cantelli (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) {a : ℝ} (ha : 0 < a) :
    μ {ω | a ≤ X ω - μ[X]} ≤
      ENNReal.ofReal (Var[X; μ] / (Var[X; μ] + a ^ 2)) := by
  let v : ℝ := Var[X; μ]
  let t : ℝ := v / a

  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact _root_.ProbabilityTheory.variance_nonneg X μ

  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hv0 ha.le

  have hat : 0 < a + t :=
    add_pos_of_pos_of_nonneg ha ht0

  have hXint : Integrable X μ :=
    hX.integrable one_le_two

  have hcenter2 : MemLp (fun ω => X ω - μ[X]) 2 μ :=
    hX.sub (memLp_const μ[X])

  have hcenterInt : Integrable (fun ω => X ω - μ[X]) μ :=
    hXint.sub (integrable_const μ[X])

  have hcenterMean : (∫ ω, X ω - μ[X] ∂μ) = 0 := by
    rw [integral_sub hXint (integrable_const μ[X])]
    simp

  have hcenterSq : (∫ ω, (X ω - μ[X]) ^ 2 ∂μ) = v := by
    dsimp [v]
    exact (_root_.ProbabilityTheory.variance_eq_integral hX.aemeasurable).symm

  have hshift2 : MemLp (fun ω => X ω - μ[X] + t) 2 μ :=
    hcenter2.add (memLp_const t)

  have hshiftSq :
      (∫ ω, (X ω - μ[X] + t) ^ 2 ∂μ) = v + t ^ 2 := by
    calc
      (∫ ω, (X ω - μ[X] + t) ^ 2 ∂μ) =
          ∫ ω, (X ω - μ[X]) ^ 2 + (2 * t) * (X ω - μ[X]) + t ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            ring
      _ = (∫ ω, (X ω - μ[X]) ^ 2 + (2 * t) * (X ω - μ[X]) ∂μ) +
            ∫ _ : Ω, t ^ 2 ∂μ := by
          exact integral_add
            (hcenter2.integrable_sq.add (hcenterInt.const_mul (2 * t)))
            (integrable_const (t ^ 2))
      _ = (∫ ω, (X ω - μ[X]) ^ 2 ∂μ) +
            (∫ ω, (2 * t) * (X ω - μ[X]) ∂μ) +
            ∫ _ : Ω, t ^ 2 ∂μ := by
          rw [integral_add hcenter2.integrable_sq (hcenterInt.const_mul (2 * t))]
      _ = v + t ^ 2 := by
          rw [hcenterSq, integral_const_mul, hcenterMean]
          simp

  have hZint :
      Integrable (fun ω => (X ω - μ[X] + t) ^ 2 / (a + t) ^ 2) μ :=
    hshift2.integrable_sq.div_const ((a + t) ^ 2)

  have hZnonneg :
      0 ≤ᵐ[μ] (fun ω => (X ω - μ[X] + t) ^ 2 / (a + t) ^ 2) := by
    filter_upwards with ω
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)

  have hthreshold :
      ∀ ω ∈ {ω | a ≤ X ω - μ[X]},
        1 ≤ (X ω - μ[X] + t) ^ 2 / (a + t) ^ 2 := by
    intro ω hω
    change a ≤ X ω - μ[X] at hω
    have hle : a + t ≤ X ω - μ[X] + t := by
      linarith
    have hsq :
        (a + t) ^ 2 ≤ (X ω - μ[X] + t) ^ 2 := by
      nlinarith
    rw [le_div_iff₀ (sq_pos_of_pos hat)]
    simpa using hsq

  have hmarkov :
      μ {ω | a ≤ X ω - μ[X]} ≤
        ENNReal.ofReal
          (∫ ω, (X ω - μ[X] + t) ^ 2 / (a + t) ^ 2 ∂μ) :=
    hZint.measure_le_integral hZnonneg hthreshold

  have hZ :
      (∫ ω, (X ω - μ[X] + t) ^ 2 / (a + t) ^ 2 ∂μ) =
        (v + t ^ 2) / (a + t) ^ 2 := by
    rw [integral_div, hshiftSq]

  have hden : v + a ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos ha]

  have halgebra :
      (v + t ^ 2) / (a + t) ^ 2 = v / (v + a ^ 2) := by
    dsimp [t]
    field_simp [ha.ne', hden]
    ring

  rw [hZ, halgebra] at hmarkov
  simpa [v] using hmarkov

end LeanFrontier.ProbabilityTheory
