import LeanFrontier.Probability.MeasurePaleyZygmund
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# Chung-Erdős inequality

This module proves the finite-event Chung-Erdős inequality, a standard second-moment lower
bound for the probability of a union.

For a finite family of measurable events `A i`,

[
  \frac{(\sum_i P(A_i))^2}
       {\sum_{i,j} P(A_i \cap A_j)}
  \le P\!\left(\bigcup_i A_i\right),
]

whenever the denominator is positive.

The proof is a direct application of the accepted measure-theoretic Paley-Zygmund inequality
to the event-count random variable

`X(ω) = ∑ i, 1_{A_i}(ω)`

at threshold `θ = 0`. The substantive work is identifying the first and second moments of
that count:

* `E[X] = ∑ i P(A_i)`;
* `E[X²] = ∑ i,j P(A_i ∩ A_j)`;
* `{X > 0} = ⋃ i, A_i`.

This gives LeanFrontier's probability cluster a reusable finite second-moment union bound and
a natural stepping stone toward Kochen-Stone/Borel-Cantelli developments.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LeanFrontier.ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- **Chung-Erdős inequality.**

For a finite family of measurable events, the probability of their union is bounded below by
the square of the sum of their probabilities divided by the sum of all pairwise-intersection
probabilities.

The denominator positivity assumption is exactly the nondegenerate condition needed for the
divided form. -/
theorem chungErdos (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hsecond :
      0 < ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) :
    ((∑ i ∈ s, μ.real (A i)) ^ 2) /
        (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) ≤
      μ.real (⋃ i ∈ s, A i) := by
  classical

  let X : Ω → ℝ :=
    fun ω => ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω

  have hterm_meas :
      ∀ i ∈ s, Measurable ((A i).indicator (fun _ => (1 : ℝ))) := by
    intro i hi
    exact (measurable_indicator_const_iff (1 : ℝ)).2 (hA i hi)

  have hXmeas : Measurable X := by
    dsimp [X]
    exact Finset.measurable_sum s hterm_meas

  have hterm_nonneg :
      ∀ ω i, i ∈ s → 0 ≤ (A i).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω i hi
    by_cases hω : ω ∈ A i <;> simp [hω]

  have hXnonneg : ∀ ω, 0 ≤ X ω := by
    intro ω
    dsimp [X]
    exact Finset.sum_nonneg fun i hi => hterm_nonneg ω i hi

  have hX2 : MemLp X 2 μ := by
    dsimp [X]
    exact memLp_finsetSum' s fun i hi =>
      (memLp_const (μ := μ) (1 : ℝ)).indicator (hA i hi)

  have hmean :
      (∫ ω, X ω ∂μ) = ∑ i ∈ s, μ.real (A i) := by
    dsimp [X]
    rw [integral_finsetSum s]
    · apply Finset.sum_congr rfl
      intro i hi
      exact integral_indicator_one (hA i hi)
    · intro i hi
      exact (integrable_const (1 : ℝ)).indicator (hA i hi)

  have hsq_pointwise :
      ∀ ω,
        X ω ^ 2 =
          ∑ i ∈ s, ∑ j ∈ s,
            (A i ∩ A j).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    dsimp [X]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [Set.inter_indicator_one]

  have hsecondMoment :
      (∫ ω, X ω ^ 2 ∂μ) =
        ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
    calc
      (∫ ω, X ω ^ 2 ∂μ) =
          ∫ ω, ∑ i ∈ s, ∑ j ∈ s,
            (A i ∩ A j).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              exact hsq_pointwise ω
      _ = ∑ i ∈ s,
          ∫ ω, ∑ j ∈ s,
            (A i ∩ A j).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
              rw [integral_finsetSum s]
              intro i hi
              exact integrable_finsetSum s fun j hj =>
                (integrable_const (1 : ℝ)).indicator ((hA i hi).inter (hA j hj))
      _ = ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finsetSum s]
              · apply Finset.sum_congr rfl
                intro j hj
                exact integral_indicator_one ((hA i hi).inter (hA j hj))
              · intro j hj
                exact (integrable_const (1 : ℝ)).indicator ((hA i hi).inter (hA j hj))

  have hevent :
      {ω | 0 < X ω} = ⋃ i ∈ s, A i := by
    ext ω
    constructor
    · intro hpos
      have hex :
          ∃ i ∈ s, 0 < (A i).indicator (fun _ => (1 : ℝ)) ω := by
        apply (Finset.sum_pos_iff_of_nonneg (fun i hi => hterm_nonneg ω i hi)).1
        simpa [X] using hpos
      rcases hex with ⟨i, hi, hpositive⟩
      have hω : ω ∈ A i := by
        by_contra hnot
        simp [hnot] at hpositive
      simp only [Set.mem_iUnion]
      exact ⟨i, ⟨hi, hω⟩⟩
    · intro hmem
      simp only [Set.mem_iUnion] at hmem
      rcases hmem with ⟨i, hi, hω⟩
      have hpositive :
          0 < (A i).indicator (fun _ => (1 : ℝ)) ω := by
        simp [hω]
      have :
          0 < ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) ω := by
        apply (Finset.sum_pos_iff_of_nonneg (fun j hj => hterm_nonneg ω j hj)).2
        exact ⟨i, hi, hpositive⟩
      simpa [X] using this

  have hsecondIntegral : 0 < ∫ ω, X ω ^ 2 ∂μ := by
    rw [hsecondMoment]
    exact hsecond

  have hpz :=
    paleyZygmund μ X hXmeas hXnonneg hX2
      (θ := 0) (by norm_num) (by norm_num) hsecondIntegral

  rw [hmean, hsecondMoment] at hpz
  simpa [hevent] using hpz

end LeanFrontier.ProbabilityTheory
