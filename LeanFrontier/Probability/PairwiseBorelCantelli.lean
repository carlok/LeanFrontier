import LeanFrontier.Probability.KochenStone
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# Pairwise-independent Borel-Cantelli from Kochen-Stone

Mathlib's second Borel-Cantelli theorem assumes full independence.  The accepted
`LeanFrontier.ProbabilityTheory.kochenStone` inequality is strong enough to recover the
classical pairwise-independent version.

For pairwise independent measurable events, the second-moment denominator differs from the
square of the first-moment sum only on the diagonal.  Since each diagonal probability is at
most one, the Kochen-Stone ratio is squeezed asymptotically to one whenever the first-moment
partial sums diverge.  Kochen-Stone then forces the limsup event to have probability one.

This is strictly weaker than mutual independence and therefore does not duplicate Mathlib's
existing `ProbabilityTheory.measure_limsup_eq_one`.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace LeanFrontier.ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

private def pairwiseFirstSum (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, μ.real (A i)

private def pairwiseSecondSum (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, μ.real (A i ∩ A j)

private noncomputable def pairwiseRatio (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) : ℝ :=
  pairwiseFirstSum μ A N ^ 2 / pairwiseSecondSum μ A N

private theorem pairwiseFirstSum_nonneg
    (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    0 ≤ pairwiseFirstSum μ A N := by
  dsimp [pairwiseFirstSum]
  exact Finset.sum_nonneg fun i hi => measureReal_nonneg

private theorem pairwiseFirstSum_le_secondSum
    (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    pairwiseFirstSum μ A N ≤ pairwiseSecondSum μ A N := by
  dsimp [pairwiseFirstSum, pairwiseSecondSum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    μ.real (A i) = μ.real (A i ∩ A i) := by rw [inter_self]
    _ ≤ ∑ j ∈ Finset.range N, μ.real (A i ∩ A j) := by
      exact Finset.single_le_sum
        (f := fun j => μ.real (A i ∩ A j))
        (fun j hj => measureReal_nonneg)
        hi

private theorem pairwiseRatio_nonneg
    (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    0 ≤ pairwiseRatio μ A N := by
  dsimp [pairwiseRatio]
  exact div_nonneg (sq_nonneg _) (by
    exact le_trans (pairwiseFirstSum_nonneg μ A N)
      (pairwiseFirstSum_le_secondSum μ A N))

private theorem pairwiseRatio_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (N : ℕ) :
    pairwiseRatio μ A N ≤ 1 := by
  by_cases hS : pairwiseFirstSum μ A N = 0
  · simp [pairwiseRatio, hS]
  have hSpos : 0 < pairwiseFirstSum μ A N :=
    lt_of_le_of_ne (pairwiseFirstSum_nonneg μ A N) (Ne.symm hS)
  have hTpos : 0 < pairwiseSecondSum μ A N :=
    hSpos.trans_le (pairwiseFirstSum_le_secondSum μ A N)
  have hce :=
    chungErdos μ (Finset.range N) A
      (fun i hi => hA i)
      (by simpa [pairwiseSecondSum] using hTpos)
  have hunion : μ.real (⋃ i ∈ Finset.range N, A i) ≤ 1 :=
    measureReal_le_one
  have hratio :
      pairwiseRatio μ A N ≤ μ.real (⋃ i ∈ Finset.range N, A i) := by
    simpa [pairwiseRatio, pairwiseFirstSum, pairwiseSecondSum] using hce
  exact hratio.trans hunion

private theorem measureReal_inter_eq_mul_of_indep
    (μ : Measure Ω) {s t : Set Ω}
    (h : ProbabilityTheory.IndepSet s t μ) :
    μ.real (s ∩ t) = μ.real s * μ.real t := by
  rw [measureReal_def, measureReal_def, measureReal_def,
    h.measure_inter_eq_mul, ENNReal.toReal_mul]

private theorem pairwiseSecondSum_le_sq_add_first
    (μ : Measure Ω) (A : ℕ → Set Ω)
    (hpair : ∀ ⦃i j : ℕ⦄, i ≠ j → ProbabilityTheory.IndepSet (A i) (A j) μ)
    (N : ℕ) :
    pairwiseSecondSum μ A N ≤
      pairwiseFirstSum μ A N ^ 2 + pairwiseFirstSum μ A N := by
  classical
  let r := Finset.range N
  let p : ℕ → ℝ := fun i => μ.real (A i)
  have hinner :
      ∀ i ∈ r,
        (∑ j ∈ r, μ.real (A i ∩ A j)) ≤
          p i * (∑ j ∈ r, p j) + p i := by
    intro i hi
    calc
      (∑ j ∈ r, μ.real (A i ∩ A j)) ≤
          ∑ j ∈ r, (p i * p j + if j = i then p i else 0) := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hji : j = i
            · subst j
              simp only [p, inter_self]
              simp
              nlinarith [sq_nonneg (μ.real (A i))]
            · have hij : i ≠ j := Ne.symm hji
              rw [measureReal_inter_eq_mul_of_indep μ (hpair hij)]
              simp [p, hji]
      _ = p i * (∑ j ∈ r, p j) + p i := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
            simp [hi]
  calc
    pairwiseSecondSum μ A N =
        ∑ i ∈ r, ∑ j ∈ r, μ.real (A i ∩ A j) := by
          rfl
    _ ≤ ∑ i ∈ r, (p i * (∑ j ∈ r, p j) + p i) := by
          exact Finset.sum_le_sum hinner
    _ = (∑ i ∈ r, p i) ^ 2 + ∑ i ∈ r, p i := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          ring
    _ = pairwiseFirstSum μ A N ^ 2 + pairwiseFirstSum μ A N := by
          rfl

/-- **Second Borel-Cantelli under pairwise independence.**

Let `A n` be measurable events in a probability space.  If distinct events are pairwise
independent and the partial sums of their probabilities diverge to `+∞`, then infinitely many
of the events occur with probability one.

The hypothesis is only pairwise independence; mutual independence is not assumed. -/
theorem measure_limsup_eq_one_of_pairwise_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hpair : ∀ ⦃i j : ℕ⦄, i ≠ j → ProbabilityTheory.IndepSet (A i) (A j) μ)
    (hdiv :
      Tendsto
        (fun N => ∑ i ∈ Finset.range N, μ.real (A i))
        atTop atTop) :
    μ (Filter.limsup A atTop) = 1 := by
  classical
  let S : ℕ → ℝ := pairwiseFirstSum μ A
  let T : ℕ → ℝ := pairwiseSecondSum μ A
  let R : ℕ → ℝ := pairwiseRatio μ A

  have hSdiv : Tendsto S atTop atTop := by
    change Tendsto
      (fun N => ∑ i ∈ Finset.range N, μ.real (A i))
      atTop atTop
    exact hdiv

  have hR_nonneg : ∀ N, 0 ≤ R N := by
    intro N
    simpa [R] using pairwiseRatio_nonneg μ A N

  have hR_le_one : ∀ N, R N ≤ 1 := by
    intro N
    simpa [R] using pairwiseRatio_le_one μ A hA N

  have hR_bdd : IsBoundedUnder (· ≤ ·) atTop R :=
    isBoundedUnder_of ⟨1, hR_le_one⟩

  have hlimsup_lower {a : ℝ} (ha : a < 1) :
      a ≤ Filter.limsup R atTop := by
    by_cases ha_neg : a < 0
    · exact ha_neg.le.trans
        (le_limsup_of_frequently_le
          (Frequently.of_forall hR_nonneg) hR_bdd)
    have ha_nonneg : 0 ≤ a := le_of_not_gt ha_neg
    have hone : 0 < 1 - a := sub_pos.mpr ha
    let K : ℝ := max 1 (a / (1 - a) + 1)
    have hSK : ∀ᶠ N in atTop, K < S N :=
      hSdiv.eventually_gt_atTop K
    have hEventually : ∀ᶠ N in atTop, a ≤ R N := by
      filter_upwards [hSK] with N hKN
      have hSpos : 0 < S N := by
        have h1K : 1 ≤ K := le_max_left _ _
        linarith
      have hTpos : 0 < T N := by
        have hST :
            S N ≤ T N := by
          simpa [S, T] using pairwiseFirstSum_le_secondSum μ A N
        exact hSpos.trans_le hST
      have hTle :
          T N ≤ S N ^ 2 + S N := by
        simpa [S, T] using
          pairwiseSecondSum_le_sq_add_first μ A hpair N
      have hthreshold : a / (1 - a) < S N := by
        have hK :
            a / (1 - a) + 1 ≤ K := le_max_right _ _
        linarith
      have hlinear : a < (1 - a) * S N := by
        have := (div_lt_iff₀ hone).1 hthreshold
        nlinarith
      have hquad :
          a * (S N ^ 2 + S N) < S N ^ 2 := by
        nlinarith [mul_pos hSpos hSpos]
      have haT : a * T N < S N ^ 2 :=
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hTle ha_nonneg)
          hquad
      have haR : a < R N := by
        dsimp [R, pairwiseRatio]
        exact (lt_div_iff₀ hTpos).2 haT
      exact haR.le
    exact le_limsup_of_frequently_le hEventually.frequently hR_bdd

  have hlimsup_ge_one : 1 ≤ Filter.limsup R atTop := by
    rw [← forall_lt_iff_le]
    intro a ha
    obtain ⟨b, hab, hb⟩ := exists_between ha
    exact hab.trans_le (hlimsup_lower hb)

  have hKS :=
    kochenStone μ A hA hdiv
  have hKS' :
      Filter.limsup R atTop ≤ μ.real (Filter.limsup A atTop) := by
    change Filter.limsup
        (fun N =>
          ((∑ i ∈ Finset.range N, μ.real (A i)) ^ 2) /
            (∑ i ∈ Finset.range N,
              ∑ j ∈ Finset.range N, μ.real (A i ∩ A j)))
        atTop ≤
      μ.real (Filter.limsup A atTop)
    exact hKS

  have hreal_ge :
      1 ≤ μ.real (Filter.limsup A atTop) :=
    hlimsup_ge_one.trans hKS'
  have hreal_le :
      μ.real (Filter.limsup A atTop) ≤ 1 :=
    measureReal_le_one
  have hreal :
      μ.real (Filter.limsup A atTop) = 1 :=
    le_antisymm hreal_le hreal_ge
  apply (ENNReal.toReal_eq_one_iff (μ (Filter.limsup A atTop))).mp
  simpa [measureReal_def] using hreal

end LeanFrontier.ProbabilityTheory
