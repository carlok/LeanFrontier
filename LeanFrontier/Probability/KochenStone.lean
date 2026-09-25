import LeanFrontier.Probability.ChungErdos
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Order.LiminfLimsup
import Mathlib.Probability.BorelCantelli
import Mathlib.Tactic

/-!
# Kochen-Stone lower bound

This module proves the classical Kochen-Stone refinement of the second Borel-Cantelli lemma from
the accepted finite Chung-Erdős inequality.

For measurable events `A n` in a probability space, assume that the partial sums of their
probabilities diverge to `+∞`. Then

`P(limsup A) ≥ limsup_N (sum_{i < N} P(A i))^2 /
                    (sum_{i,j < N} P(A i ∩ A j))`.

No independence hypothesis is used.

The proof follows the classical Chung-Erdős tail argument. For a fixed tail start `m`, apply the
finite Chung-Erdős inequality to `A m, ..., A (N-1)`. Divergence of the first-moment partial sums
makes the omitted finite prefix negligible compared with a sufficiently large prefix. This shows
that the same prefix-ratio limsup is a lower bound for every infinite tail union. Continuity from
above then identifies the intersection of those tail unions with the set-theoretic limsup.

The theorem is stated in terms of `Measure.real`, matching the accepted Chung-Erdős interface.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace LeanFrontier.ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

private def firstSum (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, μ.real (A i)

private def secondSum (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, μ.real (A i ∩ A j)

private noncomputable def ksRatio (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) : ℝ :=
  firstSum μ A N ^ 2 / secondSum μ A N

private def tailUnion (A : ℕ → Set Ω) (m : ℕ) : Set Ω :=
  ⋃ n : ℕ, ⋃ (_ : m ≤ n), A n

private theorem firstSum_nonneg (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    0 ≤ firstSum μ A N := by
  dsimp [firstSum]
  exact Finset.sum_nonneg fun i hi => measureReal_nonneg

private theorem secondSum_nonneg (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    0 ≤ secondSum μ A N := by
  dsimp [secondSum]
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj => measureReal_nonneg

private theorem firstSum_le_secondSum (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    firstSum μ A N ≤ secondSum μ A N := by
  dsimp [firstSum, secondSum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    μ.real (A i) = μ.real (A i ∩ A i) := by rw [inter_self]
    _ ≤ ∑ j ∈ Finset.range N, μ.real (A i ∩ A j) := by
      exact Finset.single_le_sum
        (f := fun j => μ.real (A i ∩ A j))
        (fun j hj => measureReal_nonneg)
        hi

private theorem secondSum_pos_of_firstSum_pos
    (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ)
    (h : 0 < firstSum μ A N) :
    0 < secondSum μ A N :=
  h.trans_le (firstSum_le_secondSum μ A N)

private theorem ksRatio_nonneg (μ : Measure Ω) (A : ℕ → Set Ω) (N : ℕ) :
    0 ≤ ksRatio μ A N := by
  dsimp [ksRatio]
  exact div_nonneg (sq_nonneg _) (secondSum_nonneg μ A N)

private theorem ksRatio_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (N : ℕ) :
    ksRatio μ A N ≤ 1 := by
  by_cases hS : firstSum μ A N = 0
  · simp [ksRatio, hS]
  have hSpos : 0 < firstSum μ A N :=
    lt_of_le_of_ne (firstSum_nonneg μ A N) (Ne.symm hS)
  have hTpos := secondSum_pos_of_firstSum_pos μ A N hSpos
  have hce :=
    chungErdos μ (Finset.range N) A
      (fun i hi => hA i)
      (by simpa [secondSum] using hTpos)
  have hunion : μ.real (⋃ i ∈ Finset.range N, A i) ≤ 1 :=
    measureReal_le_one
  have hce' :
      ksRatio μ A N ≤ μ.real (⋃ i ∈ Finset.range N, A i) := by
    simpa [ksRatio, firstSum, secondSum] using hce
  exact hce'.trans hunion

private theorem tailUnion_measurable
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (m : ℕ) :
    MeasurableSet (tailUnion A m) := by
  dsimp [tailUnion]
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun hmn => hA n

omit [MeasurableSpace Ω] in
private theorem tailUnion_antitone (A : ℕ → Set Ω) :
    Antitone (tailUnion A) := by
  intro m n hmn ω hω
  simp only [tailUnion, mem_iUnion] at hω ⊢
  rcases hω with ⟨k, hk, hω⟩
  exact ⟨k, ⟨hmn.trans hk, hω⟩⟩

omit [MeasurableSpace Ω] in
private theorem limsup_eq_iInter_tailUnion (A : ℕ → Set Ω) :
    Filter.limsup A atTop = ⋂ m, tailUnion A m := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
  rfl

private theorem tail_first_eq_sub
    (μ : Measure Ω) (A : ℕ → Set Ω) {m N : ℕ} (hmN : m ≤ N) :
    (∑ i ∈ Finset.Ico m N, μ.real (A i)) =
      firstSum μ A N - firstSum μ A m := by
  rw [Finset.sum_Ico_eq_sub _ hmN]
  rfl

private theorem tail_second_le_prefix_second
    (μ : Measure Ω) (A : ℕ → Set Ω) {m N : ℕ} (_hmN : m ≤ N) :
    (∑ i ∈ Finset.Ico m N, ∑ j ∈ Finset.Ico m N, μ.real (A i ∩ A j)) ≤
      secondSum μ A N := by
  dsimp [secondSum]
  calc
    (∑ i ∈ Finset.Ico m N,
        ∑ j ∈ Finset.Ico m N, μ.real (A i ∩ A j)) ≤
        ∑ i ∈ Finset.Ico m N,
          ∑ j ∈ Finset.range N, μ.real (A i ∩ A j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.2 (Finset.mem_Ico.1 hj).2
      · intro j hjRange hjNot
        exact measureReal_nonneg
    _ ≤ ∑ i ∈ Finset.range N,
          ∑ j ∈ Finset.range N, μ.real (A i ∩ A j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
      · intro i hiRange hiNot
        exact Finset.sum_nonneg fun j hj => measureReal_nonneg

private theorem tail_first_le_tail_second
    (μ : Measure Ω) (A : ℕ → Set Ω) {m N : ℕ} :
    (∑ i ∈ Finset.Ico m N, μ.real (A i)) ≤
      ∑ i ∈ Finset.Ico m N, ∑ j ∈ Finset.Ico m N, μ.real (A i ∩ A j) := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    μ.real (A i) = μ.real (A i ∩ A i) := by rw [inter_self]
    _ ≤ ∑ j ∈ Finset.Ico m N, μ.real (A i ∩ A j) := by
      exact Finset.single_le_sum
        (f := fun j => μ.real (A i ∩ A j))
        (fun j hj => measureReal_nonneg)
        hi

omit [MeasurableSpace Ω] in
private theorem finiteTailUnion_subset_tailUnion
    (A : ℕ → Set Ω) {m N : ℕ} :
    (⋃ i ∈ Finset.Ico m N, A i) ⊆ tailUnion A m := by
  intro ω hω
  simp only [mem_iUnion] at hω
  rcases hω with ⟨i, hi, hω⟩
  simp only [tailUnion, mem_iUnion]
  exact ⟨i, ⟨(Finset.mem_Ico.1 hi).1, hω⟩⟩

/-- **Kochen-Stone inequality.**

Let `A n` be measurable events in a probability space and suppose their probability partial
sums diverge. Then the probability that infinitely many `A n` occur is bounded below by the
limsup of the Chung-Erdős prefix ratios.

No independence assumption is required. -/
theorem kochenStone (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hdiv :
      Tendsto
        (fun N => ∑ i ∈ Finset.range N, μ.real (A i))
        atTop atTop) :
    Filter.limsup
        (fun N =>
          ((∑ i ∈ Finset.range N, μ.real (A i)) ^ 2) /
            (∑ i ∈ Finset.range N,
              ∑ j ∈ Finset.range N, μ.real (A i ∩ A j)))
        atTop ≤
      μ.real (Filter.limsup A atTop) := by
  classical

  change Filter.limsup (ksRatio μ A) atTop ≤
    μ.real (Filter.limsup A atTop)

  let S : ℕ → ℝ := firstSum μ A
  let T : ℕ → ℝ := secondSum μ A
  let R : ℕ → ℝ := ksRatio μ A

  have hSdiv : Tendsto S atTop atTop := by
    dsimp [S, firstSum]
    exact hdiv

  have hR_nonneg : ∀ N, 0 ≤ R N := by
    intro N
    simpa [R] using ksRatio_nonneg μ A N

  have hR_le_one : ∀ N, R N ≤ 1 := by
    intro N
    simpa [R] using ksRatio_le_one μ A hA N

  have hR_bdd : IsBoundedUnder (· ≤ ·) atTop R :=
    isBoundedUnder_of ⟨1, hR_le_one⟩

  have hR_cobdd : IsCoboundedUnder (· ≤ ·) atTop R :=
    IsCoboundedUnder.of_frequently_ge (Frequently.of_forall hR_nonneg)

  let L : ℝ := Filter.limsup R atTop

  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact le_limsup_of_frequently_le
      (Frequently.of_forall hR_nonneg) hR_bdd

  have htail : ∀ m : ℕ, L ≤ μ.real (tailUnion A m) := by
    intro m
    rw [← forall_lt_iff_le]
    intro a haL
    by_cases ha_neg : a < 0
    · exact ha_neg.trans_le
        (measureReal_nonneg : 0 ≤ μ.real (tailUnion A m))
    have ha_nonneg : 0 ≤ a := le_of_not_gt ha_neg
    obtain ⟨b, hab, hbL⟩ := exists_between haL
    have hb_pos : 0 < b := lt_of_le_of_lt ha_nonneg hab

    have hfreq : ∃ᶠ N in atTop, b < R N := by
      exact frequently_lt_of_lt_limsup hR_cobdd (by simpa [L] using hbL)

    let c : ℝ := S m
    have hc_nonneg : 0 ≤ c := by
      dsimp [c, S]
      exact firstSum_nonneg μ A m

    let K : ℝ := max (c + 1) (2 * b * c / (b - a) + 1)
    have hSK : ∀ᶠ N in atTop, K < S N := by
      exact hSdiv.eventually_gt_atTop K
    have hNm : ∀ᶠ N in atTop, m ≤ N := Ici_mem_atTop m

    obtain ⟨N, hbR, hKS, hmN⟩ :=
      (hfreq.and_eventually (hSK.and hNm)).exists

    have hSc : c < S N := by
      have hKc : c < K := by
        dsimp [K]
        exact lt_of_lt_of_le (lt_add_one c) (le_max_left _ _)
      exact hKc.trans hKS

    have hSpos : 0 < S N := hc_nonneg.trans_lt hSc
    have hTpos : 0 < T N := by
      dsimp [T, S] at hSpos ⊢
      exact secondSum_pos_of_firstSum_pos μ A N hSpos

    have hbR' : b < S N ^ 2 / T N := by
      simpa [R, ksRatio, S, T] using hbR
    have hratio : b * T N < S N ^ 2 :=
      (lt_div_iff₀ hTpos).1 hbR'

    have hba : 0 < b - a := sub_pos.mpr hab
    have hthreshold : 2 * b * c / (b - a) < S N := by
      have hKt : 2 * b * c / (b - a) < K := by
        dsimp [K]
        exact lt_of_lt_of_le
          (lt_add_one (2 * b * c / (b - a)))
          (le_max_right _ _)
      exact hKt.trans hKS
    have hlinear : 2 * b * c < (b - a) * S N := by
      simpa [mul_comm] using (div_lt_iff₀ hba).1 hthreshold

    have hlinmul :
        2 * b * c * S N < (b - a) * S N * S N := by
      exact mul_lt_mul_of_pos_right hlinear hSpos
    have hbc2 : 0 ≤ b * c ^ 2 :=
      mul_nonneg hb_pos.le (sq_nonneg c)
    have hquad :
        a * S N ^ 2 < b * (S N - c) ^ 2 := by
      nlinarith [hlinmul, hbc2]

    have habT :
        a * T N < (S N - c) ^ 2 := by
      by_cases ha_zero : a = 0
      · subst a
        simp only [zero_mul]
        exact sq_pos_of_pos (sub_pos.mpr hSc)
      · have ha_pos : 0 < a :=
          lt_of_le_of_ne ha_nonneg (Ne.symm ha_zero)
        have hscaled : a * (b * T N) < a * S N ^ 2 :=
          mul_lt_mul_of_pos_left hratio ha_pos
        have hbmul : a * b * T N < b * (S N - c) ^ 2 := by
          nlinarith [hscaled, hquad]
        nlinarith [hb_pos, hTpos, hbmul]

    let F : ℝ := ∑ i ∈ Finset.Ico m N, μ.real (A i)
    let D : ℝ :=
      ∑ i ∈ Finset.Ico m N,
        ∑ j ∈ Finset.Ico m N, μ.real (A i ∩ A j)

    have hF : F = S N - c := by
      dsimp [F, S, c]
      exact tail_first_eq_sub μ A hmN

    have hFpos : 0 < F := by
      rw [hF]
      exact sub_pos.mpr hSc

    have hDpos : 0 < D := by
      have hFD :
          F ≤ D := by
        dsimp [F, D]
        exact tail_first_le_tail_second μ A
      exact hFpos.trans_le hFD

    have hDleT : D ≤ T N := by
      dsimp [D, T]
      exact tail_second_le_prefix_second μ A hmN

    have haTD : a * T N < F ^ 2 := by
      rw [hF]
      exact habT

    have haD : a * D < F ^ 2 := by
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hDleT ha_nonneg) haTD

    have haRatio : a < F ^ 2 / D := by
      exact (lt_div_iff₀ hDpos).2 haD

    have hce :=
      chungErdos μ (Finset.Ico m N) A
        (fun i hi => hA i)
        (by simpa [D] using hDpos)

    have hfinite :
        F ^ 2 / D ≤ μ.real (⋃ i ∈ Finset.Ico m N, A i) := by
      simpa [F, D] using hce

    have hmono :
        μ.real (⋃ i ∈ Finset.Ico m N, A i) ≤
          μ.real (tailUnion A m) :=
      measureReal_mono (finiteTailUnion_subset_tailUnion A)

    exact haRatio.trans_le (hfinite.trans hmono)

  have hUmeas : ∀ m, NullMeasurableSet (tailUnion A m) μ := by
    intro m
    exact (tailUnion_measurable A hA m).nullMeasurableSet

  have hUanti : Antitone (tailUnion A) :=
    tailUnion_antitone A

  have hmeasure :
      Tendsto
        (fun m => μ (tailUnion A m))
        atTop
        (𝓝 (μ (⋂ m, tailUnion A m))) := by
    simpa [Function.comp_def] using
      (tendsto_measure_iInter_atTop
        (μ := μ) (s := tailUnion A)
        hUmeas hUanti ⟨0, measure_ne_top μ _⟩)

  have hmeasureReal :
      Tendsto
        (fun m => μ.real (tailUnion A m))
        atTop
        (𝓝 (μ.real (⋂ m, tailUnion A m))) := by
    simpa [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal (measure_ne_top μ (⋂ m, tailUnion A m))).comp hmeasure

  have hfinal :
      L ≤ μ.real (⋂ m, tailUnion A m) :=
    ge_of_tendsto' hmeasureReal htail

  rw [← limsup_eq_iInter_tailUnion A] at hfinal
  simpa [L, R] using hfinal

end LeanFrontier.ProbabilityTheory
