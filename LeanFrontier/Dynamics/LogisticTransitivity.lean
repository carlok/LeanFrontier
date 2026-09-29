import LeanFrontier.Dynamics.LogisticConjugacy
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Dynamics.Flow
import Mathlib.Dynamics.Transitive
import Mathlib.Tactic

/-!
# Topological transitivity of the full tent and logistic maps

The accepted Ulam homeomorphism conjugates the full tent map on `[0,1]` with the
parameter-four logistic map. This module supplies a global orbit-spreading theorem for that
conjugate pair.

The direct tent-map proof uses its two inverse branches. Given a source point `x` and a target
`y`, one can pull `y` backward while following the branch itinerary of `x`. Each backward
step halves distances, so after `n` steps the resulting exact `n`-fold preimage of `y` is
within `2⁻ⁿ` of `x`. Hence every nonempty open set contains a point whose orbit reaches any
other prescribed nonempty open set.

The result is packaged through Mathlib's `Flow.fromIter` and
`AddAction.IsTopologicallyTransitive` APIs, and then transported across
`ulamHomeomorph` to the logistic map.
-/

namespace LeanFrontier.Dynamics

open Real Set

local notation "𝕀" => Icc (0 : ℝ) 1

private def continuous_tentMap : Continuous tentMap := by
  unfold tentMap
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
  intro x hx
  change x = 1 / 2 at hx
  nlinarith

private def continuous_logisticMap : Continuous logisticMap := by
  unfold logisticMap
  fun_prop

private def continuous_tentMapIcc : Continuous tentMapIcc :=
  Continuous.subtype_mk (continuous_tentMap.comp continuous_subtype_val) _

private def continuous_logisticMapIcc : Continuous logisticMapIcc :=
  Continuous.subtype_mk (continuous_logisticMap.comp continuous_subtype_val) _

/-- The natural-number flow obtained by iterating the full tent map on the unit interval. -/
noncomputable def tentMapFlow : Flow ℕ 𝕀 :=
  Flow.fromIter continuous_tentMapIcc

/-- The natural-number flow obtained by iterating the parameter-four logistic map. -/
noncomputable def logisticMapFlow : Flow ℕ 𝕀 :=
  Flow.fromIter continuous_logisticMapIcc

/-- Pull a point one step backward through the branch of the tent map containing `x`. -/
private noncomputable def tentPullbackStep (x y : 𝕀) : 𝕀 :=
  if (x : ℝ) ≤ 1 / 2 then
    ⟨(y : ℝ) / 2, by
      constructor <;> nlinarith [y.property.1, y.property.2]⟩
  else
    ⟨1 - (y : ℝ) / 2, by
      constructor <;> nlinarith [y.property.1, y.property.2]⟩

private theorem tentMapIcc_pullbackStep (x y : 𝕀) :
    tentMapIcc (tentPullbackStep x y) = y := by
  apply Subtype.ext
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · simp only [tentPullbackStep, hx, if_pos]
    change tentMap ((y : ℝ) / 2) = (y : ℝ)
    rw [tentMap_of_le (by linarith [y.property.2])]
    ring
  · simp only [tentPullbackStep, hx, if_neg]
    change tentMap (1 - (y : ℝ) / 2) = (y : ℝ)
    unfold tentMap
    by_cases hhalf : 1 - (y : ℝ) / 2 ≤ 1 / 2
    · rw [if_pos hhalf]
      nlinarith [y.property.2]
    · rw [if_neg hhalf]
      ring

private theorem tentPullbackStep_map (x : 𝕀) :
    tentPullbackStep x (tentMapIcc x) = x := by
  apply Subtype.ext
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · simp only [tentPullbackStep, hx, if_pos]
    change tentMap (x : ℝ) / 2 = (x : ℝ)
    rw [tentMap_of_le hx]
    ring
  · simp only [tentPullbackStep, hx, if_neg]
    change 1 - tentMap (x : ℝ) / 2 = (x : ℝ)
    rw [tentMap_of_half_lt (lt_of_not_ge hx)]
    ring

private theorem dist_tentPullbackStep (x y z : 𝕀) :
    dist (tentPullbackStep x y) (tentPullbackStep x z) = dist y z / 2 := by
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · simp only [tentPullbackStep, hx, if_pos]
    change dist ((y : ℝ) / 2) ((z : ℝ) / 2) = dist (y : ℝ) (z : ℝ) / 2
    rw [Real.dist_eq, Real.dist_eq]
    have hsub :
        (y : ℝ) / 2 - (z : ℝ) / 2 = ((y : ℝ) - (z : ℝ)) / 2 := by
      ring
    rw [hsub, abs_div]
    norm_num
  · simp only [tentPullbackStep, hx, if_neg]
    change
      dist (1 - (y : ℝ) / 2) (1 - (z : ℝ) / 2) =
        dist (y : ℝ) (z : ℝ) / 2
    rw [Real.dist_eq, Real.dist_eq]
    have hsub :
        (1 - (y : ℝ) / 2) - (1 - (z : ℝ) / 2) =
          -(((y : ℝ) - (z : ℝ)) / 2) := by
      ring
    rw [hsub, abs_neg, abs_div]
    norm_num

/-- Pull `y` backward by `n` tent-map steps while following the first `n` branches of
the orbit of `x`. -/
private noncomputable def tentPullback : ℕ → 𝕀 → 𝕀 → 𝕀
  | 0, _x, y => y
  | n + 1, x, y => tentPullbackStep x (tentPullback n (tentMapIcc x) y)

private theorem tentMapIcc_iterate_pullback (n : ℕ) (x y : 𝕀) :
    tentMapIcc^[n] (tentPullback n x y) = y := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      rw [tentPullback, Function.iterate_succ_apply]
      rw [tentMapIcc_pullbackStep]
      exact ih (tentMapIcc x)

private theorem dist_tentPullback_le (n : ℕ) (x y : 𝕀) :
    dist (tentPullback n x y) x ≤ (1 / 2 : ℝ) ^ n := by
  induction n generalizing x with
  | zero =>
      change |(y : ℝ) - (x : ℝ)| ≤ 1
      rw [abs_le]
      constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]
  | succ n ih =>
      rw [tentPullback]
      calc
        dist (tentPullbackStep x (tentPullback n (tentMapIcc x) y)) x =
            dist
              (tentPullbackStep x (tentPullback n (tentMapIcc x) y))
              (tentPullbackStep x (tentMapIcc x)) := by
                rw [tentPullbackStep_map]
        _ = dist (tentPullback n (tentMapIcc x) y) (tentMapIcc x) / 2 :=
          dist_tentPullbackStep x _ _
        _ ≤ ((1 / 2 : ℝ) ^ n) / 2 := by
          gcongr
          exact ih (tentMapIcc x)
        _ = (1 / 2 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring

private theorem tentMapIcc_exists_iterate_mem
    {U V : Set 𝕀}
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVne : V.Nonempty) :
    ∃ n : ℕ, ∃ x ∈ U, tentMapIcc^[n] x ∈ V := by
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨y, hyV⟩ := hVne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo x hxU
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  let z : 𝕀 := tentPullback n x y
  have hzdist : dist z x < ε :=
    (dist_tentPullback_le n x y).trans_lt hn
  have hzU : z ∈ U := by
    apply hball
    simpa only [Metric.mem_ball', dist_comm] using hzdist
  refine ⟨n, z, hzU, ?_⟩
  rw [tentMapIcc_iterate_pullback]
  exact hyV

/-- The iteration flow of the full tent map on `[0,1]` is topologically transitive. -/
theorem tentMapFlow_isTopologicallyTransitive :
    @AddAction.IsTopologicallyTransitive ℕ 𝕀 _ _ tentMapFlow.toAddAction := by
  letI : AddAction ℕ 𝕀 := tentMapFlow.toAddAction
  refine ⟨?_⟩
  intro U V hUo hUne hVo hVne
  obtain ⟨n, x, hxU, hxV⟩ :=
    tentMapIcc_exists_iterate_mem hUo hUne hVo hVne
  refine ⟨n, ⟨tentMapIcc^[n] x, ?_, hxV⟩⟩
  change tentMapIcc^[n] x ∈ (fun z => tentMapIcc^[n] z) '' U
  exact ⟨x, hxU, rfl⟩

private theorem logisticMapIcc_exists_iterate_mem
    {U V : Set 𝕀}
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVne : V.Nonempty) :
    ∃ n : ℕ, ∃ x ∈ U, logisticMapIcc^[n] x ∈ V := by
  let U' : Set 𝕀 := (ulamHomeomorph : 𝕀 → 𝕀) ⁻¹' U
  let V' : Set 𝕀 := (ulamHomeomorph : 𝕀 → 𝕀) ⁻¹' V
  have hU'o : IsOpen U' := hUo.preimage ulamHomeomorph.continuous
  have hV'o : IsOpen V' := hVo.preimage ulamHomeomorph.continuous
  have hU'ne : U'.Nonempty := by
    obtain ⟨u, hu⟩ := hUne
    refine ⟨ulamHomeomorph.symm u, ?_⟩
    simpa [U'] using hu
  have hV'ne : V'.Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨ulamHomeomorph.symm v, ?_⟩
    simpa [V'] using hv
  obtain ⟨n, x, hxU, hxV⟩ :=
    tentMapIcc_exists_iterate_mem hU'o hU'ne hV'o hV'ne
  change ulamHomeomorph x ∈ U at hxU
  change ulamHomeomorph (tentMapIcc^[n] x) ∈ V at hxV
  refine ⟨n, ulamHomeomorph x, hxU, ?_⟩
  have hs :=
    ulamHomeomorph_semiconj_tentMap_logisticMap.iterate_right n x
  rw [← hs]
  exact hxV

/-- The iteration flow of the parameter-four logistic map on `[0,1]` is topologically
transitive, transported through the accepted Ulam homeomorphism. -/
theorem logisticMapFlow_isTopologicallyTransitive :
    @AddAction.IsTopologicallyTransitive ℕ 𝕀 _ _ logisticMapFlow.toAddAction := by
  letI : AddAction ℕ 𝕀 := logisticMapFlow.toAddAction
  refine ⟨?_⟩
  intro U V hUo hUne hVo hVne
  obtain ⟨n, x, hxU, hxV⟩ :=
    logisticMapIcc_exists_iterate_mem hUo hUne hVo hVne
  refine ⟨n, ⟨logisticMapIcc^[n] x, ?_, hxV⟩⟩
  change logisticMapIcc^[n] x ∈ (fun z => logisticMapIcc^[n] z) '' U
  exact ⟨x, hxU, rfl⟩

end LeanFrontier.Dynamics
