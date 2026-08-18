import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The tent map is semiconjugate to the logistic map

The logistic map at parameter four, `x ↦ 4 * x * (1 - x)`, and the tent map,
`x ↦ 2 * x` on `[0, 1/2]` and `x ↦ 2 * (1 - x)` on `[1/2, 1]`, are the two standard model
examples of chaotic interval dynamics. The classical bridge between them is the
Ulam-von Neumann change of variables `x ↦ sin (π * x / 2) ^ 2`, which intertwines the two
maps: `h ∘ tentMap = logisticMap ∘ h`. Every statement about iterates of the tent map is
transported by `h` to the logistic map; this is how the logistic map at parameter four is
proved chaotic in textbooks.

## Main definitions

* `LeanFrontier.Dynamics.tentMap`, `LeanFrontier.Dynamics.logisticMap` - the two interval maps, defined on all
  of `ℝ`.

## Main statements

* `LeanFrontier.Dynamics.sin_sq_semiconj_tentMap_logisticMap` - the semiconjugacy
  `sin (π * tentMap x / 2) ^ 2 = logisticMap (sin (π * x / 2) ^ 2)`, packaged as
  `Function.Semiconj`.
* `LeanFrontier.Dynamics.sin_sq_tentMap_iterate` - the same for `n`-fold iterates.
* `LeanFrontier.Dynamics.tentMap_mem_Icc`, `LeanFrontier.Dynamics.logisticMap_mem_Icc` - both maps send
  `[0, 1]` into itself.
* `LeanFrontier.Dynamics.logisticMap_eq_self_iff` - the fixed points of the logistic map are exactly
  `0` and `3/4`.
* `LeanFrontier.Dynamics.isPeriodicPt_logisticMap_two` and
  `LeanFrontier.Dynamics.logisticMap_apply_ne_self_of_period_two` - `(5 + √5)/8` and `(5 - √5)/8`
  form a genuine two-cycle of the logistic map.

## Implementation notes

Both maps are defined on all of `ℝ`, with the interval statements recorded separately as
`mem_Icc` lemmas; this keeps the definitions equation-friendly and matches how Mathlib treats
interval maps such as `Complex.exp` restrictions. The semiconjugacy needs only two
ingredients, the double angle formula and `sin (π - x) = sin x`, one for each branch of the
tent map; both branches reduce to the same identity
`sin (π * x) ^ 2 = logisticMap (sin (π * x / 2) ^ 2)`, which is `sin_sq_pi_mul` below.

The two-cycle equations are polynomial identities in `√5` and are closed by
`linear_combination` from `√5 ^ 2 = 5`; no numerical reasoning is involved.
-/

namespace LeanFrontier.Dynamics

open Real

/-- The tent map: the piecewise linear map of the unit interval with slope `2` up on
`[0, 1/2]` and slope `2` down on `[1/2, 1]`, extended to all of `ℝ` by the same formula. -/
noncomputable def tentMap (x : ℝ) : ℝ := if x ≤ 1 / 2 then 2 * x else 2 * (1 - x)

/-- The logistic map at parameter four, `x ↦ 4 * x * (1 - x)`, extended to all of `ℝ`. -/
def logisticMap (x : ℝ) : ℝ := 4 * x * (1 - x)

theorem tentMap_of_le {x : ℝ} (h : x ≤ 1 / 2) : tentMap x = 2 * x := if_pos h

theorem tentMap_of_half_lt {x : ℝ} (h : 1 / 2 < x) : tentMap x = 2 * (1 - x) :=
  if_neg (not_le.mpr h)

/-- The identity behind both branches of the semiconjugacy: doubling the angle inside
`sin ^ 2` is applying the logistic map outside. -/
theorem sin_sq_pi_mul (x : ℝ) : sin (π * x) ^ 2 = logisticMap (sin (π * x / 2) ^ 2) := by
  conv_lhs => rw [show π * x = 2 * (π * x / 2) by ring]
  rw [logisticMap, sin_two_mul, ← cos_sq']
  ring

/-- The Ulam-von Neumann semiconjugacy: `x ↦ sin (π * x / 2) ^ 2` intertwines the tent map
and the logistic map. -/
theorem sin_sq_semiconj_tentMap_logisticMap :
    Function.Semiconj (fun x => sin (π * x / 2) ^ 2) tentMap logisticMap := by
  intro x
  rcases le_or_gt x (1 / 2) with hx | hx
  · show sin (π * tentMap x / 2) ^ 2 = logisticMap (sin (π * x / 2) ^ 2)
    rw [tentMap_of_le hx]
    have h : π * (2 * x) / 2 = π * x := by ring
    rw [h]
    exact sin_sq_pi_mul x
  · show sin (π * tentMap x / 2) ^ 2 = logisticMap (sin (π * x / 2) ^ 2)
    rw [tentMap_of_half_lt hx]
    have h : π * (2 * (1 - x)) / 2 = π - π * x := by ring
    rw [h, sin_pi_sub]
    exact sin_sq_pi_mul x

/-- The semiconjugacy transports every iterate of the tent map to the corresponding iterate
of the logistic map. -/
theorem sin_sq_tentMap_iterate (n : ℕ) (x : ℝ) :
    sin (π * tentMap^[n] x / 2) ^ 2 = logisticMap^[n] (sin (π * x / 2) ^ 2) :=
  (sin_sq_semiconj_tentMap_logisticMap.iterate_right n) x

/-- The tent map sends the unit interval into itself. -/
theorem tentMap_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    tentMap x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  rcases le_or_gt x (1 / 2) with h | h
  · rw [Set.mem_Icc, tentMap_of_le h]
    constructor <;> linarith
  · rw [Set.mem_Icc, tentMap_of_half_lt h]
    constructor <;> linarith

/-- The logistic map sends the unit interval into itself. -/
theorem logisticMap_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    logisticMap x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  rw [Set.mem_Icc]
  constructor
  · simp only [logisticMap]
    nlinarith
  · simp only [logisticMap]
    nlinarith [sq_nonneg (1 - 2 * x)]

/-- The fixed points of the logistic map are exactly `0` and `3/4`. -/
theorem logisticMap_eq_self_iff {x : ℝ} : logisticMap x = x ↔ x = 0 ∨ x = 3 / 4 := by
  constructor
  · intro h
    have h' : x * (3 - 4 * x) = 0 := by
      simp only [logisticMap] at h
      linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h34
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num [logisticMap]

/-- The logistic map exchanges `(5 + √5)/8` and `(5 - √5)/8`. -/
theorem logisticMap_five_add_sqrt_five :
    logisticMap ((5 + Real.sqrt 5) / 8) = (5 - Real.sqrt 5) / 8 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [logisticMap]
  linear_combination (-(1 : ℝ) / 16) * h5

/-- The logistic map exchanges `(5 - √5)/8` and `(5 + √5)/8`. -/
theorem logisticMap_five_sub_sqrt_five :
    logisticMap ((5 - Real.sqrt 5) / 8) = (5 + Real.sqrt 5) / 8 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [logisticMap]
  linear_combination (-(1 : ℝ) / 16) * h5

/-- `(5 + √5)/8` is a periodic point of the logistic map of period two. -/
theorem isPeriodicPt_logisticMap_two :
    Function.IsPeriodicPt logisticMap 2 ((5 + Real.sqrt 5) / 8) := by
  show logisticMap^[2] ((5 + Real.sqrt 5) / 8) = (5 + Real.sqrt 5) / 8
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [logisticMap_five_add_sqrt_five, logisticMap_five_sub_sqrt_five]

/-- The two-cycle is genuine: `(5 + √5)/8` is not a fixed point, so its period is exactly
two. -/
theorem logisticMap_apply_ne_self_of_period_two :
    logisticMap ((5 + Real.sqrt 5) / 8) ≠ (5 + Real.sqrt 5) / 8 := by
  rw [logisticMap_five_add_sqrt_five]
  intro h
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have : Real.sqrt 5 = 0 := by linarith
  linarith

end LeanFrontier.Dynamics
