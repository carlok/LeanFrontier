import LeanFrontier.Dynamics.LogisticMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-!
# The tent and logistic maps are topologically conjugate on the unit interval

The accepted `LogisticMap` module proves the classical Ulam-von Neumann semiconjugacy

`x ↦ sin (π * x / 2) ^ 2`

between the full tent map and the logistic map at parameter four.  On the unit interval this
change of variables is a homeomorphism, so the semiconjugacy is in fact a topological conjugacy.

This module packages that missing structural layer.

The forward map is first restricted to the subtype `Set.Icc (0 : ℝ) 1`.  Surjectivity is proved
with the explicit preimage

`2 * arcsin (sqrt y) / π`.

Injectivity uses positivity of sine on `[0, π / 2]` together with Mathlib's injectivity of sine
on `[-π / 2, π / 2]`.  Since the closed unit interval is compact and Hausdorff, Mathlib's
`Continuous.homeoOfEquivCompactToT2` upgrades the resulting continuous equivalence to a
homeomorphism without duplicating a separate inverse-continuity proof.

Finally the accepted real-valued semiconjugacy is lifted to the interval self-maps.  Thus the
homeomorphism intertwines the tent and logistic dynamics as genuine subtype self-maps.
-/

namespace LeanFrontier.Dynamics

open Real Set

/-- The Ulam-von Neumann change of variables used in the accepted tent/logistic
semiconjugacy. -/
noncomputable def ulamMap (x : ℝ) : ℝ :=
  sin (π * x / 2) ^ 2

/-- The Ulam map always takes values in the closed unit interval. -/
theorem ulamMap_mem_Icc (x : ℝ) :
    ulamMap x ∈ Icc (0 : ℝ) 1 := by
  rw [mem_Icc]
  exact ⟨sq_nonneg _, sin_sq_le_one _⟩

/-- The Ulam map restricted as a self-map of the unit interval. -/
noncomputable def ulamMapIcc :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨ulamMap x, ulamMap_mem_Icc x⟩

/-- The real-valued Ulam map is continuous. -/
theorem continuous_ulamMap : Continuous ulamMap := by
  unfold ulamMap
  fun_prop

/-- The subtype Ulam map is continuous. -/
theorem continuous_ulamMapIcc : Continuous ulamMapIcc := by
  exact Continuous.subtype_mk
    (continuous_ulamMap.comp continuous_subtype_val) _

private theorem angle_mem_sin_injective_interval
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    π * x / 2 ∈ Icc (-(π / 2)) (π / 2) := by
  constructor
  · have hp : 0 < π := pi_pos
    have hx0 : 0 ≤ x := hx.1
    nlinarith
  · have hp : 0 < π := pi_pos
    have hx1 : x ≤ 1 := hx.2
    nlinarith

private theorem sin_angle_nonneg
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ sin (π * x / 2) := by
  have hangle := angle_mem_sin_injective_interval hx
  exact sin_nonneg_of_nonneg_of_le_pi
    (by
      have hp : 0 < π := pi_pos
      have hx0 : 0 ≤ x := hx.1
      nlinarith)
    (by
      have hp : 0 < π := pi_pos
      have hle := hangle.2
      nlinarith)

/-- The Ulam map is injective on the closed unit interval. -/
theorem ulamMapIcc_injective : Function.Injective ulamMapIcc := by
  intro x y hxy
  have hval := congrArg Subtype.val hxy
  change ulamMap (x : ℝ) = ulamMap (y : ℝ) at hval
  have hsx : 0 ≤ sin (π * (x : ℝ) / 2) :=
    sin_angle_nonneg x.property
  have hsy : 0 ≤ sin (π * (y : ℝ) / 2) :=
    sin_angle_nonneg y.property
  have hsin :
      sin (π * (x : ℝ) / 2) = sin (π * (y : ℝ) / 2) := by
    unfold ulamMap at hval
    nlinarith
  have hangle :
      π * (x : ℝ) / 2 = π * (y : ℝ) / 2 :=
    injOn_sin
      (angle_mem_sin_injective_interval x.property)
      (angle_mem_sin_injective_interval y.property)
      hsin
  apply Subtype.ext
  have hp : 0 < π := pi_pos
  nlinarith

/-- The Ulam map is surjective on the closed unit interval.

A point `y ∈ [0,1]` has the explicit preimage
`2 * arcsin (sqrt y) / π`. -/
theorem ulamMapIcc_surjective : Function.Surjective ulamMapIcc := by
  intro y
  let a : ℝ := arcsin (sqrt (y : ℝ))
  let x : ℝ := 2 * a / π
  have hy0 : 0 ≤ (y : ℝ) := y.property.1
  have hy1 : (y : ℝ) ≤ 1 := y.property.2
  have hs0 : 0 ≤ sqrt (y : ℝ) := sqrt_nonneg _
  have hs1 : sqrt (y : ℝ) ≤ 1 := sqrt_le_one.mpr hy1
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact arcsin_nonneg.mpr hs0
  have ha1 : a ≤ π / 2 := by
    dsimp [a]
    exact arcsin_le_pi_div_two _
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (mul_nonneg (by norm_num) ha0) pi_pos.le
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ pi_pos).2
    nlinarith
  let xs : Icc (0 : ℝ) 1 := ⟨x, hx0, hx1⟩
  refine ⟨xs, ?_⟩
  apply Subtype.ext
  change ulamMap x = (y : ℝ)
  have hangle : π * x / 2 = a := by
    dsimp [x]
    field_simp [ne_of_gt pi_pos]
  have hsin : sin a = sqrt (y : ℝ) := by
    dsimp [a]
    exact sin_arcsin (by linarith) hs1
  rw [ulamMap, hangle, hsin, sq_sqrt hy0]

/-- The Ulam map is a bijection of the closed unit interval. -/
theorem ulamMapIcc_bijective : Function.Bijective ulamMapIcc :=
  ⟨ulamMapIcc_injective, ulamMapIcc_surjective⟩

/-- The Ulam-von Neumann change of variables as a homeomorphism of `[0,1]`.

Compactness of the source interval and Hausdorffness of the target turn the continuous
bijection into a homeomorphism. -/
noncomputable def ulamHomeomorph :
    Icc (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ulamMapIcc ulamMapIcc_bijective)
    (by
      simpa only [Equiv.ofBijective_apply] using continuous_ulamMapIcc)

/-- The forward map of `ulamHomeomorph` is the accepted Ulam change of variables. -/
@[simp]
theorem ulamHomeomorph_apply (x : Icc (0 : ℝ) 1) :
    (ulamHomeomorph x : ℝ) = ulamMap (x : ℝ) := by
  rfl

/-- The tent map restricted as a self-map of the closed unit interval. -/
noncomputable def tentMapIcc :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨tentMap x, tentMap_mem_Icc x.property⟩

/-- The logistic map at parameter four restricted as a self-map of the closed unit interval. -/
def logisticMapIcc :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨logisticMap x, logisticMap_mem_Icc x.property⟩

/-- The Ulam homeomorphism gives a genuine topological conjugacy between the tent and logistic
self-maps of the closed unit interval. -/
theorem ulamHomeomorph_semiconj_tentMap_logisticMap :
    Function.Semiconj
      (ulamHomeomorph : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)
      tentMapIcc logisticMapIcc := by
  intro x
  apply Subtype.ext
  change
    ulamMap (tentMap (x : ℝ)) =
      logisticMap (ulamMap (x : ℝ))
  simpa only [ulamMap] using
    sin_sq_semiconj_tentMap_logisticMap (x : ℝ)

end LeanFrontier.Dynamics
