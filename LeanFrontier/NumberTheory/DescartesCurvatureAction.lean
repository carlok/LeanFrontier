import LeanFrontier.NumberTheory.DescartesCircle
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Bundled Descartes curvature vectors and Vieta reflections

The scalar Descartes-circle module already proves that replacing the fourth curvature by
the alternate Vieta root preserves Descartes' relation.  For Apollonian applications it is
more useful to package all four curvatures uniformly and let any coordinate be reflected.

This module introduces a four-curvature vector, its Descartes quadratic form, and one indexed
linear map `curvatureReflection i` covering all four coordinate reflections.  The form is
preserved, every reflection is an involution, and the last-coordinate case specializes exactly
to the accepted scalar `DescartesCircle.reflect`.

This is the algebraic action layer intended to sit between the existing scalar Descartes API
and a later geometric curvature-center representation.
-/

namespace LeanFrontier.DescartesCircle

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- A bundled Descartes curvature quadruple. -/
abbrev CurvatureVector (R : Type*) := Fin 4 → R

/-- The Descartes quadratic form
`(k₁+k₂+k₃+k₄)² - 2(k₁²+k₂²+k₃²+k₄²)`. -/
def descartesForm (v : CurvatureVector R) : R :=
  (∑ i, v i) ^ 2 - 2 * ∑ i, (v i) ^ 2

/-- The indexed Vieta reflection on curvature coordinate `i`.

Writing `S = ∑ j, v j`, the reflected coordinate is `2S - 3 v i`, equivalently
`2 * ∑_{j ≠ i} v j - v i`; all other coordinates are unchanged. -/
def curvatureReflection (i : Fin 4) : CurvatureVector R →ₗ[R] CurvatureVector R where
  toFun v j := if j = i then 2 * (∑ k, v k) - 3 * v i else v j
  map_add' x y := by
    funext j
    by_cases h : j = i
    · subst j
      simp [Finset.sum_add_distrib]
      ring
    · simp [h]
  map_smul' a x := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      simp only [ite_true]
      rw [← Finset.mul_sum]
      ring
    · simp [h, smul_eq_mul]

@[simp]
theorem curvatureReflection_apply_same (i : Fin 4) (v : CurvatureVector R) :
    curvatureReflection i v i = 2 * (∑ k, v k) - 3 * v i := by
  simp [curvatureReflection]

@[simp]
theorem curvatureReflection_apply_ne {i j : Fin 4} (h : j ≠ i) (v : CurvatureVector R) :
    curvatureReflection i v j = v j := by
  simp [curvatureReflection, h]

/-- Every coordinate Vieta reflection preserves the Descartes quadratic form. -/
theorem descartesForm_curvatureReflection (i : Fin 4) (v : CurvatureVector R) :
    descartesForm (curvatureReflection i v) = descartesForm v := by
  fin_cases i <;>
    simp [descartesForm, curvatureReflection, Fin.sum_univ_four] <;>
    ring

/-- The square of a coordinate curvature reflection, named so its structural
involution theorem has a compact elaborated statement. -/
def curvatureReflectionSquare (i : Fin 4) :
    CurvatureVector R →ₗ[R] CurvatureVector R :=
  (curvatureReflection i).comp (curvatureReflection i)

/-- The identity linear map on bundled curvature vectors. -/
def curvatureIdentity : CurvatureVector R →ₗ[R] CurvatureVector R :=
  LinearMap.id

/-- Every coordinate Vieta reflection is an involution. -/
theorem curvatureReflectionSquare_eq_identity (i : Fin 4) :
    curvatureReflectionSquare i = (curvatureIdentity : CurvatureVector R →ₗ[R] CurvatureVector R) := by
  ext v j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureReflectionSquare, curvatureIdentity, curvatureReflection,
      Fin.sum_univ_four] <;>
    ring

private theorem curvatureReflection_involutive (i : Fin 4) (v : CurvatureVector R) :
    curvatureReflection i (curvatureReflection i v) = v := by
  have h := congrArg (fun L : CurvatureVector R →ₗ[R] CurvatureVector R => L v)
    (curvatureReflectionSquare_eq_identity (R := R) i)
  simpa [curvatureReflectionSquare, curvatureIdentity] using h

/-- The bundled Descartes equation is exactly the accepted scalar `IsQuadruple` relation. -/
theorem isQuadruple_iff_descartesForm_eq_zero (v : CurvatureVector R) :
    IsQuadruple (v 0) (v 1) (v 2) (v 3) ↔ descartesForm v = 0 := by
  unfold IsQuadruple descartesForm
  simp only [Fin.sum_univ_four]
  constructor <;> intro h <;> linear_combination h

/-- Reflecting the last bundled coordinate specializes exactly to the accepted scalar
`DescartesCircle.reflect`. -/
theorem curvatureReflection_last_eq (v : CurvatureVector R) :
    curvatureReflection (3 : Fin 4) v =
      ![v 0, v 1, v 2, reflect (v 0) (v 1) (v 2) (v 3)] := by
  funext j
  fin_cases j <;>
    simp [curvatureReflection, reflect, Fin.sum_univ_four] <;>
    ring

end LeanFrontier.DescartesCircle
