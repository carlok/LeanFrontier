import LeanFrontier.NumberTheory.FordCircle
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Tactic.Linarith

/-!
# Ford circles as Euclidean spheres

`LeanFrontier.NumberTheory.FordCircle` proves the Ford-circle tangency criterion algebraically,
using the squared distance between centres. This module connects that result to Mathlib's actual
Euclidean sphere tangency predicate.

A Ford circle with fraction `p / q` is represented as a sphere in the Euclidean plane `ℂ`, with
centre `(p / q, radius q)` and radius `radius q`. For nonzero denominators, two such spheres are
externally tangent exactly when the accepted Ford-circle cross determinant has square `1`.

The proof deliberately reuses both sides of the existing interface: the exact squared-distance
criterion from `LeanFrontier.FordCircle` and Mathlib's characterization of external sphere
tangency by centre distance and nonnegative radii.
-/

namespace LeanFrontier.FordCircle

/-- The Euclidean centre of the Ford circle of `p / q`, represented in the complex plane. -/
noncomputable def euclideanCenter (p q : ℝ) : ℂ := ⟨p / q, radius q⟩

/-- The Ford circle of `p / q` as a Mathlib Euclidean sphere in the complex plane. -/
noncomputable def euclideanSphere (p q : ℝ) : EuclideanGeometry.Sphere ℂ where
  center := euclideanCenter p q
  radius := radius q

/-- The square of the Euclidean distance between the geometric Ford-circle centres is exactly
`centerDistSq` from the accepted algebraic Ford-circle module. -/
theorem dist_euclideanCenter_sq (p q r s : ℝ) :
    dist (euclideanCenter p q) (euclideanCenter r s) ^ 2 = centerDistSq p q r s := by
  rw [Complex.dist_eq, Complex.sq_norm]
  simp [euclideanCenter, centerDistSq, Complex.normSq_apply]
  ring

private theorem radius_nonneg (q : ℝ) : 0 ≤ radius q := by
  unfold radius
  positivity

/-- Two geometric Ford circles with nonzero denominators are externally tangent in Mathlib's
`EuclideanGeometry.Sphere` sense exactly when their cross determinant has square `1`.

This is the geometric form of the Farey-neighbour tangency criterion proved algebraically in
`LeanFrontier.NumberTheory.FordCircle`.
-/
theorem isExtTangent_euclideanSphere_iff
    {p q r s : ℝ} (hq : q ≠ 0) (hs : s ≠ 0) :
    (euclideanSphere p q).IsExtTangent (euclideanSphere r s) ↔
      Mediant.crossDet p q r s ^ 2 = 1 := by
  rw [EuclideanGeometry.Sphere.isExtTangent_iff_dist_center]
  change
    (dist (euclideanCenter p q) (euclideanCenter r s) = radius q + radius s ∧
      0 ≤ radius q ∧ 0 ≤ radius s) ↔ Mediant.crossDet p q r s ^ 2 = 1
  have hqrad : 0 ≤ radius q := radius_nonneg q
  have hsrad : 0 ≤ radius s := radius_nonneg s
  constructor
  · rintro ⟨hdist, -, -⟩
    apply (centerDistSq_eq_iff hq hs).1
    rw [← dist_euclideanCenter_sq, hdist]
  · intro hdet
    refine ⟨?_, hqrad, hsrad⟩
    have hsq := (centerDistSq_eq_iff hq hs).2 hdet
    rw [← dist_euclideanCenter_sq] at hsq
    have hdist_nonneg : 0 ≤ dist (euclideanCenter p q) (euclideanCenter r s) := dist_nonneg
    nlinarith

end LeanFrontier.FordCircle
