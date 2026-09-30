import LeanFrontier.Geometry.FordCircleTangency
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Tactic.Positivity

/-!
# Curvature-center coordinates for Euclidean circles

The Descartes-circle development now has a bundled curvature vector and uniform Vieta
reflections, while the Ford-circle development uses Mathlib's actual Euclidean spheres. This
module supplies the missing representation layer between those viewpoints.

A CurvatureCenter.Circle records a curvature together with its Euclidean centre in the complex
plane. Its bend-center coordinate is the product of curvature and centre. Reciprocal curvature
gives a sphere radius, so this representation is losslessly interconvertible with
EuclideanGeometry.Sphere ℂ.

For circles whose reciprocal curvatures are nonnegative, the elementary centre-distance
tangency equation is exactly Mathlib's Sphere.IsExtTangent. The final theorem instantiates
that bridge for Ford circles, showing that their curvature-center tangency is equivalent to the
accepted Farey-neighbour cross-determinant criterion.

This is deliberately only the representation/tangency layer. It does not identify the
Descartes Vieta reflection with an inversive reflection; that later step must pass through a
geometric Descartes configuration in these or equivalent coordinates.
-/

namespace LeanFrontier.CurvatureCenter

/-- A circle represented by its (possibly signed) curvature and Euclidean centre.

For positive curvature, the ordinary Euclidean radius is its reciprocal. The sign is retained
so the same representation can later support oriented Descartes configurations. -/
structure Circle where
  curvature : ℝ
  center : ℂ

/-- The bend-center coordinate: curvature multiplied by the Euclidean centre. -/
noncomputable def bendCenter (c : Circle) : ℂ :=
  (c.curvature : ℂ) * c.center

/-- Interpret curvature-center data as a Euclidean sphere with reciprocal-curvature radius. -/
noncomputable def toSphere (c : Circle) : EuclideanGeometry.Sphere ℂ where
  center := c.center
  radius := c.curvature⁻¹

/-- Encode a Euclidean sphere by reciprocal radius and its existing centre. -/
noncomputable def ofSphere (s : EuclideanGeometry.Sphere ℂ) : Circle where
  curvature := s.radius⁻¹
  center := s.center

@[simp]
theorem toSphere_ofSphere (s : EuclideanGeometry.Sphere ℂ) :
    toSphere (ofSphere s) = s := by
  rcases s with ⟨center, radius⟩
  simp [toSphere, ofSphere]

@[simp]
theorem ofSphere_toSphere (c : Circle) :
    ofSphere (toSphere c) = c := by
  rcases c with ⟨curvature, center⟩
  simp [toSphere, ofSphere]

/-- External tangency in curvature-center coordinates.

For positive curvatures this says that the distance between centres is the sum of the reciprocal
curvatures, i.e. the sum of the Euclidean radii. -/
def IsExternallyTangent (c d : Circle) : Prop :=
  dist c.center d.center = c.curvature⁻¹ + d.curvature⁻¹

/-- For nonnegative reciprocal curvatures, curvature-center external tangency is exactly
Mathlib's Euclidean-sphere external tangency predicate. -/
theorem isExternallyTangent_iff_toSphere (c d : Circle)
    (hc : 0 ≤ c.curvature⁻¹) (hd : 0 ≤ d.curvature⁻¹) :
    IsExternallyTangent c d ↔ (toSphere c).IsExtTangent (toSphere d) := by
  rw [EuclideanGeometry.Sphere.isExtTangent_iff_dist_center]
  simp [IsExternallyTangent, toSphere, hc, hd]

end LeanFrontier.CurvatureCenter

namespace LeanFrontier.FordCircle

/-- A Ford circle expressed in the generic curvature-center representation. -/
noncomputable def curvatureCircle (p q : ℝ) : CurvatureCenter.Circle :=
  CurvatureCenter.ofSphere (euclideanSphere p q)

/-- The curvature-center tangency relation for Ford circles is exactly the accepted
Farey-neighbour determinant criterion. -/
theorem isExternallyTangent_curvatureCircle_iff
    {p q r s : ℝ} (hq : q ≠ 0) (hs : s ≠ 0) :
    CurvatureCenter.IsExternallyTangent (curvatureCircle p q) (curvatureCircle r s) ↔
      Mediant.crossDet p q r s ^ 2 = 1 := by
  have hqrad : 0 ≤ (curvatureCircle p q).curvature⁻¹ := by
    simpa [curvatureCircle, CurvatureCenter.ofSphere, euclideanSphere] using
      (show 0 ≤ radius q by
        unfold radius
        positivity)
  have hsrad : 0 ≤ (curvatureCircle r s).curvature⁻¹ := by
    simpa [curvatureCircle, CurvatureCenter.ofSphere, euclideanSphere] using
      (show 0 ≤ radius s by
        unfold radius
        positivity)
  rw [CurvatureCenter.isExternallyTangent_iff_toSphere _ _ hqrad hsrad]
  simpa [curvatureCircle] using (isExtTangent_euclideanSphere_iff hq hs)

end LeanFrontier.FordCircle
