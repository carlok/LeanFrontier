import LeanFrontier.Geometry.FordCircleTangency
import LeanFrontier.NumberTheory.DescartesCircle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Farey Ford-circle Descartes configurations

For a unimodular pair of fractions, the two parent Ford circles and the Ford circle of their
mediant are pairwise externally tangent. Their reciprocal radii, together with curvature zero
for the common tangent line, satisfy Descartes' circle relation.

This module is the geometric synthesis of the accepted Farey/Ford tangency interface and the
accepted algebraic Descartes-circle development.
-/

namespace LeanFrontier.FordCircle

/-- A positive-denominator unimodular pair and its mediant form a three-circle Ford
configuration: the parent circles and mediant circle are pairwise externally tangent, and their
actual curvatures (reciprocal radii), together with the horizontal tangent line of curvature
zero, satisfy Descartes' circle relation. -/
theorem farey_mediant_descartes_configuration
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hdet : Mediant.crossDet a b c d = 1) :
    (euclideanSphere a b).IsExtTangent (euclideanSphere c d) ∧
      (euclideanSphere a b).IsExtTangent (euclideanSphere (a + c) (b + d)) ∧
      (euclideanSphere (a + c) (b + d)).IsExtTangent (euclideanSphere c d) ∧
      DescartesCircle.IsQuadruple (0 : ℝ)
        (radius b)⁻¹ (radius d)⁻¹ (radius (b + d))⁻¹ := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hbd : 0 < b + d := add_pos hb hd
  have hbd0 : b + d ≠ 0 := ne_of_gt hbd
  have hparent :
      (euclideanSphere a b).IsExtTangent (euclideanSphere c d) := by
    apply (isExtTangent_euclideanSphere_iff hb0 hd0).2
    rw [hdet]
    norm_num
  have hleftDet : Mediant.crossDet a b (a + c) (b + d) = 1 := by
    rw [Mediant.crossDet_left_mediant, hdet]
  have hleft :
      (euclideanSphere a b).IsExtTangent (euclideanSphere (a + c) (b + d)) := by
    apply (isExtTangent_euclideanSphere_iff hb0 hbd0).2
    rw [hleftDet]
    norm_num
  have hrightDet : Mediant.crossDet (a + c) (b + d) c d = 1 := by
    rw [Mediant.crossDet_mediant_right, hdet]
  have hright :
      (euclideanSphere (a + c) (b + d)).IsExtTangent (euclideanSphere c d) := by
    apply (isExtTangent_euclideanSphere_iff hbd0 hd0).2
    rw [hrightDet]
    norm_num
  have hdesc :
      DescartesCircle.IsQuadruple (0 : ℝ)
        (2 * b ^ 2) (2 * d ^ 2) (2 * (b + d) ^ 2) := by
    unfold DescartesCircle.IsQuadruple
    ring
  refine ⟨hparent, hleft, hright, ?_⟩
  simpa [radius] using hdesc

end LeanFrontier.FordCircle
