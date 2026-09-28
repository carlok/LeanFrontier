import LeanFrontier.Geometry.Varignon
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic

/-!
# Metric consequences of Varignon's theorem

Varignon's theorem says that the midpoints of the four sides of an arbitrary quadrilateral form
a parallelogram.  In a real normed affine space, its adjacent side lengths are half the lengths
of the two diagonals of the original quadrilateral.  Consequently, the perimeter of the
Varignon parallelogram is the sum of those diagonal lengths.

Unlike the affine theorem itself, these corollaries use the metric structure.  The perimeter
identity explicitly reuses `LeanFrontier.AffineGeometry.varignon_theorem` to identify opposite
side lengths.
-/

namespace LeanFrontier.EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Adjacent sides of the Varignon parallelogram have lengths equal to half the two diagonals
of the original quadrilateral. -/
theorem varignon_adjacent_side_lengths (a b c d : P) :
    dist (midpoint ℝ a b) (midpoint ℝ b c) = dist a c / 2 ∧
    dist (midpoint ℝ b c) (midpoint ℝ c d) = dist b d / 2 := by
  constructor
  · rw [dist_eq_norm_vsub V, midpoint_comm a b, midpoint_vsub_midpoint_same_left,
      norm_smul, dist_eq_norm_vsub V]
    norm_num
  · rw [dist_eq_norm_vsub V, midpoint_comm b c, midpoint_vsub_midpoint_same_left,
      norm_smul, dist_eq_norm_vsub V]
    norm_num

/-- The perimeter of the Varignon parallelogram equals the sum of the lengths of the two
diagonals of the original quadrilateral. -/
theorem varignon_perimeter (a b c d : P) :
    dist (midpoint ℝ a b) (midpoint ℝ b c) +
        dist (midpoint ℝ b c) (midpoint ℝ c d) +
        dist (midpoint ℝ c d) (midpoint ℝ d a) +
        dist (midpoint ℝ d a) (midpoint ℝ a b) =
      dist a c + dist b d := by
  have hsides := varignon_adjacent_side_lengths a b c d
  have hv := LeanFrontier.AffineGeometry.varignon_theorem a b c d
  have hop₁ :
      dist (midpoint ℝ c d) (midpoint ℝ d a) =
        dist (midpoint ℝ a b) (midpoint ℝ b c) := by
    have h := congrArg norm hv.1
    simpa [dist_eq_norm_vsub, dist_comm] using h.symm
  have hop₂ :
      dist (midpoint ℝ d a) (midpoint ℝ a b) =
        dist (midpoint ℝ b c) (midpoint ℝ c d) := by
    have h := congrArg norm hv.2
    simpa [dist_eq_norm_vsub, dist_comm] using h.symm
  rw [hop₁, hop₂, hsides.1, hsides.2]
  ring

end LeanFrontier.EuclideanGeometry
