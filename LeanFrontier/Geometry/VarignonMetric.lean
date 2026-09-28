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
    ring
  · rw [dist_eq_norm_vsub V, midpoint_comm b c, midpoint_vsub_midpoint_same_left,
      norm_smul, dist_eq_norm_vsub V]
    norm_num
    ring

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
    have hdist :
        dist (midpoint ℝ b c) (midpoint ℝ a b) =
          dist (midpoint ℝ c d) (midpoint ℝ d a) := by
      simpa [dist_eq_norm_vsub] using congrArg norm hv.1
    calc
      dist (midpoint ℝ c d) (midpoint ℝ d a) =
          dist (midpoint ℝ b c) (midpoint ℝ a b) := hdist.symm
      _ = dist (midpoint ℝ a b) (midpoint ℝ b c) := dist_comm _ _
  have hop₂ :
      dist (midpoint ℝ d a) (midpoint ℝ a b) =
        dist (midpoint ℝ b c) (midpoint ℝ c d) := by
    have hdist :
        dist (midpoint ℝ c d) (midpoint ℝ b c) =
          dist (midpoint ℝ d a) (midpoint ℝ a b) := by
      simpa [dist_eq_norm_vsub] using congrArg norm hv.2
    calc
      dist (midpoint ℝ d a) (midpoint ℝ a b) =
          dist (midpoint ℝ c d) (midpoint ℝ b c) := hdist.symm
      _ = dist (midpoint ℝ b c) (midpoint ℝ c d) := dist_comm _ _
  rw [hop₁, hop₂, hsides.1, hsides.2]
  ring

end LeanFrontier.EuclideanGeometry
