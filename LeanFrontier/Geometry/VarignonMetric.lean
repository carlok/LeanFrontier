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

/-- Opposite sides of the Varignon parallelogram have equal lengths.  This is the metric
form of the two vector equalities in `LeanFrontier.AffineGeometry.varignon_theorem`. -/
theorem varignon_opposite_side_lengths (a b c d : P) :
    dist (midpoint ℝ a b) (midpoint ℝ b c) =
        dist (midpoint ℝ c d) (midpoint ℝ d a) ∧
    dist (midpoint ℝ b c) (midpoint ℝ c d) =
        dist (midpoint ℝ d a) (midpoint ℝ a b) := by
  have hv := LeanFrontier.AffineGeometry.varignon_theorem a b c d
  constructor
  · have hdist :
        dist (midpoint ℝ b c) (midpoint ℝ a b) =
          dist (midpoint ℝ c d) (midpoint ℝ d a) := by
      simpa only [dist_eq_norm_vsub V] using congrArg norm hv.1
    calc
      dist (midpoint ℝ a b) (midpoint ℝ b c) =
          dist (midpoint ℝ b c) (midpoint ℝ a b) := dist_comm _ _
      _ = dist (midpoint ℝ c d) (midpoint ℝ d a) := hdist
  · have hdist :
        dist (midpoint ℝ c d) (midpoint ℝ b c) =
          dist (midpoint ℝ d a) (midpoint ℝ a b) := by
      simpa only [dist_eq_norm_vsub V] using congrArg norm hv.2
    calc
      dist (midpoint ℝ b c) (midpoint ℝ c d) =
          dist (midpoint ℝ c d) (midpoint ℝ b c) := dist_comm _ _
      _ = dist (midpoint ℝ d a) (midpoint ℝ a b) := hdist

/-- The perimeter of the Varignon parallelogram equals the sum of the lengths of the two
diagonals of the original quadrilateral. -/
theorem varignon_perimeter (a b c d : P) :
    dist (midpoint ℝ a b) (midpoint ℝ b c) +
        dist (midpoint ℝ b c) (midpoint ℝ c d) +
        dist (midpoint ℝ c d) (midpoint ℝ d a) +
        dist (midpoint ℝ d a) (midpoint ℝ a b) =
      dist a c + dist b d := by
  rcases varignon_adjacent_side_lengths a b c d with ⟨h₁, h₂⟩
  rcases varignon_opposite_side_lengths a b c d with ⟨h₃, h₄⟩
  rw [← h₃, ← h₄, h₁, h₂]
  calc
    dist a c / 2 + dist b d / 2 + dist a c / 2 + dist b d / 2 =
        (dist a c / 2 + dist a c / 2) + (dist b d / 2 + dist b d / 2) := by
      ac_rfl
    _ = dist a c + dist b d := by rw [add_halves, add_halves]

end LeanFrontier.EuclideanGeometry
