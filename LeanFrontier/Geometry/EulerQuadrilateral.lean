import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Euler's quadrilateral theorem

For any four points `a b c d` in a real Euclidean affine space, let `m` and `n` be the
midpoints of the diagonals `ac` and `bd`. Euler's quadrilateral theorem states

```
AB² + BC² + CD² + DA² = AC² + BD² + 4 MN².
```

The proof is a threefold use of Apollonius's theorem. Applying Apollonius to the triangles
`bac` and `dac` expresses the four side squares through the first diagonal and the distances
to its midpoint. A third application to the triangle `mbd` turns those two midpoint distances
into the second diagonal and the distance between the diagonal midpoints.
-/

namespace LeanFrontier.EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Euler's quadrilateral theorem.** For any four points in a real Euclidean affine space, the
sum of the squares of the four side lengths equals the sum of the squares of the diagonal lengths
plus four times the square of the distance between the diagonal midpoints. -/
theorem euler_quadrilateral (a b c d : P) :
    dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 =
      dist a c ^ 2 + dist b d ^ 2 +
        4 * dist (midpoint ℝ a c) (midpoint ℝ b d) ^ 2 := by
  let m : P := midpoint ℝ a c
  let n : P := midpoint ℝ b d

  have h₁ :=
    _root_.EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      b a c
  have h₂ :=
    _root_.EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      d a c
  have h₃ :=
    _root_.EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      m b d

  change
    dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 =
      dist a c ^ 2 + dist b d ^ 2 + 4 * dist m n ^ 2

  change
    dist b a ^ 2 + dist b c ^ 2 =
      2 * (dist b m ^ 2 + (dist a c / 2) ^ 2) at h₁
  change
    dist d a ^ 2 + dist d c ^ 2 =
      2 * (dist d m ^ 2 + (dist a c / 2) ^ 2) at h₂
  change
    dist m b ^ 2 + dist m d ^ 2 =
      2 * (dist m n ^ 2 + (dist b d / 2) ^ 2) at h₃

  rw [dist_comm b a, dist_comm b m] at h₁
  rw [dist_comm d c, dist_comm d m] at h₂

  nlinarith [h₁, h₂, h₃]

end LeanFrontier.EuclideanGeometry
