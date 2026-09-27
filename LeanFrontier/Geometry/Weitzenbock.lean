import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Weitzenböck's inequality

For every Euclidean triangle with side lengths `a`, `b`, `c` and area `K`,
Weitzenböck's inequality states

`4 * √(3 : ℝ) * K ≤ a² + b² + c²`.

We use the angle-area formula
`K = (1 / 2) * a * b * sin γ`, where `γ` is the angle between the sides `a` and `b`.
The proof first derives the Heron-equivalent identity

`16 K² = 2a²b² + 2b²c² + 2c²a² - a⁴ - b⁴ - c⁴`

directly from the law of cosines and `sin² γ + cos² γ = 1`.  The desired squared
inequality then reduces to the sum of the three nonnegative squares
`(a²-b²)²`, `(b²-c²)²`, and `(c²-a²)²`.

The statement includes degenerate triangles: Mathlib's angle convention makes the displayed
area expression vanish whenever either adjacent side is zero.
-/

open scoped EuclideanGeometry

namespace LeanFrontier.EuclideanGeometry

open Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Weitzenböck's inequality.** For three points in a real Euclidean affine space, four times
`√3` times the triangle area is at most the sum of the squares of its side lengths.

The area is written as `(1/2)ab sin γ`, with `γ` the angle at the middle point. -/
theorem weitzenbock_inequality (p₁ p₂ p₃ : P) :
    4 * √(3 : ℝ) *
        (1 / 2 * dist p₁ p₂ * dist p₃ p₂ * sin (∠ p₁ p₂ p₃)) ≤
      dist p₁ p₂ ^ 2 + dist p₃ p₂ ^ 2 + dist p₁ p₃ ^ 2 := by
  let a : ℝ := dist p₁ p₂
  let b : ℝ := dist p₃ p₂
  let c : ℝ := dist p₁ p₃
  let γ : ℝ := ∠ p₁ p₂ p₃
  let K : ℝ := 1 / 2 * a * b * sin γ
  let S : ℝ := a ^ 2 + b ^ 2 + c ^ 2
  change 4 * √(3 : ℝ) * K ≤ S

  have ha : 0 ≤ a := by
    dsimp [a]
    exact dist_nonneg
  have hb : 0 ≤ b := by
    dsimp [b]
    exact dist_nonneg
  have hc : 0 ≤ c := by
    dsimp [c]
    exact dist_nonneg
  have hsin : 0 ≤ sin γ := by
    dsimp [γ, _root_.EuclideanGeometry.angle]
    exact InnerProductGeometry.sin_angle_nonneg _ _
  have hcos :
      c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cos γ := by
    dsimp [a, b, c, γ]
    simpa [pow_two] using
      _root_.EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
        p₁ p₂ p₃
  have htrig : sin γ ^ 2 + cos γ ^ 2 = 1 :=
    sin_sq_add_cos_sq γ

  have harea :
      16 * K ^ 2 =
        2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 -
          a ^ 4 - b ^ 4 - c ^ 4 := by
    dsimp [K]
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring]
    simp_rw [hcos]
    linear_combination 4 * a ^ 2 * b ^ 2 * htrig

  have hsquared : 48 * K ^ 2 ≤ S ^ 2 := by
    dsimp [S]
    nlinarith [harea, sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
      sq_nonneg (c ^ 2 - a ^ 2)]

  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hleft : 0 ≤ 4 * √(3 : ℝ) * K := by
    positivity
  have hsqrt : (√(3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

  rw [← sq_le_sq₀ hleft hS]
  calc
    (4 * √(3 : ℝ) * K) ^ 2 = 48 * K ^ 2 := by
      nlinarith
    _ ≤ S ^ 2 := hsquared

end LeanFrontier.EuclideanGeometry
