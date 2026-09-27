import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Tactic

/-!
# Varignon's theorem

For any quadrilateral, the midpoints of its four sides form a parallelogram.

We state this in affine-vector form. If

* `e` is the midpoint of `ab`,
* `f` is the midpoint of `bc`,
* `g` is the midpoint of `cd`,
* `h` is the midpoint of `da`,

then the opposite side vectors of `efgh` agree:

`f -ᵥ e = g -ᵥ h` and `g -ᵥ f = h -ᵥ e`.

This formulation is purely affine; no metric or inner-product structure is required.
-/

namespace LeanFrontier.AffineGeometry

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- **Varignon's theorem.** The four side midpoints of an arbitrary quadrilateral form a
parallelogram, expressed by equality of both pairs of opposite side vectors. -/
theorem varignon_theorem (a b c d : P) :
    (midpoint ℝ b c -ᵥ midpoint ℝ a b =
      midpoint ℝ c d -ᵥ midpoint ℝ d a) ∧
    (midpoint ℝ c d -ᵥ midpoint ℝ b c =
      midpoint ℝ d a -ᵥ midpoint ℝ a b) := by
  constructor
  · rw [midpoint_vsub_midpoint, midpoint_vsub_midpoint,
      midpoint_eq_smul_add, midpoint_eq_smul_add]
    congr 1
    rw [add_comm (b -ᵥ a) (c -ᵥ b), vsub_add_vsub_cancel]
    rw [vsub_add_vsub_cancel]
  · rw [midpoint_vsub_midpoint, midpoint_vsub_midpoint,
      midpoint_eq_smul_add, midpoint_eq_smul_add]
    congr 1
    rw [add_comm (c -ᵥ b) (d -ᵥ c), vsub_add_vsub_cancel]
    rw [vsub_add_vsub_cancel]

end LeanFrontier.AffineGeometry
