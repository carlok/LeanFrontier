import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

namespace LeanFrontier.Algebra

/-- A three-variable square identity for the initial library seed. -/
theorem add_add_sq {α : Type*} (a b c : α) [CommRing α] :
    (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * a * c + 2 * b * c := by
  ring

end LeanFrontier.Algebra
