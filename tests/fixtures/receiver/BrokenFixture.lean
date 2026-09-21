import Mathlib.Tactic.Ring

/-! A deliberately broken module: the receiver must report the Lean error. -/

namespace LeanFrontier.BrokenFixture

theorem sq_add_sq_ne (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  ring

end LeanFrontier.BrokenFixture
