import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Receiver probe

Not mathematics anyone needs. This module exists to make the ordinary receiver
run end to end on a pull request, so that the `leanchecker` step added in #99 is
observed executing inside the sandboxed validator rather than only in unit tests
and on a developer machine. To be closed unmerged.
-/

namespace LeanFrontier.Probe

/-- The binomial cube, stated over a commutative ring. -/
theorem add_cube_of_probe {α : Type*} [CommRing α] (a b : α) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring

end LeanFrontier.Probe
