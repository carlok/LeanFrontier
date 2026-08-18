import Mathlib.Algebra.Order.Ring.Lemmas

/-!
# Receiver probe

Not mathematics anyone needs. This module exists to make the ordinary receiver
run end to end on a pull request, so that the `leanchecker` step added in #99
is observed executing inside the sandboxed validator rather than only in unit
tests and on a developer machine. To be closed unmerged.
-/

namespace LeanFrontier.Probe

/-- A square is never negative, stated over a linear ordered ring. -/
theorem sq_nonneg_of_probe {R : Type*} [LinearOrderedRing R] (x : R) : 0 ≤ x * x :=
  mul_self_nonneg x

end LeanFrontier.Probe
