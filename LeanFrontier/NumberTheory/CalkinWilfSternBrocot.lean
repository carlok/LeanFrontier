import LeanFrontier.NumberTheory.CalkinWilf
import LeanFrontier.NumberTheory.SternBrocot

/-!
# Calkin-Wilf and Stern-Brocot path reversal

The accepted Calkin-Wilf and Stern-Brocot developments use the same two elementary pair
updates but compose them in opposite path orders.

For a root-to-leaf Boolean path `p`, the Calkin-Wilf pair reached by `p.reverse` is exactly
the Stern-Brocot pair reached by `p`. Consequently, a Calkin-Wilf path and a Stern-Brocot
path encode the same positive rational pair exactly when the paths are reverses of one another.

This is the explicit bridge between the two accepted tree enumerations; it does not identify
their traversal orders.
-/

namespace LeanFrontier.CalkinWilf

/-- Reversing a root-to-leaf path converts the Calkin-Wilf pair convention into the
Stern-Brocot pair convention. -/
theorem pair_reverse_eq_sternBrocot (path : List Bool) :
    pair path.reverse = SternBrocot.pair path := by
  induction path with
  | nil =>
      rfl
  | cons dir path ih =>
      cases dir <;>
        simp [List.reverse_cons, pair_append, SternBrocot.pair, ih]

/-- A Calkin-Wilf path and a Stern-Brocot path reach the same numerator-denominator pair
exactly when the two root-to-leaf paths are reverses of one another. -/
theorem pair_eq_sternBrocot_iff_reverse (p q : List Bool) :
    pair p = SternBrocot.pair q ↔ p = q.reverse := by
  rw [← pair_reverse_eq_sternBrocot q]
  exact pair_eq_iff p q.reverse

end LeanFrontier.CalkinWilf
