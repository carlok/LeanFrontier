import LeanFrontier.NumberTheory.SternBrocot
import LeanFrontier.NumberTheory.SternBrocot.Intervals
import Mathlib.Data.List.Induction

/-!
# Stern-Brocot nodes as interval mediants

The accepted Stern-Brocot path module represents a node directly as a natural
numerator-denominator pair. The accepted interval module represents the same path by its two
integer boundary pairs.

This module identifies those two representations: the node reached by a path is exactly the
mediant of the path's interval boundaries.

The proof first records the useful structural fact that prepending a left or right direction
applies the corresponding linear numerator-denominator map to both interval boundaries. Since
that map preserves addition, the interval mediant obeys exactly the same recursion as
`SternBrocot.pair`.
-/

namespace LeanFrontier.SternBrocot

private def mapPair (dir : Bool) (p : ℤ × ℤ) : ℤ × ℤ :=
  if dir then (p.1 + p.2, p.2) else (p.1, p.1 + p.2)

private def mapBounds
    (dir : Bool) (state : (ℤ × ℤ) × (ℤ × ℤ)) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  (mapPair dir state.1, mapPair dir state.2)

private theorem bounds_cons (dir : Bool) (path : List Bool) :
    bounds (dir :: path) = mapBounds dir (bounds path) := by
  induction path using List.reverseRecOn with
  | nil =>
      cases dir <;> rfl
  | append_singleton path last ih =>
      have hcons :
          dir :: (path ++ [last]) = (dir :: path) ++ [last] := by
        rfl
      rw [hcons, bounds_append, bounds_append, ih]
      cases dir <;> cases last <;>
        simp [mapBounds, mapPair, add_assoc, add_left_comm, add_comm]

/-- The direct Stern-Brocot node represented by a path is exactly the mediant of the two
boundary pairs of the interval represented by the same path. The interval uses integers, so the
natural numerator and denominator of `pair path` are cast to `ℤ`. -/
theorem mediant_bounds_eq_pair (path : List Bool) :
    (bounds path).1.1 + (bounds path).2.1 = ((pair path).1 : ℤ) ∧
      (bounds path).1.2 + (bounds path).2.2 = ((pair path).2 : ℤ) := by
  induction path with
  | nil =>
      constructor <;> rfl
  | cons dir path ih =>
      rw [bounds_cons]
      cases dir
      · simp only [mapBounds, mapPair, Bool.false_eq_true, if_false, Prod.fst, Prod.snd, pair]
        constructor
        · exact ih.1
        · rw [Nat.cast_add]
          omega
      · simp only [mapBounds, mapPair, if_true, Prod.fst, Prod.snd, pair]
        constructor
        · rw [Nat.cast_add]
          omega
        · exact ih.2

end LeanFrontier.SternBrocot
