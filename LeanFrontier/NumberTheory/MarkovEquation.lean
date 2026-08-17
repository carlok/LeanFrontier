import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Markov equation and its Vieta involution

A *Markov triple* is an integer solution of `x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z`. Fixing `x`
and `y`, the equation is a monic quadratic in `z` whose two roots sum to `3 * x * y`, so from one
solution a second is obtained by replacing `z` with `3 * x * y - z`. That replacement is the
Vieta jump, and iterating it from `(1, 1, 1)` produces the Markov tree, hence every Markov
triple.

This module defines the equation and the jump and proves the facts that make the tree work: the
jump sends solutions to solutions, it is an involution, and it is Vieta's product relation for
the two roots, which also makes it positivity preserving.

## Main definitions

* `LeanFrontier.MarkovEquation.IsSolution` - the Markov equation.
* `LeanFrontier.MarkovEquation.jump` - the Vieta jump `3 * x * y - z` in the last coordinate.

## Main statements

* `LeanFrontier.MarkovEquation.isSolution_jump` - the jump preserves the equation.
* `LeanFrontier.MarkovEquation.jump_jump` - the jump is an involution, so the tree edges are
  reversible.
* `LeanFrontier.MarkovEquation.mul_jump_eq` - Vieta's product relation `z * (3 * x * y - z)
  = x ^ 2 + y ^ 2` for the two roots.
* `LeanFrontier.MarkovEquation.jump_pos` - the jump of a positive solution is positive.
* `LeanFrontier.MarkovEquation.isSolution_one_one_one` - the root of the Markov tree.

## Implementation notes

The equation is stated for integers, which is the classical setting; nothing here needs a
larger coefficient ring.

Solutions are carried as three separate coordinates rather than as a bundled triple, and the
jump acts on the last coordinate only. The other two jumps are this one composed with a
permutation of the arguments, so stating them separately would only restate this result.

The tree's descent ordering, which needs the largest coordinate to be identified and excludes
the singular triple `(1, 1, 1)`, is not proved here; it belongs with a Markov tree object
rather than with the bare involution.
-/

namespace LeanFrontier.MarkovEquation

variable {x y z : ℤ}

/-- The Markov equation `x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z`. Its integer solutions are the
Markov triples. -/
def IsSolution (x y z : ℤ) : Prop := x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

/-- The Vieta jump in the last coordinate: the second root of the Markov equation read as a
quadratic in `z`. -/
def jump (x y z : ℤ) : ℤ := 3 * x * y - z

/-- Vieta's product relation for the two roots of the Markov equation in its last coordinate. -/
theorem mul_jump_eq (h : IsSolution x y z) : z * jump x y z = x ^ 2 + y ^ 2 := by
  unfold IsSolution at h
  unfold jump
  linear_combination -h

/-- The Vieta jump sends Markov triples to Markov triples. -/
theorem isSolution_jump (h : IsSolution x y z) : IsSolution x y (jump x y z) := by
  unfold IsSolution at h ⊢
  unfold jump
  linear_combination h

/-- The Vieta jump is an involution, so each edge of the Markov tree can be traversed in both
directions. -/
theorem jump_jump (x y z : ℤ) : jump x y (jump x y z) = z := by
  unfold jump
  ring

/-- A Markov triple with positive first and last coordinate has a positive jump: the second root
of a positive triple is again positive. -/
theorem jump_pos (hx : 0 < x) (hz : 0 < z) (h : IsSolution x y z) : 0 < jump x y z := by
  have hprod : z * jump x y z = x ^ 2 + y ^ 2 := mul_jump_eq h
  nlinarith [sq_nonneg y, mul_pos hx hx, sq_nonneg (jump x y z)]

/-- `(1, 1, 1)` is a Markov triple; it is the root from which the Vieta jumps generate the
Markov tree. -/
theorem isSolution_one_one_one : IsSolution 1 1 1 := by
  unfold IsSolution
  norm_num

end LeanFrontier.MarkovEquation
