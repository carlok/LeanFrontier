import LeanFrontier.NumberTheory.MarkovTree.MarkovNumber
import Mathlib.Tactic

/-!
# Algebra of the two forward Markov-number labels

At an oriented Markov node there are two forward Vieta moves.  The accepted
`markovNumber` API identifies the back coordinate with the unique largest
coordinate, but future uniqueness arguments also need an explicit comparison
between the two *child* labels.

If the parent Markov number is `M` and the two non-back coordinates, in
Boolean forward-move order, are `u` and `v`, then the two child labels are

`3 M v - u` and `3 M u - v`.

Consequently their difference factors as

`(3 M + 1) (v - u)`.

Since `M > 0`, the factor `3 M + 1` is positive.  Thus jumping the smaller
of the two non-back coordinates produces the larger child Markov number, and
the two child labels are equal exactly when those two parent coordinates are
equal.

This is local algebra only; no Markov uniqueness statement is used.
-/

namespace LeanFrontier.MarkovTree

/-- The parent coordinate selected by one of the two forward Boolean directions. -/
def OrientedNode.forwardCoordinate (n : OrientedNode) (dir : Bool) : ℤ :=
  n.state.coordinate (forwardMove n.back dir)

/-- The Markov-number coordinate of every oriented node is positive. -/
theorem markovNumber_pos (n : OrientedNode) :
    0 < n.markovNumber := by
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  rcases hpos with ⟨hx, hy, hz⟩
  cases back with
  | first =>
      simpa [OrientedNode.markovNumber, State.coordinate] using hx
  | second =>
      simpa [OrientedNode.markovNumber, State.coordinate] using hy
  | third =>
      simpa [OrientedNode.markovNumber, State.coordinate] using hz

/-- Either non-back coordinate of an oriented node is positive. -/
theorem forwardCoordinate_pos (n : OrientedNode) (dir : Bool) :
    0 < n.forwardCoordinate dir := by
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  rcases hpos with ⟨hx, hy, hz⟩
  cases back <;> cases dir <;>
    simp [OrientedNode.forwardCoordinate, State.coordinate, forwardMove] <;>
    assumption

/-- Exact formula for the Markov-number label of either forward child.

The coordinate being jumped is `forwardCoordinate dir`; the other non-back
coordinate is `forwardCoordinate (!dir)`. -/
theorem child_markovNumber_formula (n : OrientedNode) (dir : Bool) :
    (child n dir).markovNumber =
      3 * n.markovNumber * n.forwardCoordinate (!dir) -
        n.forwardCoordinate dir := by
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  cases back <;> cases dir <;>
    simp [child, OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
      State.coordinate, move, forwardMove, MarkovEquation.jump] <;>
    ring

/-- The difference of the two child Markov-number labels factors through the
difference of the two non-back parent coordinates. -/
theorem child_markovNumber_sub_child_markovNumber (n : OrientedNode) :
    (child n false).markovNumber - (child n true).markovNumber =
      (3 * n.markovNumber + 1) *
        (n.forwardCoordinate true - n.forwardCoordinate false) := by
  rw [child_markovNumber_formula n false, child_markovNumber_formula n true]
  simp
  ring

/-- The factor controlling the difference of the two child labels is positive. -/
theorem three_mul_markovNumber_add_one_pos (n : OrientedNode) :
    0 < 3 * n.markovNumber + 1 := by
  have h := markovNumber_pos n
  nlinarith

/-- The child reached by `false` has the smaller Markov-number label exactly
when the parent coordinate selected by `true` is smaller.

Equivalently, among the two forward Vieta moves, jumping the larger current
coordinate produces the smaller child label. -/
theorem child_false_markovNumber_lt_child_true_iff (n : OrientedNode) :
    (child n false).markovNumber < (child n true).markovNumber ↔
      n.forwardCoordinate true < n.forwardCoordinate false := by
  have hfactor := child_markovNumber_sub_child_markovNumber n
  have hpos := three_mul_markovNumber_add_one_pos n
  constructor
  · intro hchild
    by_contra hcoord
    have hle :
        n.forwardCoordinate false ≤ n.forwardCoordinate true :=
      le_of_not_gt hcoord
    have hprod :
        0 ≤ (3 * n.markovNumber + 1) *
          (n.forwardCoordinate true - n.forwardCoordinate false) :=
      mul_nonneg (le_of_lt hpos) (sub_nonneg.mpr hle)
    rw [← hfactor] at hprod
    linarith
  · intro hcoord
    have hprod :
        (3 * n.markovNumber + 1) *
            (n.forwardCoordinate true - n.forwardCoordinate false) < 0 :=
      mul_neg_of_pos_of_neg hpos (sub_neg.mpr hcoord)
    rw [← hfactor] at hprod
    linarith

/-- The two immediate child Markov numbers coincide exactly when the two
non-back parent coordinates coincide. -/
theorem child_markovNumber_eq_iff_forwardCoordinate_eq (n : OrientedNode) :
    (child n false).markovNumber = (child n true).markovNumber ↔
      n.forwardCoordinate false = n.forwardCoordinate true := by
  have hfactor := child_markovNumber_sub_child_markovNumber n
  have hpos := three_mul_markovNumber_add_one_pos n
  constructor
  · intro hchild
    have hzero :
        (3 * n.markovNumber + 1) *
            (n.forwardCoordinate true - n.forwardCoordinate false) = 0 := by
      rw [← hfactor, hchild]
      ring
    have hdiff :
        n.forwardCoordinate true - n.forwardCoordinate false = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos)
    exact (sub_eq_zero.mp hdiff).symm
  · intro hcoord
    rw [child_markovNumber_formula n false,
      child_markovNumber_formula n true]
    simp
    rw [hcoord]

end LeanFrontier.MarkovTree
