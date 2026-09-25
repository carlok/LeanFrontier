import LeanFrontier.NumberTheory.MarkovTree.MarkovNumber
import Mathlib.Tactic

/-!
# Coordinate divisibility in Markov triples

Reading the Markov equation

`x^2 + y^2 + z^2 = 3xyz`

modulo any one coordinate shows that this coordinate divides the sum of the
squares of the other two.

This module packages that elementary but useful arithmetic fact uniformly over
the accepted `Move` coordinate selector.  For an oriented node, selecting its
`back` coordinate specializes the result to the Markov-number / maximum
coordinate.

Combined later with pairwise coprimality, this is the standard input for
constructing a square root of `-1` modulo a Markov number.
-/

namespace LeanFrontier.MarkovTree

/-- Sum of the squares of the two coordinates not selected by `m`. -/
def State.otherSquareSum (s : State) : Move → ℤ
  | .first => s.y ^ 2 + s.z ^ 2
  | .second => s.x ^ 2 + s.z ^ 2
  | .third => s.x ^ 2 + s.y ^ 2

/-- In any bundled Markov solution, each coordinate divides the sum of squares
of the other two coordinates. -/
theorem coordinate_dvd_otherSquareSum
    (s : State) (m : Move) (h : s.IsSolution) :
    s.coordinate m ∣ s.otherSquareSum m := by
  rcases s with ⟨x, y, z⟩
  change MarkovEquation.IsSolution x y z at h
  unfold MarkovEquation.IsSolution at h
  cases m with
  | first =>
      refine ⟨3 * y * z - x, ?_⟩
      change y ^ 2 + z ^ 2 = x * (3 * y * z - x)
      nlinarith
  | second =>
      refine ⟨3 * x * z - y, ?_⟩
      change x ^ 2 + z ^ 2 = y * (3 * x * z - y)
      nlinarith
  | third =>
      refine ⟨3 * x * y - z, ?_⟩
      change x ^ 2 + y ^ 2 = z * (3 * x * y - z)
      nlinarith

/-- The Markov-number coordinate of an oriented node divides the sum of squares
of its two non-back coordinates. -/
theorem markovNumber_dvd_otherSquareSum (n : OrientedNode) :
    n.markovNumber ∣ n.state.otherSquareSum n.back := by
  simpa [OrientedNode.markovNumber] using
    coordinate_dvd_otherSquareSum n.state n.back n.solution

end LeanFrontier.MarkovTree
