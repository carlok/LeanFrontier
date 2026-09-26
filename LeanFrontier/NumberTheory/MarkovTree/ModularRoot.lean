import LeanFrontier.NumberTheory.MarkovTree.ChildLabels
import LeanFrontier.NumberTheory.MarkovTree.Coprime
import LeanFrontier.NumberTheory.MarkovTree.SumSquaresDivisibility
import LeanFrontier.NumberTheory.SquareRootNegOne
import Mathlib.Tactic

/-!
# A square root of minus one modulo every oriented Markov number

The accepted Markov-tree arithmetic gives two complementary facts at an
oriented node:

* its Markov-number coordinate divides the sum of squares of the two non-back
  coordinates;
* all three coordinates are pairwise coprime.

The imported generic coprime-sum-of-two-squares lemma therefore applies: either
non-back coordinate is invertible modulo the Markov number, and their quotient
squares to `-1`.

This module packages that consequence directly against the oriented-tree API.
It is arithmetic infrastructure only; no uniqueness claim is made.
-/

namespace LeanFrontier.MarkovTree

/-- The Markov-number coordinate is coprime to either of the two non-back
coordinates selected by a Boolean forward direction. -/
theorem markovNumber_isCoprime_forwardCoordinate
    (n : OrientedNode) (dir : Bool) :
    IsCoprime n.markovNumber (n.forwardCoordinate dir) := by
  have hcop := n.pairwiseCoprime
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  change IsCoprime x y ∧ IsCoprime x z ∧ IsCoprime y z at hcop
  cases back with
  | first =>
      cases dir with
      | false =>
          simpa [OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
            State.coordinate, forwardMove] using hcop.1
      | true =>
          simpa [OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
            State.coordinate, forwardMove] using hcop.2.1
  | second =>
      cases dir with
      | false =>
          simpa [OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
            State.coordinate, forwardMove] using hcop.1.symm
      | true =>
          simpa [OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
            State.coordinate, forwardMove] using hcop.2.2
  | third =>
      cases dir with
      | false =>
          simpa [OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
            State.coordinate, forwardMove] using hcop.2.1.symm
      | true =>
          simpa [OrientedNode.markovNumber, OrientedNode.forwardCoordinate,
            State.coordinate, forwardMove] using hcop.2.2.symm

/-- The complementary square sum at the back coordinate is exactly the sum of
squares of the two Boolean forward coordinates. -/
theorem otherSquareSum_back_eq_forwardCoordinate_squares
    (n : OrientedNode) :
    n.state.otherSquareSum n.back =
      n.forwardCoordinate false ^ 2 + n.forwardCoordinate true ^ 2 := by
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  cases back <;>
    simp [State.otherSquareSum, OrientedNode.forwardCoordinate,
      State.coordinate, forwardMove, add_comm]

/-- Every accepted oriented Markov number admits an integer square root of
`-1` modulo itself. -/
theorem exists_sq_modEq_neg_one_markovNumber (n : OrientedNode) :
    ∃ r : ℤ, r ^ 2 ≡ -1 [ZMOD n.markovNumber] := by
  apply LeanFrontier.Int.exists_sq_modEq_neg_one_of_isCoprime_of_dvd_sq_add_sq
      (u := n.forwardCoordinate false)
      (v := n.forwardCoordinate true)
  · exact markovNumber_isCoprime_forwardCoordinate n true
  · have hdiv := markovNumber_dvd_otherSquareSum n
    rw [otherSquareSum_back_eq_forwardCoordinate_squares n] at hdiv
    exact hdiv

end LeanFrontier.MarkovTree
