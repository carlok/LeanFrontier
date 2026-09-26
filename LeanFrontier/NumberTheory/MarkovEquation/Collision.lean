import LeanFrontier.NumberTheory.MarkovEquation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Collision factorization for Markov triples

If two Markov triples share one coordinate, a classical identity factors the comparison of their
other two coordinate pairs.

For solutions `(a₁,b₁,c)` and `(a₂,b₂,c)`,

`
(a₁*a₂ - b₁*b₂) * (a₁*b₂ - b₁*a₂)
  = c^2 * (a₁*b₁ - a₂*b₂).
`

This identity appears as Lemma 2.1 in Anitha Srinivasan,
*Markoff numbers and ambiguous classes*, J. Théorie des Nombres de Bordeaux 21 (2009),
757-770. It is useful in uniqueness arguments because the two factors on the left encode the
same-sign and opposite-sign possibilities for the square roots of `-1` modulo a common Markov
number.

The statement is purely algebraic and does not assume positivity or that the shared coordinate is
largest.
-/

namespace LeanFrontier.MarkovEquation

/-- If two Markov triples share their third coordinate, their two remaining coordinate pairs
satisfy Srinivasan's collision factorization. -/
theorem collision_factorization
    {a₁ b₁ a₂ b₂ c : ℤ}
    (h₁ : IsSolution a₁ b₁ c)
    (h₂ : IsSolution a₂ b₂ c) :
    (a₁ * a₂ - b₁ * b₂) * (a₁ * b₂ - b₁ * a₂) =
      c ^ 2 * (a₁ * b₁ - a₂ * b₂) := by
  unfold IsSolution at h₁ h₂
  calc
    (a₁ * a₂ - b₁ * b₂) * (a₁ * b₂ - b₁ * a₂) =
        a₂ * b₂ * (a₁ ^ 2 + b₁ ^ 2) -
          a₁ * b₁ * (a₂ ^ 2 + b₂ ^ 2) := by
            ring
    _ = c ^ 2 * (a₁ * b₁ - a₂ * b₂) := by
      linear_combination (a₂ * b₂) * h₁ - (a₁ * b₁) * h₂

end LeanFrontier.MarkovEquation
