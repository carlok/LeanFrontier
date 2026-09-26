import LeanFrontier.NumberTheory.MarkovTree.Coprime
import LeanFrontier.NumberTheory.MarkovTree.SumSquaresDivisibility
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Quadratic residues attached to Markov numbers

Two accepted arithmetic ingredients meet naturally at an oriented Markov node.

First, the Markov-number / back coordinate divides the sum of squares of the other two
coordinates.  Second, positive Markov triples are pairwise coprime.  Thus that complementary
sum of two squares is primitive.

Mathlib's sum-of-two-squares modular theorem then gives a square root of `-1` modulo the
complementary square sum, and divisibility transports it to the Markov-number modulus.

As a standard consequence, no prime divisor of a Markov-number label is congruent to
`3 mod 4`.

These are arithmetic invariants of the label.  They do not assert that the label determines the
whole Markov triple.
-/

namespace LeanFrontier.MarkovTree

private theorem natAbs_dvd_natAbs_of_dvd {a b : ℤ} (h : a ∣ b) :
    a.natAbs ∣ b.natAbs := by
  rcases h with ⟨k, rfl⟩
  rw [Int.natAbs_mul]
  exact dvd_mul_right _ _

/-- Every oriented Markov-number label carries a square root of `-1` modulo its absolute value.

The complementary coordinates are coprime, their squares sum to a multiple of the Markov number,
and the primitive sum-of-two-squares theorem supplies the modular square root. -/
theorem isSquare_neg_one_mod_markovNumber (n : OrientedNode) :
    IsSquare (-1 : ZMod n.markovNumber.natAbs) := by
  have hcop := n.pairwiseCoprime
  have hdiv := markovNumber_dvd_otherSquareSum n
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  change IsCoprime x y ∧ IsCoprime x z ∧ IsCoprime y z at hcop
  cases back with
  | first =>
      change IsSquare (-1 : ZMod x.natAbs)
      change x ∣ y ^ 2 + z ^ 2 at hdiv
      have hs : IsSquare (-1 : ZMod (y ^ 2 + z ^ 2).natAbs) :=
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime rfl hcop.2.2
      exact ZMod.isSquare_neg_one_of_dvd (natAbs_dvd_natAbs_of_dvd hdiv) hs
  | second =>
      change IsSquare (-1 : ZMod y.natAbs)
      change y ∣ x ^ 2 + z ^ 2 at hdiv
      have hs : IsSquare (-1 : ZMod (x ^ 2 + z ^ 2).natAbs) :=
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime rfl hcop.2.1
      exact ZMod.isSquare_neg_one_of_dvd (natAbs_dvd_natAbs_of_dvd hdiv) hs
  | third =>
      change IsSquare (-1 : ZMod z.natAbs)
      change z ∣ x ^ 2 + y ^ 2 at hdiv
      have hs : IsSquare (-1 : ZMod (x ^ 2 + y ^ 2).natAbs) :=
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime rfl hcop.1
      exact ZMod.isSquare_neg_one_of_dvd (natAbs_dvd_natAbs_of_dvd hdiv) hs

/-- No prime divisor of an oriented Markov-number label is congruent to three modulo four. -/
theorem prime_dvd_markovNumber_mod_four_ne_three
    (n : OrientedNode) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ n.markovNumber.natAbs) :
    p % 4 ≠ 3 := by
  have hmarkovPos : 0 < n.markovNumber := by
    rw [markovNumber_eq_max]
    exact lt_of_lt_of_le n.positive.1 (le_max_left _ _)
  have hnonzero : n.markovNumber.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (ne_of_gt hmarkovPos)
  have hmem : p ∈ n.markovNumber.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hd, hnonzero⟩
  exact Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
    hmem (isSquare_neg_one_mod_markovNumber n)

end LeanFrontier.MarkovTree
