import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The mediant of two fractions and the Stern-Brocot determinant

Given two fractions written as numerator/denominator pairs `(a, b)` and `(c, d)`, their
*mediant* is the fraction `(a + c) / (b + d)`. Replacing one of the two pairs by the mediant
pair `(a + c, b + d)` is the single step that generates the Stern-Brocot tree, and hence every
Farey sequence.

The invariant that controls this construction is the cross determinant `b * c - a * d` of the
matrix whose columns are the two pairs. This module defines both notions and proves the facts
that make the construction work:

* the cross determinant is unchanged when either pair is replaced by the mediant pair, so
  *unimodularity* `b * c - a * d = 1` propagates to both children of a Stern-Brocot node;
* a unimodular pair has a mediant that is automatically in lowest terms; and
* over an ordered field the mediant lies strictly between the two fractions, because a positive
  cross determinant is exactly the statement that the first fraction is smaller.

## Main definitions

* `LeanFrontier.Mediant.crossDet` - the cross determinant `b * c - a * d` of two
  numerator/denominator pairs, over any commutative ring.
* `LeanFrontier.Mediant.mediant` - the mediant `(a + c) / (b + d)`, over any division ring.

## Main statements

* `LeanFrontier.Mediant.crossDet_left_mediant` and
  `LeanFrontier.Mediant.crossDet_mediant_right` - the cross determinant is preserved by both
  Stern-Brocot descents, so unimodularity is inherited by both children of a node.
* `LeanFrontier.Mediant.isCoprime_mediant` - the mediant of a unimodular pair is in lowest
  terms.
* `LeanFrontier.Mediant.div_lt_div_iff_crossDet_pos` - a positive cross determinant characterizes
  the order of the two fractions.
* `LeanFrontier.Mediant.div_lt_mediant` and `LeanFrontier.Mediant.mediant_lt_div` - strict
  betweenness of the mediant.

## Implementation notes

The two ingredients live at different levels of generality and are kept there. The determinant
identities and the lowest-terms statement are ring identities, so they are stated over an
arbitrary commutative ring and apply in particular to `ℤ`, which is the case used for the
Stern-Brocot tree. Only the betweenness statements need an order and division, so they are
stated over a linearly ordered field.

Fractions are carried as separate numerator and denominator arguments rather than as a bundled
pair or as a `Rat`. The mediant is not a function of the two rational values - it depends on the
chosen representatives - so a formulation on reduced rationals would be a different, weaker
statement.

`mediant` is total: a vanishing `b + d` yields `0` under Lean's field convention. The
betweenness statements assume `0 < b` and `0 < d`, which makes `b + d` positive, so they never
meet that degenerate case.
-/

namespace LeanFrontier.Mediant

variable {R : Type*} [CommRing R]
variable {F : Type*} [DivisionRing F]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The cross determinant `b * c - a * d` of the numerator/denominator pairs `(a, b)` and
`(c, d)`, that is, the determinant of the matrix with those two columns. The pairs are called
*unimodular*, or Farey neighbours, when this value is `1`. -/
def crossDet (a b c d : R) : R := b * c - a * d

/-- The mediant `(a + c) / (b + d)` of the fractions `a / b` and `c / d`. -/
def mediant (a b c d : F) : F := (a + c) / (b + d)

/-- Replacing the second pair by the mediant pair leaves the cross determinant unchanged. -/
theorem crossDet_left_mediant (a b c d : R) :
    crossDet a b (a + c) (b + d) = crossDet a b c d := by
  unfold crossDet
  ring

/-- Replacing the first pair by the mediant pair leaves the cross determinant unchanged. -/
theorem crossDet_mediant_right (a b c d : R) :
    crossDet (a + c) (b + d) c d = crossDet a b c d := by
  unfold crossDet
  ring

/-- The numerator and denominator of the mediant of a unimodular pair are coprime: the mediant
of two Farey neighbours is already in lowest terms. -/
theorem isCoprime_mediant (a b c d : R) (h : crossDet a b c d = 1) :
    IsCoprime (a + c) (b + d) := by
  refine ⟨b, -a, ?_⟩
  unfold crossDet at h
  linear_combination h

/-- Over a linearly ordered field, two fractions with positive denominators are in increasing
order exactly when their cross determinant is positive. -/
theorem div_lt_div_iff_crossDet_pos {a b c d : K} (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d ↔ 0 < crossDet a b c d := by
  rw [div_lt_div_iff₀ hb hd]
  unfold crossDet
  rw [sub_pos, mul_comm b c]

/-- The mediant is strictly larger than the smaller of the two fractions. -/
theorem div_lt_mediant {a b c d : K} (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) :
    a / b < mediant a b c d := by
  have hbd : 0 < b + d := by linarith
  rw [div_lt_div_iff₀ hb hd] at h
  unfold mediant
  rw [div_lt_div_iff₀ hb hbd]
  linarith

/-- The mediant is strictly smaller than the larger of the two fractions. -/
theorem mediant_lt_div {a b c d : K} (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) :
    mediant a b c d < c / d := by
  have hbd : 0 < b + d := by linarith
  rw [div_lt_div_iff₀ hb hd] at h
  unfold mediant
  rw [div_lt_div_iff₀ hbd hd]
  linarith

end LeanFrontier.Mediant
