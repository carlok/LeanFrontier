import LeanFrontier.NumberTheory.Mediant
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The least denominator between two Farey neighbours

Two fractions `a / b` and `c / d` with positive denominators are *Farey neighbours* when their
cross determinant `b * c - a * d` is `1`. This module proves that the mediant is then the
simplest fraction lying strictly between them: any `p / q` with `q > 0` and
`a / b < p / q < c / d` has `q ≥ b + d`, and `q = b + d` forces `p = a + c`.

Since the mediant `(a + c) / (b + d)` does lie strictly between the two, as recorded in the
mediant submission, these two results say that it is the unique fraction of least denominator in
the open interval. That is the property which makes the Stern-Brocot tree the tool for best
rational approximation.

## Main definitions

* `LeanFrontier.Farey.IsStrictlyBetween` - strict betweenness of `p / q` between `a / b` and
  `c / d`, written with cross multiplication so that it needs no division and no positivity.

## Main statements

* `LeanFrontier.Farey.add_le_of_isStrictlyBetween` - a fraction strictly between two Farey
  neighbours has denominator at least the sum of theirs.
* `LeanFrontier.Farey.eq_add_of_denom_eq_add` - if its denominator is exactly that sum, its
  numerator is the sum of the numerators, so the fraction is the mediant.

## Implementation notes

Both proofs rest on the identity `q = b * (c * q - p * d) + d * (p * b - a * q)`, valid whenever
the cross determinant is `1`. Strict betweenness makes both bracketed integers at least `1`, so
the first result is immediate and the second follows because equality forces both of them to
equal `1`.

Fractions are carried as separate numerator and denominator arguments, as in the mediant
submission, and `LeanFrontier.Mediant.crossDet` is reused rather than restated. Working over the
integers is what gives the results their content: the step from `a * q < p * b` to
`1 ≤ p * b - a * q` is exactly where integrality enters, and over the rationals the statements
would be vacuous.
-/

namespace LeanFrontier.Farey

variable {a b c d p q : ℤ}

/-- `p / q` lies strictly between `a / b` and `c / d`, expressed by cross multiplication. For
positive `b`, `d` and `q` this is the usual `a / b < p / q` and `p / q < c / d`. -/
def IsStrictlyBetween (a b p q c d : ℤ) : Prop := a * q < p * b ∧ p * d < c * q

private theorem one_le_sub_of_lt {x y : ℤ} (h : x < y) : 1 ≤ y - x := by omega

/-- The key identity: with cross determinant `1`, the denominator `q` decomposes along the two
strictness gaps. -/
private theorem denom_decomposition (hdet : Mediant.crossDet a b c d = 1) :
    q = b * (c * q - p * d) + d * (p * b - a * q) := by
  unfold Mediant.crossDet at hdet
  linear_combination (-q) * hdet

/-- A fraction strictly between two Farey neighbours has denominator at least the sum of their
denominators. -/
theorem add_le_of_isStrictlyBetween (hb : 0 < b) (hd : 0 < d)
    (hdet : Mediant.crossDet a b c d = 1) (h : IsStrictlyBetween a b p q c d) :
    b + d ≤ q := by
  obtain ⟨hleft, hright⟩ := h
  have hY : 1 ≤ p * b - a * q := one_le_sub_of_lt hleft
  have hX : 1 ≤ c * q - p * d := one_le_sub_of_lt hright
  have key : q = b * (c * q - p * d) + d * (p * b - a * q) := denom_decomposition hdet
  nlinarith [mul_le_mul_of_nonneg_left hX hb.le, mul_le_mul_of_nonneg_left hY hd.le]

/-- If a fraction strictly between two Farey neighbours attains the least possible denominator,
it is the mediant: its numerator is forced to be the sum of the numerators. -/
theorem eq_add_of_denom_eq_add (hb : 0 < b) (hd : 0 < d)
    (hdet : Mediant.crossDet a b c d = 1) (h : IsStrictlyBetween a b p q c d)
    (hq : q = b + d) : p = a + c := by
  obtain ⟨hleft, hright⟩ := h
  subst hq
  have hY : 1 ≤ p * b - a * (b + d) := one_le_sub_of_lt hleft
  have hX : 1 ≤ c * (b + d) - p * d := one_le_sub_of_lt hright
  have key : b + d = b * (c * (b + d) - p * d) + d * (p * b - a * (b + d)) :=
    denom_decomposition hdet
  have hzero : b * (c * (b + d) - p * d - 1) + d * (p * b - a * (b + d) - 1) = 0 := by
    linarith
  have hbnn : 0 ≤ b * (c * (b + d) - p * d - 1) := mul_nonneg hb.le (by linarith)
  have hdnn : 0 ≤ d * (p * b - a * (b + d) - 1) := mul_nonneg hd.le (by linarith)
  have hbeq : b * (p * b - a * (b + d) - 1) = 0 := by
    have hde : d * (p * b - a * (b + d) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hde with hcontra | hgap
    · exact absurd hcontra hd.ne'
    · rw [hgap, mul_zero]
  have hgap : p * b - a * (b + d) = 1 := by
    rcases mul_eq_zero.mp hbeq with hcontra | hgap
    · exact absurd hcontra hb.ne'
    · linarith
  unfold Mediant.crossDet at hdet
  have hfin : b * (p - a - c) = 0 := by linear_combination hgap - hdet
  rcases mul_eq_zero.mp hfin with hcontra | hres
  · exact absurd hcontra hb.ne'
  · linarith

end LeanFrontier.Farey
