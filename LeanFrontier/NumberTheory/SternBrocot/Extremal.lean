import LeanFrontier.NumberTheory.SternBrocot.Intervals
import LeanFrontier.NumberTheory.Farey

/-!
# Extremal mediants in Stern-Brocot intervals

The accepted Stern-Brocot interval state carries two unimodular boundary pairs. Their mediant is
therefore strictly between them in the cross-multiplied Farey sense. Once both boundary
denominators are positive, the accepted Farey denominator theorem makes this mediant the unique
interior fraction of least denominator.

This module packages that extremal property at every finite Stern-Brocot interval state.
-/

namespace LeanFrontier.SternBrocot

/-- The mediant of the two boundary pairs at every Stern-Brocot path lies strictly between the
boundaries in the integer cross-multiplication sense. This remains meaningful on the outer
spines, where one boundary denominator may still be zero. -/
theorem mediant_isStrictlyBetween_bounds (path : List Bool) :
    Farey.IsStrictlyBetween
      (bounds path).1.1 (bounds path).1.2
      ((bounds path).1.1 + (bounds path).2.1)
      ((bounds path).1.2 + (bounds path).2.2)
      (bounds path).2.1 (bounds path).2.2 := by
  have hdet := crossDet_bounds path
  unfold Mediant.crossDet at hdet
  unfold Farey.IsStrictlyBetween
  constructor <;> nlinarith

/-- If both boundary denominators of a Stern-Brocot interval are positive, every interior
fraction has denominator at least the mediant denominator. Equality of denominators forces the
interior numerator to be the mediant numerator, so the mediant is the unique least-denominator
interior representative. -/
theorem mediant_leastDenominator_bounds (path : List Bool)
    (hleft : 0 < (bounds path).1.2) (hright : 0 < (bounds path).2.2)
    {p q : ℤ}
    (hbetween :
      Farey.IsStrictlyBetween
        (bounds path).1.1 (bounds path).1.2
        p q
        (bounds path).2.1 (bounds path).2.2) :
    (bounds path).1.2 + (bounds path).2.2 ≤ q ∧
      (q = (bounds path).1.2 + (bounds path).2.2 →
        p = (bounds path).1.1 + (bounds path).2.1) := by
  have hdet := crossDet_bounds path
  constructor
  · exact Farey.add_le_of_isStrictlyBetween hleft hright hdet hbetween
  · intro hq
    exact Farey.eq_add_of_denom_eq_add hleft hright hdet hbetween hq

end LeanFrontier.SternBrocot
