import LeanFrontier.NumberTheory.Farey
import LeanFrontier.NumberTheory.FordCircle
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The largest Ford circle in a Farey gap

For positive-denominator Farey neighbours `a / b < c / d`, the accepted Farey development
shows that every integer fraction `p / q` strictly between them has `q ≥ b + d`, with equality
only for the mediant. Since a Ford-circle radius is `1 / (2 * q ^ 2)`, denominator minimality
becomes radius maximality.

This module composes those two accepted interfaces. It proves that the mediant itself lies in
the open Farey gap and that its Ford circle is the unique largest Ford circle represented by an
integer numerator/positive denominator in that gap.
-/

namespace LeanFrontier.FordCircle

/-- Between positive-denominator Farey neighbours, the mediant lies in the open gap and its
Ford-circle radius is maximal there. Equality of radii uniquely identifies the mediant
numerator and denominator.

Fractions are intentionally represented by integer numerator/denominator pairs, matching the
accepted `Farey` and `Mediant` APIs. The strict-betweenness hypothesis forces every competing
denominator to be at least `b + d > 0`, so non-reduced or negative-denominator representatives
cannot create a spurious equality case. -/
theorem mediant_is_unique_largest_in_farey_gap
    {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : Mediant.crossDet a b c d = 1) :
    Farey.IsStrictlyBetween a b (a + c) (b + d) c d ∧
      ∀ {p q : ℤ}, Farey.IsStrictlyBetween a b p q c d →
        radius (q : ℝ) ≤ radius ((b + d : ℤ) : ℝ) ∧
          (radius (q : ℝ) = radius ((b + d : ℤ) : ℝ) ↔
            p = a + c ∧ q = b + d) := by
  have hmediant : Farey.IsStrictlyBetween a b (a + c) (b + d) c d := by
    unfold Farey.IsStrictlyBetween
    have hdet' := hdet
    unfold Mediant.crossDet at hdet'
    constructor <;> nlinarith
  refine ⟨hmediant, ?_⟩
  intro p q hbetween
  have hden : b + d ≤ q :=
    Farey.add_le_of_isStrictlyBetween hb hd hdet hbetween
  have hbd_pos_int : 0 < b + d := add_pos hb hd
  have hq_pos_int : 0 < q := hbd_pos_int.trans_le hden
  have hden_real : ((b + d : ℤ) : ℝ) ≤ (q : ℝ) := Int.cast_le.mpr hden
  have hbd_pos : (0 : ℝ) < ((b + d : ℤ) : ℝ) := Int.cast_pos.mpr hbd_pos_int
  have hq_pos : (0 : ℝ) < (q : ℝ) := Int.cast_pos.mpr hq_pos_int
  have hsq :
      ((b + d : ℤ) : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 :=
    (sq_le_sq₀ hbd_pos.le hq_pos.le).2 hden_real
  have hradius : radius (q : ℝ) ≤ radius ((b + d : ℤ) : ℝ) := by
    unfold radius
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  refine ⟨hradius, ?_⟩
  constructor
  · intro heq
    have hqeq : q = b + d := by
      by_contra hne
      have hlt_int : b + d < q := lt_of_le_of_ne hden (Ne.symm hne)
      have hlt : ((b + d : ℤ) : ℝ) < (q : ℝ) := Int.cast_lt.mpr hlt_int
      have hsq_lt :
          ((b + d : ℤ) : ℝ) ^ 2 < (q : ℝ) ^ 2 :=
        (sq_lt_sq₀ hbd_pos.le hq_pos.le).2 hlt
      have hden_lt :
          2 * ((b + d : ℤ) : ℝ) ^ 2 < 2 * (q : ℝ) ^ 2 := by
        nlinarith
      have hradius_lt : radius (q : ℝ) < radius ((b + d : ℤ) : ℝ) := by
        unfold radius
        exact one_div_lt_one_div_of_lt (by positivity) hden_lt
      exact (ne_of_lt hradius_lt) heq
    have hp :=
      Farey.eq_add_of_denom_eq_add hb hd hdet hbetween hqeq
    exact ⟨hp, hqeq⟩
  · rintro ⟨-, rfl⟩
    rfl

end LeanFrontier.FordCircle
