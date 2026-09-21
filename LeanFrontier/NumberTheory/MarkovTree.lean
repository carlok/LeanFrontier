import LeanFrontier.NumberTheory.MarkovEquation

/-!
# Descent for ordered positive Markov triples

The Vieta involution from `LeanFrontier.NumberTheory.MarkovEquation`
is the local move underlying the Markov tree.

For a positive solution ordered `x ≤ y ≤ z`, the exceptional root
`(1, 1, 1)` is the only case in which the largest two coordinates can
coincide without a descending Vieta move. Away from that root, jumping
the largest coordinate produces another positive coordinate at or below
the middle one, and hence strictly decreases the largest coordinate.
-/

namespace LeanFrontier.MarkovTree

private theorem root_of_middle_eq_largest
    {x y z : ℤ}
    (hx : 0 < x)
    (hxy : x ≤ y)
    (hyz_eq : y = z)
    (h : MarkovEquation.IsSolution x y z) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  subst z
  unfold MarkovEquation.IsSolution at h

  have hy : 0 < y := lt_of_lt_of_le hx hxy

  have hsq : x ^ 2 ≤ y ^ 2 := by
    have hprod : 0 ≤ (y - x) * (y + x) := by
      exact mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
    nlinarith

  have hx1 : 1 ≤ x := by
    have h1 : 0 + 1 ≤ x := Int.add_one_le_iff.mpr hx
    simpa using h1

  have hx_lt_two : x < 2 := by
    by_contra hx_not
    have hx2 : 2 ≤ x := le_of_not_gt hx_not
    nlinarith

  have hx_le_one : x ≤ 1 := by
    have hlt : x < 1 + 1 := by simpa using hx_lt_two
    exact Int.lt_add_one_iff.mp hlt

  have hx_eq : x = 1 := le_antisymm hx_le_one hx1
  subst x

  have hy1 : 1 ≤ y := by
    have h1 : 0 + 1 ≤ y := Int.add_one_le_iff.mpr hy
    simpa using h1

  have hy_le : y ≤ 1 := by
    by_contra hy_not
    have hy_gt_one : 1 < y := lt_of_not_ge hy_not
    have hy2' : 1 + 1 ≤ y := Int.add_one_le_iff.mpr hy_gt_one
    have hy2 : 2 ≤ y := by simpa using hy2'
    nlinarith

  have hy_eq : y = 1 := le_antisymm hy_le hy1
  subst y

  exact ⟨rfl, rfl, rfl⟩

/--
For a positive ordered Markov triple other than `(1, 1, 1)`, the Vieta
jump in the largest coordinate is again positive, lies at or below the
middle coordinate, and therefore strictly decreases the largest coordinate.
-/
theorem jump_descends_ordered_positive
    {x y z : ℤ}
    (hx : 0 < x)
    (hxy : x ≤ y)
    (hyz : y ≤ z)
    (h : MarkovEquation.IsSolution x y z)
    (hne : ¬ (x = 1 ∧ y = 1 ∧ z = 1)) :
    0 < MarkovEquation.jump x y z ∧
      MarkovEquation.jump x y z ≤ y ∧
      MarkovEquation.jump x y z < z := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hz : 0 < z := lt_of_lt_of_le hy hyz

  have hyz_ne : y ≠ z := by
    intro hyz_eq
    exact hne (root_of_middle_eq_largest hx hxy hyz_eq h)

  have hyz_lt : y < z := lt_of_le_of_ne hyz hyz_ne

  have hjump_pos : 0 < MarkovEquation.jump x y z :=
    MarkovEquation.jump_pos hx hz h

  have hsq : x ^ 2 ≤ y ^ 2 := by
    have hprod : 0 ≤ (y - x) * (y + x) := by
      exact mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
    nlinarith

  have hx1 : 1 ≤ x := by
    have h1 : 0 + 1 ≤ x := Int.add_one_le_iff.mpr hx
    simpa using h1

  have hx_minus_one : 0 ≤ x - 1 := sub_nonneg.mpr hx1
  have htail : 0 ≤ (x - 1) * y ^ 2 :=
    mul_nonneg hx_minus_one (sq_nonneg y)

  have hpoly : x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 ≤ 0 := by
    nlinarith

  have hfactor :
      (y - z) * (y - MarkovEquation.jump x y z) =
        x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 := by
    calc
      (y - z) * (y - MarkovEquation.jump x y z) =
          y ^ 2 - 3 * x * y ^ 2 + z * MarkovEquation.jump x y z := by
            rw [MarkovEquation.jump]
            ring
      _ = x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 := by
            rw [MarkovEquation.mul_jump_eq h]
            ring

  have hleft_neg : y - z < 0 := by linarith

  have hjump_le : MarkovEquation.jump x y z ≤ y := by
    have hright_nonneg : 0 ≤ y - MarkovEquation.jump x y z := by
      by_contra hn
      have hright_neg : y - MarkovEquation.jump x y z < 0 :=
        lt_of_not_ge hn
      have hpositive :
          0 < (y - z) * (y - MarkovEquation.jump x y z) :=
        mul_pos_of_neg_of_neg hleft_neg hright_neg
      nlinarith
    exact sub_nonneg.mp hright_nonneg

  exact ⟨hjump_pos, hjump_le, lt_of_le_of_lt hjump_le hyz_lt⟩

end LeanFrontier.MarkovTree
