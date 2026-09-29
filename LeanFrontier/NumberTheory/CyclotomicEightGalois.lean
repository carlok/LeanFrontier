import LeanFrontier.NumberTheory.DiscriminantTowerWitness
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The Galois group of the eighth cyclotomic field

The accepted discriminant witness already gives explicit quadratic subfields inside
`ℚ(ζ₈)`. This module records the structural reason there are exactly three quadratic
directions to find: the full Galois group is the Klein four group.

Mathlib supplies the generic cyclotomic equivalence

`Gal(ℚ(ζ₈)/ℚ) ≃* (ZMod 8)ˣ`.

We prove that the target has order four and exponent two, package that as
`IsKleinFour`, and transport the structure back across the cyclotomic equivalence.
An explicit (noncanonical) equivalence with the standard model
`Multiplicative (ZMod 2 × ZMod 2)` is then exposed for downstream subgroup-lattice
arguments.

The intended next consumer is the classification of the three index-two subgroups and,
through Galois correspondence, the three quadratic intermediate fields.
-/

namespace LeanFrontier.NumberTheory.DiscriminantTower

open NumberField

noncomputable section

local instance cyclotomicEight_isCyclotomic_galois :
    IsCyclotomicExtension {8} ℚ CyclotomicEight :=
  CyclotomicField.isCyclotomicExtension 8 ℚ

/-- The unit group modulo eight is a Klein four group. Kept as proof data here because
Mathlib already provides all of the underlying arithmetic facts. -/
private def zmodEightUnitsIsKleinFour : IsKleinFour (ZMod 8)ˣ where
  card_four := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  exponent_two := by
    apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
    · have horder : orderOf (-1 : (ZMod 8)ˣ) = 2 := by
        rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod 8) 8]
        norm_num
      rw [← horder]
      exact Monoid.order_dvd_exponent (-1 : (ZMod 8)ˣ)

/-- The Galois group of the eighth cyclotomic field over `ℚ` is a Klein four group.

This uses Mathlib's generic cyclotomic Galois equivalence rather than constructing
automorphisms by hand from the explicit generators. -/
theorem cyclotomicEight_galoisGroup_isKleinFour :
    IsKleinFour (Gal(CyclotomicEight/ℚ)) := by
  let e : Gal(CyclotomicEight/ℚ) ≃* (ZMod 8)ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod 8 CyclotomicEight
  let h : IsKleinFour (ZMod 8)ˣ := zmodEightUnitsIsKleinFour
  constructor
  · rw [Nat.card_congr e.toEquiv]
    exact h.card_four
  · rw [Monoid.exponent_eq_of_mulEquiv e]
    exact h.exponent_two

/-- A concrete group isomorphism from the Galois group of `ℚ(ζ₈)` to the standard
Klein-four model. The choice is intentionally noncanonical; downstream lattice results
should depend only on the group structure. -/
noncomputable def cyclotomicEightGalEquivKleinFour :
    Gal(CyclotomicEight/ℚ) ≃* Multiplicative (ZMod 2 × ZMod 2) := by
  letI : IsKleinFour (Gal(CyclotomicEight/ℚ)) :=
    cyclotomicEight_galoisGroup_isKleinFour
  exact Classical.choice IsKleinFour.nonempty_mulEquiv

end

end LeanFrontier.NumberTheory.DiscriminantTower
