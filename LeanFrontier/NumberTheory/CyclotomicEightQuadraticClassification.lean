import LeanFrontier.NumberTheory.CyclotomicEightGalois
import LeanFrontier.NumberTheory.CyclotomicEightGaussian
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic

/-!
# The three quadratic intermediate fields of the eighth cyclotomic field

The accepted structural pieces now give two complementary descriptions of
`ℚ(ζ₈)/ℚ`:

* its Galois group is Klein four;
* the three classical quadratic directions `√2`, `√-2`, and `i` are available
  internally.

This module proves the global counting statement: the extension has exactly three
quadratic intermediate fields.

The proof is structural. Galois correspondence identifies quadratic intermediate
fields with index-two subgroups of the Galois group. The accepted Klein-four
equivalence transports those subgroups to `Multiplicative (𝔽₂²)`. Reinterpreting
them additively turns index-two subgroups into one-dimensional `𝔽₂`-subspaces.
Those are precisely the points of the projective line `ℙ(𝔽₂²)`, whose cardinality
is `2 + 1 = 3` by Mathlib's projectivization cardinality theorem.
-/

namespace LeanFrontier.NumberTheory.DiscriminantTower

open NumberField
open scoped LinearAlgebra.Projectivization

noncomputable section

local instance : NeZero (8 : ℕ) := ⟨by decide⟩

local instance cyclotomicEight_isCyclotomic_classification :
    IsCyclotomicExtension {8} ℚ CyclotomicEight :=
  CyclotomicField.isCyclotomicExtension 8 ℚ

local instance cyclotomicEight_finiteDimensional_classification :
    FiniteDimensional ℚ CyclotomicEight :=
  IsCyclotomicExtension.finiteDimensional {8} ℚ CyclotomicEight

local instance cyclotomicEight_isGalois_classification :
    IsGalois ℚ CyclotomicEight :=
  IsCyclotomicExtension.isGalois {8} ℚ CyclotomicEight

private abbrev GalEight := Gal(CyclotomicEight/ℚ)
private abbrev KleinFourModel := Multiplicative (ZMod 2 × ZMod 2)
private abbrev F2Plane := ZMod 2 × ZMod 2

/-- The type of quadratic intermediate fields of `ℚ(ζ₈)/ℚ`. -/
def CyclotomicEightQuadraticFields :=
  {K : IntermediateField ℚ CyclotomicEight // Module.finrank ℚ K = 2}

private def IndexTwoSubgroups (G : Type*) [Group G] :=
  {H : Subgroup G // H.index = 2}

private def OneDimensionalF2Subspaces :=
  {S : Submodule (ZMod 2) F2Plane // Module.finrank (ZMod 2) S = 1}

private noncomputable def quadraticFieldsEquivIndexTwoGal :
    CyclotomicEightQuadraticFields ≃ IndexTwoSubgroups GalEight where
  toFun K :=
    ⟨K.1.fixingSubgroup,
      (IntermediateField.finrank_eq_fixingSubgroup_index
        CyclotomicEight K.1).symm.trans K.2⟩
  invFun H :=
    ⟨IntermediateField.fixedField H.1, by
      calc
        Module.finrank ℚ (IntermediateField.fixedField H.1) =
            (IntermediateField.fixedField H.1).fixingSubgroup.index :=
          IntermediateField.finrank_eq_fixingSubgroup_index
            CyclotomicEight (IntermediateField.fixedField H.1)
        _ = H.1.index := by
          rw [IntermediateField.fixingSubgroup_fixedField]
        _ = 2 := H.2⟩
  left_inv K := by
    apply Subtype.ext
    exact IsGalois.fixedField_fixingSubgroup K.1
  right_inv H := by
    apply Subtype.ext
    exact IntermediateField.fixingSubgroup_fixedField H.1

private noncomputable def galIndexTwoEquivKleinIndexTwo :
    IndexTwoSubgroups GalEight ≃ IndexTwoSubgroups KleinFourModel :=
  Equiv.subtypeEquiv cyclotomicEightGalEquivKleinFour.mapSubgroup.toEquiv fun H => by
    change
      H.index = 2 ↔
        (Subgroup.map (cyclotomicEightGalEquivKleinFour : GalEight →* KleinFourModel) H).index = 2
    rw [Subgroup.index_map_equiv]

private noncomputable def kleinSubgroupToF2Subspace :
    Subgroup KleinFourModel ≃o Submodule (ZMod 2) F2Plane :=
  Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)

private theorem card_kleinSubgroup_eq_card_subspace (H : Subgroup KleinFourModel) :
    Nat.card H = Nat.card (kleinSubgroupToF2Subspace H) := by
  let e : H ≃ (kleinSubgroupToF2Subspace H) :=
    Equiv.subtypeEquiv Multiplicative.ofAdd.symm (fun x => by rfl)
  exact Nat.card_congr e

private theorem klein_index_two_iff_finrank_one (H : Subgroup KleinFourModel) :
    H.index = 2 ↔ Module.finrank (ZMod 2) (kleinSubgroupToF2Subspace H) = 1 := by
  let S := kleinSubgroupToF2Subspace H
  have hamb : Nat.card KleinFourModel = 4 := by
    calc
      Nat.card KleinFourModel = Nat.card F2Plane :=
        Nat.card_congr Multiplicative.ofAdd.symm
      _ = 4 := by simp [F2Plane]
  have hcard : Nat.card H = Nat.card S := card_kleinSubgroup_eq_card_subspace H
  have hpow : Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  constructor
  · intro hindex
    have hmul := H.index_mul_card
    rw [hindex, hamb] at hmul
    have hHcard : Nat.card H = 2 := by omega
    have hpowe : 2 ^ Module.finrank (ZMod 2) S = 2 ^ 1 := by
      rw [← hpow, ← hcard, hHcard]
      norm_num
    exact Nat.pow_right_injective (by omega) hpowe
  · intro hfinrank
    have hScard : Nat.card S = 2 := by
      rw [hpow, hfinrank]
      norm_num
    have hHcard : Nat.card H = 2 := hcard.trans hScard
    have hmul := H.index_mul_card
    rw [hHcard, hamb] at hmul
    omega

private noncomputable def kleinIndexTwoEquivOneDimensional :
    IndexTwoSubgroups KleinFourModel ≃ OneDimensionalF2Subspaces :=
  Equiv.subtypeEquiv kleinSubgroupToF2Subspace.toEquiv
    klein_index_two_iff_finrank_one

private noncomputable def quadraticFieldsEquivProjectiveLine :
    CyclotomicEightQuadraticFields ≃ ℙ (ZMod 2) F2Plane :=
  quadraticFieldsEquivIndexTwoGal.trans <|
    galIndexTwoEquivKleinIndexTwo.trans <|
      kleinIndexTwoEquivOneDimensional.trans <|
        (Projectivization.equivSubmodule (ZMod 2) F2Plane).symm

/-- The eighth cyclotomic field has exactly three quadratic intermediate fields. -/
theorem cyclotomicEight_quadraticFields_card :
    Nat.card CyclotomicEightQuadraticFields = 3 := by
  calc
    Nat.card CyclotomicEightQuadraticFields =
        Nat.card (ℙ (ZMod 2) F2Plane) :=
      Nat.card_congr quadraticFieldsEquivProjectiveLine
    _ = Nat.card (ZMod 2) + 1 :=
      Projectivization.card_of_finrank_two (ZMod 2) F2Plane (by simp)
    _ = 3 := by simp

end

end LeanFrontier.NumberTheory.DiscriminantTower
