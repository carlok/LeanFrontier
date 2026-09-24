import LeanFrontier.NumberTheory.DiscriminantTower
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Tactic

/-!
# The explicit quadratic tower inside the eighth cyclotomic field

This file constructs the intended witness for
`LeanFrontier.NumberTheory.DiscriminantTower.CoprimalityIsLoadBearing`.

Let `ζ` be a primitive eighth root of unity.  The two elements

* `u = ζ + ζ^7`,
* `v = ζ - ζ^7`

satisfy `u^2 = 2` and `v^2 = -2`.  Their generated intermediate fields are therefore
the two quadratic subfields corresponding to `ℚ(√2)` and `ℚ(√-2)`.

The first layer below records the explicit field-theoretic structure: both subfields have degree
two, their supremum is the full eighth cyclotomic field, and hence they are linearly disjoint.
The discriminant computation is developed on top of this structure.
-/

namespace LeanFrontier.NumberTheory.DiscriminantTower

open scoped IntermediateField
open Polynomial IntermediateField NumberField

noncomputable section

abbrev CyclotomicEight := CyclotomicField 8 ℚ

noncomputable def zetaEight : CyclotomicEight :=
  IsCyclotomicExtension.zeta 8 ℚ CyclotomicEight

private def zetaEight_spec : IsPrimitiveRoot zetaEight 8 := by
  exact IsCyclotomicExtension.zeta_spec 8 ℚ CyclotomicEight

private def zetaEight_pow_eight : zetaEight ^ 8 = 1 :=
  zetaEight_spec.pow_eq_one

private def zetaEight_pow_four : zetaEight ^ 4 = -1 := by
  have hsq : (zetaEight ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact zetaEight_pow_eight
  exact (sq_eq_one_iff.mp hsq).resolve_left <|
    zetaEight_spec.pow_ne_one_of_pos_of_lt (by decide) (by decide)

noncomputable def sqrtTwoGen : CyclotomicEight :=
  zetaEight + zetaEight ^ 7

noncomputable def sqrtNegTwoGen : CyclotomicEight :=
  zetaEight - zetaEight ^ 7

private def zetaEight_pow_six : zetaEight ^ 6 = -(zetaEight ^ 2) := by
  calc
    zetaEight ^ 6 = zetaEight ^ 2 * zetaEight ^ 4 := by ring
    _ = -(zetaEight ^ 2) := by rw [zetaEight_pow_four]; ring

private def zetaEight_pow_fourteen : zetaEight ^ 14 = zetaEight ^ 6 := by
  calc
    zetaEight ^ 14 = zetaEight ^ 6 * zetaEight ^ 8 := by ring
    _ = zetaEight ^ 6 := by rw [zetaEight_pow_eight, mul_one]

theorem sqrtTwoGen_sq : sqrtTwoGen ^ 2 = (2 : CyclotomicEight) := by
  rw [sqrtTwoGen]
  calc
    (zetaEight + zetaEight ^ 7) ^ 2 =
        zetaEight ^ 2 + 2 * zetaEight ^ 8 + zetaEight ^ 14 := by ring
    _ = 2 := by
      rw [zetaEight_pow_eight, zetaEight_pow_fourteen, zetaEight_pow_six]
      ring

theorem sqrtNegTwoGen_sq : sqrtNegTwoGen ^ 2 = (-2 : CyclotomicEight) := by
  rw [sqrtNegTwoGen]
  calc
    (zetaEight - zetaEight ^ 7) ^ 2 =
        zetaEight ^ 2 - 2 * zetaEight ^ 8 + zetaEight ^ 14 := by ring
    _ = -2 := by
      rw [zetaEight_pow_eight, zetaEight_pow_fourteen, zetaEight_pow_six]
      ring

noncomputable def sqrtTwoField : IntermediateField ℚ CyclotomicEight :=
  ℚ⟮sqrtTwoGen⟯

noncomputable def sqrtNegTwoField : IntermediateField ℚ CyclotomicEight :=
  ℚ⟮sqrtNegTwoGen⟯

private def quadPlusZ : ℤ[X] := X ^ 2 - C 2
private def quadMinusZ : ℤ[X] := X ^ 2 + C 2
private def quadPlusQ : ℚ[X] := X ^ 2 - C 2
private def quadMinusQ : ℚ[X] := X ^ 2 + C 2

private def spanTwo : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

private def spanTwo_prime : spanTwo.IsPrime := by
  rw [spanTwo, Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0),
    Int.prime_iff_natAbs_prime]
  norm_num

private def quadPlusZ_eisenstein : quadPlusZ.IsEisensteinAt spanTwo := by
  apply (show quadPlusZ.Monic by
    rw [quadPlusZ]
    monicity).isEisensteinAt_of_mem_of_notMem
  · exact spanTwo_prime.ne_top
  · intro n hn
    rw [quadPlusZ] at hn ⊢
    have hn' : n < 2 := by simpa using hn
    interval_cases n <;>
      simp [spanTwo, Ideal.mem_span_singleton]
  · simp [quadPlusZ, spanTwo, Ideal.mem_span_singleton, pow_two]
    norm_num

private def quadMinusZ_eisenstein : quadMinusZ.IsEisensteinAt spanTwo := by
  apply (show quadMinusZ.Monic by
    rw [quadMinusZ]
    monicity).isEisensteinAt_of_mem_of_notMem
  · exact spanTwo_prime.ne_top
  · intro n hn
    rw [quadMinusZ] at hn ⊢
    have hn' : n < 2 := by simpa using hn
    interval_cases n <;>
      simp [spanTwo, Ideal.mem_span_singleton]
  · simp [quadMinusZ, spanTwo, Ideal.mem_span_singleton, pow_two]
    norm_num

private def quadPlusZ_irreducible : Irreducible quadPlusZ :=
  quadPlusZ_eisenstein.irreducible spanTwo_prime
    (by
      rw [quadPlusZ]
      exact (show (X ^ 2 - C (2 : ℤ)).Monic by monicity).isPrimitive)
    (by simp [quadPlusZ])

private def quadMinusZ_irreducible : Irreducible quadMinusZ :=
  quadMinusZ_eisenstein.irreducible spanTwo_prime
    (by
      rw [quadMinusZ]
      exact (show (X ^ 2 + C (2 : ℤ)).Monic by monicity).isPrimitive)
    (by simp [quadMinusZ])

private def quadPlusQ_irreducible : Irreducible quadPlusQ := by
  have h :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (show quadPlusZ.IsPrimitive by
        rw [quadPlusZ]
        exact (show (X ^ 2 - C (2 : ℤ)).Monic by monicity).isPrimitive)).mp
      quadPlusZ_irreducible
  simpa [quadPlusZ, quadPlusQ] using h

private def quadMinusQ_irreducible : Irreducible quadMinusQ := by
  have h :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (show quadMinusZ.IsPrimitive by
        rw [quadMinusZ]
        exact (show (X ^ 2 + C (2 : ℤ)).Monic by monicity).isPrimitive)).mp
      quadMinusZ_irreducible
  simpa [quadMinusZ, quadMinusQ] using h

private def minpoly_sqrtTwoGen : minpoly ℚ sqrtTwoGen = quadPlusQ := by
  symm
  apply minpoly.eq_of_irreducible_of_monic quadPlusQ_irreducible
  · rw [quadPlusQ]
    simp only [aeval_sub, aeval_pow, aeval_X, aeval_C]
    rw [sqrtTwoGen_sq]
    norm_num
  · rw [quadPlusQ]
    monicity

private def minpoly_sqrtNegTwoGen : minpoly ℚ sqrtNegTwoGen = quadMinusQ := by
  symm
  apply minpoly.eq_of_irreducible_of_monic quadMinusQ_irreducible
  · rw [quadMinusQ]
    simp only [aeval_add, aeval_pow, aeval_X, aeval_C]
    rw [sqrtNegTwoGen_sq]
    norm_num
  · rw [quadMinusQ]
    monicity

/-- The two explicit subfields generated by `ζ + ζ^7` and `ζ - ζ^7` are both quadratic. -/
theorem quadraticFields_degrees :
    Module.finrank ℚ sqrtTwoField = 2 ∧
      Module.finrank ℚ sqrtNegTwoField = 2 := by
  constructor
  · rw [sqrtTwoField, IntermediateField.adjoin.finrank
      (IsIntegral.of_finite ℚ sqrtTwoGen), minpoly_sqrtTwoGen]
    simp [quadPlusQ]
  · rw [sqrtNegTwoField, IntermediateField.adjoin.finrank
      (IsIntegral.of_finite ℚ sqrtNegTwoGen), minpoly_sqrtNegTwoGen]
    simp [quadMinusQ]

private def zetaEight_eq_half_sum :
    zetaEight = (2 : CyclotomicEight)⁻¹ * (sqrtTwoGen + sqrtNegTwoGen) := by
  rw [sqrtTwoGen, sqrtNegTwoGen]
  norm_num
  ring

/-- The two quadratic subfields generate the full eighth cyclotomic field. -/
theorem quadraticFields_sup :
    sqrtTwoField ⊔ sqrtNegTwoField = (⊤ : IntermediateField ℚ CyclotomicEight) := by
  apply top_unique
  rw [← IsCyclotomicExtension.adjoin_primitive_root_eq_top zetaEight_spec,
    IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst x
  rw [zetaEight_eq_half_sum]
  exact (sqrtTwoField ⊔ sqrtNegTwoField).mul_mem
    ((sqrtTwoField ⊔ sqrtNegTwoField).algebraMap_mem ((2 : ℚ)⁻¹))
    ((sqrtTwoField ⊔ sqrtNegTwoField).add_mem
      (le_sup_left (show sqrtTwoGen ∈ sqrtTwoField from
        IntermediateField.mem_adjoin_simple_self ℚ sqrtTwoGen))
      (le_sup_right (show sqrtNegTwoGen ∈ sqrtNegTwoField from
        IntermediateField.mem_adjoin_simple_self ℚ sqrtNegTwoGen)))

private def cyclotomicEight_degree :
    Module.finrank ℚ CyclotomicEight = 4 := by
  simpa using
    (IsCyclotomicExtension.Rat.finrank 8 CyclotomicEight)

private def cyclotomicEight_discr_abs :
    (NumberField.discr CyclotomicEight).natAbs = 256 := by
  simpa using
    (IsCyclotomicExtension.Rat.natAbs_discr (n := 8) (K := CyclotomicEight))

/-- The two explicit quadratic subfields are linearly disjoint over `ℚ`. -/
theorem quadraticFields_linearDisjoint :
    sqrtTwoField.LinearDisjoint sqrtNegTwoField := by
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  rw [quadraticFields_sup, IntermediateField.finrank_top', cyclotomicEight_degree,
    quadraticFields_degrees.1, quadraticFields_degrees.2]
  norm_num

/-- The ambient eighth cyclotomic field already has the degree and discriminant required by the
load-bearing witness. -/
theorem cyclotomicEight_ambient_invariants :
    Module.finrank ℚ CyclotomicEight = 4 ∧
      (NumberField.discr CyclotomicEight).natAbs = 256 :=
  ⟨cyclotomicEight_degree, cyclotomicEight_discr_abs⟩

end

end LeanFrontier.NumberTheory.DiscriminantTower
