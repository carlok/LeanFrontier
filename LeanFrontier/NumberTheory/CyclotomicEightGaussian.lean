import LeanFrontier.NumberTheory.DiscriminantTowerWitness
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

/-!
# The Gaussian quadratic subfield inside the eighth cyclotomic field

The accepted discriminant witness already constructs the two quadratic directions
corresponding to `ℚ(√2)` and `ℚ(√-2)`. Their product gives the missing classical
third direction:

`(√2 · √-2) / 2 = i`.

This module packages that element intrinsically inside `CyclotomicEight`, proves its
square is `-1`, identifies its exact minimal polynomial over `ℚ` as `X² + 1`,
and proves that the generated intermediate field is quadratic.

The intended downstream consumer is the structural classification of all three
quadratic intermediate fields via the Klein-four Galois group.
-/

namespace LeanFrontier.NumberTheory.DiscriminantTower

open Polynomial IntermediateField

noncomputable section

/-- The Gaussian generator inside `ℚ(ζ₈)`, obtained from the already accepted
`√2` and `√-2` generators. -/
noncomputable def sqrtNegOneGen : CyclotomicEight :=
  sqrtTwoGen * sqrtNegTwoGen / 2

/-- The Gaussian generator is a square root of `-1`. -/
theorem sqrtNegOneGen_sq :
    sqrtNegOneGen ^ 2 = (-1 : CyclotomicEight) := by
  rw [sqrtNegOneGen, div_pow, mul_pow, sqrtTwoGen_sq, sqrtNegTwoGen_sq]
  norm_num

private def quadIQ : ℚ[X] := X ^ 2 + C 1

private theorem quadIQ_irreducible : Irreducible quadIQ := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [quadIQ]
  · intro x hx
    rw [Polynomial.IsRoot.def] at hx
    simp [quadIQ] at hx
    nlinarith [sq_nonneg x]

private theorem minpoly_sqrtNegOneGen :
    minpoly ℚ sqrtNegOneGen = quadIQ := by
  symm
  apply minpoly.eq_of_irreducible_of_monic quadIQ_irreducible
  · rw [quadIQ]
    simp only [map_add, map_pow, aeval_X, aeval_C]
    rw [sqrtNegOneGen_sq]
    norm_num
  · exact monic_X_pow_add_C (1 : ℚ) (by decide)

/-- The internal Gaussian generator has the expected quadratic minimal polynomial. -/
theorem sqrtNegOneGen_minpoly :
    minpoly ℚ sqrtNegOneGen = X ^ 2 + C 1 := by
  simpa [quadIQ] using minpoly_sqrtNegOneGen

/-- The third classical quadratic subfield of `ℚ(ζ₈)`, corresponding to `ℚ(i)`. -/
noncomputable def gaussianField : IntermediateField ℚ CyclotomicEight :=
  ℚ⟮sqrtNegOneGen⟯

/-- The degree of the Gaussian intermediate field. Naming the full finrank expression keeps
the structural theorem compact for receiver fingerprinting. -/
noncomputable def gaussianFieldDegree : ℕ :=
  Module.finrank ℚ gaussianField

/-- The Gaussian intermediate field inside the eighth cyclotomic field has degree two. -/
theorem gaussianField_degree :
    gaussianFieldDegree = 2 := by
  rw [gaussianFieldDegree, gaussianField, IntermediateField.adjoin.finrank
      (IsIntegral.of_finite ℚ sqrtNegOneGen), minpoly_sqrtNegOneGen]
  simp [quadIQ]

end

end LeanFrontier.NumberTheory.DiscriminantTower
