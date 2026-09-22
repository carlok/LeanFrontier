import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Tactic.NormNum

/-!
# Coprimality of the different ideals in the compositum discriminant identity

For two linearly disjoint subfields `K₁` and `K₂` of a number field `L` whose compositum is all
of `L`, Mathlib records the identity

`|discr L| = |discr K₁| ^ [K₂ : ℚ] * |discr K₂| ^ [K₁ : ℚ]`

under the assumption that the different ideals of `K₁` and `K₂`, pushed into the ring of integers
of `L`, are coprime. Coprimality fails exactly when the two subfields share a ramified prime, and
this module records the claim that the identity fails with it.

The witness proposed for that claim is `ℚ(√2)` and `ℚ(√-2)` inside `ℚ(ζ₈)`. The two quadratic
subfields are linearly disjoint over `ℚ`, their compositum is the whole cyclotomic field, and both
ramify only at `2`, so their different ideals share the prime above `2` and are not coprime. The
identity would then predict `8 ^ 2 * 8 ^ 2 = 4096` for `|discr ℚ(ζ₈)|`, whose value is `256`.

What is established here is the reduction rather than the witness. Given a field and two subfields
with those degrees and those discriminants, the identity is contradicted and the claim follows.
The work left is therefore explicit: exhibit the cyclotomic tower and settle the five numerical
facts about it. Each is a separate obligation, and none of them is assumed anywhere below.

## Main definitions

* `LeanFrontier.DiscriminantTower.DiscrIdentity` - the compositum discriminant identity for a
  given field and pair of subfields, stated with no assumption on the different ideals.
* `LeanFrontier.DiscriminantTower.CoprimalityIsLoadBearing` - the claim that the identity, freed
  of the coprimality assumption, is false. Unresolved.

## Main statements

* `LeanFrontier.DiscriminantTower.loadBearing_of_witness` - a field of degree four over `ℚ` with
  discriminant of absolute value `256`, split into two quadratic subfields of discriminant
  absolute value `8`, settles the claim above.

## Implementation notes

`DiscrIdentity` is a definition rather than an inlined statement so that the claim and the
reduction refer to the same proposition, and so that a later resolution can be stated against it
without restating the identity a third time. The quantification is over `Type` rather than an
arbitrary universe: the intended witness is a subfield of the complex numbers, and the smaller
statement is the one a resolution has to reach.

The proof of the reduction is a rewrite followed by arithmetic. That is the point of stating it:
the mathematics sits entirely in the five hypotheses, which is where the remaining effort belongs
rather than in the bookkeeping around them.
-/

namespace LeanFrontier.DiscriminantTower

open NumberField Module

/-- The compositum discriminant identity for `K₁` and `K₂` inside `L`, with no assumption on the
different ideals. -/
def DiscrIdentity (L : Type) [Field L] [NumberField L]
    (K₁ K₂ : IntermediateField ℚ L) : Prop :=
  (discr L).natAbs = (discr K₁).natAbs ^ finrank ℚ K₂ * (discr K₂).natAbs ^ finrank ℚ K₁

/-- The coprimality assumption on the two different ideals cannot be dropped: there are a number
field and a pair of linearly disjoint subfields with compositum everything for which the identity
fails. Unresolved. -/
def CoprimalityIsLoadBearing : Prop :=
  ¬ ∀ (L : Type) [Field L] [NumberField L] (K₁ K₂ : IntermediateField ℚ L),
      K₁.LinearDisjoint K₂ → K₁ ⊔ K₂ = ⊤ → DiscrIdentity L K₁ K₂

/-- `K₁` and `K₂` split `L`: they are linearly disjoint and their compositum is all of `L`. -/
def Splits (L : Type) [Field L] [NumberField L] (K₁ K₂ : IntermediateField ℚ L) : Prop :=
  K₁.LinearDisjoint K₂ ∧ K₁ ⊔ K₂ = ⊤

/-- The absolute value of the discriminant of a subfield, as a natural number. -/
noncomputable def discrAbs {L : Type} [Field L] [NumberField L] (K : IntermediateField ℚ L) : ℕ :=
  (discr K).natAbs

/-- The degree of a subfield over `ℚ`. -/
noncomputable def degree {L : Type} [Field L] [NumberField L] (K : IntermediateField ℚ L) : ℕ :=
  finrank ℚ K

/-- A field of degree four over `ℚ` with discriminant of absolute value `256`, split into two
linearly disjoint quadratic subfields each of discriminant absolute value `8`, resolves
`CoprimalityIsLoadBearing`. The identity predicts `4096` where the hypothesis gives `256`. -/
theorem loadBearing_of_witness (L : Type) [Field L] [NumberField L]
    (K₁ K₂ : IntermediateField ℚ L) (hsplit : Splits L K₁ K₂)
    (hL : (discr L).natAbs = 256)
    (h₁ : discrAbs K₁ = 8) (h₂ : discrAbs K₂ = 8)
    (n₁ : degree K₁ = 2) (n₂ : degree K₂ = 2) :
    CoprimalityIsLoadBearing := by
  intro identity
  have h := identity L K₁ K₂ hsplit.1 hsplit.2
  unfold DiscrIdentity at h
  rw [hL, show (discr K₁).natAbs = 8 from h₁, show (discr K₂).natAbs = 8 from h₂,
    show finrank ℚ K₁ = 2 from n₁, show finrank ℚ K₂ = 2 from n₂] at h
  norm_num at h

end LeanFrontier.DiscriminantTower
