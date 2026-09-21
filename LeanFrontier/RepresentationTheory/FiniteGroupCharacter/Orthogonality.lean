import LeanFrontier.RepresentationTheory.FiniteGroupCharacter

/-!
# Orthogonality of finite-group multiplicative characters

Distinct one-dimensional multiplicative characters of a finite group have zero
sum after taking their pointwise quotient. The proof packages the quotient in
the unit group and reuses the accepted zero-sum theorem for nontrivial
characters.
-/

open scoped BigOperators

namespace LeanFrontier.FiniteGroupCharacter

variable {G K : Type*} [Group G] [Fintype G] [Field K]

/-- The pointwise quotient of two distinct multiplicative characters of a finite
group has sum zero. -/
theorem sum_div_eq_zero_of_ne (chi psi : G →* K) (hchi : chi ≠ psi) :
    ∑ g : G, chi g / psi g = 0 := by
  let qUnits : G →* Kˣ := chi.toHomUnits / psi.toHomUnits
  let q : G →* K := (Units.coeHom K).comp qUnits
  have hqUnits : qUnits ≠ 1 := by
    intro hq
    apply hchi
    apply MonoidHom.ext
    intro g
    have hg := congrArg (fun f : G →* Kˣ => f g) (eq_of_div_eq_one hq)
    simpa using congrArg (fun u : Kˣ => (u : K)) hg
  have hq : q ≠ 1 := by
    intro hq'
    apply hqUnits
    apply MonoidHom.ext
    intro g
    apply Units.ext
    have hg := congrArg (fun f : G →* K => f g) hq'
    simpa [q, qUnits] using hg
  have hz := sum_monoidHom_eq_zero_of_ne_one q hq
  simpa [q, qUnits] using hz

end LeanFrontier.FiniteGroupCharacter
