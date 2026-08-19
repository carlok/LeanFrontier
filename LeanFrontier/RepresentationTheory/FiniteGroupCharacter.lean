import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Sums of finite-group multiplicative characters

A nontrivial multiplicative character of a finite group has sum zero in any
ring without zero divisors.  The codomain need not be commutative.
-/

open scoped BigOperators

namespace LeanFrontier.FiniteGroupCharacter

variable {G R : Type*} [Group G] [Fintype G] [Ring R] [NoZeroDivisors R]

/-- A nontrivial monoid homomorphism from a finite group into a ring without
zero divisors has sum zero. -/
theorem sum_monoidHom_eq_zero_of_ne_one (chi : G →* R) (hchi : chi ≠ 1) :
    ∑ g : G, chi g = 0 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hchi
  have ha' : chi a ≠ 1 := by simpa using ha
  have hreindex : (∑ g : G, chi (a * g)) = ∑ g : G, chi g :=
    (Equiv.mulLeft a).bijective.sum_comp (fun g : G ↦ chi g)
  have hscale : chi a * (∑ g : G, chi g) = ∑ g : G, chi g := by
    rw [Finset.mul_sum]
    simpa only [map_mul] using hreindex
  have hzero : (chi a - 1) * (∑ g : G, chi g) = 0 := by
    rw [sub_mul, hscale, one_mul, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ha')

end LeanFrontier.FiniteGroupCharacter
