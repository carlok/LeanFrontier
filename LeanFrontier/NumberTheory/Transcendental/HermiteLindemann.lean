import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Algebraic.Integral

/-!
# A conditional Hermite--Lindemann corollary

The exponential form of Hermite--Lindemann makes complex exponentiation
injective when it is restricted to algebraic numbers.  The premise is explicit
because the pinned Mathlib release does not yet export Hermite--Lindemann.
-/

namespace LeanFrontier.HermiteLindemann

/-- Hermite--Lindemann implies that complex exponentiation is injective when
restricted to algebraic numbers. -/
theorem exp_injOn_isAlgebraic
    (hermiteLindemann :
      ∀ {z : ℂ}, z ≠ 0 → IsAlgebraic ℤ z → Transcendental ℤ (Complex.exp z)) :
    Set.InjOn Complex.exp {z : ℂ | IsAlgebraic ℤ z} := by
  intro a ha b hb hab
  by_contra hne
  have htrans := hermiteLindemann (sub_ne_zero.mpr hne) (ha.sub hb)
  have hexp : Complex.exp (a - b) = 1 :=
    Complex.exp_eq_exp_iff_exp_sub_eq_one.mp hab
  rw [hexp] at htrans
  exact htrans isAlgebraic_one

end LeanFrontier.HermiteLindemann
