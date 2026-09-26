import Mathlib.Algebra.Ring.Parity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring

/-!
# A gcd identity for Markov slope-scale expressions

For primitive integers `x,y` and odd `M`, consider the quadratic pair

`
L = x^2 + y^2 + 3*M*x*y,
T = y^2 - x^2
`

and the linear pair

`
U = 3*M*x + 2*y,
V = 3*M*y + 2*x.
`

These pairs have exactly the same integer common divisors.  Consequently their
integer gcds agree.

The identity is useful in slope-scale reductions of Markov collision arithmetic:
a gcd introduced from the quadratic pair can equivalently be read from the
linear pair.  After dividing by that common factor, the elementary relations
`L+T = y*U` and `L-T = x*V` recover primitive quotient factors.

The results below are elementary integer arithmetic and do not assume the
Markov equation or any uniqueness conjecture.
-/

namespace LeanFrontier.MarkovEquation

/-- For primitive `x,y` and odd `M`, the quadratic slope-scale pair and
its associated linear pair have exactly the same integer common divisors. -/
theorem slope_scale_common_divisors_iff
    {M x y q : ℤ}
    (hxy : IsCoprime x y)
    (hM : Odd M) :
    (q ∣ x ^ 2 + y ^ 2 + 3 * M * x * y ∧ q ∣ y ^ 2 - x ^ 2) ↔
      (q ∣ 3 * M * x + 2 * y ∧ q ∣ 3 * M * y + 2 * x) := by
  constructor
  · rintro ⟨hL, hT⟩
    have hcopxT : IsCoprime x (y ^ 2 - x ^ 2) := by
      rw [pow_two x, IsCoprime.sub_mul_right_right_iff]
      exact hxy.pow_right
    have hcopyNegT : IsCoprime y (x ^ 2 - y ^ 2) := by
      rw [pow_two y, IsCoprime.sub_mul_right_right_iff]
      exact hxy.symm.pow_right
    have hcopyT : IsCoprime y (y ^ 2 - x ^ 2) := by
      rw [show y ^ 2 - x ^ 2 = -(x ^ 2 - y ^ 2) by ring,
        IsCoprime.neg_right_iff]
      exact hcopyNegT
    have hcopqx : IsCoprime q x :=
      (hcopxT.of_isCoprime_of_dvd_right hT).symm
    have hcopqy : IsCoprime q y :=
      (hcopyT.of_isCoprime_of_dvd_right hT).symm
    have hxV : q ∣ x * (3 * M * y + 2 * x) := by
      have h := dvd_sub hL hT
      convert h using 1 <;> ring
    have hyU : q ∣ y * (3 * M * x + 2 * y) := by
      have h := dvd_add hL hT
      convert h using 1 <;> ring
    exact ⟨hcopqy.dvd_of_dvd_mul_left hyU,
      hcopqx.dvd_of_dvd_mul_left hxV⟩
  · rintro ⟨hU, hV⟩
    have h2T : q ∣ 2 * (y ^ 2 - x ^ 2) := by
      have h := dvd_sub (hU.mul_left y) (hV.mul_left x)
      convert h using 1 <;> ring
    have h3MT : q ∣ 3 * M * (y ^ 2 - x ^ 2) := by
      have h := dvd_sub (hV.mul_left y) (hU.mul_left x)
      convert h using 1 <;> ring
    rcases hM with ⟨k, hk⟩
    have hT : q ∣ y ^ 2 - x ^ 2 := by
      have h :=
        dvd_sub h3MT (h2T.mul_left (3 * k + 1))
      convert h using 1 <;> rw [hk] <;> ring
    have hL : q ∣ x ^ 2 + y ^ 2 + 3 * M * x * y := by
      have h := dvd_add (hV.mul_left x) hT
      convert h using 1 <;> ring
    exact ⟨hL, hT⟩

/-- The gcd form of `slope_scale_common_divisors_iff`. -/
theorem slope_scale_gcd_eq
    {M x y : ℤ}
    (hxy : IsCoprime x y)
    (hM : Odd M) :
    Int.gcd (x ^ 2 + y ^ 2 + 3 * M * x * y) (y ^ 2 - x ^ 2) =
      Int.gcd (3 * M * x + 2 * y) (3 * M * y + 2 * x) := by
  apply Nat.dvd_antisymm
  · rw [← Int.natCast_dvd_natCast]
    have hpair :
        ((Int.gcd (x ^ 2 + y ^ 2 + 3 * M * x * y) (y ^ 2 - x ^ 2) : ℤ) ∣
            3 * M * x + 2 * y) ∧
          ((Int.gcd (x ^ 2 + y ^ 2 + 3 * M * x * y) (y ^ 2 - x ^ 2) : ℤ) ∣
            3 * M * y + 2 * x) :=
      (slope_scale_common_divisors_iff
        (q := (Int.gcd (x ^ 2 + y ^ 2 + 3 * M * x * y) (y ^ 2 - x ^ 2) : ℤ))
        hxy hM).mp
        ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
    exact Int.dvd_coe_gcd hpair.1 hpair.2
  · rw [← Int.natCast_dvd_natCast]
    have hpair :
        ((Int.gcd (3 * M * x + 2 * y) (3 * M * y + 2 * x) : ℤ) ∣
            x ^ 2 + y ^ 2 + 3 * M * x * y) ∧
          ((Int.gcd (3 * M * x + 2 * y) (3 * M * y + 2 * x) : ℤ) ∣
            y ^ 2 - x ^ 2) :=
      (slope_scale_common_divisors_iff
        (q := (Int.gcd (3 * M * x + 2 * y) (3 * M * y + 2 * x) : ℤ))
        hxy hM).mpr
        ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
    exact Int.dvd_coe_gcd hpair.1 hpair.2

/-- If a common factor `Q` is removed from the slope-scale expressions, the
remaining linear quotient factors are recoverable as gcds when `x,y` are
primitive.

This packages the identities
`L + T = y U` and `L - T = x V`: if
`L = Q*A`, `T = Q*B`, `U = Q*C`, and `V = Q*D`, then
`A+B = y*C` and `A-B = x*D`.  Primitivity of `x,y` then gives the two
displayed gcds. -/
theorem slope_scale_primitive_quotient_gcd
    {M x y Q A B C D : ℤ}
    (hxy : IsCoprime x y)
    (hQ : Q ≠ 0)
    (hL : x ^ 2 + y ^ 2 + 3 * M * x * y = Q * A)
    (hT : y ^ 2 - x ^ 2 = Q * B)
    (hU : 3 * M * x + 2 * y = Q * C)
    (hV : 3 * M * y + 2 * x = Q * D) :
    Int.gcd (x * C) (A + B) = C.natAbs ∧
      Int.gcd (A - B) (y * D) = D.natAbs := by
  have hplus : A + B = y * C := by
    apply mul_left_cancel₀ hQ
    calc
      Q * (A + B) = Q * A + Q * B := by ring
      _ = (x ^ 2 + y ^ 2 + 3 * M * x * y) + (y ^ 2 - x ^ 2) := by
        rw [← hL, ← hT]
      _ = y * (3 * M * x + 2 * y) := by ring
      _ = y * (Q * C) := by rw [hU]
      _ = Q * (y * C) := by ring
  have hminus : A - B = x * D := by
    apply mul_left_cancel₀ hQ
    calc
      Q * (A - B) = Q * A - Q * B := by ring
      _ = (x ^ 2 + y ^ 2 + 3 * M * x * y) - (y ^ 2 - x ^ 2) := by
        rw [← hL, ← hT]
      _ = x * (3 * M * y + 2 * x) := by ring
      _ = x * (Q * D) := by rw [hV]
      _ = Q * (x * D) := by ring
  constructor
  · rw [hplus, Int.gcd_mul_right,
      Int.isCoprime_iff_gcd_eq_one.mp hxy, one_mul]
  · rw [hminus, Int.gcd_mul_right,
      Int.isCoprime_iff_gcd_eq_one.mp hxy, one_mul]

end LeanFrontier.MarkovEquation
