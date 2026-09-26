import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring

/-!
# A gcd collapse for Markov slope-scale expressions

A primitive pair `(x,y)` gives rise to two quadratic expressions

`L = x^2 + y^2 + 3*M*x*y`,  `T = y^2 - x^2`

and two linear expressions

`U = 3*M*x + 2*y`,  `V = 3*M*y + 2*x`.

When `x` and `y` are coprime and `2` is coprime to `3*M`, these pairs have exactly the
same integer common divisors.  In particular their integer gcds coincide.

The result is useful in slope-scale parametrizations of the Markov equation, where the quadratic
gcd initially appears as an auxiliary quantity while the linear pair controls the primitive
defect factors.
-/

namespace LeanFrontier.MarkovEquation

/-- The quadratic slope-scale pair and the associated linear pair have the same common divisors.

The hypothesis `IsCoprime 2 (3*M)` is the exact parity condition used in the reverse direction;
for odd `M` it holds automatically. -/
theorem slopeScale_commonDivisor_iff
    {M x y q : ℤ}
    (hxy : IsCoprime x y)
    (h23 : IsCoprime (2 : ℤ) (3 * M)) :
    (q ∣ x ^ 2 + y ^ 2 + 3 * M * x * y ∧ q ∣ y ^ 2 - x ^ 2) ↔
      (q ∣ 3 * M * x + 2 * y ∧ q ∣ 3 * M * y + 2 * x) := by
  have hTy : IsCoprime (y ^ 2 - x ^ 2) y := by
    rw [show y ^ 2 - x ^ 2 = -(x ^ 2 - y * y) by ring,
      IsCoprime.neg_left_iff, IsCoprime.sub_mul_right_left_iff]
    exact hxy.pow_left
  have hTx : IsCoprime (y ^ 2 - x ^ 2) x := by
    rw [show y ^ 2 - x ^ 2 = y ^ 2 - x * x by ring,
      IsCoprime.sub_mul_right_left_iff]
    exact hxy.symm.pow_left

  constructor
  · rintro ⟨hL, hT⟩
    have hqy : IsCoprime q y :=
      hTy.of_isCoprime_of_dvd_left hT
    have hqx : IsCoprime q x :=
      hTx.of_isCoprime_of_dvd_left hT

    have hyU : q ∣ y * (3 * M * x + 2 * y) := by
      rcases hL with ⟨l, hl⟩
      rcases hT with ⟨t, ht⟩
      refine ⟨l + t, ?_⟩
      calc
        y * (3 * M * x + 2 * y) =
            (x ^ 2 + y ^ 2 + 3 * M * x * y) + (y ^ 2 - x ^ 2) := by ring
        _ = q * l + q * t := by rw [hl, ht]
        _ = q * (l + t) := by ring

    have hxV : q ∣ x * (3 * M * y + 2 * x) := by
      rcases hL with ⟨l, hl⟩
      rcases hT with ⟨t, ht⟩
      refine ⟨l - t, ?_⟩
      calc
        x * (3 * M * y + 2 * x) =
            (x ^ 2 + y ^ 2 + 3 * M * x * y) - (y ^ 2 - x ^ 2) := by ring
        _ = q * l - q * t := by rw [hl, ht]
        _ = q * (l - t) := by ring

    exact ⟨hqy.dvd_of_dvd_mul_left hyU, hqx.dvd_of_dvd_mul_left hxV⟩

  · rintro ⟨hU, hV⟩
    rcases hU with ⟨u, hu⟩
    rcases hV with ⟨v, hv⟩

    have h2T : q ∣ 2 * (y ^ 2 - x ^ 2) := by
      refine ⟨y * u - x * v, ?_⟩
      calc
        2 * (y ^ 2 - x ^ 2) =
            y * (3 * M * x + 2 * y) - x * (3 * M * y + 2 * x) := by ring
        _ = y * (q * u) - x * (q * v) := by rw [hu, hv]
        _ = q * (y * u - x * v) := by ring

    have h3MT : q ∣ (3 * M) * (y ^ 2 - x ^ 2) := by
      refine ⟨y * v - x * u, ?_⟩
      calc
        (3 * M) * (y ^ 2 - x ^ 2) =
            y * (3 * M * y + 2 * x) - x * (3 * M * x + 2 * y) := by ring
        _ = y * (q * v) - x * (q * u) := by rw [hv, hu]
        _ = q * (y * v - x * u) := by ring

    obtain ⟨a, b, hab⟩ := h23
    rcases h2T with ⟨c, hc⟩
    rcases h3MT with ⟨d, hd⟩
    have hT : q ∣ y ^ 2 - x ^ 2 := by
      refine ⟨a * c + b * d, ?_⟩
      calc
        y ^ 2 - x ^ 2 = 1 * (y ^ 2 - x ^ 2) := by ring
        _ = (a * 2 + b * (3 * M)) * (y ^ 2 - x ^ 2) := by rw [hab]
        _ = a * (2 * (y ^ 2 - x ^ 2)) +
              b * ((3 * M) * (y ^ 2 - x ^ 2)) := by ring
        _ = a * (q * c) + b * (q * d) := by rw [hc, hd]
        _ = q * (a * c + b * d) := by ring

    rcases hT with ⟨t, ht⟩
    have hL : q ∣ x ^ 2 + y ^ 2 + 3 * M * x * y := by
      refine ⟨y * u - t, ?_⟩
      calc
        x ^ 2 + y ^ 2 + 3 * M * x * y =
            y * (3 * M * x + 2 * y) - (y ^ 2 - x ^ 2) := by ring
        _ = y * (q * u) - q * t := by rw [hu, ht]
        _ = q * (y * u - t) := by ring

    exact ⟨hL, ⟨t, ht⟩⟩

/-- The gcd collapse corresponding to `slopeScale_commonDivisor_iff`. -/
theorem slopeScale_gcd_eq
    {M x y : ℤ}
    (hxy : IsCoprime x y)
    (h23 : IsCoprime (2 : ℤ) (3 * M)) :
    Int.gcd (x ^ 2 + y ^ 2 + 3 * M * x * y) (y ^ 2 - x ^ 2) =
      Int.gcd (3 * M * x + 2 * y) (3 * M * y + 2 * x) := by
  apply Nat.dvd_antisymm
  · rw [← Int.natCast_dvd_natCast]
    have h :=
      (slopeScale_commonDivisor_iff
        (q := (Int.gcd (x ^ 2 + y ^ 2 + 3 * M * x * y) (y ^ 2 - x ^ 2) : ℤ))
        hxy h23).mp
        ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
    exact Int.dvd_coe_gcd h.1 h.2
  · rw [← Int.natCast_dvd_natCast]
    have h :=
      (slopeScale_commonDivisor_iff
        (q := (Int.gcd (3 * M * x + 2 * y) (3 * M * y + 2 * x) : ℤ))
        hxy h23).mpr
        ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
    exact Int.dvd_coe_gcd h.1 h.2

end LeanFrontier.MarkovEquation
