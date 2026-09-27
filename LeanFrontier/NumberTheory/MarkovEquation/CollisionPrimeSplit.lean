import LeanFrontier.NumberTheory.MarkovEquation.Collision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Prime-power splitting of Markov collision factors

Srinivasan's collision factorization becomes especially rigid at an odd prime divisor of the
shared Markov coordinate.  The two factors

`
E = a₁*a₂ - b₁*b₂
`

and

`
D = a₁*b₂ - b₁*a₂
`

cannot both be divisible by such a prime when the relevant coordinates are coprime to the shared
coordinate.

Combining this separation with `collision_factorization` gives the prime-power form needed in
classical uniqueness arguments: if `p^k ∣ c`, then the whole square `(p^k)^2` divides one of
`E` or `D`.

Modulo `p`, the two alternatives correspond to the same-root and opposite-root choices for the
square roots of `-1` attached to the two Markov triples.
-/

namespace LeanFrontier.MarkovEquation

/-- Let `p` be an odd prime dividing the common coordinate `c`.  If `a₁` and `a₂` are
coprime to `c`, then `p` cannot divide both collision factors.

The hypotheses are stated only with the two coprimality facts actually needed by the elementary
argument.  Pairwise coprimality of positive Markov triples supplies them in the intended
application. -/
theorem odd_prime_not_dvd_both_collision_factors
    {a₁ b₁ a₂ b₂ c : ℤ} {p : ℕ}
    (h₂ : IsSolution a₂ b₂ c)
    (hc₁ : IsCoprime a₁ c)
    (hc₂ : IsCoprime a₂ c)
    (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hpc : (p : ℤ) ∣ c) :
    ¬((p : ℤ) ∣ (a₁ * a₂ - b₁ * b₂) ∧
      (p : ℤ) ∣ (a₁ * b₂ - b₁ * a₂)) := by
  intro hboth
  rcases hboth with ⟨hE, hD⟩

  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp

  have hcop₁p : IsCoprime a₁ (p : ℤ) :=
    hc₁.of_isCoprime_of_dvd_right hpc
  have hcop₂p : IsCoprime a₂ (p : ℤ) :=
    hc₂.of_isCoprime_of_dvd_right hpc
  have hpa₁ : ¬(p : ℤ) ∣ a₁ :=
    (hpInt.coprime_iff_not_dvd).mp hcop₁p.symm
  have hpa₂ : ¬(p : ℤ) ∣ a₂ :=
    (hpInt.coprime_iff_not_dvd).mp hcop₂p.symm

  rcases hE with ⟨e, he⟩
  rcases hD with ⟨d, hd⟩
  have hdiff : (p : ℤ) ∣ a₂ ^ 2 - b₂ ^ 2 := by
    have hcomb : (p : ℤ) ∣ a₁ * (a₂ ^ 2 - b₂ ^ 2) := by
      refine ⟨a₂ * e - b₂ * d, ?_⟩
      calc
        a₁ * (a₂ ^ 2 - b₂ ^ 2) =
            a₂ * (a₁ * a₂ - b₁ * b₂) -
              b₂ * (a₁ * b₂ - b₁ * a₂) := by
                ring
        _ = a₂ * ((p : ℤ) * e) - b₂ * ((p : ℤ) * d) := by
              rw [he, hd]
        _ = (p : ℤ) * (a₂ * e - b₂ * d) := by
              ring
    exact (Int.Prime.dvd_mul' hp hcomb).resolve_left hpa₁

  have hsum : (p : ℤ) ∣ a₂ ^ 2 + b₂ ^ 2 := by
    rcases hpc with ⟨q, hq⟩
    refine ⟨q * jump a₂ b₂ c, ?_⟩
    calc
      a₂ ^ 2 + b₂ ^ 2 = c * jump a₂ b₂ c := (mul_jump_eq h₂).symm
      _ = ((p : ℤ) * q) * jump a₂ b₂ c := by rw [hq]
      _ = (p : ℤ) * (q * jump a₂ b₂ c) := by ring

  have htwo : (p : ℤ) ∣ 2 * a₂ ^ 2 := by
    rcases hsum with ⟨s, hs⟩
    rcases hdiff with ⟨t, ht⟩
    refine ⟨s + t, ?_⟩
    calc
      2 * a₂ ^ 2 =
          (a₂ ^ 2 + b₂ ^ 2) + (a₂ ^ 2 - b₂ ^ 2) := by ring
      _ = (p : ℤ) * s + (p : ℤ) * t := by rw [hs, ht]
      _ = (p : ℤ) * (s + t) := by ring

  rcases prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp htwo with hpeq | hpa₂abs
  · exact hp2 hpeq
  · apply hpa₂
    rwa [Int.natCast_dvd]

/-- If a positive power of an odd prime divides the shared coordinate of two Markov triples, then
the square of that prime power divides one entire collision factor, and the prime itself does not
divide both factors.

This is the arithmetic prime-power split behind the same-root/opposite-root decomposition used in
classical partial proofs of Markov uniqueness. -/
theorem odd_prime_power_collision_factor_split
    {a₁ b₁ a₂ b₂ c : ℤ} {p k : ℕ}
    (h₁ : IsSolution a₁ b₁ c)
    (h₂ : IsSolution a₂ b₂ c)
    (hc₁ : IsCoprime a₁ c)
    (hc₂ : IsCoprime a₂ c)
    (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hk : 0 < k)
    (hpkc : ((p : ℤ) ^ k) ∣ c) :
    ((((p : ℤ) ^ k) ^ 2 ∣ (a₁ * a₂ - b₁ * b₂)) ∨
      (((p : ℤ) ^ k) ^ 2 ∣ (a₁ * b₂ - b₁ * a₂))) ∧
    ¬((p : ℤ) ∣ (a₁ * a₂ - b₁ * b₂) ∧
      (p : ℤ) ∣ (a₁ * b₂ - b₁ * a₂)) := by
  have hpc : (p : ℤ) ∣ c :=
    (dvd_pow_self (p : ℤ) (Nat.ne_of_gt hk)).trans hpkc
  have hsep :=
    odd_prime_not_dvd_both_collision_factors (b₁ := b₁) h₂ hc₁ hc₂ hp hp2 hpc

  have hpk2c2 : (((p : ℤ) ^ k) ^ 2) ∣ c ^ 2 :=
    pow_dvd_pow_of_dvd hpkc 2
  have hprod :
      (((p : ℤ) ^ k) ^ 2) ∣
        (a₁ * a₂ - b₁ * b₂) * (a₁ * b₂ - b₁ * a₂) := by
    rcases hpk2c2 with ⟨w, hw⟩
    refine ⟨w * (a₁ * b₁ - a₂ * b₂), ?_⟩
    calc
      (a₁ * a₂ - b₁ * b₂) * (a₁ * b₂ - b₁ * a₂) =
          c ^ 2 * (a₁ * b₁ - a₂ * b₂) :=
        collision_factorization h₁ h₂
      _ = (((p : ℤ) ^ k) ^ 2 * w) * (a₁ * b₁ - a₂ * b₂) := by
            rw [hw]
      _ = ((p : ℤ) ^ k) ^ 2 * (w * (a₁ * b₁ - a₂ * b₂)) := by
            ring

  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsplit :
      (((p : ℤ) ^ k) ^ 2 ∣ (a₁ * a₂ - b₁ * b₂)) ∨
        (((p : ℤ) ^ k) ^ 2 ∣ (a₁ * b₂ - b₁ * a₂)) := by
    by_cases hE : (p : ℤ) ∣ (a₁ * a₂ - b₁ * b₂)
    · have hD : ¬(p : ℤ) ∣ (a₁ * b₂ - b₁ * a₂) := by
        intro hD
        exact hsep ⟨hE, hD⟩
      have hcopD :
          IsCoprime (p : ℤ) (a₁ * b₂ - b₁ * a₂) :=
        (hpInt.coprime_iff_not_dvd).mpr hD
      have hcopPkD :
          IsCoprime ((p : ℤ) ^ k) (a₁ * b₂ - b₁ * a₂) :=
        hcopD.pow_left
      have hcopPk2D :
          IsCoprime (((p : ℤ) ^ k) ^ 2) (a₁ * b₂ - b₁ * a₂) :=
        hcopPkD.pow_left
      exact Or.inl (hcopPk2D.dvd_of_dvd_mul_right hprod)
    · have hcopE :
          IsCoprime (p : ℤ) (a₁ * a₂ - b₁ * b₂) :=
        (hpInt.coprime_iff_not_dvd).mpr hE
      have hcopPkE :
          IsCoprime ((p : ℤ) ^ k) (a₁ * a₂ - b₁ * b₂) :=
        hcopE.pow_left
      have hcopPk2E :
          IsCoprime (((p : ℤ) ^ k) ^ 2) (a₁ * a₂ - b₁ * b₂) :=
        hcopPkE.pow_left
      exact Or.inr (hcopPk2E.dvd_of_dvd_mul_left hprod)

  exact ⟨hsplit, hsep⟩

end LeanFrontier.MarkovEquation
