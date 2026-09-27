import Mathlib

/-!
# A053067 fixed-width concatenation and residue avoidance

Algebraic infrastructure for the OEIS A053067 concatenation sequence.

The main algebraic object is the fixed-width append recurrence

  F(q,L,0) = 0
  F(q,L,n+1) = q * F(q,L,n) + (L+n).

When q = 1 in a target semiring (in particular modulo a modulus dividing
q-1), the positional weights disappear and the recurrence is just the sum of
the consecutive block.
-/

namespace LeanFrontier.A053067

/-- Concatenate n consecutive values starting at L, using the fixed
positional base q. The definition is algebraic and works in any semiring. -/
def fixedConcat {R : Type*} [Semiring R] (q L : R) : ℕ → R
  | 0 => 0
  | n + 1 => q * fixedConcat q L n + (L + (n : R))

@[simp]
theorem fixedConcat_zero {R : Type*} [Semiring R] (q L : R) :
    fixedConcat q L 0 = 0 := rfl

@[simp]
theorem fixedConcat_succ {R : Type*} [Semiring R] (q L : R) (n : ℕ) :
    fixedConcat q L (n + 1) =
      q * fixedConcat q L n + (L + (n : R)) := rfl


/-- Fixed-width concatenation commutes with semiring homomorphisms. -/
theorem map_fixedConcat {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (q L : R) (n : ℕ) :
    f (fixedConcat q L n) = fixedConcat (f q) (f L) n := by
  induction n with
  | zero =>
      simp [fixedConcat]
  | succ n ih =>
      simp [fixedConcat, ih]


/-- Casting a natural fixed concatenation into any semiring commutes with the
recurrence. -/
theorem natCast_fixedConcat {R : Type*} [Semiring R]
    (q L n : ℕ) :
    ((fixedConcat q L n : ℕ) : R) =
      fixedConcat (q : R) (L : R) n := by
  simpa using
    (map_fixedConcat (Nat.castRingHom R) q L n)



/-- If the append base is 1, fixed-width concatenation is just the ordinary
sum of the consecutive block. -/
theorem fixedConcat_one_eq_sum {R : Type*} [Semiring R] (L : R) (n : ℕ) :
    fixedConcat (1 : R) L n =
      ∑ i ∈ Finset.range n, (L + (i : R)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [fixedConcat_succ, Finset.sum_range_succ, ih]
      simp [add_assoc]

/-- A rewrite-friendly version: any base equal to 1 gives the same ordinary
sum. In applications R = ZMod m and the hypothesis is 10^d = 1. -/
theorem fixedConcat_eq_sum_of_eq_one {R : Type*} [Semiring R]
    (q L : R) (n : ℕ) (hq : q = 1) :
    fixedConcat q L n =
      ∑ i ∈ Finset.range n, (L + (i : R)) := by
  subst q
  exact fixedConcat_one_eq_sum L n


/-- Division-free closed form for n+1 consecutive appended values.

This is the form used throughout the A053067 congruence analysis. Stating the
theorem at n+1 avoids any subtraction on natural-number indices. -/
theorem fixedConcat_closed_succ {R : Type*} [CommRing R]
    (q L : R) (n : ℕ) :
    (q - 1)^2 * fixedConcat q L (n + 1) =
      q^(n + 1) * ((q - 1) * L + 1) -
        ((q - 1) * (L + (n : R)) + q) := by
  induction n with
  | zero =>
      simp [fixedConcat]
      ring
  | succ n ih =>
      calc
        (q - 1)^2 * fixedConcat q L (n + 1 + 1) =
            q * ((q - 1)^2 * fixedConcat q L (n + 1)) +
              (q - 1)^2 * (L + ((n + 1 : ℕ) : R)) := by
                rw [fixedConcat_succ]
                ring
        _ =
            q * (q^(n + 1) * ((q - 1) * L + 1) -
              ((q - 1) * (L + (n : R)) + q)) +
              (q - 1)^2 * (L + ((n + 1 : ℕ) : R)) := by
                rw [ih]
        _ =
            q^((n + 1) + 1) * ((q - 1) * L + 1) -
              ((q - 1) * (L + ((n + 1 : ℕ) : R)) + q) := by
                push_cast
                rw [pow_succ]
                ring

/-- Abstract residue-one criterion.

If the append base and first block value are both 1, the block length also
casts to 1, and the casted index offsets sum to zero, then the complete
fixed-width concatenation is 1. This separates the generic concatenation
algebra from the number-theoretic construction of suitable A053067 indices. -/
theorem fixedConcat_eq_one_of_residue_data {R : Type*} [CommRing R]
    (q L : R) (n : ℕ)
    (hq : q = 1)
    (hL : L = 1)
    (hn : (n : R) = 1)
    (hoffsets : (∑ i ∈ Finset.range n, (i : R)) = 0) :
    fixedConcat q L n = 1 := by
  rw [fixedConcat_eq_sum_of_eq_one q L n hq]
  calc
    (∑ i ∈ Finset.range n, (L + (i : R))) =
        (∑ _i ∈ Finset.range n, L) +
          (∑ i ∈ Finset.range n, (i : R)) := by
            rw [Finset.sum_add_distrib]
    _ = (n : R) * L + (∑ i ∈ Finset.range n, (i : R)) := by
          simp
    _ = 1 := by
          rw [hL, hn, hoffsets]
          simp

/-- Division-free formula for the casted sum of the offsets 0,...,n-1. -/
theorem two_mul_sum_range_cast {R : Type*} [CommRing R] (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (i : R)) =
      (n : R) * ((n : R) - 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [mul_add, ih]
      ring

/-- If n casts to 1 and 2 is not a zero divisor, the triangular offset
sum vanishes. -/
theorem sum_range_cast_eq_zero_of_cast_eq_one {R : Type*} [CommRing R]
    [NoZeroDivisors R] (n : ℕ) (hn : (n : R) = 1)
    (h2ne : (2 : R) ≠ 0) :
    (∑ i ∈ Finset.range n, (i : R)) = 0 := by
  have htwo :
      2 * (∑ i ∈ Finset.range n, (i : R)) = 0 := by
    rw [two_mul_sum_range_cast, hn]
    ring
  rcases mul_eq_zero.mp htwo with h2 | hsum
  · exact (h2ne h2).elim
  · exact hsum

/-- In a domain, base 1, start 1, and length congruent to 1 force the
concatenation residue to be 1. -/
theorem fixedConcat_eq_one_of_cast_eq_one {R : Type*} [CommRing R]
    [NoZeroDivisors R] (q L : R) (n : ℕ)
    (hq : q = 1) (hL : L = 1) (hn : (n : R) = 1)
    (h2ne : (2 : R) ≠ 0) :
    fixedConcat q L n = 1 := by
  exact fixedConcat_eq_one_of_residue_data q L n hq hL hn
    (sum_range_cast_eq_zero_of_cast_eq_one n hn h2ne)

/-- The algebraic triangular-block start used by A053067 after passing to a
field in which 2 is invertible. -/
def triangularStart {R : Type*} [Field R] (x : R) : R :=
  x * (x - 1) / 2 + 1

/-- If the block length is 1 in the target field, its triangular A053067
start is also 1. -/
theorem triangularStart_eq_one_of_eq_one {R : Type*} [Field R]
    (x : R) (hx : x = 1) :
    triangularStart x = 1 := by
  rw [hx]
  simp [triangularStart]

/-- Residue-one specialization for the algebraic A053067 triangular start.

In a field of characteristic different from 2, if the fixed append base is
1 and the natural block length casts to 1, then the corresponding fixed-width
A053067 concatenation residue is 1. -/
theorem fixedConcat_triangular_eq_one {R : Type*} [Field R]
    (q : R) (n : ℕ)
    (hq : q = 1) (hn : (n : R) = 1) (h2ne : (2 : R) ≠ 0) :
    fixedConcat q (triangularStart (n : R)) n = 1 := by
  apply fixedConcat_eq_one_of_cast_eq_one q (triangularStart (n : R)) n
  · exact hq
  · exact triangularStart_eq_one_of_eq_one (n : R) hn
  · exact hn
  · exact h2ne

/-- Natural-number A053067 block start, written with `Nat.choose` so its cast
to a field is clean.  By `Nat.choose_two_right` this is exactly
`n * (n - 1) / 2 + 1`. -/
def natTriangularStart (n : ℕ) : ℕ :=
  n.choose 2 + 1

/-- Casting the natural A053067 block start agrees with the algebraic
`triangularStart`. -/
theorem cast_natTriangularStart {R : Type*} [Field R] [NeZero (2 : R)]
    (n : ℕ) :
    ((natTriangularStart n : ℕ) : R) = triangularStart (n : R) := by
  simp [natTriangularStart, triangularStart, Nat.cast_choose_two]

/-- Natural A053067 specialization of the residue-one lemma.

If the fixed append base is 1 and the natural block length casts to 1, then
the concatenation beginning at the actual natural triangular block start is
1 in the target field. -/
theorem fixedConcat_natTriangular_eq_one {R : Type*} [Field R]
    [NeZero (2 : R)] (q : R) (n : ℕ)
    (hq : q = 1) (hn : (n : R) = 1) :
    fixedConcat q (((natTriangularStart n : ℕ) : R)) n = 1 := by
  rw [cast_natTriangularStart]
  exact fixedConcat_triangular_eq_one q n hq hn (NeZero.ne (2 : R))

/-- General residue-one criterion used by the rough-values construction.

In an odd-characteristic field, if the first appended value and the natural
block length both reduce to 1, and the positional base satisfies `q^n = q`,
then the complete fixed-width concatenation reduces to 1.  The condition
`q^n = q` is what follows from `n = 1` modulo the multiplicative order of
`q`. -/
theorem fixedConcat_eq_one_of_pow_eq_self {R : Type*} [Field R]
    [NeZero (2 : R)] (q L : R) (n : ℕ)
    (hL : L = 1) (hn : (n : R) = 1) (hpow : q ^ n = q) :
    fixedConcat q L n = 1 := by
  by_cases hq : q = 1
  · exact fixedConcat_eq_one_of_cast_eq_one q L n hq hL hn
      (NeZero.ne (2 : R))
  · cases n with
    | zero =>
        norm_num at hn
    | succ k =>
        have hk : (k : R) = 0 := by
          have hks : (k : R) + 1 = 1 := by
            simpa using hn
          have hsub := congrArg (fun x : R => x - 1) hks
          simpa using hsub
        have hclosed := fixedConcat_closed_succ (R := R) q L k
        have hmul :
            (q - 1)^2 * fixedConcat q L (k + 1) = (q - 1)^2 := by
          calc
            (q - 1)^2 * fixedConcat q L (k + 1) =
                q^(k + 1) * ((q - 1) * L + 1) -
                  ((q - 1) * (L + (k : R)) + q) := hclosed
            _ = (q - 1)^2 := by
                  rw [hpow, hL, hk]
                  ring
        have hqm1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
        have hsq : (q - 1)^2 ≠ 0 := pow_ne_zero 2 hqm1
        have hmul' :
            (q - 1)^2 * fixedConcat q L (k + 1) = (q - 1)^2 * 1 := by
          simpa using hmul
        exact (mul_left_cancel₀ hsq) hmul'

/-- Natural-triangular specialization of `fixedConcat_eq_one_of_pow_eq_self`.
This is the exact algebraic congruence used to avoid every small prime in
`ROUGH_VALUES.md`. -/
theorem fixedConcat_natTriangular_eq_one_of_pow_eq_self
    {R : Type*} [Field R] [NeZero (2 : R)]
    (q : R) (n : ℕ) (hn : (n : R) = 1) (hpow : q ^ n = q) :
    fixedConcat q (((natTriangularStart n : ℕ) : R)) n = 1 := by
  rw [cast_natTriangularStart]
  exact fixedConcat_eq_one_of_pow_eq_self q (triangularStart (n : R)) n
    (triangularStart_eq_one_of_eq_one (n : R) hn) hn hpow

/-- Prime-modulus specialization of the general residue-one mechanism.

For an odd prime `p`, if the natural block length is `1 mod p` and the
positional base satisfies `q^n = q` in `ZMod p`, then the actual natural
triangular-start fixed-width concatenation is `1 mod p`. -/
theorem zmod_fixedConcat_natTriangular_eq_one
    (p q n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hnmod : n ≡ 1 [MOD p])
    (hpow : (q : ZMod p) ^ n = (q : ZMod p)) :
    fixedConcat (q : ZMod p)
      (((natTriangularStart n : ℕ) : ZMod p)) n = 1 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have htwo_le : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (Nat.le_antisymm hp_le htwo_le)
  letI : NeZero (2 : ZMod p) := ⟨h2ne⟩
  have hn : (n : ZMod p) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff n 1 p).2 hnmod
  exact fixedConcat_natTriangular_eq_one_of_pow_eq_self
    (q : ZMod p) n hn hpow




/-- Prime-modulus residue-one lemma in the form used by the Euclid-style
finite-prime-avoidance construction: if the fixed positional base is 1 mod p
and the triangular block length is 1 mod p, then the whole fixed-width
triangular concatenation is 1 mod p. -/
theorem zmod_fixedConcat_natTriangular_eq_one_of_base_one
    (p q n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hnmod : n ≡ 1 [MOD p])
    (hq : (q : ZMod p) = 1) :
    fixedConcat (q : ZMod p)
      (((natTriangularStart n : ℕ) : ZMod p)) n = 1 := by
  apply zmod_fixedConcat_natTriangular_eq_one p q n hp2 hnmod
  rw [hq]
  simp





/-- The natural fixed-width triangular A053067 recurrence at positional base
q. When q = 10^d and the whole block has width d, this is the decimal
concatenation. -/
def natFixedA (q n : ℕ) : ℕ :=
  fixedConcat q (natTriangularStart n) n

/-- Natural-number version of the prime-modulus residue-one theorem. -/
theorem zmod_natFixedA_eq_one_of_base_one
    (p q n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hnmod : n ≡ 1 [MOD p])
    (hq : (q : ZMod p) = 1) :
    ((natFixedA q n : ℕ) : ZMod p) = 1 := by
  rw [natFixedA, natCast_fixedConcat]
  exact zmod_fixedConcat_natTriangular_eq_one_of_base_one
    p q n hp2 hnmod hq



/-- Decimal-base specialization of the natural residue-one theorem. -/
theorem zmod_natFixedA_decimal_eq_one
    (p d n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hnmod : n ≡ 1 [MOD p])
    (hqmod : 10 ^ d ≡ 1 [MOD p]) :
    ((natFixedA (10 ^ d) n : ℕ) : ZMod p) = 1 := by
  apply zmod_natFixedA_eq_one_of_base_one p (10 ^ d) n hp2 hnmod
  simpa using (ZMod.natCast_eq_natCast_iff (10 ^ d) 1 p).2 hqmod

/-- Under the residue-one hypotheses, the odd prime p does not divide the
natural fixed-width A053067 recurrence value. -/
theorem prime_not_dvd_natFixedA_decimal
    (p d n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hnmod : n ≡ 1 [MOD p])
    (hqmod : 10 ^ d ≡ 1 [MOD p]) :
    ¬ p ∣ natFixedA (10 ^ d) n := by
  intro hdiv
  have hzero :
      ((natFixedA (10 ^ d) n : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (natFixedA (10 ^ d) n) p).2 hdiv
  have hone :=
    zmod_natFixedA_decimal_eq_one p d n hp2 hnmod hqmod
  rw [hone] at hzero
  exact one_ne_zero hzero



/-- Finite-set modular core of the Euclid-style avoidance theorem.

If one natural block length n and one decimal width d satisfy the residue-one
conditions simultaneously for every odd prime in a finite set S, then none of
those primes divides the natural fixed-width A053067 recurrence value. -/
theorem finset_prime_avoidance
    (S : Finset ℕ) (d n : ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, p ≠ 2)
    (hnmod : ∀ p ∈ S, n ≡ 1 [MOD p])
    (hqmod : ∀ p ∈ S, 10 ^ d ≡ 1 [MOD p]) :
    ∀ p ∈ S, ¬ p ∣ natFixedA (10 ^ d) n := by
  intro p hp
  letI : Fact p.Prime := ⟨hprime p hp⟩
  exact prime_not_dvd_natFixedA_decimal
    p d n (hodd p hp) (hnmod p hp) (hqmod p hp)


/-- The factor of a modulus supported on the decimal primes 2 and 5. -/
def tenPart (m : ℕ) : ℕ :=
  ordProj[2] m * ordProj[5] (ordCompl[2] m)

/-- The complementary factor, hence coprime to 10 for nonzero moduli. -/
def tenCoprimePart (m : ℕ) : ℕ :=
  ordCompl[5] (ordCompl[2] m)

/-- The decimal and prime-to-decimal parts reconstruct the original modulus. -/
theorem tenPart_mul_tenCoprimePart (m : ℕ) :
    tenPart m * tenCoprimePart m = m := by
  rw [tenPart, tenCoprimePart, mul_assoc,
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[2] m) 5,
    Nat.ordProj_mul_ordCompl_eq_self m 2]

/-- The complementary modulus has no factor 2 or 5. -/
theorem tenCoprimePart_coprime_ten {m : ℕ} (hm : m ≠ 0) :
    (tenCoprimePart m).Coprime 10 := by
  have htwoBase : (2 : ℕ).Coprime (ordCompl[2] m) :=
    Nat.coprime_ordCompl Nat.prime_two hm
  have hcomp2ne : ordCompl[2] m ≠ 0 :=
    (Nat.ordCompl_pos 2 hm).ne'
  have hstarDvd : tenCoprimePart m ∣ ordCompl[2] m := by
    exact Nat.ordCompl_dvd (ordCompl[2] m) 5
  have htwo : (2 : ℕ).Coprime (tenCoprimePart m) :=
    Nat.Coprime.of_dvd_right hstarDvd htwoBase
  have hfive : (5 : ℕ).Coprime (tenCoprimePart m) := by
    exact Nat.coprime_ordCompl Nat.prime_five hcomp2ne
  rw [show 10 = 2 * 5 by norm_num]
  exact htwo.symm.mul_right hfive.symm


/-- The decimal-supported and prime-to-decimal parts of a nonzero modulus are coprime. -/
theorem tenPart_coprime_tenCoprimePart {m : ℕ} (hm : m ≠ 0) :
    (tenPart m).Coprime (tenCoprimePart m) := by
  have hb10 : (tenCoprimePart m).Coprime 10 :=
    tenCoprimePart_coprime_ten hm
  have hb2 : (tenCoprimePart m).Coprime 2 := by
    apply Nat.Coprime.of_dvd_right (b₂ := 10)
    · norm_num
    · exact hb10
  have hb5 : (tenCoprimePart m).Coprime 5 := by
    apply Nat.Coprime.of_dvd_right (b₂ := 10)
    · norm_num
    · exact hb10
  have h2pow :
      (2 ^ m.factorization 2).Coprime (tenCoprimePart m) :=
    (hb2.symm).pow_left _
  have h5pow :
      (5 ^ (ordCompl[2] m).factorization 5).Coprime
        (tenCoprimePart m) :=
    (hb5.symm).pow_left _
  simpa [tenPart] using h2pow.mul_left h5pow

/-- An exponent large enough that the 2/5-supported part of m divides 10^e. -/
def tenExponent (m : ℕ) : ℕ :=
  m.factorization 2 + (ordCompl[2] m).factorization 5 + 1

theorem tenExponent_pos (m : ℕ) : 0 < tenExponent m := by
  simp [tenExponent]

/-- The decimal part of a modulus is absorbed by a sufficiently large power of 10. -/
theorem tenPart_dvd_pow_ten (m : ℕ) :
    tenPart m ∣ 10 ^ tenExponent m := by
  let a := m.factorization 2
  let b := (ordCompl[2] m).factorization 5
  have h2 : 2 ^ a ∣ 2 ^ (a + b + 1) :=
    Nat.pow_dvd_pow 2 (by omega)
  have h5 : 5 ^ b ∣ 5 ^ (a + b + 1) :=
    Nat.pow_dvd_pow 5 (by omega)
  have hmul : 2 ^ a * 5 ^ b ∣ 2 ^ (a + b + 1) * 5 ^ (a + b + 1) :=
    mul_dvd_mul h2 h5
  simpa [tenPart, tenExponent, a, b, ← mul_pow] using hmul

/-- If the positional base vanishes modulo a, a nonempty fixed concatenation
is congruent to its final appended value. -/
theorem natFixedA_modEq_last_of_base_dvd
    {a q n : ℕ} (hn : 0 < n) (hq : a ∣ q) :
    natFixedA q n ≡ natTriangularStart n + (n - 1) [MOD a] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hzero :
      q * fixedConcat q (natTriangularStart (k + 1)) k ≡ 0 [MOD a] := by
    simpa using (hq.modEq_zero_nat.mul_right
      (fixedConcat q (natTriangularStart (k + 1)) k))
  have hadd := hzero.add
    (Nat.ModEq.refl (natTriangularStart (k + 1) + k))
  simpa [natFixedA, fixedConcat, Nat.add_assoc] using hadd

/-- If n is 1 modulo 2a, the final integer in its triangular block is 1 modulo a. -/
theorem triangularLast_modEq_one_of_index_modEq_one
    {a n : ℕ} (hn : 0 < n) (hmod : n ≡ 1 [MOD 2 * a]) :
    natTriangularStart n + (n - 1) ≡ 1 [MOD a] := by
  have hone : 1 ≤ n := hn
  have hdvd : 2 * a ∣ n - 1 := by
    exact (Nat.modEq_iff_dvd' hone).mp hmod.symm
  obtain ⟨t, ht⟩ := hdvd
  have hnEq : n = 2 * a * t + 1 := by
    calc
      n = (n - 1) + 1 := (Nat.sub_add_cancel hone).symm
      _ = 2 * a * t + 1 := by rw [ht]
  have hchoose : a ∣ n.choose 2 := by
    rw [hnEq, Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [show (2 * a * t + 1) * (2 * a * t) =
      2 * ((2 * a * t + 1) * (a * t)) by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    exact ⟨(2 * a * t + 1) * t, by ring⟩
  have hmodA : n ≡ 1 [MOD a] := by
    apply hmod.of_dvd
    exact ⟨2, by ring⟩
  have hsum := hchoose.modEq_zero_nat.add hmodA
  simpa [natTriangularStart, Nat.add_assoc, Nat.add_sub_of_le hone] using hsum


/-- Combined residue-one criterion for the natural fixed-width A053067 recurrence. -/
theorem natFixedA_modEq_one_of_base_dvd_and_index
    {a q n : ℕ} (hn : 0 < n) (hq : a ∣ q)
    (hmod : n ≡ 1 [MOD 2 * a]) :
    natFixedA q n ≡ 1 [MOD a] :=
  (natFixedA_modEq_last_of_base_dvd hn hq).trans
    (triangularLast_modEq_one_of_index_modEq_one hn hmod)


/-- A genuine fixed-width A053067 index: all integers in the triangular block
from the start through its last term have exactly d decimal digits. -/
def IsFixedWidthIndex (d n : ℕ) : Prop :=
  0 < d ∧
    10 ^ (d - 1) ≤ natTriangularStart n ∧
    natTriangularStart n + (n - 1) < 10 ^ d

/-- Universal residue-one theorem for A053067, in an explicitly unbounded form.

For every nonzero modulus m and every lower bound B, there is a genuine
fixed-width A053067 index n > B whose fixed-width decimal concatenation is
congruent to 1 modulo m. -/
theorem exists_fixedWidth_residue_one_above
    (m B : ℕ) (hm : 0 < m) :
    ∃ d n : ℕ,
      B < n ∧
      IsFixedWidthIndex d n ∧
      natFixedA (10 ^ d) n ≡ 1 [MOD m] := by
  let a := tenPart m
  let b := tenCoprimePart m
  let e := tenExponent m
  let M := b * (2 * a)
  let R := M + e + B + 3
  let t := Nat.totient b * R
  let d := 2 * t
  let N := 10 ^ t
  let n := M * (N / M + 1) + 1

  have hm0 : m ≠ 0 := hm.ne'
  have ha : 0 < a := by
    dsimp [a, tenPart]
    exact Nat.mul_pos (Nat.ordProj_pos m 2)
      (Nat.ordProj_pos (ordCompl[2] m) 5)
  have hb : 0 < b := by
    dsimp [b, tenCoprimePart]
    exact Nat.ordCompl_pos 5 ((Nat.ordCompl_pos 2 hm0).ne')
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.mul_pos hb (Nat.mul_pos (by norm_num) ha)
  have hR : 0 < R := by
    dsimp [R]
    omega
  have hphi : 0 < Nat.totient b := Nat.totient_pos.mpr hb
  have hRt : R ≤ t := by
    dsimp [t]
    exact Nat.le_mul_of_pos_left R hphi
  have ht : 0 < t := lt_of_lt_of_le hR hRt
  have hd : 0 < d := by
    dsimp [d]
    omega
  have he_le_d : e ≤ d := by
    dsimp [R] at hRt
    dsimp [d]
    omega
  have hMtwo_le_t : M + 2 ≤ t := by
    dsimp [R] at hRt
    omega
  have hB_lt_t : B < t := by
    dsimp [R] at hRt
    omega

  have hselfPow : ∀ x : ℕ, 0 < x → x < 10 ^ x := by
    intro x hx
    induction x with
    | zero => omega
    | succ x ih =>
        by_cases hx0 : x = 0
        · subst x
          norm_num
        · have ihx := ih (Nat.pos_of_ne_zero hx0)
          rw [pow_succ]
          have hp : 0 < 10 ^ x := pow_pos (by norm_num) _
          omega
  have htN : t < N := by
    simpa [N] using hselfPow t ht
  have hBN : B < N := hB_lt_t.trans htN

  have hfourPow : ∀ x : ℕ, 4 * (x + 1) ≤ 10 ^ (x + 2) := by
    intro x
    induction x with
    | zero => norm_num
    | succ x ih =>
        calc
          4 * (x + 1 + 1) ≤ 10 * (4 * (x + 1)) := by omega
          _ ≤ 10 * 10 ^ (x + 2) := Nat.mul_le_mul_left 10 ih
          _ = 10 ^ (x + 1 + 2) := by
            rw [show x + 1 + 2 = (x + 2) + 1 by omega, pow_succ]
            ring
  have hfourMN : 4 * (M + 1) ≤ N := by
    calc
      4 * (M + 1) ≤ 10 ^ (M + 2) := hfourPow M
      _ ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) hMtwo_le_t
      _ = N := by rfl
  have hNpos : 0 < N := by
    dsimp [N]
    exact pow_pos (by norm_num) _

  have hNltCore : N < M * (N / M + 1) :=
    Nat.lt_mul_div_succ N hM
  have hNn : N < n := by
    dsimp [n]
    omega
  have hfloor : M * (N / M) ≤ N := Nat.mul_div_le N M
  have hnUpper : n ≤ N + M + 1 := by
    dsimp [n]
    rw [mul_add, mul_one]
    omega
  have hfourN : 4 * n ≤ 5 * N := by
    omega
  have hNfour : 4 ≤ N := by
    omega
  have htwoSucc : 2 * (n + 1) ≤ 3 * N := by
    omega
  have hprodUpper : 8 * (n * (n + 1)) ≤ 15 * (N * N) := by
    calc
      8 * (n * (n + 1)) = (4 * n) * (2 * (n + 1)) := by ring
      _ ≤ (5 * N) * (3 * N) := Nat.mul_le_mul hfourN htwoSucc
      _ = 15 * (N * N) := by ring
  have hNNpos : 0 < N * N := Nat.mul_pos hNpos hNpos
  have hprodLt : n * (n + 1) < 2 * (N * N) := by
    by_contra h
    have hge : 2 * (N * N) ≤ n * (n + 1) := Nat.le_of_not_gt h
    have h16 : 16 * (N * N) ≤ 8 * (n * (n + 1)) := by
      have hx := Nat.mul_le_mul_left 8 hge
      nlinarith
    have hbad : 16 * (N * N) ≤ 15 * (N * N) :=
      h16.trans hprodUpper
    omega

  have hnpos : 0 < n := lt_trans hNpos hNn
  have hNm1 : N ≤ n - 1 := by omega
  have hprodLower : N * N ≤ n * (n - 1) :=
    Nat.mul_le_mul hNn.le hNm1
  have hNNpow : N * N = 10 ^ d := by
    change 10 ^ t * 10 ^ t = 10 ^ (2 * t)
    rw [← pow_add]
    congr 1
    omega
  have hdOne : 1 ≤ d := hd
  have hstep : 10 ^ (d - 1) * 10 = 10 ^ d := by
    rw [← pow_succ, Nat.sub_add_cancel hdOne]
  have htwoLower :
      2 * 10 ^ (d - 1) ≤ n * (n - 1) := by
    have hten :
        10 * 10 ^ (d - 1) = N * N := by
      rw [mul_comm, hstep, hNNpow]
    have hsmall : 2 * 10 ^ (d - 1) ≤ N * N := by
      rw [← hten]
      have hp : 0 < 10 ^ (d - 1) := pow_pos (by norm_num) _
      nlinarith
    exact hsmall.trans hprodLower
  have hstart :
      10 ^ (d - 1) ≤ natTriangularStart n := by
    have hchoose :
        10 ^ (d - 1) ≤ n * (n - 1) / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      simpa [mul_comm] using htwoLower
    rw [natTriangularStart, Nat.choose_two_right]
    omega
  have hlast :
      natTriangularStart n + (n - 1) = n * (n + 1) / 2 := by
    rw [natTriangularStart, Nat.choose_two_right]
    have hone : 1 ≤ n := hnpos
    calc
      n * (n - 1) / 2 + 1 + (n - 1) =
          n * (n - 1) / 2 + n := by omega
      _ = (n + 1) * ((n + 1) - 1) / 2 := (Nat.triangle_succ n).symm
      _ = n * (n + 1) / 2 := by
        simp only [Nat.add_sub_cancel]
        rw [mul_comm]
  have hfinish :
      natTriangularStart n + (n - 1) < 10 ^ d := by
    rw [hlast, ← hNNpow]
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).2
    simpa [mul_comm] using hprodLt
  have hfixed : IsFixedWidthIndex d n := ⟨hd, hstart, hfinish⟩

  have hindexM : n ≡ 1 [MOD M] := by
    dsimp [n]
    exact Nat.ModEq.modulus_mul_add
  have htwoA_M : 2 * a ∣ M := by
    refine ⟨b, ?_⟩
    dsimp [M]
    ring
  have htwoB_M : 2 * b ∣ M := by
    refine ⟨a, ?_⟩
    dsimp [M]
    ring
  have hindexA : n ≡ 1 [MOD 2 * a] :=
    hindexM.of_dvd htwoA_M
  have hindexB : n ≡ 1 [MOD 2 * b] :=
    hindexM.of_dvd htwoB_M

  have hpowA : a ∣ 10 ^ d := by
    have hae : a ∣ 10 ^ e := by
      simpa [a, e] using tenPart_dvd_pow_ten m
    exact hae.trans (Nat.pow_dvd_pow 10 he_le_d)
  have hresA : natFixedA (10 ^ d) n ≡ 1 [MOD a] :=
    natFixedA_modEq_one_of_base_dvd_and_index hnpos hpowA hindexA

  have h10b : (10 : ℕ).Coprime b := by
    exact (tenCoprimePart_coprime_ten hm0).symm
  have heuler : 10 ^ Nat.totient b ≡ 1 [MOD b] :=
    Nat.ModEq.pow_totient h10b
  have hphiD : Nat.totient b ∣ d := by
    refine ⟨2 * R, ?_⟩
    dsimp [d, t]
    ring
  obtain ⟨j, hj⟩ := hphiD
  have hbaseB : 10 ^ d ≡ 1 [MOD b] := by
    rw [hj, pow_mul]
    simpa using heuler.pow j
  have hresB : natFixedA (10 ^ d) n ≡ 1 [MOD b] := by
    have hone : 1 ≤ n := hnpos
    have hdivChoose : b ∣ n.choose 2 := by
      have hdvd : 2 * b ∣ n - 1 := by
        exact (Nat.modEq_iff_dvd' hone).mp hindexB.symm
      obtain ⟨s, hs⟩ := hdvd
      have hnEq : n = 2 * b * s + 1 := by
        calc
          n = (n - 1) + 1 := (Nat.sub_add_cancel hone).symm
          _ = 2 * b * s + 1 := by rw [hs]
      rw [hnEq, Nat.choose_two_right]
      simp only [Nat.add_sub_cancel]
      rw [show (2 * b * s + 1) * (2 * b * s) =
        2 * ((2 * b * s + 1) * (b * s)) by ring]
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      exact ⟨(2 * b * s + 1) * s, by ring⟩
    have hnmodB : n ≡ 1 [MOD b] := by
      apply hindexB.of_dvd
      exact ⟨2, by ring⟩
    have hLmodB : natTriangularStart n ≡ 1 [MOD b] := by
      have hx := hdivChoose.modEq_zero_nat.add (Nat.ModEq.refl 1)
      simpa [natTriangularStart] using hx
    have hqZ : ((10 ^ d : ℕ) : ZMod b) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff (10 ^ d) 1 b).2 hbaseB
    have hLZ : ((natTriangularStart n : ℕ) : ZMod b) = 1 := by
      simpa using
        (ZMod.natCast_eq_natCast_iff (natTriangularStart n) 1 b).2 hLmodB
    have hnZ : (n : ZMod b) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff n 1 b).2 hnmodB
    have hoffsets :
        (∑ i ∈ Finset.range n, (i : ZMod b)) = 0 := by
      rw [← Nat.cast_sum, Finset.sum_range_id, ← Nat.choose_two_right]
      exact (ZMod.natCast_eq_zero_iff (n.choose 2) b).2 hdivChoose
    have hcast : ((natFixedA (10 ^ d) n : ℕ) : ZMod b) = 1 := by
      rw [natFixedA, natCast_fixedConcat]
      exact fixedConcat_eq_one_of_residue_data
        ((10 ^ d : ℕ) : ZMod b)
        ((natTriangularStart n : ℕ) : ZMod b) n
        hqZ hLZ hnZ hoffsets
    have hcast' :
        ((natFixedA (10 ^ d) n : ℕ) : ZMod b) = ((1 : ℕ) : ZMod b) := by
      simpa using hcast
    exact
      (ZMod.natCast_eq_natCast_iff (natFixedA (10 ^ d) n) 1 b).1 hcast'

  have hab : a.Coprime b := by
    simpa [a, b] using tenPart_coprime_tenCoprimePart hm0
  have hresAB : natFixedA (10 ^ d) n ≡ 1 [MOD a * b] :=
    (Nat.modEq_and_modEq_iff_modEq_mul
      (a := natFixedA (10 ^ d) n) (b := 1) (m := a) (n := b) hab).1
      (And.intro hresA hresB)
  have habm : a * b = m := by
    simpa [a, b] using tenPart_mul_tenCoprimePart m
  rw [habm] at hresAB

  exact ⟨d, n, hBN.trans hNn, hfixed, hresAB⟩

end LeanFrontier.A053067
