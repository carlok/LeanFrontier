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

end LeanFrontier.A053067
