import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Defs

/-!
# The Thue-Morse sequence and Prouhet's theorem

`thueMorse n` records the parity of the number of ones in the binary expansion of `n`, and
`thueMorseSign n` is the associated `±1`-valued sequence `(-1) ^ (binary digit sum)`.

Prouhet's theorem (1851) states that splitting `{0, 1, ..., 2 ^ k - 1}` according to that parity
produces two blocks with equal power sums for every exponent below `k`. It is the classical
explicit solution of the Prouhet-Tarry-Escott problem, and the reason the Thue-Morse sequence
appears in fair-division arguments.

## Main definitions

* `LeanFrontier.Nat.thueMorse` - the Thue-Morse sequence, valued in `Bool`.
* `LeanFrontier.Nat.thueMorseSign` - the same sequence valued in `{1, -1} ⊆ ℤ`.

## Main statements

* `LeanFrontier.Nat.thueMorse_two_mul` and `LeanFrontier.Nat.thueMorse_two_mul_add_one` - the
  two defining substitution rules of the sequence.
* `LeanFrontier.Nat.thueMorseSign_eq_ite` - the two descriptions agree.
* `LeanFrontier.Nat.sum_range_thueMorseSign_mul_pow` - the signed power sums
  `∑ n < 2 ^ k, (-1) ^ s₂ n * n ^ j` vanish for every `j < k`.
* `LeanFrontier.Nat.sum_pow_eq_sum_pow_thueMorse` - Prouhet's theorem in its partition form.

## Implementation notes

The sequence is defined through `Nat.digits 2` rather than by well-founded recursion, so the two
substitution rules are consequences of `Nat.digits_add` rather than definitional unfoldings, and
no auxiliary recursion needs its own termination argument.

The signed form carries the induction. Splitting `range (2 ^ (k + 1))` into even and odd indices
turns the signed sum for exponent `j` into a combination of the signed sums for exponents below
`j`, because `(2 * i) ^ j - (2 * i + 1) ^ j` expands by the binomial theorem with its leading term
cancelled. Each surviving exponent is smaller than `k`, so one induction on `k` suffices and no
inner induction on `j` is needed.
-/

namespace LeanFrontier.Nat

open Finset

/-- The Thue-Morse sequence: `thueMorse n` is `true` exactly when the binary expansion of `n`
contains an odd number of ones. -/
def thueMorse (n : ℕ) : Bool := decide (Odd (Nat.digits 2 n).sum)

/-- The `±1`-valued Thue-Morse sequence `(-1) ^ s₂ n`, where `s₂ n` is the binary digit sum. -/
def thueMorseSign (n : ℕ) : ℤ := (-1) ^ (Nat.digits 2 n).sum

private theorem digits_sum_two_mul (n : ℕ) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [show 2 * n = 0 + 2 * n by ring,
      Nat.digits_add 2 (by norm_num) 0 n (by norm_num) (Or.inr hn.ne')]
    simp

private theorem digits_sum_two_mul_add_one (n : ℕ) :
    (Nat.digits 2 (2 * n + 1)).sum = (Nat.digits 2 n).sum + 1 := by
  rw [show 2 * n + 1 = 1 + 2 * n by ring,
    Nat.digits_add 2 (by norm_num) 1 n (by norm_num) (Or.inl one_ne_zero)]
  simp [Nat.add_comm]

@[simp] theorem thueMorse_zero : thueMorse 0 = false := by simp [thueMorse]

/-- Doubling leaves the Thue-Morse value unchanged: a trailing binary zero adds no one. -/
theorem thueMorse_two_mul (n : ℕ) : thueMorse (2 * n) = thueMorse n := by
  simp [thueMorse, digits_sum_two_mul]

/-- A trailing binary one flips the Thue-Morse value. -/
theorem thueMorse_two_mul_add_one (n : ℕ) : thueMorse (2 * n + 1) = !thueMorse n := by
  rw [thueMorse, thueMorse, digits_sum_two_mul_add_one]
  rcases Nat.even_or_odd (Nat.digits 2 n).sum with h | h
  · simp [h, Nat.not_odd_iff_even]
  · simp [Nat.odd_add_one, h]

/-- The `±1`-valued sequence is the `Bool`-valued one read as a sign. -/
theorem thueMorseSign_eq_ite (n : ℕ) :
    thueMorseSign n = if thueMorse n then -1 else 1 := by
  rcases Nat.even_or_odd (Nat.digits 2 n).sum with h | h
  · rw [thueMorseSign, h.neg_one_pow, if_neg]
    simp [thueMorse, Nat.not_odd_iff_even, h]
  · rw [thueMorseSign, h.neg_one_pow, if_pos]
    simp [thueMorse, h]

private theorem thueMorseSign_two_mul (n : ℕ) : thueMorseSign (2 * n) = thueMorseSign n := by
  simp [thueMorseSign, digits_sum_two_mul]

private theorem thueMorseSign_two_mul_add_one (n : ℕ) :
    thueMorseSign (2 * n + 1) = -thueMorseSign n := by
  rw [thueMorseSign, thueMorseSign, digits_sum_two_mul_add_one, pow_succ]
  ring

private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ n ∈ range (2 * m), f n = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (fun i => f (2 * i) + f (2 * i + 1)) m, ih, add_assoc]

/-- The signed power sums of the Thue-Morse sequence vanish: for every exponent `j` below `k`,
`∑ n < 2 ^ k, (-1) ^ s₂ n * n ^ j = 0`. -/
theorem sum_range_thueMorseSign_mul_pow {j k : ℕ} (hjk : j < k) :
    ∑ n ∈ range (2 ^ k), thueMorseSign n * (n : ℤ) ^ j = 0 := by
  induction k generalizing j with
  | zero => exact absurd hjk (Nat.not_lt_zero j)
  | succ k ih =>
    have key : ∀ i : ℕ,
        thueMorseSign (2 * i) * ((2 * i : ℕ) : ℤ) ^ j
            + thueMorseSign (2 * i + 1) * ((2 * i + 1 : ℕ) : ℤ) ^ j
          = ∑ m ∈ range j, -((j.choose m : ℤ) * 2 ^ m * (thueMorseSign i * (i : ℤ) ^ m)) := by
      intro i
      have hbin : ((2 * i + 1 : ℕ) : ℤ) ^ j
          = ∑ m ∈ range (j + 1), ((2 : ℤ) * (i : ℤ)) ^ m * (j.choose m : ℤ) := by
        push_cast
        rw [add_pow]
        simp
      have hrhs : ∑ m ∈ range j, -((j.choose m : ℤ) * 2 ^ m * (thueMorseSign i * (i : ℤ) ^ m))
          = -(thueMorseSign i * ∑ m ∈ range j, ((2 : ℤ) * (i : ℤ)) ^ m * (j.choose m : ℤ)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun m _ => by rw [mul_pow]; ring
      rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one, hbin, Finset.sum_range_succ,
        Nat.choose_self, hrhs]
      push_cast
      ring
    rw [pow_succ, mul_comm (2 ^ k) 2, sum_range_two_mul, Finset.sum_congr rfl fun i _ => key i,
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hzero : ∑ i ∈ range (2 ^ k), thueMorseSign i * (i : ℤ) ^ m = 0 :=
      ih (lt_of_lt_of_le (Finset.mem_range.mp hm) (Nat.lt_succ_iff.mp hjk))
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hzero, mul_zero, neg_zero]

/-- **Prouhet's theorem**: splitting `{0, 1, ..., 2 ^ k - 1}` by the Thue-Morse parity of its
elements gives two blocks with the same sum of `j`-th powers for every exponent `j < k`. -/
theorem sum_pow_eq_sum_pow_thueMorse {j k : ℕ} (hjk : j < k) :
    ∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = false), n ^ j
      = ∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = true), n ^ j := by
  have hsplit := sum_range_thueMorseSign_mul_pow (j := j) (k := k) hjk
  rw [← Finset.sum_filter_add_sum_filter_not (range (2 ^ k)) (fun n => thueMorse n = false)]
    at hsplit
  have hfalse : ∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = false),
      thueMorseSign n * (n : ℤ) ^ j
        = ∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = false), ((n : ℤ) ^ j) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have : thueMorse n = false := (Finset.mem_filter.mp hn).2
    rw [thueMorseSign_eq_ite, this]
    simp
  have htrue : ∑ n ∈ (range (2 ^ k)).filter (fun n => ¬ thueMorse n = false),
      thueMorseSign n * (n : ℤ) ^ j
        = -∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = true), ((n : ℤ) ^ j) := by
    have hfilter : (range (2 ^ k)).filter (fun n => ¬ thueMorse n = false)
        = (range (2 ^ k)).filter (fun n => thueMorse n = true) :=
      Finset.filter_congr fun n _ => by simp
    rw [← Finset.sum_neg_distrib, hfilter]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [thueMorseSign_eq_ite, (Finset.mem_filter.mp hn).2]
    simp
  rw [hfalse, htrue] at hsplit
  have : ((∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = false), n ^ j : ℕ) : ℤ)
      = ((∑ n ∈ (range (2 ^ k)).filter (fun n => thueMorse n = true), n ^ j : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast this

end LeanFrontier.Nat
