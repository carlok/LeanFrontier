import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Log

/-!
# The Josephus problem with step two

`n` people stand in a circle, numbered `1` to `n`. Starting from person `1`, every second
person is eliminated: person `2` leaves first, then person `4`, and so on around the shrinking
circle until one person remains. `josephus n` is the number of the survivor, so the sequence
begins `1, 1, 3, 1, 3, 5, 7, 1, 3, ...` (OEIS A006257).

The classical closed form is proved: writing `n = 2 ^ m + l` with `l < 2 ^ m`, the survivor is
`2 * l + 1`. Equivalently, the survivor is obtained from the binary expansion of `n` by moving
its leading bit to the end.

## Main definitions

* `LeanFrontier.Nat.josephus` - the survivor of the elimination process, via the halving
  recurrences `J (2 * n) = 2 * J n - 1` and `J (2 * n + 1) = 2 * J n + 1`.

## Main statements

* `LeanFrontier.Nat.josephus_two_pow_add` - the closed form: `l < 2 ^ m` implies
  `josephus (2 ^ m + l) = 2 * l + 1`.
* `LeanFrontier.Nat.josephus_eq_two_mul_sub_two_pow_log` - the same closed form written with
  `Nat.log`, with no side condition beyond `n ≠ 0`.
* `LeanFrontier.Nat.odd_josephus` - the survivor is always odd: everyone in an even position
  is eliminated in the first pass.
* `LeanFrontier.Nat.josephus_le` - the survivor number never exceeds `n`.
* `LeanFrontier.Nat.josephus_eq_self_iff` - the last person survives exactly when `n + 1` is a
  power of two, i.e. `n = 2 ^ m - 1`.

## Implementation notes

The function recurses on `n / 2`, so the definition is well founded rather than structural and
termination is discharged by `Nat.div_lt_self`. The two halving equations
`josephus_two_mul` and `josephus_two_mul_add_one` are proved from the definition and are the
only interface later proofs use.

In the even case the recurrence subtracts one in `ℕ`; no truncation occurs because the
recursive value is always positive, which is `josephus_pos`. The closed form is a single
induction on the exponent `m` with a parity split on the offset `l`, and every other statement
is derived from the closed form by rewriting `n` as `2 ^ Nat.log 2 n + (n - 2 ^ Nat.log 2 n)`.
-/

namespace LeanFrontier.Nat

/-- The Josephus survivor for step two: with people `1, ..., n` in a circle and every second
person eliminated starting from person `2`, `josephus n` is the number of the last person
remaining. After the first pass only the odd positions survive, which gives the halving
recurrences `josephus (2 * n) = 2 * josephus n - 1` and
`josephus (2 * n + 1) = 2 * josephus n + 1`. -/
def josephus (n : ℕ) : ℕ :=
  if _h : n ≤ 1 then n
  else if n % 2 = 0 then 2 * josephus (n / 2) - 1
  else 2 * josephus (n / 2) + 1
  decreasing_by all_goals exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem josephus_zero : josephus 0 = 0 := by simp [josephus]

@[simp] theorem josephus_one : josephus 1 = 1 := by simp [josephus]

/-- The even halving recurrence: eliminating the even positions from `2 * n` people leaves the
`n` odd positions, and the survivor among those relabels back through `k ↦ 2 * k - 1`. -/
theorem josephus_two_mul {n : ℕ} (hn : n ≠ 0) :
    josephus (2 * n) = 2 * josephus n - 1 := by
  rw [josephus]
  have h1 : ¬2 * n ≤ 1 := by omega
  have h2 : 2 * n % 2 = 0 := by omega
  have h3 : 2 * n / 2 = n := by omega
  simp [h1, h2, h3]

/-- The odd halving recurrence: with `2 * n + 1` people the first pass also removes person `1`,
and the survivor among the remaining `n` relabels through `k ↦ 2 * k + 1`. -/
theorem josephus_two_mul_add_one (n : ℕ) :
    josephus (2 * n + 1) = 2 * josephus n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [josephus]
    have h1 : ¬2 * n + 1 ≤ 1 := by omega
    have h3 : (2 * n + 1) / 2 = n := by omega
    simp [h1, h3]

/-- The survivor's number is positive as soon as anybody is standing in the circle. -/
theorem josephus_pos {n : ℕ} (hn : n ≠ 0) : 0 < josephus n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hk0 : k ≠ 0 := by omega
      have hrec := ih k (by omega) hk0
      have := josephus_two_mul hk0
      omega
    · have := josephus_two_mul_add_one k
      omega

/-- The closed form for the Josephus problem with step two: if `n = 2 ^ m + l` with
`l < 2 ^ m`, the survivor is `2 * l + 1`. -/
theorem josephus_two_pow_add {m l : ℕ} (hl : l < 2 ^ m) :
    josephus (2 ^ m + l) = 2 * l + 1 := by
  induction m generalizing l with
  | zero =>
    have : l = 0 := by omega
    subst this
    simp
  | succ m ih =>
    have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have hm : (0 : ℕ) < 2 ^ m := Nat.two_pow_pos m
    rcases Nat.even_or_odd' l with ⟨j, hj | hj⟩
    · have hsplit : 2 ^ (m + 1) + l = 2 * (2 ^ m + j) := by omega
      have hij := ih (l := j) (by omega)
      rw [hsplit, josephus_two_mul (by omega), hij]
      omega
    · have hsplit : 2 ^ (m + 1) + l = 2 * (2 ^ m + j) + 1 := by omega
      have hij := ih (l := j) (by omega)
      rw [hsplit, josephus_two_mul_add_one, hij]
      omega

/-- The survivor among `2 ^ m` people is person `1`. -/
theorem josephus_two_pow (m : ℕ) : josephus (2 ^ m) = 1 := by
  simpa using josephus_two_pow_add (m := m) (l := 0) (Nat.two_pow_pos m)

/-- The closed form written with `Nat.log`: the survivor among `n` people is
`2 * (n - 2 ^ Nat.log 2 n) + 1`, twice the offset past the largest power of two plus one. -/
theorem josephus_eq_two_mul_sub_two_pow_log {n : ℕ} (hn : n ≠ 0) :
    josephus n = 2 * (n - 2 ^ Nat.log 2 n) + 1 := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hpow : (2 : ℕ) ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by
    rw [Nat.pow_succ]; omega
  have hsplit : n = 2 ^ Nat.log 2 n + (n - 2 ^ Nat.log 2 n) := by omega
  conv_lhs => rw [hsplit]
  rw [josephus_two_pow_add (by omega)]

/-- The survivor's number is odd: the first pass around the circle eliminates everyone whose
number is even. -/
theorem odd_josephus {n : ℕ} (hn : n ≠ 0) : Odd (josephus n) :=
  ⟨n - 2 ^ Nat.log 2 n, josephus_eq_two_mul_sub_two_pow_log hn⟩

/-- The survivor's number is at most `n`. -/
theorem josephus_le (n : ℕ) : josephus n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
    have hpow : (2 : ℕ) ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by
      rw [Nat.pow_succ]; omega
    have := josephus_eq_two_mul_sub_two_pow_log (by omega : n ≠ 0)
    omega

/-- Person `n` survives if and only if `n + 1` is a power of two: the survivor equals `n`
exactly when `n = 2 ^ m - 1`, i.e. when the binary expansion of `n` is all ones. -/
theorem josephus_eq_self_iff {n : ℕ} : josephus n = n ↔ ∃ m, n = 2 ^ m - 1 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, rfl⟩
    · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
      have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
      have hpow : (2 : ℕ) ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by
        rw [Nat.pow_succ]; omega
      have := josephus_eq_two_mul_sub_two_pow_log (by omega : n ≠ 0)
      exact ⟨Nat.log 2 n + 1, by omega⟩
  · rintro ⟨m, rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hk : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      have hsplit : 2 ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by omega
      rw [hsplit, josephus_two_pow_add (by omega)]
      omega

/-- The classical instance: among `41` people, the survivor stands in position `19`. -/
example : josephus 41 = 19 := by
  have : (41 : ℕ) = 2 ^ 5 + 9 := by decide
  rw [this, josephus_two_pow_add (by decide)]

end LeanFrontier.Nat
