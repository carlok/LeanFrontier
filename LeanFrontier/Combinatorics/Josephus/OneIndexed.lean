import LeanFrontier.Combinatorics.Josephus
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Log

/-!
# The one-indexed Josephus function and the bridge to `survivor`

`LeanFrontier.Combinatorics.Josephus` numbers the circle `0, ..., n - 1` and computes the
survivor's position with the shift-and-wrap recurrence. This module treats the classical
one-indexed convention, where the people are numbered `1, ..., n`: `josephus n` is defined
independently, by the well-founded halving recursion `J (2 n) = 2 J n - 1` and
`J (2 n + 1) = 2 J n + 1`, and the two developments are then reconciled by the bridge

`josephus n = survivor n + 1` for `n ≠ 0` (`josephus_eq_survivor_add_one`).

Since the two functions arise from different recursions - one steps the circle size by one,
the other halves it - the bridge is a genuine theorem, and it cross-validates both
formalizations: each is the other shifted by one.

The remaining public statements are the ones with no counterpart in the zero-indexed module:
positivity, oddness of the survivor's number, the power-of-two case `josephus (2 ^ m) = 1`,
the bound `josephus n ≤ n`, and the fixed-point characterization
`josephus n = n ↔ ∃ m, n = 2 ^ m - 1` (the last person survives exactly when the binary
expansion of `n` is all ones).

## Main definitions

* `LeanFrontier.Josephus.josephus` - the one-indexed survivor, by halving recursion.

## Main statements

* `LeanFrontier.Josephus.josephus_eq_survivor_add_one` - the bridge between the conventions.
* `LeanFrontier.Josephus.josephus_pos` and `LeanFrontier.Josephus.josephus_le` - the
  survivor's number is in `[1, n]`.
* `LeanFrontier.Josephus.odd_josephus` - the survivor's number is always odd: the first pass
  eliminates everyone with an even number.
* `LeanFrontier.Josephus.josephus_two_pow` - among `2 ^ m` people, person `1` survives.
* `LeanFrontier.Josephus.josephus_eq_self_iff` - person `n` survives iff `n = 2 ^ m - 1`.

## Implementation notes

The halving recurrences and the closed form `josephus (2 ^ m + l) = 2 * l + 1` are proved
from the definition but kept `private`: as public statements they would only mirror the
accepted `survivor_two_mul`, `survivor_two_mul_add_one` and `survivor_two_pow_add` through
the bridge, and the module's public surface is meant to add to the accepted theory, not to
restate it. The bridge itself is one rewrite connecting the two `Nat.log` closed forms.
-/

namespace LeanFrontier.Josephus

/-- The one-indexed Josephus survivor for step two: with people `1, ..., n` in a circle and
every second person eliminated starting from person `2`, `josephus n` is the number of the
last person remaining. After the first pass only the odd numbers survive, which gives the
halving recurrences `josephus (2 * n) = 2 * josephus n - 1` and
`josephus (2 * n + 1) = 2 * josephus n + 1`. -/
def josephus (n : ℕ) : ℕ :=
  if _h : n ≤ 1 then n
  else if n % 2 = 0 then 2 * josephus (n / 2) - 1
  else 2 * josephus (n / 2) + 1
  decreasing_by all_goals exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem josephus_zero : josephus 0 = 0 := by simp [josephus]

@[simp] theorem josephus_one : josephus 1 = 1 := by simp [josephus]

private theorem josephus_two_mul {n : ℕ} (hn : n ≠ 0) :
    josephus (2 * n) = 2 * josephus n - 1 := by
  rw [josephus]
  have h1 : ¬2 * n ≤ 1 := by omega
  have h2 : 2 * n % 2 = 0 := by omega
  have h3 : 2 * n / 2 = n := by omega
  simp [h1, h2, h3]

private theorem josephus_two_mul_add_one (n : ℕ) :
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

private theorem josephus_two_pow_add {m l : ℕ} (hl : l < 2 ^ m) :
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

/-- Among `2 ^ m` people, the survivor is person `1`. -/
theorem josephus_two_pow (m : ℕ) : josephus (2 ^ m) = 1 := by
  simpa using josephus_two_pow_add (m := m) (l := 0) (Nat.two_pow_pos m)

private theorem josephus_eq_two_mul_sub_two_pow_log {n : ℕ} (hn : n ≠ 0) :
    josephus n = 2 * (n - 2 ^ Nat.log 2 n) + 1 := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hpow : (2 : ℕ) ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by
    rw [Nat.pow_succ]; omega
  have hsplit : n = 2 ^ Nat.log 2 n + (n - 2 ^ Nat.log 2 n) := by omega
  conv_lhs => rw [hsplit]
  rw [josephus_two_pow_add (by omega)]

/-- The bridge between the two conventions: the one-indexed survivor is the zero-indexed
survivor shifted by one. Both functions are defined by independent recursions - `survivor`
steps the circle size by one, `josephus` halves it - so this identity cross-validates the
two formalizations. -/
theorem josephus_eq_survivor_add_one {n : ℕ} (hn : n ≠ 0) :
    josephus n = survivor n + 1 := by
  rw [josephus_eq_two_mul_sub_two_pow_log hn,
    survivor_eq_two_mul_sub_two_pow_log n hn]

/-- The survivor's number is odd: the first pass around the circle eliminates everyone whose
number is even. -/
theorem odd_josephus {n : ℕ} (hn : n ≠ 0) : Odd (josephus n) :=
  ⟨n - 2 ^ Nat.log 2 n, josephus_eq_two_mul_sub_two_pow_log hn⟩

/-- The survivor's number is at most `n`. -/
theorem josephus_le (n : ℕ) : josephus n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [josephus_eq_survivor_add_one (by omega)]
    have := survivor_lt_self n (by omega)
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

/-- The classical instance: among `41` people, the survivor stands in position `19` -
one-indexed here, position `18` in the zero-indexed convention. -/
example : josephus 41 = 19 := by
  have : (41 : ℕ) = 2 ^ 5 + 9 := by decide
  rw [this, josephus_two_pow_add (by decide)]

end LeanFrontier.Josephus
