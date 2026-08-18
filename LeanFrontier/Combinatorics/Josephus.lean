import Mathlib.Data.Nat.Log

/-!
# The Josephus problem for step two

`n` people stand in a circle, numbered `0, 1, ..., n - 1`. Starting the count at person `0`,
every second person still standing is removed, going around the circle repeatedly, until one
person remains. `survivor n` is the number of that last person.

Removing person `1` first and then renumbering the remaining circle from the new starting
point gives the recurrence used here as the definition:
`survivor 0 = 0` and `survivor (n + 1) = (survivor n + 2) % (n + 1)`.

## Main definitions

* `LeanFrontier.Josephus.survivor` - the position of the last person standing.

## Main statements

* `LeanFrontier.Josephus.survivor_lt_self` - the survivor is a position of the circle it
  belongs to.
* `LeanFrontier.Josephus.survivor_two_pow_add` - writing `n = 2 ^ m + k` with `k < 2 ^ m`,
  the survivor is `2 * k`. In binary this deletes the leading one of `n` and appends a zero.
* `LeanFrontier.Josephus.survivor_eq_two_mul_sub_two_pow_log` - the same closed form phrased
  with `Nat.log`, so it needs no decomposition of `n`.
* `LeanFrontier.Josephus.survivor_two_mul` and
  `LeanFrontier.Josephus.survivor_two_mul_add_one` - the halving recurrences, which read one
  binary digit of `n` at a time.
* `LeanFrontier.Josephus.survivor_eq_zero_iff` - the first person survives exactly when the
  circle has a power of two members.

## Implementation notes

The recurrence in the definition steps `n` by one and is therefore structural, which keeps the
definition free of well-founded recursion. Everything else is derived from the single induction
in the closed form: at each step the shifted value `survivor n + 2` is already smaller than the
new circle, except when `n + 1` is exactly a power of two, and then it wraps to `0`.

The closed form is stated in the `2 ^ m + k` form as well as with `Nat.log`. The former is the
one a caller uses when the binary size of `n` is known, the latter avoids producing a witness;
neither is derivable from the other by `rfl`.
-/

namespace LeanFrontier.Josephus

/-- `survivor n` is the zero-based position of the last person standing when `n` people in a
circle are removed every second place, counting from person `0`. Removing person `1` and
renumbering from person `2` turns a circle of `n + 1` people into a circle of `n` people, which
is the shift by `2` modulo `n + 1` below. -/
def survivor : ℕ → ℕ
  | 0 => 0
  | n + 1 => (survivor n + 2) % (n + 1)

@[simp] theorem survivor_zero : survivor 0 = 0 := rfl

/-- The defining shift-and-wrap recurrence. -/
theorem survivor_succ (n : ℕ) : survivor (n + 1) = (survivor n + 2) % (n + 1) := rfl

/-- The survivor of a nonempty circle is one of its positions. -/
theorem survivor_lt_self (n : ℕ) (hn : n ≠ 0) : survivor n < n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [survivor_succ]
  exact Nat.mod_lt _ (Nat.succ_pos k)

/-- The closed form, proved by the single induction of the module. It is stated for `k + 1` so
that the induction hypothesis is available at every step without a side condition. -/
private theorem survivor_succ_eq (k : ℕ) :
    survivor (k + 1) = 2 * (k + 1 - 2 ^ Nat.log 2 (k + 1)) := by
  induction k with
  | zero => simp [survivor]
  | succ j ih =>
    have hj : j + 1 ≠ 0 := Nat.succ_ne_zero j
    have hle : 2 ^ Nat.log 2 (j + 1) ≤ j + 1 := Nat.pow_log_le_self 2 hj
    have hlt : j + 1 < 2 ^ (Nat.log 2 (j + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by omega) (j + 1)
    have hpow : 2 ^ (Nat.log 2 (j + 1) + 1) = 2 * 2 ^ Nat.log 2 (j + 1) := by
      rw [Nat.pow_succ]; omega
    rw [survivor_succ, ih]
    rcases Nat.lt_or_ge (j + 2) (2 ^ (Nat.log 2 (j + 1) + 1)) with hcase | hcase
    · have hlog : Nat.log 2 (j + 2) = Nat.log 2 (j + 1) :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) hcase
      rw [hlog, Nat.mod_eq_of_lt (by omega)]
      omega
    · have heq : j + 2 = 2 ^ (Nat.log 2 (j + 1) + 1) := by omega
      have hlog : Nat.log 2 (j + 2) = Nat.log 2 (j + 1) + 1 :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [Nat.pow_succ]; omega)
      have hnum : 2 * (j + 1 - 2 ^ Nat.log 2 (j + 1)) + 2
          = 2 ^ (Nat.log 2 (j + 1) + 1) := by omega
      have hmod : j + 1 + 1 = 2 ^ (Nat.log 2 (j + 1) + 1) := by omega
      rw [hlog, hnum, hmod, Nat.mod_self]
      omega

/-- The survivor of a circle of `n` people is `2 * (n - 2 ^ ⌊log₂ n⌋)`. -/
theorem survivor_eq_two_mul_sub_two_pow_log (n : ℕ) (hn : n ≠ 0) :
    survivor n = 2 * (n - 2 ^ Nat.log 2 n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact survivor_succ_eq k

/-- Writing the size of the circle as `2 ^ m + k` with `k < 2 ^ m`, the survivor is `2 * k`:
in binary, the leading one of `n` is deleted and a zero is appended. -/
theorem survivor_two_pow_add (m k : ℕ) (hk : k < 2 ^ m) : survivor (2 ^ m + k) = 2 * k := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hlog : Nat.log 2 (2 ^ m + k) = m :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [Nat.pow_succ]; omega)
  rw [survivor_eq_two_mul_sub_two_pow_log _ (by omega), hlog]
  omega

/-- Doubling the circle doubles the survivor. -/
theorem survivor_two_mul (n : ℕ) (hn : n ≠ 0) : survivor (2 * n) = 2 * survivor n := by
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hpow : 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by rw [Nat.pow_succ]; omega
  have hpow2 : 2 ^ (Nat.log 2 n + 1 + 1) = 2 * 2 ^ (Nat.log 2 n + 1) := by rw [Nat.pow_succ]; omega
  have hlog : Nat.log 2 (2 * n) = Nat.log 2 n + 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  rw [survivor_eq_two_mul_sub_two_pow_log _ (by omega),
    survivor_eq_two_mul_sub_two_pow_log _ hn, hlog]
  omega

/-- Doubling the circle and adding one person moves the survivor two places on. -/
theorem survivor_two_mul_add_one (n : ℕ) (hn : n ≠ 0) :
    survivor (2 * n + 1) = 2 * survivor n + 2 := by
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hpow : 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by rw [Nat.pow_succ]; omega
  have hpow2 : 2 ^ (Nat.log 2 n + 1 + 1) = 2 * 2 ^ (Nat.log 2 n + 1) := by rw [Nat.pow_succ]; omega
  have hlog : Nat.log 2 (2 * n + 1) = Nat.log 2 n + 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  rw [survivor_eq_two_mul_sub_two_pow_log _ (by omega),
    survivor_eq_two_mul_sub_two_pow_log _ hn, hlog]
  omega

/-- The person who starts the count survives exactly when the circle has a power of two
members. -/
theorem survivor_eq_zero_iff (n : ℕ) (hn : n ≠ 0) : survivor n = 0 ↔ ∃ m, n = 2 ^ m := by
  constructor
  · intro h
    refine ⟨Nat.log 2 n, ?_⟩
    have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
    rw [survivor_eq_two_mul_sub_two_pow_log n hn] at h
    omega
  · rintro ⟨m, rfl⟩
    rw [survivor_eq_two_mul_sub_two_pow_log _ hn, Nat.log_pow (by omega)]
    omega

end LeanFrontier.Josephus
