import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Sylvester's sequence

Sylvester's sequence is `2, 3, 7, 43, 1807, 3263443, ...`, defined by `S 0 = 2` and
`S (n + 1) = S n ^ 2 - S n + 1`. It is the sequence produced by the greedy algorithm for
writing `1` as a sum of distinct unit fractions, and it is the standard doubly exponential
example of an infinite family of pairwise coprime naturals.

Here it is defined by the subtraction-free recurrence `S (n + 1) = S n * (S n - 1) + 1`, which
agrees with the classical one because `1 ≤ S n`; `sylvesterNumber_succ_eq_sq_sub_add_one`
records that agreement.

## Main definitions

* `LeanFrontier.Nat.sylvesterNumber` - the sequence itself.

## Main statements

* `LeanFrontier.Nat.sylvesterNumber_eq_prod_add_one` - each term is one more than the product
  of all earlier terms.
* `LeanFrontier.Nat.coprime_sylvesterNumber_sylvesterNumber` - distinct terms are coprime.
* `LeanFrontier.Nat.sum_range_inv_sylvesterNumber` - the reciprocals telescope:
  `∑ i < n, 1 / S i = 1 - 1 / (S n - 1)` in any field of characteristic zero.
* `LeanFrontier.Nat.strictMono_sylvesterNumber` - the sequence is strictly increasing.

## Implementation notes

The product identity is the engine of the module: it gives coprimality exactly as
`Nat.fermatNumber_eq_prod_add_two` yields Goldbach's result on Fermat numbers, and it is the
`n`-th partial product appearing in the telescoping reciprocal identity.

The reciprocal identity is stated for an arbitrary field of characteristic zero rather than for
`ℚ` alone. Nothing beyond injectivity of the natural number cast is used, so the rational, real
and complex forms are instances of one statement.

Both `sylvesterNumber n` and `sylvesterNumber n - 1` are nonzero, so no division by zero occurs
and the identity needs no side condition.
-/

namespace LeanFrontier.Nat

/-- Sylvester's sequence: `S 0 = 2` and `S (n + 1) = S n * (S n - 1) + 1`, so that
`S n - 1` is the product of all earlier terms. -/
def sylvesterNumber : ℕ → ℕ
  | 0 => 2
  | n + 1 => sylvesterNumber n * (sylvesterNumber n - 1) + 1

@[simp] theorem sylvesterNumber_zero : sylvesterNumber 0 = 2 := rfl

theorem sylvesterNumber_succ (n : ℕ) :
    sylvesterNumber (n + 1) = sylvesterNumber n * (sylvesterNumber n - 1) + 1 := rfl

/-- Every term is at least `2`; in particular no term is `0` or `1`. -/
theorem two_le_sylvesterNumber (n : ℕ) : 2 ≤ sylvesterNumber n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sylvesterNumber_succ]
    have h : 2 * 1 ≤ sylvesterNumber n * (sylvesterNumber n - 1) :=
      Nat.mul_le_mul ih (by omega)
    omega

/-- The defining recurrence in its classical form. -/
theorem sylvesterNumber_succ_eq_sq_sub_add_one (n : ℕ) :
    sylvesterNumber (n + 1) = sylvesterNumber n ^ 2 - sylvesterNumber n + 1 := by
  have hsq : sylvesterNumber n ^ 2
      = sylvesterNumber n * (sylvesterNumber n - 1) + sylvesterNumber n := by
    obtain ⟨k, hk⟩ : ∃ k, sylvesterNumber n = k + 1 :=
      ⟨sylvesterNumber n - 1, by have := two_le_sylvesterNumber n; omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  rw [sylvesterNumber_succ, hsq, Nat.add_sub_cancel]

/-- Each term is one more than the product of all the earlier ones. -/
theorem sylvesterNumber_eq_prod_add_one (n : ℕ) :
    sylvesterNumber n = (∏ i ∈ Finset.range n, sylvesterNumber i) + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, sylvesterNumber_succ]
    have h : sylvesterNumber n - 1 = ∏ i ∈ Finset.range n, sylvesterNumber i := by
      rw [ih]; exact Nat.add_sub_cancel _ _
    rw [h]
    ring

/-- Distinct terms of Sylvester's sequence are coprime. -/
theorem coprime_sylvesterNumber_sylvesterNumber {m n : ℕ} (h : m ≠ n) :
    Nat.Coprime (sylvesterNumber m) (sylvesterNumber n) := by
  wlog hlt : m < n
  · exact (this h.symm (by omega)).symm
  rw [sylvesterNumber_eq_prod_add_one n,
    Nat.coprime_add_iff_right (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hlt))]
  exact Nat.coprime_one_right _

/-- Sylvester's sequence is strictly increasing. -/
theorem strictMono_sylvesterNumber : StrictMono sylvesterNumber := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [sylvesterNumber_succ]
  calc sylvesterNumber n = sylvesterNumber n * 1 := (Nat.mul_one _).symm
    _ ≤ sylvesterNumber n * (sylvesterNumber n - 1) :=
        Nat.mul_le_mul le_rfl (by have := two_le_sylvesterNumber n; omega)
    _ < sylvesterNumber n * (sylvesterNumber n - 1) + 1 := Nat.lt_succ_self _

variable {K : Type*} [Field K] [CharZero K]

private theorem cast_sylvesterNumber_ne_zero (n : ℕ) : (sylvesterNumber n : K) ≠ 0 := by
  have h : sylvesterNumber n ≠ 0 := by have := two_le_sylvesterNumber n; omega
  exact_mod_cast h

private theorem cast_sylvesterNumber_sub_one_ne_zero (n : ℕ) :
    (sylvesterNumber n : K) - 1 ≠ 0 := by
  have h : sylvesterNumber n ≠ 1 := by have := two_le_sylvesterNumber n; omega
  intro hzero
  rw [sub_eq_zero] at hzero
  exact h (by exact_mod_cast hzero)

omit [CharZero K] in
private theorem cast_sylvesterNumber_succ (n : ℕ) :
    (sylvesterNumber (n + 1) : K)
      = (sylvesterNumber n : K) * ((sylvesterNumber n : K) - 1) + 1 := by
  have h : 1 ≤ sylvesterNumber n := by have := two_le_sylvesterNumber n; omega
  rw [sylvesterNumber_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_sub h, Nat.cast_one]

/-- The reciprocals of Sylvester's sequence telescope: the partial sums of `1 / S i` are
`1 - 1 / (S n - 1)`, so the greedy unit fraction expansion of `1` never overshoots. -/
theorem sum_range_inv_sylvesterNumber (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : K) / sylvesterNumber i
      = 1 - 1 / ((sylvesterNumber n : K) - 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hS : (sylvesterNumber n : K) ≠ 0 := cast_sylvesterNumber_ne_zero n
    have hP : (sylvesterNumber n : K) - 1 ≠ 0 := cast_sylvesterNumber_sub_one_ne_zero n
    have hsucc : (sylvesterNumber (n + 1) : K) - 1
        = (sylvesterNumber n : K) * ((sylvesterNumber n : K) - 1) := by
      rw [cast_sylvesterNumber_succ]; ring
    rw [Finset.sum_range_succ, ih, hsucc]
    field_simp
    ring

end LeanFrontier.Nat
