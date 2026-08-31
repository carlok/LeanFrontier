import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init

/-!
# The Tribonacci numbers

The *Tribonacci sequence* is the three-term linear recurrence `T 0 = 0`, `T 1 = 1`, `T 2 = 1`,
`T (n + 3) = T (n + 2) + T (n + 1) + T n` (OEIS A000073). Unlike the Padovan sequence already in
the corpus, whose recurrence skips the immediately preceding term
(`P (n + 3) = P (n + 1) + P n`), each Tribonacci term is the sum of all three of its immediate
predecessors, so it is not an instance of the same skip-one recurrence, nor of the two-term
Horadam framework already in the corpus.

## Main definitions

* `LeanFrontier.Tribonacci.tribonacci` - the sequence itself.

## Main statements

* `LeanFrontier.Tribonacci.tribonacci_succ_pos` - every term from index `1` onward is at least
  `1`.
* `LeanFrontier.Tribonacci.tribonacci_two_mul_sum_add_one` - the partial sums satisfy
  `2 * (∑ i ∈ range (n + 1), T i) + 1 = T (n + 2) + T n`.

## Implementation notes

`T 0 = 0`, so positivity is stated from index `1` rather than `0`.

The sum identity is stated with a doubled left-hand side, `2 * (...) + 1`, rather than dividing
the right-hand side by `2`, so that no natural-number division or truncated subtraction appears;
the two sides agree because `T (n + 2) + T n` is always odd, but that parity fact is not itself
claimed.

`tribonacci_add_three` restates the recursive equation in additive form and is used internally by
both statements; it is not claimed as an entrypoint since it is exactly the definitional equation
of `tribonacci` and adds nothing beyond what the definition already publishes.
-/

namespace LeanFrontier.Tribonacci

/-- The Tribonacci sequence: `T 0 = 0`, `T 1 = 1`, `T 2 = 1`, and
`T (n + 3) = T (n + 2) + T (n + 1) + T n`. -/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

theorem tribonacci_add_three (n : ℕ) :
    tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl

/-- Every Tribonacci term from index `1` onward is at least `1`. -/
theorem tribonacci_succ_pos (n : ℕ) : 1 ≤ tribonacci (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | m + 2 =>
      have e : m + 2 + 1 = m + 3 := by omega
      have hrec : tribonacci (m + 3) = tribonacci (m + 2) + tribonacci (m + 1) + tribonacci m :=
        tribonacci_add_three m
      have h : 1 ≤ tribonacci (m + 2) := ih (m + 1) (by omega)
      rw [e, hrec]
      omega

/-- The partial sums of the Tribonacci sequence satisfy
`2 * (∑ i ∈ range (n + 1), T i) + 1 = T (n + 2) + T n`. -/
theorem tribonacci_two_mul_sum_add_one (n : ℕ) :
    2 * (∑ i ∈ Finset.range (n + 1), tribonacci i) + 1 = tribonacci (n + 2) + tribonacci n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have e1 : n + 1 + 2 = n + 3 := by omega
    have hrec : tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n :=
      tribonacci_add_three n
    rw [Finset.sum_range_succ, e1, hrec]
    omega

end LeanFrontier.Tribonacci
