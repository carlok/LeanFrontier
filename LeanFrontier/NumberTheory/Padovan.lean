import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init

/-!
# The Padovan sequence

The *Padovan sequence* is the three-term linear recurrence `P 0 = P 1 = P 2 = 1` and
`P (n + 3) = P (n + 1) + P n` (OEIS A000931). Like the Fibonacci numbers it grows by adding
earlier terms, but each new term skips the immediately preceding one, so it is not an instance
of a two-term Horadam recurrence.

## Main definitions

* `LeanFrontier.Padovan.padovan` - the sequence itself.

## Main statements

* `LeanFrontier.Padovan.padovan_pos` - every term is at least `1`.
* `LeanFrontier.Padovan.padovan_sum_add_two` - the partial sums telescope:
  `(∑ i ∈ range (n + 1), P i) + 2 = P (n + 2) + P (n + 3)`.

## Implementation notes

The sum identity is stated with `+ 2` on the left rather than `- 2` on the right, so that no
truncated natural subtraction appears; `padovan_pos` shows the right-hand side is always at
least `2`, so the subtracted form is equivalent but avoids stating it.

`padovan_add_three` restates the recursive equation in additive form and is used internally by
both statements; it is not claimed as an entrypoint since it is exactly the definitional
equation of `padovan` and adds nothing beyond what the definition already publishes.
-/

namespace LeanFrontier.Padovan

/-- The Padovan sequence: `P 0 = P 1 = P 2 = 1` and `P (n + 3) = P (n + 1) + P n`. -/
def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => padovan (n + 1) + padovan n

theorem padovan_add_three (n : ℕ) : padovan (n + 3) = padovan (n + 1) + padovan n := rfl

/-- Every term of the Padovan sequence is at least `1`. -/
theorem padovan_pos (n : ℕ) : 1 ≤ padovan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | m + 3 =>
      rw [padovan_add_three]
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      omega

/-- The partial sums of the Padovan sequence telescope against two later terms:
`(∑ i ∈ range (n + 1), P i) + 2 = P (n + 2) + P (n + 3)`. -/
theorem padovan_sum_add_two (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), padovan i) + 2 = padovan (n + 2) + padovan (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have e1 : n + 1 + 1 = n + 2 := by omega
    have e2 : n + 1 + 2 = n + 3 := by omega
    have e3 : n + 1 + 3 = n + 4 := by omega
    have hrec : padovan (n + 4) = padovan (n + 2) + padovan (n + 1) := by
      rw [← e3, ← e1]; exact padovan_add_three (n + 1)
    rw [Finset.sum_range_succ, e2, e3, hrec]
    omega

end LeanFrontier.Padovan
