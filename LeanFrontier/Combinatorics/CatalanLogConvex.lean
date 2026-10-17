import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic

/-!
# A strict log-convexity identity for the Catalan numbers

The Catalan sequence is strictly log-convex: `C_(n+1)^2 < C_n * C_(n+2)`
for every natural number `n`. The proof establishes an exact positive
defect identity for the pair of adjacent recurrence equations. This
recovers the classical monotonicity of successive Catalan ratios without
using real-valued division.

The only input is Mathlib's central-binomial formula for `catalan`,
together with the recurrence of central binomial coefficients.
-/

namespace LeanFrontier.Combinatorics

/-- The first-order Catalan recurrence, obtained by cancelling the
nonzero factor `n+1` from the central-binomial recurrence. -/
theorem catalan_succ_mul (n : ℕ) :
    (n + 2) * catalan (n + 1) =
      2 * (2 * n + 1) * catalan n := by
  have h : (n + 1) * ((n + 2) * catalan (n + 1)) =
      (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    calc
      (n + 1) * ((n + 2) * catalan (n + 1)) =
          (n + 1) * Nat.centralBinom (n + 1) := by
            rw [succ_mul_catalan_eq_centralBinom]
      _ = 2 * (2 * n + 1) * Nat.centralBinom n :=
        Nat.succ_mul_centralBinom_succ n
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
        rw [← succ_mul_catalan_eq_centralBinom n]
        ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

private theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hc := Nat.centralBinom_pos n
  by_contra hn
  have hz : catalan n = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, mul_zero] at h
  omega

/-- An exact identity exhibiting the strict log-convexity gap of the
Catalan sequence. Multiplying the difference of adjacent products by
`(n+2)(n+3)` produces exactly `6 C_n C_(n+1)`. -/
theorem catalan_logConvex_identity (n : ℕ) :
    ((n + 2) * (n + 3)) * (catalan n * catalan (n + 2)) =
      ((n + 2) * (n + 3)) * (catalan (n + 1) ^ 2) +
        6 * catalan n * catalan (n + 1) := by
  have h₁ := catalan_succ_mul n
  have h₂ := catalan_succ_mul (n + 1)
  calc
    ((n + 2) * (n + 3)) * (catalan n * catalan (n + 2)) =
        ((n + 2) * catalan n) * ((n + 3) * catalan (n + 2)) := by ring
    _ = ((n + 2) * catalan n) *
          (2 * (2 * (n + 1) + 1) * catalan (n + 1)) := by rw [h₂]
    _ = ((n + 2) * catalan (n + 1)) *
          ((n + 3) * catalan (n + 1)) +
          6 * catalan n * catalan (n + 1) := by
        rw [h₁]
        ring
    _ = ((n + 2) * (n + 3)) * (catalan (n + 1) ^ 2) +
          6 * catalan n * catalan (n + 1) := by ring

/-- **Strict log-convexity of Catalan numbers.** Each Catalan number
is the strict geometric mean bound for its two neighbours, so the
ratio of consecutive terms is strictly increasing. -/
theorem catalan_strict_logConvex (n : ℕ) :
    catalan (n + 1) ^ 2 < catalan n * catalan (n + 2) := by
  have h := catalan_logConvex_identity n
  have hp : 0 < 6 * catalan n * catalan (n + 1) := by
    have h₁ := catalan_pos n
    have h₂ := catalan_pos (n + 1)
    positivity
  have hk : 0 < (n + 2) * (n + 3) := by positivity
  by_contra hn
  have hle :
      catalan n * catalan (n + 2) ≤ catalan (n + 1) ^ 2 := by omega
  have hmul :=
    Nat.mul_le_mul_left ((n + 2) * (n + 3)) hle
  omega

end LeanFrontier.Combinatorics
