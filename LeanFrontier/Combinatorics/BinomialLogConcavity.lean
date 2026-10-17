import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Log-concavity of the rows of Pascal's triangle

For each fixed `n`, the binomial coefficient sequence `k ↦ n.choose k`
is log-concave: adjacent coefficients satisfy the Turán inequality
`choose n k * choose n (k+2) ≤ (choose n (k+1))²`.

The stronger exact identity below exhibits a positive algebraic defect, and
implies *strict* log-concavity whenever `k < n` (so the middle coefficient is
positive). It is derived from Mathlib's two adjacent Pascal-row factorial
identities `Nat.choose_succ_right_eq`; no new binomial coefficient is defined.

This complements Mathlib's unimodality and central-binomial-coefficient
bounds by recording the multiplicative shape of an entire Pascal row.
-/

namespace LeanFrontier.Combinatorics

/-- An exact Turán identity for three consecutive entries of a Pascal row.

The nonnegative rightmost summand measures the strict failure of equality in
the binomial log-concavity inequality. The identity also holds at and beyond
the end of a row, where binomial coefficients are defined to vanish. -/
theorem choose_adjacent_turan_identity (n k : ℕ) :
    (n.choose (k + 1)) ^ 2 * (k + 1) * (k + 2) =
      n.choose k * n.choose (k + 2) * (k + 1) * (k + 2) +
        n.choose k * n.choose (k + 1) * (n + 1) := by
  by_cases hk : k < n
  · let d : ℕ := n - (k + 1)
    have hd : n - k = d + 1 := by
      dsimp [d]
      omega
    have hn : n + 1 = d + k + 2 := by
      dsimp [d]
      omega
    have hfirst :
        n.choose (k + 1) * (k + 1) =
          n.choose k * (n - k) :=
      Nat.choose_succ_right_eq n k
    have hsecond :
        n.choose (k + 2) * (k + 2) =
          n.choose (k + 1) * d := by
      simpa [d, Nat.add_assoc] using
        (Nat.choose_succ_right_eq n (k + 1))
    calc
      (n.choose (k + 1)) ^ 2 * (k + 1) * (k + 2) =
          (n.choose (k + 1) * (k + 1)) *
            n.choose (k + 1) * (k + 2) := by ring
      _ = (n.choose k * (n - k)) *
            n.choose (k + 1) * (k + 2) := by rw [hfirst]
      _ = n.choose k * n.choose (k + 1) *
            ((d + 1) * (k + 2)) := by rw [hd]; ring
      _ = n.choose k * n.choose (k + 1) *
            ((k + 1) * d + (n + 1)) := by rw [hn]; ring
      _ = n.choose k * (n.choose (k + 1) * d) * (k + 1) +
            n.choose k * n.choose (k + 1) * (n + 1) := by ring
      _ = n.choose k * (n.choose (k + 2) * (k + 2)) * (k + 1) +
            n.choose k * n.choose (k + 1) * (n + 1) := by rw [hsecond]
      _ = n.choose k * n.choose (k + 2) * (k + 1) * (k + 2) +
            n.choose k * n.choose (k + 1) * (n + 1) := by ring
  · have hmiddle : n.choose (k + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have hright : n.choose (k + 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hmiddle, hright]

/-- **Log-concavity of binomial coefficients.** Every row of Pascal's
triangle satisfies the multiplicative adjacent-coefficient inequality,
including the zero tails beyond the end of the row. -/
theorem choose_logConcave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  have h := choose_adjacent_turan_identity n k
  have ht : 0 < (k + 1) * (k + 2) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ ht
  calc
    (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2)) =
        n.choose k * n.choose (k + 2) * (k + 1) * (k + 2) := by ring
    _ ≤ (n.choose (k + 1)) ^ 2 * (k + 1) * (k + 2) := by
      rw [h]
      omega
    _ = (n.choose (k + 1)) ^ 2 * ((k + 1) * (k + 2)) := by ring

/-- The binomial Turán inequality is strict as soon as the middle entry
of the three consecutive coefficients is nonzero. -/
theorem choose_strict_logConcave (n k : ℕ) (hk : k < n) :
    n.choose k * n.choose (k + 2) < (n.choose (k + 1)) ^ 2 := by
  have h := choose_adjacent_turan_identity n k
  have hleft : 0 < n.choose k := Nat.choose_pos (by omega)
  have hmiddle : 0 < n.choose (k + 1) := Nat.choose_pos (by omega)
  have hgap :
      0 < n.choose k * n.choose (k + 1) * (n + 1) := by
    positivity
  have hprod :
      (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2)) <
        (n.choose (k + 1)) ^ 2 * ((k + 1) * (k + 2)) := by
    have hs :
        n.choose k * n.choose (k + 2) * (k + 1) * (k + 2) <
          (n.choose (k + 1)) ^ 2 * (k + 1) * (k + 2) := by
      rw [h]
      omega
    nlinarith
  by_contra hnot
  have hrev :
      (n.choose (k + 1)) ^ 2 ≤ n.choose k * n.choose (k + 2) := by omega
  have hmul := Nat.mul_le_mul_right ((k + 1) * (k + 2)) hrev
  omega

end LeanFrontier.Combinatorics
