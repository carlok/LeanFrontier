import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-!
# A square root of minus one from a coprime sum of two squares

Suppose an integer `m` divides `u^2 + v^2` and is coprime to `v`.
Then `v` is invertible modulo `m`, so informally `u / v` is a square
root of `-1` modulo `m`.

This module proves the statement directly over integer congruences, without
introducing a quotient ring or choosing a modular inverse operation.  A Bezout
witness for `IsCoprime m v` supplies the inverse coefficient explicitly.

The result is intended as reusable arithmetic infrastructure; in particular,
positive Markov triples provide exactly these hypotheses for their maximum
coordinate and either smaller coordinate.
-/

namespace LeanFrontier.Int

/-- If `m ∣ u² + v²` and `m` is coprime to `v`, then `-1` has a
square root modulo `m`. -/
theorem exists_sq_modEq_neg_one_of_isCoprime_of_dvd_sq_add_sq
    {m u v : ℤ}
    (hcop : IsCoprime m v)
    (hdiv : m ∣ u ^ 2 + v ^ 2) :
    ∃ r : ℤ, r ^ 2 ≡ -1 [ZMOD m] := by
  rcases hcop with ⟨a, b, hbezout⟩
  rcases hdiv with ⟨k, hk⟩
  let r : ℤ := u * b
  have hdvd : m ∣ r ^ 2 + 1 := by
    refine ⟨b ^ 2 * k + a ^ 2 * m + 2 * a * b * v, ?_⟩
    dsimp [r]
    calc
      (u * b) ^ 2 + 1 =
          b ^ 2 * (u ^ 2 + v ^ 2) +
            (a * m) ^ 2 + 2 * (a * m) * (b * v) := by
              rw [← hbezout]
              ring
      _ = b ^ 2 * (m * k) +
            (a * m) ^ 2 + 2 * (a * m) * (b * v) := by
              rw [hk]
      _ = m * (b ^ 2 * k + a ^ 2 * m + 2 * a * b * v) := by
              ring
  refine ⟨r, ?_⟩
  have hmod : (-1 : ℤ) ≡ r ^ 2 [ZMOD m] := by
    rw [Int.modEq_iff_dvd]
    simpa [sub_neg_eq_add] using hdvd
  exact hmod.symm

end LeanFrontier.Int
