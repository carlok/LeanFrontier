import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nesbitt's inequality

For positive real numbers `a`, `b`, and `c`, Nesbitt's inequality states

`3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b)`.

The proof clears the positive common denominator and uses the identity

`2 * N - 3 * D =
  (a - b)^2 * (a + b) + (b - c)^2 * (b + c) + (c - a)^2 * (c + a)`,

whose right-hand side is nonnegative.
-/

namespace LeanFrontier.Nesbitt

/-- **Nesbitt's inequality** for three positive real numbers. -/
theorem inequality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (3 : ℝ) / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have hab : 0 < a + b := by positivity
  have hbc : 0 < b + c := by positivity
  have hca : 0 < c + a := by positivity
  let D : ℝ := (a + b) * (b + c) * (c + a)
  let N : ℝ :=
    a * (a + b) * (c + a) +
      b * (a + b) * (b + c) +
      c * (b + c) * (c + a)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hsum : a / (b + c) + b / (c + a) + c / (a + b) = N / D := by
    dsimp [N, D]
    field_simp [ne_of_gt hab, ne_of_gt hbc, ne_of_gt hca]
    <;> ring
  have hnonneg :
      0 ≤ (a - b) ^ 2 * (a + b) +
        (b - c) ^ 2 * (b + c) +
        (c - a) ^ 2 * (c + a) := by
    positivity
  have hid :
      2 * N - 3 * D =
        (a - b) ^ 2 * (a + b) +
          (b - c) ^ 2 * (b + c) +
          (c - a) ^ 2 * (c + a) := by
    dsimp [N, D]
    ring
  have hND : 3 * D ≤ 2 * N := by
    nlinarith [hnonneg, hid]
  rw [hsum]
  apply (le_div_iff₀ hD).2
  nlinarith [hND]

end LeanFrontier.Nesbitt
