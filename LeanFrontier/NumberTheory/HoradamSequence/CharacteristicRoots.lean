import LeanFrontier.NumberTheory.HoradamSequence
import Mathlib.Tactic

/-!
# Characteristic roots and the Binet formula for Horadam sequences

A Horadam sequence with characteristic polynomial `X² - P X + Q` has a
division-free closed form whenever its roots `r`, `s` satisfy
`P = r + s` and `Q = r * s`.

For arbitrary coefficients `c` and `d`, the sequence with initial data
`c+d` and `c*r+d*s` is exactly `c*r^n + d*s^n`. This statement works
over any commutative ring, even if the roots coincide, their difference is a
zero divisor, or the characteristic is positive.

The companion identity `W 0 (r-s) n = r^n-s^n` is a division-free
version of the familiar difference-of-powers Binet formula.
-/

namespace LeanFrontier.Horadam

variable {R : Type*} [CommRing R]

/-- **Characteristic-root formula for Horadam sequences.** If the
characteristic polynomial factors as `(X-r)(X-s)`, its solutions with
root-adapted initial conditions are linear combinations of the two
geometric progressions. No division or distinctness assumption is needed. -/
theorem W_roots (r s c d : R) (n : ℕ) :
    W (r + s) (r * s) (c + d) (c * r + d * s) n =
      c * r ^ n + d * s ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [W]
  | one =>
    simp [W]
  | more n ih₀ ih₁ =>
    have hr : (r + s) * r ^ (n + 1) - (r * s) * r ^ n = r ^ (n + 2) := by
      calc
        (r + s) * r ^ (n + 1) - (r * s) * r ^ n =
            r ^ n * r ^ 2 := by
              rw [pow_succ]
              ring
        _ = r ^ (n + 2) := by rw [pow_add]
    have hs : (r + s) * s ^ (n + 1) - (r * s) * s ^ n = s ^ (n + 2) := by
      calc
        (r + s) * s ^ (n + 1) - (r * s) * s ^ n =
            s ^ n * s ^ 2 := by
              rw [pow_succ]
              ring
        _ = s ^ (n + 2) := by rw [pow_add]
    rw [W_add_two, ih₁, ih₀]
    calc
      (r + s) * (c * r ^ (n + 1) + d * s ^ (n + 1)) -
          (r * s) * (c * r ^ n + d * s ^ n) =
        c * ((r + s) * r ^ (n + 1) - (r * s) * r ^ n) +
          d * ((r + s) * s ^ (n + 1) - (r * s) * s ^ n) := by ring
      _ = c * r ^ (n + 2) + d * s ^ (n + 2) := by rw [hr, hs]

/-- The difference-of-powers form of Binet's identity, valid in arbitrary
commutative rings without dividing by `r-s`. It specializes to the
numerator of the classical Fibonacci and Lucas root formulas. -/
theorem W_root_difference (r s : R) (n : ℕ) :
    W (r + s) (r * s) 0 (r - s) n = r ^ n - s ^ n := by
  simpa [sub_eq_add_neg] using (W_roots r s (1 : R) (-1 : R) n)

end LeanFrontier.Horadam
