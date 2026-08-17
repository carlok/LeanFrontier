import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Horadam sequences and the general Cassini identity

A *Horadam sequence* is the solution `W` of the two term linear recurrence
`W (n + 2) = P * W (n + 1) - Q * W n` with prescribed initial values `W 0 = a` and `W 1 = b`,
over an arbitrary commutative ring. Taking `P = 1`, `Q = -1`, `a = 0`, `b = 1` gives the
Fibonacci numbers, `a = 2`, `b = P` gives the Lucas sequences of the second kind, and
`P = 2 * x`, `Q = 1` gives the Chebyshev recurrence.

The main result is the determinant, or Cassini, identity: the quantity
`W n * W (n + 2) - W (n + 1) ^ 2` is the initial value of that same quantity multiplied by
`Q ^ n`. Mathlib records this only for the Fibonacci numbers, where `Q = -1` makes the factor
alternate in sign.

## Main definitions

* `LeanFrontier.Horadam.W` - the Horadam sequence with parameters `P`, `Q` and initial values
  `a`, `b`.

## Main statements

* `LeanFrontier.Horadam.W_mul_W_add_two_sub_sq` - the general Cassini identity.
* `LeanFrontier.Horadam.W_add_initial` - the sequence is additive in its pair of initial
  values, so the solutions of one recurrence form a module.
* `LeanFrontier.Horadam.W_add_two` - the defining recurrence.

## Implementation notes

The Cassini identity is stated with the initial determinant `W 0 * W 2 - W 1 ^ 2` on the right
rather than its expansion `a * (P * b - Q * a) - b ^ 2`. The two agree by the defining
equations, and the unexpanded form makes the identity read as a statement about one quantity
being multiplied by `Q` at each step.

No bridge to `Nat.fib` or `Int.fib` is included. Such a bridge would restate Mathlib's existing
Fibonacci Cassini identity rather than add to it, and the specialization is immediate for a
consumer.

The two initial values are not restated as separate results: the equation compiler already
publishes them for `W`, so a public copy would duplicate an existing declaration. Consumers get
them from `simp [W]`.
-/

namespace LeanFrontier.Horadam

variable {R : Type*} [CommRing R] (P Q a b : R)

/-- The Horadam sequence: `W 0 = a`, `W 1 = b`, and `W (n + 2) = P * W (n + 1) - Q * W n`. -/
def W : ℕ → R
  | 0 => a
  | 1 => b
  | n + 2 => P * W (n + 1) - Q * W n

/-- The defining recurrence of a Horadam sequence. -/
theorem W_add_two (n : ℕ) :
    W P Q a b (n + 2) = P * W P Q a b (n + 1) - Q * W P Q a b n := by
  simp [W]

/-- One step of the determinant recurrence: the Cassini quantity is multiplied by `Q`. -/
private theorem det_succ (n : ℕ) :
    W P Q a b (n + 1) * W P Q a b (n + 3) - W P Q a b (n + 2) ^ 2
      = Q * (W P Q a b n * W P Q a b (n + 2) - W P Q a b (n + 1) ^ 2) := by
  have h3 : W P Q a b (n + 3) = P * W P Q a b (n + 2) - Q * W P Q a b (n + 1) := W_add_two P Q a b (n + 1)
  have h2 : W P Q a b (n + 2) = P * W P Q a b (n + 1) - Q * W P Q a b n := W_add_two P Q a b n
  linear_combination (W P Q a b (n + 1)) * h3 - (W P Q a b (n + 2)) * h2

/-- The **Cassini identity** for a Horadam sequence: the determinant
`W n * W (n + 2) - W (n + 1) ^ 2` is its initial value scaled by `Q ^ n`. For the Fibonacci
numbers `Q = -1`, which is why the classical statement alternates in sign. -/
theorem W_mul_W_add_two_sub_sq (n : ℕ) :
    W P Q a b n * W P Q a b (n + 2) - W P Q a b (n + 1) ^ 2
      = Q ^ n * (W P Q a b 0 * W P Q a b 2 - W P Q a b 1 ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show W P Q a b (n + 1) * W P Q a b (n + 3) - W P Q a b (n + 2) ^ 2
      = Q ^ (n + 1) * (W P Q a b 0 * W P Q a b 2 - W P Q a b 1 ^ 2)
    rw [det_succ, ih, pow_succ]
    ring

/-- A Horadam sequence is additive in its initial values: the solutions of one recurrence are
closed under addition, hence form a module over the coefficient ring. -/
theorem W_add_initial (a₁ a₂ b₁ b₂ : R) (n : ℕ) :
    W P Q (a₁ + a₂) (b₁ + b₂) n = W P Q a₁ b₁ n + W P Q a₂ b₂ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [W]
  | one => simp [W]
  | more n ih1 ih2 =>
    rw [W_add_two, W_add_two, W_add_two, ih1, ih2]
    ring

end LeanFrontier.Horadam
