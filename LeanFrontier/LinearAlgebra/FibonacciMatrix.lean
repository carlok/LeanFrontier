import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The Fibonacci Q-matrix

The Q-matrix `!![1, 1; 1, 0]` represents the Fibonacci recurrence as a linear map: its
powers are exactly the Fibonacci numbers,

`Q ^ (n + 1) = !![F (n + 2), F (n + 1); F (n + 1), F n]`.

This one identity is the linear-algebraic engine of Fibonacci theory: taking determinants
gives Cassini's identity (via `det_fibMatrix_pow` and `Matrix.det_fin_two`), taking traces
gives the Lucas numbers `F n + F (n + 2)`, and multiplying powers gives the addition
formulas. It also places `Q` in `GL₂(ℤ)`, since its determinant is the unit `-1`.

## Main definitions

* `LeanFrontier.Matrix.fibMatrix` - the Q-matrix, over `ℤ`.

## Main statements

* `LeanFrontier.Matrix.fibMatrix_pow_succ` - the power formula
  `Q ^ (n + 1) = !![F (n + 2), F (n + 1); F (n + 1), F n]`.
* `LeanFrontier.Matrix.det_fibMatrix` and `LeanFrontier.Matrix.det_fibMatrix_pow` - the
  determinants `det Q = -1` and `det (Q ^ n) = (-1) ^ n`.
* `LeanFrontier.Matrix.trace_fibMatrix_pow_succ` - the trace
  `trace (Q ^ (n + 1)) = F n + F (n + 2)`, which is the Lucas number `L (n + 1)`.
* `LeanFrontier.Matrix.isUnit_fibMatrix` - `Q` is a unit of the matrix ring, i.e. an
  element of `GL₂(ℤ)`.

## Implementation notes

The matrix lives over `ℤ` rather than `ℕ` so that the determinant identities are stated
without truncation and the unit group is the interesting one. The power formula is one
induction whose step is concrete `2 × 2` multiplication via `Matrix.mul_fin_two` followed by
entrywise Fibonacci recurrences; the determinant and trace statements are then rewrites.

Cassini's identity, the scalar consequence of `det_fibMatrix_pow`, is deliberately not
restated: Mathlib already proves it for the bidirectional `Int.fib` in
`Mathlib.Data.Int.Fib.Lemmas`.
-/

namespace LeanFrontier.Matrix

/-- The Fibonacci Q-matrix `!![1, 1; 1, 0]` over `ℤ`: the companion matrix of
`x ^ 2 - x - 1`, whose powers generate the Fibonacci numbers. -/
def fibMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- The Q-matrix power formula: `Q ^ (n + 1) = !![F (n + 2), F (n + 1); F (n + 1), F n]`. -/
theorem fibMatrix_pow_succ (n : ℕ) :
    fibMatrix ^ (n + 1)
      = !![(Nat.fib (n + 2) : ℤ), Nat.fib (n + 1); Nat.fib (n + 1), Nat.fib n] := by
  induction n with
  | zero =>
    rw [pow_one, fibMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ n ih =>
    show fibMatrix ^ (n + 2)
      = !![(Nat.fib (n + 3) : ℤ), Nat.fib (n + 2); Nat.fib (n + 2), Nat.fib (n + 1)]
    have key2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two
    have key3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      exact_mod_cast Nat.fib_add_two
    rw [pow_succ, ih, fibMatrix, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith [key2, key3]

/-- The Q-matrix has determinant `-1`. -/
@[simp] theorem det_fibMatrix : fibMatrix.det = -1 := by
  rw [fibMatrix, Matrix.det_fin_two_of]
  norm_num

/-- The powers of the Q-matrix alternate in determinant: `det (Q ^ n) = (-1) ^ n`.
Expanding the left side with `fibMatrix_pow_succ` and `Matrix.det_fin_two` recovers
Cassini's identity. -/
theorem det_fibMatrix_pow (n : ℕ) : (fibMatrix ^ n).det = (-1) ^ n := by
  rw [Matrix.det_pow, det_fibMatrix]

/-- The trace of `Q ^ (n + 1)` is `F n + F (n + 2)`, the Lucas number `L (n + 1)`. -/
theorem trace_fibMatrix_pow_succ (n : ℕ) :
    (fibMatrix ^ (n + 1)).trace = Nat.fib n + Nat.fib (n + 2) := by
  rw [fibMatrix_pow_succ, Matrix.trace_fin_two_of]
  ring

/-- The Q-matrix is a unit of the matrix ring: it lies in `GL₂(ℤ)`, since its determinant
is the unit `-1`. -/
theorem isUnit_fibMatrix : IsUnit fibMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, det_fibMatrix]
  exact isUnit_one.neg

/-- The `n = 4` instance of the power formula: `Q ^ 5 = !![8, 5; 5, 3]`. -/
example : fibMatrix ^ 5 = !![8, 5; 5, 3] := by
  rw [fibMatrix_pow_succ]
  norm_num [show Nat.fib 6 = 8 from rfl, show Nat.fib 5 = 5 from rfl,
    show Nat.fib 4 = 3 from rfl]

end LeanFrontier.Matrix
