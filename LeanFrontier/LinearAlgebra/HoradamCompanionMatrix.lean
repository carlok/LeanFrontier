import LeanFrontier.NumberTheory.HoradamSequence
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Companion matrices for Horadam recurrences

This module connects the general Horadam recurrence

`W (n + 2) = P * W (n + 1) - Q * W n`

to Mathlib's `LinearRecurrence` abstraction and to the explicit companion matrix

`!![P, -Q; 1, 0]`.

The companion matrix advances the state vector `![W (n + 1), W n]`; its powers advance
arbitrary initial states through the whole recurrence. For the fundamental sequence
`U n = W P Q 0 1 n`, `companionPowerFormula P Q n` is the explicit matrix

`!![U (n+2), -Q * U (n+1); U (n+1), -Q * U n]`,

and `companionMatrix_pow_succ` identifies it with `A^(n+1)`.

The companion matrix has determinant `Q`, trace `P`, and the same characteristic polynomial
as the corresponding order-two scalar recurrence. Positive powers have trace
`U (n+2) - Q * U n` and determinant `Q^(n+1)`, which also gives their characteristic
polynomial explicitly.
-/

namespace LeanFrontier.Horadam

open Polynomial

variable {R : Type*} [CommRing R]

/-- The order-two `LinearRecurrence` underlying the Horadam recurrence with parameters `P, Q`.
Its coefficients are `[-Q, P]`, so a solution satisfies
`u (n + 2) = P * u (n + 1) - Q * u n`. -/
def recurrence (P Q : R) : LinearRecurrence R where
  order := 2
  coeffs := ![-Q, P]

/-- Every Horadam sequence is a solution of its associated Mathlib `LinearRecurrence`. -/
theorem W_isSolution_recurrence (P Q a b : R) :
    (recurrence P Q).IsSolution (W P Q a b) := by
  rw [recurrence]
  intro n
  rw [W_add_two]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']
  ring

/-- The characteristic polynomial of the Horadam recurrence is `X² - P X + Q`. -/
theorem recurrence_charPoly (P Q : R) :
    (recurrence P Q).charPoly = X ^ 2 - C P * X + C Q := by
  rw [recurrence, LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← Polynomial.smul_X_eq_monomial]
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  ring

/-- The companion matrix of `x² - P x + Q`. -/
def companionMatrix (P Q : R) : Matrix (Fin 2) (Fin 2) R :=
  !![P, -Q; 1, 0]

/-- One multiplication by the companion matrix advances a recurrence state by one step. -/
theorem companionMatrix_mulVec (P Q x y : R) :
    Matrix.mulVec (companionMatrix P Q) ![x, y] = ![P * x - Q * y, x] := by
  ext i
  fin_cases i <;> simp [companionMatrix, Matrix.mulVec] <;> ring

/-- The companion matrix advances the Horadam state vector by one recurrence step. -/
theorem companionMatrix_mulVec_W_state (P Q a b : R) (n : ℕ) :
    Matrix.mulVec (companionMatrix P Q) ![W P Q a b (n + 1), W P Q a b n]
      = ![W P Q a b (n + 2), W P Q a b (n + 1)] := by
  rw [companionMatrix_mulVec, W_add_two]

/-- The `n`th power of the companion matrix sends the initial state `![b, a]` to the
`n`th Horadam state `![W (n+1), W n]`. This is the state-space realization of the recurrence
for arbitrary initial conditions. -/
theorem companionMatrix_pow_mulVec_initial (P Q a b : R) (n : ℕ) :
    Matrix.mulVec (companionMatrix P Q ^ n) ![b, a]
      = ![W P Q a b (n + 1), W P Q a b n] := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, companionMatrix_mulVec, W_add_two]

/-- The explicit matrix built from the fundamental Horadam sequence `U n = W P Q 0 1 n`
that represents the `(n+1)`st power of the companion matrix. -/
def companionPowerFormula (P Q : R) (n : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  !![W P Q 0 1 (n + 2), -Q * W P Q 0 1 (n + 1);
     W P Q 0 1 (n + 1), -Q * W P Q 0 1 n]

/-- Explicit powers of the Horadam companion matrix in terms of the fundamental sequence:
`A^(n+1) = companionPowerFormula P Q n`. -/
theorem companionMatrix_pow_succ (P Q : R) (n : ℕ) :
    companionMatrix P Q ^ (n + 1) = companionPowerFormula P Q n := by
  induction n with
  | zero =>
    rw [pow_one, companionMatrix, companionPowerFormula]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W]
  | succ n ih =>
    rw [pow_succ, ih, companionPowerFormula, companionMatrix, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [companionPowerFormula, W_add_two] <;> ring

/-- The determinant of the Horadam companion matrix is `Q`. -/
@[simp] theorem det_companionMatrix (P Q : R) :
    (companionMatrix P Q).det = Q := by
  rw [companionMatrix, Matrix.det_fin_two_of]
  ring

/-- Powers of the companion matrix have determinant `Q^n`. -/
theorem det_companionMatrix_pow (P Q : R) (n : ℕ) :
    (companionMatrix P Q ^ n).det = Q ^ n := by
  rw [Matrix.det_pow, det_companionMatrix]

/-- The trace of the Horadam companion matrix is `P`. -/
@[simp] theorem trace_companionMatrix (P Q : R) :
    (companionMatrix P Q).trace = P := by
  rw [companionMatrix, Matrix.trace_fin_two_of]
  simp

/-- The trace of a positive companion-matrix power is the diagonal combination of the
fundamental Horadam sequence appearing in the explicit power formula. -/
theorem trace_companionMatrix_pow_succ_fundamental (P Q : R) (n : ℕ) :
    (companionMatrix P Q ^ (n + 1)).trace
      = W P Q 0 1 (n + 2) - Q * W P Q 0 1 n := by
  rw [companionMatrix_pow_succ, companionPowerFormula, Matrix.trace_fin_two_of]
  ring

/-- The companion matrix and the scalar recurrence have the same characteristic polynomial. -/
theorem charpoly_companionMatrix [Nontrivial R] (P Q : R) :
    (companionMatrix P Q).charpoly = (recurrence P Q).charPoly := by
  rw [Matrix.charpoly_fin_two, trace_companionMatrix, det_companionMatrix, recurrence_charPoly]

/-- The polynomial determined by the fundamental-sequence trace and determinant of the
`(n+1)`st companion-matrix power. -/
noncomputable def companionPowerCharPoly (P Q : R) (n : ℕ) : Polynomial R :=
  X ^ 2 - C (W P Q 0 1 (n + 2) - Q * W P Q 0 1 n) * X + C (Q ^ (n + 1))

/-- The characteristic polynomial of a positive companion-matrix power is the polynomial
specified by its fundamental Horadam trace and determinant. -/
theorem charpoly_companionMatrix_pow_succ_fundamental [Nontrivial R] (P Q : R) (n : ℕ) :
    (companionMatrix P Q ^ (n + 1)).charpoly = companionPowerCharPoly P Q n := by
  rw [Matrix.charpoly_fin_two, trace_companionMatrix_pow_succ_fundamental,
      det_companionMatrix_pow, companionPowerCharPoly]

end LeanFrontier.Horadam
