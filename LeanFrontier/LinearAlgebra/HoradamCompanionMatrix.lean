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
`U n = W P Q 0 1 n`, its powers are explicitly

`A^(n+1) = !![U (n+2), -Q * U (n+1); U (n+1), -Q * U n]`.

Its determinant is `Q`, its trace is `P`, and its characteristic polynomial agrees with the
characteristic polynomial of the corresponding order-two linear recurrence.
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
  ring

/-- The companion matrix of `x² - P x + Q`. -/
def companionMatrix (P Q : R) : Matrix (Fin 2) (Fin 2) R :=
  !![P, -Q; 1, 0]

/-- One multiplication by the companion matrix advances a recurrence state by one step. -/
theorem companionMatrix_mulVec (P Q x y : R) :
    companionMatrix P Q *ᵥ ![x, y] = ![P * x - Q * y, x] := by
  ext i
  fin_cases i <;> simp [companionMatrix, Matrix.mulVec] <;> ring

/-- The companion matrix advances the Horadam state vector by one recurrence step. -/
theorem companionMatrix_mulVec_W_state (P Q a b : R) (n : ℕ) :
    companionMatrix P Q *ᵥ ![W P Q a b (n + 1), W P Q a b n]
      = ![W P Q a b (n + 2), W P Q a b (n + 1)] := by
  rw [companionMatrix_mulVec, W_add_two]

/-- The `n`th power of the companion matrix sends the initial state `![b, a]` to the
`n`th Horadam state `![W (n+1), W n]`. This is the state-space realization of the recurrence
for arbitrary initial conditions. -/
theorem companionMatrix_pow_mulVec_initial (P Q a b : R) (n : ℕ) :
    companionMatrix P Q ^ n *ᵥ ![b, a]
      = ![W P Q a b (n + 1), W P Q a b n] := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, companionMatrix_mulVec, W_add_two]

/-- Explicit powers of the Horadam companion matrix in terms of the fundamental sequence
`U n = W P Q 0 1 n`:
`A^(n+1) = !![U (n+2), -Q U (n+1); U (n+1), -Q U n]`. -/
theorem companionMatrix_pow_succ (P Q : R) (n : ℕ) :
    companionMatrix P Q ^ (n + 1) =
      !![W P Q 0 1 (n + 2), -Q * W P Q 0 1 (n + 1);
         W P Q 0 1 (n + 1), -Q * W P Q 0 1 n] := by
  induction n with
  | zero =>
    rw [pow_one, companionMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W]
  | succ n ih =>
    show companionMatrix P Q ^ (n + 2) =
      !![W P Q 0 1 (n + 3), -Q * W P Q 0 1 (n + 2);
         W P Q 0 1 (n + 2), -Q * W P Q 0 1 (n + 1)]
    rw [pow_succ, ih, companionMatrix, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W_add_two] <;> ring

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

/-- The companion matrix and the scalar recurrence have the same characteristic polynomial. -/
theorem charpoly_companionMatrix [Nontrivial R] (P Q : R) :
    (companionMatrix P Q).charpoly = (recurrence P Q).charPoly := by
  rw [Matrix.charpoly_fin_two, trace_companionMatrix, det_companionMatrix, recurrence_charPoly]

end LeanFrontier.Horadam
