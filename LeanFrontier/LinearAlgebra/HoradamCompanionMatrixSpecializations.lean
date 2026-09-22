import LeanFrontier.LinearAlgebra.HoradamCompanionMatrix
import LeanFrontier.LinearAlgebra.FibonacciMatrix
import LeanFrontier.NumberTheory.LucasNumber
import Mathlib.Tactic.NormNum

/-!
# Fibonacci and Lucas specializations of the Horadam companion matrix

This module connects the generic Horadam companion-matrix theory to LeanFrontier's existing
Fibonacci Q-matrix and Lucas-number developments.  The specialization `P = 1`, `Q = -1`
turns the Horadam recurrence into the Fibonacci recurrence, so the generic companion matrix is
exactly `LeanFrontier.Matrix.fibMatrix` and the fundamental Horadam sequence is `Nat.fib` after
casting to `ℤ`.  Combining these bridges with the generic trace theorem identifies traces of
positive Fibonacci Q-matrix powers with Lucas numbers.
-/

namespace LeanFrontier.Horadam

/-- The Horadam companion matrix for `P = 1`, `Q = -1` is LeanFrontier's Fibonacci Q-matrix. -/
theorem companionMatrix_fibonacci :
    companionMatrix (1 : ℤ) (-1) = LeanFrontier.Matrix.fibMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [companionMatrix, LeanFrontier.Matrix.fibMatrix]

/-- The fundamental Horadam sequence for `P = 1`, `Q = -1` is the Fibonacci sequence,
viewed in `ℤ`. -/
theorem W_fibonacci_eq_fib (n : ℕ) :
    W (1 : ℤ) (-1) 0 1 n = (Nat.fib n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [W]
  | one => simp [W]
  | more n ih0 ih1 =>
    have hf : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two
    rw [W_add_two, ih0, ih1, hf]
    ring

/-- The trace of a positive Fibonacci Q-matrix power is the corresponding Lucas number.
This is obtained by specializing the generic Horadam trace formula and then identifying the
fundamental Horadam sequence with Fibonacci numbers. -/
theorem trace_fibMatrix_pow_succ_eq_lucas (n : ℕ) :
    (LeanFrontier.Matrix.fibMatrix ^ (n + 1)).trace
      = (LeanFrontier.Nat.lucas (n + 1) : ℤ) := by
  rw [← companionMatrix_fibonacci, trace_companionMatrix_pow_succ_fundamental,
      W_fibonacci_eq_fib, W_fibonacci_eq_fib]
  have hlu : (LeanFrontier.Nat.lucas (n + 1) : ℤ)
      = Nat.fib n + Nat.fib (n + 2) := by
    exact_mod_cast LeanFrontier.Nat.lucas_succ_eq_fib_add_fib n
  rw [hlu]
  ring

end LeanFrontier.Horadam
