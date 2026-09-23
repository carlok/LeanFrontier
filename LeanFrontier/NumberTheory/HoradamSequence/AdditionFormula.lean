import LeanFrontier.LinearAlgebra.HoradamCompanionMatrix
import Mathlib.Tactic

/-!
# Addition formula for Horadam sequences

For fixed recurrence parameters `P, Q`, write

`U n = W P Q 0 1 n`

for the fundamental Horadam sequence.  The accepted companion-matrix development
shows that the matrix

`A = [[P, -Q], [1, 0]]`

advances arbitrary Horadam state vectors and gives an explicit formula for
`A^(m+1)` in terms of `U`.

This module extracts the corresponding scalar addition law

`W (m+n+1) = U (m+1) * W (n+1) - Q * U m * W n`.

It is the general second-order recurrence analogue of the familiar Fibonacci
addition formulas.  The shifted indexing avoids natural-number subtraction and
works uniformly over an arbitrary commutative ring.
-/

namespace LeanFrontier.Horadam

variable {R : Type*} [CommRing R]

/-- **Horadam addition formula.**

Let `U k = W P Q 0 1 k` be the fundamental sequence for the recurrence
`W (n+2) = P W (n+1) - Q W n`.  Then every solution with initial data
`a, b` satisfies

`W (m+n+1) = U (m+1) W (n+1) - Q U m W n`.

The proof factors the state evolution at time `m+n+1` into `n` steps followed
by `m+1` steps, then evaluates the latter power using the accepted explicit
companion-matrix formula. -/
theorem W_addition_formula (P Q a b : R) (m n : ℕ) :
    W P Q a b (m + n + 1) =
      W P Q 0 1 (m + 1) * W P Q a b (n + 1) -
        Q * W P Q 0 1 m * W P Q a b n := by
  have hidx : m + n + 1 = (m + 1) + n := by omega
  have hstate := companionMatrix_pow_mulVec_initial P Q a b (m + n + 1)
  rw [hidx, pow_add, ← Matrix.mulVec_mulVec,
      companionMatrix_pow_mulVec_initial P Q a b n,
      companionMatrix_pow_succ P Q m] at hstate
  have hcoord :=
    congrArg (fun v : Fin 2 → R => v (1 : Fin 2)) hstate
  simpa [companionPowerFormula, Matrix.mulVec, Fin.sum_univ_two] using hcoord

end LeanFrontier.Horadam
