import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Translation rigidity of polynomials

Over a characteristic-zero integral domain, a polynomial invariant under one
nonzero additive translation is constant.
-/

open scoped Polynomial
open Polynomial

namespace LeanFrontier.Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- A polynomial over a characteristic-zero integral domain with a nonzero
additive period is constant. -/
theorem eq_C_eval_zero_of_comp_X_add_C_eq_self {p : R[X]} {a : R} (ha : a ≠ 0)
    (hperiod : p.comp (X + C a) = p) :
    p = C (p.eval 0) := by
  have htaylor : taylor a p = p := hperiod
  have htaylor_nat : ∀ n : ℕ, taylor ((n : R) * a) p = p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          taylor ((n.succ : R) * a) p = taylor ((n : R) * a + a) p := by
            congr 2
            push_cast
            ring
          _ = taylor ((n : R) * a) (taylor a p) := (taylor_taylor p _ _).symm
          _ = p := by rw [htaylor, ih]
  let q : R[X] := p - C (p.eval 0)
  have hinjective : Function.Injective (fun n : ℕ ↦ (n : R) * a) := by
    intro m n hmn
    apply Nat.cast_injective (R := R)
    exact mul_right_cancel₀ ha hmn
  have hroot : Set.range (fun n : ℕ ↦ (n : R) * a) ⊆ {x | q.IsRoot x} := by
    rintro x ⟨n, rfl⟩
    have heval : p.eval ((n : R) * a) = p.eval 0 := by
      have := congrArg (fun f : R[X] ↦ f.eval 0) (htaylor_nat n)
      simpa [taylor_eval] using this
    simp [q, IsRoot, heval]
  have hinfinite : Set.Infinite {x | q.IsRoot x} :=
    (Set.infinite_range_of_injective hinjective).mono hroot
  have hq : q = 0 := q.eq_zero_of_infinite_isRoot hinfinite
  exact sub_eq_zero.mp hq

end LeanFrontier.Polynomial
