import LeanFrontier.Algebra.LinearRecurrence.Casoratian
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Discrete Lagrange–Green identity for forced second-order recurrences

The accepted discrete Abel identity describes the determinant (Casoratian)
of two solutions of a common homogeneous second-order recurrence.
For *forced* solutions

  u (n+2) = p n * u (n+1) - q n * u n + f n,
  v (n+2) = p n * v (n+1) - q n * v n + g n,

the Casoratian obeys the discrete Lagrange identity

  D (n+1) = q n * D n + u (n+1) * g n - f n * v (n+1).

Unrolling this identity gives a discrete Green/variation-of-constants
formula: the initial Casoratian propagates by a product, while each
forcing contribution propagates through the *subsequent* coefficients.

Both results hold in every commutative ring, including positive
characteristic and rings with zero divisors; no inverse is needed.
-/

namespace LeanFrontier.LinearRecurrence

variable {R : Type*} [CommRing R]

/-- Exact variation-of-constants formula for a first-order, nonautonomous
inhomogeneous scalar recurrence, with coefficients in any commutative ring.
The forcing at step `j` is multiplied by the coefficients of all later
steps, from `j+1` through `n-1`. -/
theorem affine_recurrence_eq_sum_prod (q h d : ℕ → R)
    (hd : ∀ n, d (n + 1) = q n * d n + h n) (n : ℕ) :
    d n = (∏ i ∈ Finset.range n, q i) * d 0 +
      ∑ j ∈ Finset.range n,
        (∏ i ∈ Finset.Ico (j + 1) n, q i) * h j := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hsum :
          q n * (∑ j ∈ Finset.range n,
            (∏ i ∈ Finset.Ico (j + 1) n, q i) * h j) + h n =
          ∑ j ∈ Finset.range (n + 1),
            (∏ i ∈ Finset.Ico (j + 1) (n + 1), q i) * h j := by
        rw [Finset.sum_range_succ]
        simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j + 1 ≤ n := by
          have hlt := Finset.mem_range.mp hj
          omega
        rw [Finset.prod_Ico_succ_top hjle]
        ring
      calc
        d (n + 1) = q n * d n + h n := hd n
        _ = q n * ((∏ i ∈ Finset.range n, q i) * d 0 +
              ∑ j ∈ Finset.range n,
                (∏ i ∈ Finset.Ico (j + 1) n, q i) * h j) + h n := by
                rw [ih]
        _ = (∏ i ∈ Finset.range (n + 1), q i) * d 0 +
              ∑ j ∈ Finset.range (n + 1),
                (∏ i ∈ Finset.Ico (j + 1) (n + 1), q i) * h j := by
                rw [Finset.prod_range_succ, ← hsum]
                ring

/-- **Discrete Lagrange identity.** If two solutions of the same
variable-coefficient second-order recurrence are driven by forcing terms
`f` and `g`, their Casoratian acquires the exact source term
`u (n+1) * g n - f n * v (n+1)`. This is the inhomogeneous
counterpart of `casoratian_succ`. -/
theorem casoratian_forced_succ (p q u v f g : ℕ → R)
    (hu : ∀ n, u (n + 2) =
      p n * u (n + 1) - q n * u n + f n)
    (hv : ∀ n, v (n + 2) =
      p n * v (n + 1) - q n * v n + g n)
    (n : ℕ) :
    casoratian u v (n + 1) =
      q n * casoratian u v n +
        (u (n + 1) * g n - f n * v (n + 1)) := by
  unfold casoratian
  rw [hu n, hv n]
  ring

/-- **Discrete Lagrange–Green formula.** The Casoratian of two forced
second-order solutions is the propagated initial determinant plus an
explicit weighted sum of all forcing contributions. The `j`th source
is weighted by `∏ (i : j+1 ≤ i < n), q i`; thus no division by any
recurrence coefficient is needed, including when `q i = 0`. -/
theorem casoratian_forced_eq_sum_prod (p q u v f g : ℕ → R)
    (hu : ∀ n, u (n + 2) =
      p n * u (n + 1) - q n * u n + f n)
    (hv : ∀ n, v (n + 2) =
      p n * v (n + 1) - q n * v n + g n)
    (n : ℕ) :
    casoratian u v n =
      (∏ i ∈ Finset.range n, q i) * casoratian u v 0 +
        ∑ j ∈ Finset.range n,
          (∏ i ∈ Finset.Ico (j + 1) n, q i) *
            (u (j + 1) * g j - f j * v (j + 1)) := by
  exact affine_recurrence_eq_sum_prod q
    (fun j => u (j + 1) * g j - f j * v (j + 1))
    (casoratian u v)
    (casoratian_forced_succ p q u v f g hu hv) n

end LeanFrontier.LinearRecurrence
