import LeanFrontier.NumberTheory.HoradamSequence
import Mathlib.Tactic

/-!
# Discrete Abel's identity for second-order recurrences

Two solutions `u`, `v` of the same variable-coefficient recurrence

  x (n+2) = p n * x (n+1) - q n * x n

have a *Casoratian*, or discrete Wronskian,

  D n = u n * v (n+1) - u (n+1) * v n.

Discrete Abel's identity is `D (n+1) = q n * D n`, and therefore
`D n = (∏ k < n, q k) * D 0`. Unlike an argument through ratios or a
fundamental matrix inverse, this holds in any commutative ring without
assuming the leading coefficient is invertible.

For constant coefficients it specializes to the two-solution Horadam
determinant law `D n = Q^n * (a*d-b*c)`.
-/

namespace LeanFrontier.LinearRecurrence

variable {R : Type*} [CommRing R]

/-- The Casoratian of two discrete sequences: the determinant of their
consecutive two-dimensional state vectors. -/
def casoratian (u v : ℕ → R) (n : ℕ) : R :=
  u n * v (n + 1) - u (n + 1) * v n

/-- **Discrete Abel identity, one-step form.** The Casoratian of two
solutions of a common variable-coefficient recurrence is multiplied by
`q n` at each step. -/
theorem casoratian_succ (p q u v : ℕ → R)
    (hu : ∀ n, u (n + 2) = p n * u (n + 1) - q n * u n)
    (hv : ∀ n, v (n + 2) = p n * v (n + 1) - q n * v n)
    (n : ℕ) :
    casoratian u v (n + 1) = q n * casoratian u v n := by
  unfold casoratian
  rw [hu n, hv n]
  ring

/-- **Discrete Abel–Liouville identity.** The Casoratian of two
solutions of the same second-order recurrence equals its initial
value multiplied by the product of the variable coefficients `q k`.
There are no nonvanishing, characteristic, or division hypotheses. -/
theorem casoratian_eq_prod (p q u v : ℕ → R)
    (hu : ∀ n, u (n + 2) = p n * u (n + 1) - q n * u n)
    (hv : ∀ n, v (n + 2) = p n * v (n + 1) - q n * v n)
    (n : ℕ) :
    casoratian u v n =
      (∏ k ∈ Finset.range n, q k) * casoratian u v 0 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc
      casoratian u v (n + 1) = q n * casoratian u v n :=
        casoratian_succ p q u v hu hv n
      _ = q n * ((∏ k ∈ Finset.range n, q k) * casoratian u v 0) := by rw [ih]
      _ = (∏ k ∈ Finset.range (n + 1), q k) * casoratian u v 0 := by
        rw [Finset.prod_range_succ]
        ring

/-- The two-solution Casoratian for the accepted Horadam recurrence
`W(n+2) = P*W(n+1) - Q*W(n)`. In particular, the determinant of
two independently initialized solutions is controlled exactly by
the determinant of their initial states. -/
theorem casoratian_horadam (P Q a b c d : R) (n : ℕ) :
    casoratian (LeanFrontier.Horadam.W P Q a b)
      (LeanFrontier.Horadam.W P Q c d) n =
        Q ^ n * (a * d - b * c) := by
  have hu (k : ℕ) :
      LeanFrontier.Horadam.W P Q a b (k + 2) =
        P * LeanFrontier.Horadam.W P Q a b (k + 1) -
          Q * LeanFrontier.Horadam.W P Q a b k :=
    LeanFrontier.Horadam.W_add_two P Q a b k
  have hv (k : ℕ) :
      LeanFrontier.Horadam.W P Q c d (k + 2) =
        P * LeanFrontier.Horadam.W P Q c d (k + 1) -
          Q * LeanFrontier.Horadam.W P Q c d k :=
    LeanFrontier.Horadam.W_add_two P Q c d k
  induction n with
  | zero =>
    simp [casoratian, LeanFrontier.Horadam.W]
  | succ n ih =>
    have hstep :=
      casoratian_succ (fun _ => P) (fun _ => Q)
        (LeanFrontier.Horadam.W P Q a b)
        (LeanFrontier.Horadam.W P Q c d) hu hv n
    rw [hstep, ih, pow_succ]
    ring

end LeanFrontier.LinearRecurrence
