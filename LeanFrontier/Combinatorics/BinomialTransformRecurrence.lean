import LeanFrontier.Combinatorics.BinomialTransform
import Mathlib.Tactic

/-!
# Weighted binomial transforms of second-order recurrences

A weighted binomial transform translates the characteristic polynomial of a
constant-coefficient linear recurrence. If a sequence satisfies
  f(n+2) = s*f(n+1) + t*f(n),
then its weight-a binomial transform satisfies
  g(n+2) = (s+2*a)*g(n+1) + (t-s*a-a^2)*g(n).
Thus the characteristic polynomial X^2-s*X-t is shifted by a.

The statement works over every commutative ring, including positive
characteristic, and reuses the weighted transform and its Pascal recurrence
already established in LeanFrontier.
-/

namespace LeanFrontier.Combinatorics

variable {R : Type*} [CommRing R]

private theorem binomialTransform_linear_combination
    (a s t : R) (f g : ℕ → R) (n : ℕ) :
    binomialTransform a (fun k => s * f k + t * g k) n =
      s * binomialTransform a f n + t * binomialTransform a g n := by
  unfold binomialTransform
  calc
    (∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * a ^ (n - k) * (s * f k + t * g k)) =
      ∑ k ∈ Finset.range (n + 1),
        (s * ((n.choose k : R) * a ^ (n - k) * f k) +
          t * ((n.choose k : R) * a ^ (n - k) * g k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = s * (∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * a ^ (n - k) * f k) +
          t * (∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * a ^ (n - k) * g k) := by
      rw [Finset.sum_add_distrib, ← mul_sum, ← mul_sum]

/-- A weighted binomial transform translates the characteristic polynomial of
a second-order linear recurrence by its weight. Over a commutative ring, the
transformed recurrence has characteristic polynomial
  X^2 - (s+2*a)*X - (t-s*a-a^2) = (X-a)^2 - s*(X-a) - t.
No nonzero or invertibility hypotheses on the coefficients are needed. -/
theorem binomialTransform_secondOrderRecurrence
    (a s t : R) (f : ℕ → R)
    (hf : ∀ n : ℕ, f (n + 2) = s * f (n + 1) + t * f n)
    (n : ℕ) :
    binomialTransform a f (n + 2) =
      (s + 2 * a) * binomialTransform a f (n + 1) +
        (t - s * a - a ^ 2) * binomialTransform a f n := by
  let G (k : ℕ) : R := binomialTransform a f k
  let S (k : ℕ) : R := binomialTransform a (fun j => f (j + 1)) k
  let T (k : ℕ) : R := binomialTransform a (fun j => f (j + 2)) k
  have h₁ : G (n + 1) = a * G n + S n :=
    binomialTransform_succ a f n
  have h₂ : G (n + 2) = a * G (n + 1) + S (n + 1) := by
    simpa [Nat.add_assoc] using (binomialTransform_succ a f (n + 1))
  have h₃ : S (n + 1) = a * S n + T n := by
    simpa [Nat.add_assoc] using
      (binomialTransform_succ a (fun j => f (j + 1)) n)
  have h₄ : T n = s * S n + t * G n := by
    have heq :
        T n = binomialTransform a (fun k => s * f (k + 1) + t * f k) n := by
      dsimp [T]
      apply congrArg (fun u : ℕ → R => binomialTransform a u n)
      funext k
      exact hf k
    rw [heq]
    exact binomialTransform_linear_combination a s t (fun k => f (k + 1)) f n
  have hs : S n = G (n + 1) - a * G n := by
    calc
      S n = (a * G n + S n) - a * G n := by ring
      _ = G (n + 1) - a * G n := by rw [← h₁]
  change G (n + 2) =
    (s + 2 * a) * G (n + 1) + (t - s * a - a ^ 2) * G n
  calc
    G (n + 2) = a * G (n + 1) + S (n + 1) := h₂
    _ = a * G (n + 1) + (a * S n + T n) := by rw [h₃]
    _ = a * G (n + 1) + (a * S n + (s * S n + t * G n)) := by rw [h₄]
    _ = (s + 2 * a) * G (n + 1) + (t - s * a - a ^ 2) * G n := by
      rw [hs]
      ring

end LeanFrontier.Combinatorics
