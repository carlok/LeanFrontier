import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Weighted binomial transforms and their composition law

For a commutative ring `R`, the weight-`a` binomial transform sends a
sequence `f : ℕ → R` to

`(Bₐ f)(n) = ∑ k ≤ n, (n.choose k : R) * a ^ (n-k) * f(k)`.

The main result is the weighted binomial inversion/group law
`Bₐ (B_b f) = B_(a+b) f`. In particular `B_(-a)` is the inverse of
`Bₐ`. This is a reusable form of binomial inversion: the ordinary
binomial transform corresponds to `a = 1`.

Mathlib already has binomial sum identities and Gregory–Newton formulas
for forward differences. This module uses the existing Pascal-row sum
recurrence instead of defining another finite-difference operator.
-/

namespace LeanFrontier.Combinatorics

open Finset

variable {R : Type*} [CommRing R]

/-- The weighted binomial transform of a sequence over a commutative ring. -/
def binomialTransform (a : R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n + 1), (n.choose k : R) * a ^ (n - k) * f k

/-- The Pascal recurrence for a weighted binomial transform. The right
summand is the transform of the shifted input sequence. -/
theorem binomialTransform_succ (a : R) (f : ℕ → R) (n : ℕ) :
    binomialTransform a f (n + 1) =
      a * binomialTransform a f n +
        binomialTransform a (fun k => f (k + 1)) n := by
  have h := Finset.sum_choose_succ_mul
    (R := R) (fun i j => a ^ j * f i) n
  change
    (∑ i ∈ range (n + 2), ((n + 1).choose i : R) *
      a ^ (n + 1 - i) * f i) =
      a * (∑ i ∈ range (n + 1), (n.choose i : R) *
        a ^ (n - i) * f i) +
      ∑ i ∈ range (n + 1), (n.choose i : R) *
        a ^ (n - i) * f (i + 1)
  calc
    _ = (∑ i ∈ range (n + 1), (n.choose i : R) *
          a ^ (n + 1 - i) * f i) +
        ∑ i ∈ range (n + 1), (n.choose i : R) *
          a ^ (n - i) * f (i + 1) := by
        simpa only [mul_assoc] using h
    _ = _ := by
      congr 1
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := Finset.mem_range_succ_iff.mp hk
      have hsub : n + 1 - k = (n - k) + 1 := by omega
      rw [hsub, pow_succ]
      ring

private theorem binomialTransform_add
    (a : R) (f g : ℕ → R) (n : ℕ) :
    binomialTransform a (fun k => f k + g k) n =
      binomialTransform a f n + binomialTransform a g n := by
  simp only [binomialTransform, mul_add, Finset.sum_add_distrib]

private theorem binomialTransform_const_mul
    (a b : R) (f : ℕ → R) (n : ℕ) :
    binomialTransform a (fun k => b * f k) n =
      b * binomialTransform a f n := by
  unfold binomialTransform
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- **Composition law for weighted binomial transforms.** These transforms
form an action of the additive monoid of the coefficient ring on sequences:
transforming with `b` and then `a` is the same as transforming once with
`a + b`. -/
theorem binomialTransform_comp (a b : R) (f : ℕ → R) (n : ℕ) :
    binomialTransform a (binomialTransform b f) n =
      binomialTransform (a + b) f n := by
  induction n generalizing f with
  | zero =>
      simp [binomialTransform]
  | succ n ih =>
      calc
        binomialTransform a (binomialTransform b f) (n + 1) =
            a * binomialTransform a (binomialTransform b f) n +
              binomialTransform a
                (fun k => binomialTransform b f (k + 1)) n :=
          binomialTransform_succ a (binomialTransform b f) n
        _ = a * binomialTransform a (binomialTransform b f) n +
              binomialTransform a
                (fun k => b * binomialTransform b f k +
                  binomialTransform b (fun j => f (j + 1)) k) n := by
          congr 1
          apply congrArg (fun g : ℕ → R => binomialTransform a g n)
          funext k
          exact binomialTransform_succ b f k
        _ = a * binomialTransform a (binomialTransform b f) n +
              (b * binomialTransform a (binomialTransform b f) n +
                binomialTransform a
                  (binomialTransform b (fun j => f (j + 1))) n) := by
          rw [binomialTransform_add, binomialTransform_const_mul]
        _ = (a + b) * binomialTransform (a + b) f n +
              binomialTransform (a + b) (fun j => f (j + 1)) n := by
          rw [ih f, ih (fun j => f (j + 1))]
          ring
        _ = binomialTransform (a + b) f (n + 1) :=
          (binomialTransform_succ (a + b) f n).symm

/-- Transforming with weight zero is the identity. -/
theorem binomialTransform_zero (f : ℕ → R) (n : ℕ) :
    binomialTransform (0 : R) f n = f n := by
  induction n generalizing f with
  | zero =>
      simp [binomialTransform]
  | succ n ih =>
      rw [binomialTransform_succ]
      simpa using ih (fun k => f (k + 1))

/-- **Weighted binomial inversion.** The binomial transform of weight `-a`
undoes the binomial transform of weight `a`, for every sequence over any
commutative ring. -/
theorem binomialTransform_inverse (a : R) (f : ℕ → R) (n : ℕ) :
    binomialTransform (-a) (binomialTransform a f) n = f n := by
  rw [binomialTransform_comp, neg_add_cancel, binomialTransform_zero]

end LeanFrontier.Combinatorics
