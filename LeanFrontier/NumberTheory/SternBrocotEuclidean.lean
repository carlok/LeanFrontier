import LeanFrontier.NumberTheory.SternBrocot
import Mathlib.Tactic

/-!
# Euclidean quotients from Stern-Brocot path runs

The accepted Stern-Brocot path API encodes a positive reduced rational by a Boolean path,
where `false` is a left move and `true` is a right move.  The classical bridge from this
tree to the Euclidean algorithm starts with a simple observation: an initial run of identical
moves records one Euclidean quotient.

If a run of `k` left moves is followed by a right move, then the denominator divided by the
numerator is exactly `k`.  Symmetrically, a run of `k` right moves followed by a left move
gives numerator divided by denominator equal to `k`.  When the path terminates instead of
changing direction, the quotient is `k + 1`; this is the endpoint convention behind the
usual ambiguity of finite continued fractions.

These statements provide the first arithmetic interface needed to identify Stern-Brocot
run lengths with Euclidean-algorithm / continued-fraction coefficients.
-/

namespace LeanFrontier.SternBrocot

private theorem pair_false_run (k : ℕ) (path : List Bool) :
    pair (List.replicate k false ++ path) =
      ((pair path).1, (pair path).2 + (pair path).1 * k) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [pair]
      rw [ih]
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem pair_true_run (k : ℕ) (path : List Bool) :
    pair (List.replicate k true ++ path) =
      ((pair path).1 + (pair path).2 * k, (pair path).2) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [pair]
      rw [ih]
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- An initial nonterminal Stern-Brocot run records one Euclidean quotient.

A run of `k` left moves followed by a right move gives denominator/numerator quotient `k`;
a run of `k` right moves followed by a left move gives numerator/denominator quotient `k`.
The theorem is stated uniformly in the run direction. -/
theorem initial_run_euclidean_quotient (dir : Bool) (k : ℕ) (path : List Bool) :
    let p := pair (List.replicate k dir ++ (Bool.not dir :: path))
    (if dir then p.1 / p.2 else p.2 / p.1) = k := by
  cases dir
  · simp only [Bool.not_false, if_false]
    rw [pair_false_run]
    simp only [pair, Prod.fst, Prod.snd]
    have hp := pair_positive_coprime path
    have hpos : 0 < (pair path).1 + (pair path).2 := by omega
    have hlt : (pair path).2 < (pair path).1 + (pair path).2 := by omega
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · simp only [Bool.not_true, if_true]
    rw [pair_true_run]
    simp only [pair, Prod.fst, Prod.snd]
    have hp := pair_positive_coprime path
    have hpos : 0 < (pair path).1 + (pair path).2 := by omega
    have hlt : (pair path).1 < (pair path).1 + (pair path).2 := by omega
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- A terminal Stern-Brocot run has Euclidean quotient one larger than its run length.

This is the endpoint case complementary to `initial_run_euclidean_quotient`: starting from the
root pair `(1,1)`, a path consisting entirely of `k` copies of one direction has quotient
`k + 1` in that direction. -/
theorem terminal_run_euclidean_quotient (dir : Bool) (k : ℕ) :
    let p := pair (List.replicate k dir)
    (if dir then p.1 / p.2 else p.2 / p.1) = k + 1 := by
  cases dir
  · simp only [if_false]
    have h := pair_false_run k []
    simp [pair] at h
    rw [h]
    simp
    omega
  · simp only [if_true]
    have h := pair_true_run k []
    simp [pair] at h
    rw [h]
    simp
    omega

end LeanFrontier.SternBrocot
