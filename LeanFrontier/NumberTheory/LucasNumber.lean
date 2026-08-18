import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lucas numbers

The Lucas numbers `2, 1, 3, 4, 7, 11, 18, ...` (OEIS A000032) satisfy the Fibonacci
recurrence with the starting values `2, 1`. They are the natural companion sequence of the
Fibonacci numbers: `L n = F (n - 1) + F (n + 1)`, the two sequences are entangled by
`F (2 * n) = F n * L n`, and `(L n)² - 5 (F n)² = 4 * (-1) ^ n`, which is why
`(L n + √5 F n) / 2 = φ ^ n`.

## Main definitions

* `LeanFrontier.Nat.lucas` - the Lucas numbers.

## Main statements

* `LeanFrontier.Nat.lucas_succ_eq_fib_add_fib` - the bridge `L (n + 1) = F n + F (n + 2)`,
  stated with a shifted index so that no natural subtraction appears.
* `LeanFrontier.Nat.fib_two_mul_eq_fib_mul_lucas` - the doubling identity
  `F (2 * n) = F n * L n`.
* `LeanFrontier.Nat.lucas_sq_eq_five_mul_fib_sq_add` - the Pell-type identity
  `(L n)² = 5 (F n)² + 4 * (-1) ^ n` over `ℤ`.
* `LeanFrontier.Nat.fib_succ_sq_sub_fib_mul_fib_add_two` - the Cassini-type identity
  `(F (n + 1))² - F n * F (n + 2) = (-1) ^ n` over `ℤ`, in the subtraction-free index form
  used to prove the Pell-type identity.
* `LeanFrontier.Nat.sum_range_lucas` - the partial sums: `∑ i < n, L i = L (n + 1) - 1`.

## Implementation notes

Everything is reduced through the bridge `lucas_succ_eq_fib_add_fib` to Fibonacci algebra:
the doubling identity is `Nat.fib_add` plus the bridge, and the Pell-type identity is four
times the Cassini-type identity after the substitution `L (n + 1) = 2 F n + F (n + 1)`. The
two signed identities are stated over `ℤ` since their right sides alternate in sign; both
proofs are `linear_combination` closures, with no case analysis on the parity of `n`.

Mathlib proves Cassini's identity for the bidirectional `Int.fib` in
`Mathlib.Data.Int.Fib.Lemmas`; the version here is about casts of `Nat.fib` with shifted
indices, which is the form the Lucas identities consume directly. This repository's accepted
Horadam module proves a Cassini-type identity for the general two-term recurrence over a
commutative ring; the Lucas numbers specialize it, but the fib-Lucas bridges proved here are
about the interaction of two specific sequences and are not instances of a single Horadam
statement.
-/

namespace LeanFrontier.Nat

/-- The Lucas numbers: the Fibonacci recurrence with starting values `2, 1`, giving
`2, 1, 3, 4, 7, 11, 18, ...`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- Lucas numbers are positive. -/
theorem lucas_pos : ∀ n, 0 < lucas n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have h1 := lucas_pos n
    rw [lucas_add_two]
    omega

/-- The bridge to the Fibonacci numbers: `L (n + 1) = F n + F (n + 2)`. The index is
shifted by one so that the statement needs no natural subtraction. -/
theorem lucas_succ_eq_fib_add_fib : ∀ n, lucas (n + 1) = Nat.fib n + Nat.fib (n + 2)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have h1 := lucas_succ_eq_fib_add_fib n
    have h2 : lucas (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) :=
      lucas_succ_eq_fib_add_fib (n + 1)
    have hrec : lucas (n + 3) = lucas (n + 1) + lucas (n + 2) := lucas_add_two (n + 1)
    have f1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have f2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have f3 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    show lucas (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    omega

/-- The doubling identity `F (2 * n) = F n * L n`: a Fibonacci number at an even index
factors through the Lucas number at half the index. -/
theorem fib_two_mul_eq_fib_mul_lucas (n : ℕ) :
    Nat.fib (2 * n) = Nat.fib n * lucas n := by
  rcases n with - | n
  · simp
  · have hadd := Nat.fib_add n (n + 1)
    have hidx : 2 * (n + 1) = n + (n + 1) + 1 := by ring
    rw [hidx, hadd, lucas_succ_eq_fib_add_fib]
    ring

/-- The Cassini-type identity in the subtraction-free index form:
`(F (n + 1))² - F n * F (n + 2) = (-1) ^ n` over `ℤ`. -/
theorem fib_succ_sq_sub_fib_mul_fib_add_two (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have f2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two
    have f3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      exact_mod_cast Nat.fib_add_two
    rw [f2] at ih
    rw [f3, f2]
    linear_combination (-1 : ℤ) * ih

/-- The Pell-type identity `(L n)² = 5 (F n)² + 4 * (-1) ^ n`: the pair `(L n, F n)` lies
on one of the two conics `x² - 5 y² = ± 4`, which is why `(L n + √5 F n) / 2 = φ ^ n`. -/
theorem lucas_sq_eq_five_mul_fib_sq_add (n : ℕ) :
    (lucas n : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 * (-1) ^ n := by
  rcases n with - | n
  · norm_num
  · have hlu : (lucas (n + 1) : ℤ) = Nat.fib n + Nat.fib (n + 2) := by
      exact_mod_cast lucas_succ_eq_fib_add_fib n
    have f2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two
    have hc := fib_succ_sq_sub_fib_mul_fib_add_two n
    rw [f2] at hc
    rw [hlu, f2]
    linear_combination (-4 : ℤ) * hc

/-- The partial sums of the Lucas numbers: `∑ i < n, L i = L (n + 1) - 1`. -/
theorem sum_range_lucas (n : ℕ) :
    ∑ i ∈ Finset.range n, lucas i = lucas (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, lucas_add_two]
    have := lucas_pos (n + 1)
    omega

/-- The classical instance `F 10 = F 5 * L 5`: `55 = 5 * 11`. -/
example : Nat.fib 10 = Nat.fib 5 * lucas 5 := by decide

end LeanFrontier.Nat
