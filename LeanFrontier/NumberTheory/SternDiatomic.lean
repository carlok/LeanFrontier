import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring

/-!
# Stern's diatomic sequence

Stern's diatomic sequence, also called `fusc`, is `0, 1, 1, 2, 1, 3, 2, 3, 1, ...`, determined by
`fusc 0 = 0`, `fusc 1 = 1`, and

`fusc (2 * n) = fusc n`,  `fusc (2 * n + 1) = fusc n + fusc (n + 1)`.

Its consecutive pairs `(fusc n, fusc (n + 1))` run exactly once through all pairs of coprime
naturals, which is the arithmetic content of the Stern-Brocot tree: the fraction
`fusc n / fusc (n + 1)` enumerates the positive rationals, each in lowest terms.

This module defines the sequence and proves the two facts that make that enumeration work:
consecutive values are coprime, and every value after the first is positive.

## Main definitions

* `LeanFrontier.SternDiatomic.fusc` - the sequence.

## Main statements

* `LeanFrontier.SternDiatomic.coprime_fusc_fusc_succ` - consecutive values are coprime, so
  `fusc n / fusc (n + 1)` is always in lowest terms.
* `LeanFrontier.SternDiatomic.fusc_pos` - every value except the initial one is positive.
* `LeanFrontier.SternDiatomic.fusc_two_mul` and
  `LeanFrontier.SternDiatomic.fusc_two_mul_add_one` - the two defining equations.

## Implementation notes

The definition recurses on `n / 2`, so it is by well-founded rather than structural recursion,
and the two equations above are proved from it rather than holding by reduction. They are the
interface every later result uses; the raw form produced by the equation compiler, which is a
single case split on the parity of `n`, is not used again.

Coprimality is proved by strong induction with a parity split, and each case is exactly one of
Mathlib's `Nat.coprime_self_add_right` and `Nat.coprime_add_self_left`: halving turns a
neighbouring pair into a pair whose sum is one of its members. That is the same
mediant-and-determinant mechanism recorded for fractions in this repository's mediant and Ford
circle submissions, seen here on the numerators and denominators instead.
-/

namespace LeanFrontier.SternDiatomic

/-- Stern's diatomic sequence: `fusc 0 = 0`, `fusc 1 = 1`, `fusc (2 * n) = fusc n` and
`fusc (2 * n + 1) = fusc n + fusc (n + 1)`. -/
def fusc : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 2 = 0 then fusc ((n + 2) / 2)
      else fusc ((n + 2) / 2) + fusc ((n + 2) / 2 + 1)
decreasing_by
  · omega
  · omega
  · omega

/-- Halving an even index leaves the value unchanged. -/
theorem fusc_two_mul (n : ℕ) : fusc (2 * n) = fusc n := by
  rcases n with _ | k
  · rfl
  · have hm : 2 * (k + 1) = 2 * k + 2 := by ring
    have heven : (2 * k + 2) % 2 = 0 := by omega
    have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
    rw [hm, fusc, if_pos heven, hdiv]

/-- An odd index splits into the two neighbouring values at half the index. -/
theorem fusc_two_mul_add_one (n : ℕ) : fusc (2 * n + 1) = fusc n + fusc (n + 1) := by
  rcases n with _ | k
  · simp [fusc]
  · have hm : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    have hodd : ¬ ((2 * k + 1 + 2) % 2 = 0) := by omega
    have hdiv : (2 * k + 1 + 2) / 2 = k + 1 := by omega
    rw [hm, fusc, if_neg hodd, hdiv]

/-- Consecutive values of Stern's diatomic sequence are coprime, so the fraction
`fusc n / fusc (n + 1)` is always in lowest terms. -/
theorem coprime_fusc_fusc_succ (n : ℕ) : Nat.Coprime (fusc n) (fusc (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨k, hk⟩ := heven
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk, hk0]
        simp [fusc]
      · have hn : n = 2 * k := by omega
        rw [hn, fusc_two_mul, fusc_two_mul_add_one]
        exact Nat.coprime_self_add_right.mpr (ih k (by omega))
    · obtain ⟨k, hk⟩ := hodd
      have hsucc : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [hk, fusc_two_mul_add_one, hsucc, fusc_two_mul]
      exact Nat.coprime_add_self_left.mpr (ih k (by omega))

/-- Every value of Stern's diatomic sequence after the initial one is positive. -/
theorem fusc_pos {n : ℕ} (hn : n ≠ 0) : 0 < fusc n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨k, hk⟩ := heven
      have hkpos : 0 < k := by omega
      have hn2 : n = 2 * k := by omega
      rw [hn2, fusc_two_mul]
      exact ih k (by omega) (by omega)
    · obtain ⟨k, hk⟩ := hodd
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk, hk0]
        simp [fusc]
      · rw [hk, fusc_two_mul_add_one]
        have := ih k (by omega) (by omega)
        omega

end LeanFrontier.SternDiatomic
