import LeanFrontier.NumberTheory.SternDiatomic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci maxima on dyadic rows of Stern's diatomic sequence

On the dyadic row
`2^n ≤ k < 2^(n+1)`, Stern's diatomic sequence has maximum `fib (n + 2)`.

The proof uses a stronger adjacent-pair invariant. On row `n`, both entries of
`(fusc k, fusc (k + 1))` are at most `fib (n + 2)`, while their sum is at most
`fib (n + 3)`. The two child operations preserve those bounds because the next Fibonacci
number is the sum of the previous two.

Attainment is proved constructively: every row contains adjacent Stern pairs in both Fibonacci
orientations,
`(fib (n + 1), fib (n + 2))` and `(fib (n + 2), fib (n + 1))`.
-/

namespace LeanFrontier.SternDiatomic

private theorem fib_next_two (n : ℕ) :
    Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
  simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 1))

private theorem row_pair_bounds (n k : ℕ)
    (hlo : (2 : ℕ) ^ n ≤ k) (hhi : k < (2 : ℕ) ^ (n + 1)) :
    fusc k ≤ Nat.fib (n + 2) ∧
      fusc (k + 1) ≤ Nat.fib (n + 2) ∧
      fusc k + fusc (k + 1) ≤ Nat.fib (n + 3) := by
  induction n generalizing k with
  | zero =>
      have hk : k = 1 := by
        norm_num at hlo hhi ⊢
        omega
      subst k
      norm_num [fusc, Nat.fib]
  | succ n ih =>
      have hlo' : 2 * ((2 : ℕ) ^ n) ≤ k := by
        simpa [pow_succ, Nat.mul_comm] using hlo
      have hhi' : k < 2 * ((2 : ℕ) ^ (n + 1)) := by
        simpa [pow_succ, Nat.mul_comm, Nat.add_assoc] using hhi
      rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
      · subst k
        have hjlo : (2 : ℕ) ^ n ≤ j := by omega
        have hjhi : j < (2 : ℕ) ^ (n + 1) := by omega
        rcases ih j hjlo hjhi with ⟨ha, hb, hab⟩
        have hmono : Nat.fib (n + 2) ≤ Nat.fib (n + 3) :=
          Nat.fib_mono (by omega)
        have hfib : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 2))
        rw [fusc_two_mul, fusc_two_mul_add_one]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        constructor
        · exact ha.trans hmono
        constructor
        · exact hab
        · calc
            fusc j + (fusc j + fusc (j + 1)) ≤
                Nat.fib (n + 2) + Nat.fib (n + 3) :=
              Nat.add_le_add ha hab
            _ = Nat.fib (n + 4) := hfib.symm
      · subst k
        have hjlo : (2 : ℕ) ^ n ≤ j := by omega
        have hjhi : j < (2 : ℕ) ^ (n + 1) := by omega
        rcases ih j hjlo hjhi with ⟨ha, hb, hab⟩
        have hmono : Nat.fib (n + 2) ≤ Nat.fib (n + 3) :=
          Nat.fib_mono (by omega)
        have hfib : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 2))
        have hsucc : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
        rw [fusc_two_mul_add_one, hsucc, fusc_two_mul]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        constructor
        · exact hab
        constructor
        · exact hb.trans hmono
        · calc
            fusc j + (fusc (j + 1) + fusc (j + 1)) =
                (fusc j + fusc (j + 1)) + fusc (j + 1) := by
              simp [Nat.add_assoc]
            _ ≤ Nat.fib (n + 3) + Nat.fib (n + 2) :=
              Nat.add_le_add hab hb
            _ = Nat.fib (n + 4) := by
              rw [Nat.add_comm]
              exact hfib.symm

private theorem row_fibonacci_pairs (n : ℕ) :
    ∃ i j,
      (2 : ℕ) ^ n ≤ i ∧ i < (2 : ℕ) ^ (n + 1) ∧
      (2 : ℕ) ^ n ≤ j ∧ j < (2 : ℕ) ^ (n + 1) ∧
      fusc i = Nat.fib (n + 1) ∧
      fusc (i + 1) = Nat.fib (n + 2) ∧
      fusc j = Nat.fib (n + 2) ∧
      fusc (j + 1) = Nat.fib (n + 1) := by
  induction n with
  | zero =>
      refine ⟨1, 1, ?_⟩
      norm_num [fusc, Nat.fib]
  | succ n ih =>
      obtain ⟨i, j, hilo, hihi, hjlo, hjhi, hi0, hi1, hj0, hj1⟩ := ih
      have hrowLoI : (2 : ℕ) ^ (n + 1) ≤ 2 * j := by
        simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 hjlo
      have hrowHiI : 2 * j < (2 : ℕ) ^ (n + 2) := by
        have hdouble : 2 * j < 2 * ((2 : ℕ) ^ (n + 1)) :=
          Nat.mul_lt_mul_of_pos_left hjhi (by omega)
        simpa [pow_succ, Nat.mul_comm, Nat.add_assoc] using hdouble
      have hrowLoJ : (2 : ℕ) ^ (n + 1) ≤ 2 * i + 1 := by
        have hdouble : 2 * ((2 : ℕ) ^ n) ≤ 2 * i := Nat.mul_le_mul_left 2 hilo
        simpa [pow_succ, Nat.mul_comm] using Nat.le_trans hdouble (Nat.le_add_right _ _)
      have hrowHiJ : 2 * i + 1 < (2 : ℕ) ^ (n + 2) := by
        have hdouble : 2 * i < 2 * ((2 : ℕ) ^ (n + 1)) :=
          Nat.mul_lt_mul_of_pos_left hihi (by omega)
        have hodd : 2 * i + 1 < 2 * ((2 : ℕ) ^ (n + 1)) := by omega
        simpa [pow_succ, Nat.mul_comm, Nat.add_assoc] using hodd
      have hfib : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) :=
        fib_next_two n
      refine ⟨2 * j, 2 * i + 1, hrowLoI, hrowHiI, hrowLoJ, hrowHiJ, ?_, ?_, ?_, ?_⟩
      · rw [fusc_two_mul, hj0]
      · rw [fusc_two_mul_add_one, hj0, hj1]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfib.symm
      · rw [fusc_two_mul_add_one, hi0, hi1]
        simpa [Nat.add_assoc] using hfib.symm
      · have hsucc : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
        rw [hsucc, fusc_two_mul, hi1]

/-- On every dyadic row of Stern's diatomic sequence, the largest value is the corresponding
Fibonacci number. More precisely, every value with `2^n ≤ k < 2^(n+1)` is at most
`fib (n + 2)`, and some index in that same row attains equality. -/
theorem fib_is_max_on_dyadic_row (n : ℕ) :
    (∀ k : ℕ, ((2 : ℕ) ^ n ≤ k ∧ k < (2 : ℕ) ^ (n + 1)) →
      fusc k ≤ Nat.fib (n + 2)) ∧
    ∃ k : ℕ, (2 : ℕ) ^ n ≤ k ∧ k < (2 : ℕ) ^ (n + 1) ∧
      fusc k = Nat.fib (n + 2) := by
  constructor
  · intro k hk
    exact (row_pair_bounds n k hk.1 hk.2).1
  · obtain ⟨i, j, hilo, hihi, hjlo, hjhi, hi0, hi1, hj0, hj1⟩ :=
      row_fibonacci_pairs n
    exact ⟨j, hjlo, hjhi, hj0⟩

end LeanFrontier.SternDiatomic
