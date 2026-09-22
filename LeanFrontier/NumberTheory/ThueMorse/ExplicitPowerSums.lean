import LeanFrontier.NumberTheory.PowerSums
import LeanFrontier.NumberTheory.ThueMorse
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

/-!
# Explicit Thue-Morse cube sums

Prouhet's theorem says that the two Thue-Morse parity classes in
`{0, ..., 2^(k+4)-1}` have the same cube sum.  Nicomachus's theorem evaluates
the cube sum of the whole interval.  Combining the two identifies each half
explicitly.

The shift by four makes the Prouhet hypothesis for cubes automatic and exposes
the factor of `2^4` needed to divide the total cube sum by two without using
natural-number division.
-/

namespace LeanFrontier.Nat

open Finset

/-- Each Thue-Morse parity class in `{0, ..., 2^(k+4)-1}` has cube sum
`32 * (2^k)^2 * (2^(k+4)-1)^2`.

This composes Prouhet's equal-power-sum partition with Nicomachus's closed form
for the total sum of cubes. -/
theorem sum_cubes_thueMorse_partition (k : ℕ) :
    (∑ n ∈ (range (2 ^ (k + 4))).filter (fun n => thueMorse n = false), n ^ 3)
          = 32 * (2 ^ k) ^ 2 * (2 ^ (k + 4) - 1) ^ 2
      ∧
    (∑ n ∈ (range (2 ^ (k + 4))).filter (fun n => thueMorse n = true), n ^ 3)
          = 32 * (2 ^ k) ^ 2 * (2 ^ (k + 4) - 1) ^ 2 := by
  have heq := sum_pow_eq_sum_pow_thueMorse (j := 3) (k := k + 4) (by omega)
  have hfilter :
      (range (2 ^ (k + 4))).filter (fun n => ¬ thueMorse n = false)
        = (range (2 ^ (k + 4))).filter (fun n => thueMorse n = true) :=
    Finset.filter_congr fun n _ => by simp
  have hsplit :
      (∑ n ∈ range (2 ^ (k + 4)), n ^ 3)
        = (∑ n ∈ (range (2 ^ (k + 4))).filter (fun n => thueMorse n = false), n ^ 3)
          + (∑ n ∈ (range (2 ^ (k + 4))).filter (fun n => thueMorse n = true), n ^ 3) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (range (2 ^ (k + 4))) (fun n => thueMorse n = false)]
    rw [hfilter]
  have hpow : 2 ^ (k + 4) = 16 * 2 ^ k := by
    rw [pow_add]
    norm_num
    ring
  have hsum :
      (∑ n ∈ range (2 ^ (k + 4)), n)
        = 8 * 2 ^ k * (2 ^ (k + 4) - 1) := by
    have hsum2 := Finset.sum_range_id_mul_two (2 ^ (k + 4))
    rw [hpow] at hsum2
    nlinarith
  have htotal :
      (∑ n ∈ range (2 ^ (k + 4)), n ^ 3)
        = 64 * (2 ^ k) ^ 2 * (2 ^ (k + 4) - 1) ^ 2 := by
    rw [← LeanFrontier.PowerSums.sum_cubes_eq_sum_sq, hsum]
    ring
  constructor <;> nlinarith

end LeanFrontier.Nat
