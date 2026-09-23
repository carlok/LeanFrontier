import LeanFrontier.NumberTheory.SylvesterSequence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The reciprocal series of Sylvester's sequence

The accepted Sylvester-sequence development proves the exact finite telescoping identity

`∑ i < n, 1 / S i = 1 - 1 / (S n - 1)`.

This module closes the classical Egyptian-fraction story by showing that the remainder tends
to zero, hence the full reciprocal series sums to one.

The only analytic input is that the strictly increasing natural sequence `S n` tends to
`+∞`, so `((S n : ℝ) - 1)⁻¹ → 0`.
-/

open scoped BigOperators Topology
open Filter

namespace LeanFrontier.Nat

/-- The reciprocals of Sylvester's sequence sum to one:

`1/2 + 1/3 + 1/7 + 1/43 + ⋯ = 1`.

This is the infinite-series completion of `sum_range_inv_sylvesterNumber`. -/
theorem hasSum_inv_sylvesterNumber :
    HasSum (fun n : ℕ => (1 : ℝ) / sylvesterNumber n) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hS_nat : Tendsto sylvesterNumber atTop atTop :=
      strictMono_sylvesterNumber.tendsto_atTop
    have hS_real : Tendsto (fun n : ℕ => (sylvesterNumber n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hS_nat
    have hden :
        Tendsto (fun n : ℕ => (sylvesterNumber n : ℝ) - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) hS_real
    have hinv :
        Tendsto ((fun r : ℝ => r⁻¹) ∘
          fun n : ℕ => (sylvesterNumber n : ℝ) - 1) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hden
    have hrem :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((sylvesterNumber n : ℝ) - 1))
          atTop (nhds 0) := by
      refine hinv.congr' ?_
      exact Filter.Eventually.of_forall fun n => by
        simp [Function.comp_apply, one_div]
    have hpartial :
        Tendsto
          (fun n : ℕ => (1 : ℝ) -
            1 / ((sylvesterNumber n : ℝ) - 1))
          atTop (nhds 1) := by
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hrem
    refine hpartial.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact (sum_range_inv_sylvesterNumber (K := ℝ) n).symm
  · intro n
    positivity

end LeanFrontier.Nat
