import LeanFrontier.Dynamics.LogisticConjugacy
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Dense periodic points for the full tent and logistic maps

The accepted topological conjugacy between the full tent map and the logistic map at parameter
four makes it enough to prove density for the tent map.

For each positive `n`, the grid points

`2 * k / (2^n - 1)`

that lie in `[0,1]` are periodic for the tent map.  The proof sends such a point through the
Ulam homeomorphism.  Its image is `sin (pi * k / (2^n - 1))^2`; after `n` logistic iterates
the angle has been multiplied by `2^n`, hence differs from the original angle by `k*pi`,
which does not change the square of the sine.

The mesh `2 / (2^n - 1)` tends to zero.  Choosing the grid point immediately below any point of
the unit interval therefore proves density.  The homeomorphic conjugacy then transports density
and periodicity to the logistic map.
-/

namespace LeanFrontier.Dynamics

open Real Set

private theorem logisticMap_iterate_sin_sq (n : ℕ) (x : ℝ) :
    logisticMap^[n] (sin (π * x) ^ 2) =
      sin (π * ((2 : ℝ) ^ n * x)) ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have h := (sin_sq_pi_mul (2 * ((2 : ℝ) ^ n * x))).symm
      convert h using 1 <;> ring_nf [pow_succ]

private theorem logisticMapIcc_iterate_val
    (n : ℕ) (x : Icc (0 : ℝ) 1) :
    (((logisticMapIcc^[n]) x : Icc (0 : ℝ) 1) : ℝ) =
      logisticMap^[n] (x : ℝ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

private theorem logistic_periodic_ulam_grid
    (n k : ℕ) (hn : 0 < n) :
    logisticMap^[n]
        (ulamMap (2 * (k : ℝ) / ((2 : ℝ) ^ n - 1))) =
      ulamMap (2 * (k : ℝ) / ((2 : ℝ) ^ n - 1)) := by
  have hpow : (1 : ℝ) < (2 : ℝ) ^ n :=
    one_lt_pow₀ (by norm_num) hn.ne'
  have hden : (2 : ℝ) ^ n - 1 ≠ 0 := by linarith
  rw [ulamMap, ulamMap]
  have hhalf :
      π * (2 * (k : ℝ) / ((2 : ℝ) ^ n - 1)) / 2 =
        π * ((k : ℝ) / ((2 : ℝ) ^ n - 1)) := by
    ring
  rw [hhalf, logisticMap_iterate_sin_sq]
  have hangle :
      π * ((2 : ℝ) ^ n * ((k : ℝ) / ((2 : ℝ) ^ n - 1))) =
        π * ((k : ℝ) / ((2 : ℝ) ^ n - 1)) + k * π := by
    field_simp [hden]
    ring
  rw [hangle, sin_add_nat_mul_pi, mul_pow]
  have hsign : (((-1 : ℝ) ^ k) ^ 2) = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  rw [hsign, one_mul]

private theorem tent_periodic_grid
    (n k : ℕ) (hn : 0 < n)
    (hmem : 2 * (k : ℝ) / ((2 : ℝ) ^ n - 1) ∈ Icc (0 : ℝ) 1) :
    Function.IsPeriodicPt tentMapIcc n
      ⟨2 * (k : ℝ) / ((2 : ℝ) ^ n - 1), hmem⟩ := by
  let x : Icc (0 : ℝ) 1 :=
    ⟨2 * (k : ℝ) / ((2 : ℝ) ^ n - 1), hmem⟩
  change (tentMapIcc^[n]) x = x
  apply ulamHomeomorph.injective
  calc
    ulamHomeomorph ((tentMapIcc^[n]) x) =
        (logisticMapIcc^[n]) (ulamHomeomorph x) :=
      (ulamHomeomorph_semiconj_tentMap_logisticMap.iterate_right n x)
    _ = ulamHomeomorph x := by
      apply Subtype.ext
      rw [logisticMapIcc_iterate_val]
      simpa only [ulamHomeomorph_apply, x] using
        logistic_periodic_ulam_grid n k hn

/-- The periodic points of the full tent map are dense in the closed unit interval. -/
theorem dense_periodicPts_tentMapIcc :
    Dense (Function.periodicPts tentMapIcc) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨n, hnlarge⟩ :=
    pow_unbounded_of_one_lt (2 / ε + 2) (by norm_num : (1 : ℝ) < 2)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have hdiv : 0 < (2 : ℝ) / ε := div_pos (by norm_num) hε
    norm_num at hnlarge
    linarith
  let q : ℝ := (2 : ℝ) ^ n - 1
  have hq : 0 < q := by
    dsimp [q]
    have hp : (1 : ℝ) < (2 : ℝ) ^ n :=
      one_lt_pow₀ (by norm_num) hn.ne'
    linarith
  have hqbig : (2 : ℝ) / ε < q := by
    dsimp [q]
    linarith
  have hmesh : (2 : ℝ) / q < ε := by
    have hmul : 2 < q * ε := (div_lt_iff₀ hε).mp hqbig
    rw [div_lt_iff₀ hq]
    nlinarith

  let k : ℕ := ⌊(x : ℝ) * q / 2⌋₊
  let yR : ℝ := 2 * (k : ℝ) / q
  have harg : 0 ≤ (x : ℝ) * q / 2 := by positivity
  have hk_lower : (k : ℝ) ≤ (x : ℝ) * q / 2 := by
    dsimp [k]
    exact Nat.floor_le harg
  have hk_upper : (x : ℝ) * q / 2 < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one _
  have hy_le_x : yR ≤ (x : ℝ) := by
    dsimp [yR]
    apply (div_le_iff₀ hq).2
    nlinarith
  have hy0 : 0 ≤ yR := by
    dsimp [yR]
    positivity
  have hy1 : yR ≤ 1 := hy_le_x.trans x.property.2
  have hgap : (x : ℝ) - yR < 2 / q := by
    have heq :
        (x : ℝ) - yR =
          ((x : ℝ) * q - 2 * (k : ℝ)) / q := by
      dsimp [yR]
      field_simp [hq.ne']
      ring
    rw [heq, div_lt_div_iff₀ hq hq]
    nlinarith
  let y : Icc (0 : ℝ) 1 := ⟨yR, hy0, hy1⟩
  have hdist : dist x y < ε := by
    change |(x : ℝ) - yR| < ε
    rw [abs_of_nonneg (sub_nonneg.mpr hy_le_x)]
    exact hgap.trans hmesh
  have hperiod : Function.IsPeriodicPt tentMapIcc n y := by
    dsimp [y, yR, q]
    exact tent_periodic_grid n k hn ⟨hy0, hy1⟩
  have hmem : y ∈ Function.periodicPts tentMapIcc :=
    Function.mk_mem_periodicPts hn hperiod
  refine ⟨y, ?_, hmem⟩
  simpa only [Metric.mem_ball'] using hdist

/-- The periodic points of the logistic map at parameter four are dense in the closed unit
interval. -/
theorem dense_periodicPts_logisticMapIcc :
    Dense (Function.periodicPts logisticMapIcc) := by
  have himage :
      Dense
        ((ulamHomeomorph : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1) ''
          Function.periodicPts tentMapIcc) :=
    ulamHomeomorph.surjective.denseRange.dense_image
      ulamHomeomorph.continuous dense_periodicPts_tentMapIcc
  exact himage.mono
    ulamHomeomorph_semiconj_tentMap_logisticMap.mapsTo_periodicPts.image_subset

end LeanFrontier.Dynamics
