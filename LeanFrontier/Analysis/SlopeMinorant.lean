import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The greatest minorant with bounded increments

Fix two nonnegative rates `a` and `b`. Call a sequence `v : ℕ → ℝ` *step bounded* when it
rises by at most `a` and falls by at most `b` at every step, that is
`v (i + 1) ≤ v i + a` and `v i ≤ v (i + 1) + b`. Fix also a *ceiling* `L : ℕ → ℝ` that has
to be respected at the indices of a nonempty finite set `s`.

This file constructs the greatest step bounded sequence lying below that ceiling and
proves that it deserves the name. The construction is a one sided inf convolution: reading
`slack a b i j` as the cost of the arc from `j` to `i`, the value at `i` is the cheapest
way to reach `i` from a constrained index,
`minorant a b L s hs i = ⨅ j ∈ s, (L j + slack a b i j)`.

The two rates are kept apart on purpose. With `a = b` the step bound is the discrete
Lipschitz condition and `slack a a i j` is `a` times the distance from `i` to `j`, so the
construction is the largest Lipschitz sequence below a partial ceiling. Mathlib has the
McShane-Whitney extension of a function already known to be Lipschitz on a subset,
`LipschitzOnWith.extend_real`; the object here is different, since the ceiling is an
arbitrary function and the conclusion is a greatest element rather than an extension.

## Main definitions

* `LeanFrontier.BoundedSlope.slack` - the asymmetric cost of moving between two indices.
* `LeanFrontier.BoundedSlope.StepBounded` - the two sided increment bound on a sequence.
* `LeanFrontier.BoundedSlope.minorant` - the candidate greatest element.

## Main results

* `LeanFrontier.BoundedSlope.StepBounded.le_add_slack` - a step bounded sequence is
  controlled at every index by its value at every other index, at the cost `slack`.
* `LeanFrontier.BoundedSlope.minorant_le_ceiling` - it obeys the ceiling on `s`.
* `LeanFrontier.BoundedSlope.minorant_stepBounded` - it is itself step bounded.
* `LeanFrontier.BoundedSlope.le_minorant` - it dominates every competitor, so the three
  results together say it is the greatest element of the feasible set.
* `LeanFrontier.BoundedSlope.minorant_eq_ceiling_of_stepBounded` - a ceiling that is
  already step bounded is its own minorant on `s`.
-/

namespace LeanFrontier.BoundedSlope

variable {a b : ℝ} {L M v : ℕ → ℝ} {s : Finset ℕ}

/-- `slack a b i j` is how far above its value at `j` a sequence may stand when read at
`i`, if it climbs at rate at most `a` and descends at rate at most `b`. Exactly one of the
two truncated differences is nonzero. -/
def slack (a b : ℝ) (i j : ℕ) : ℝ := a * ((i - j : ℕ) : ℝ) + b * ((j - i : ℕ) : ℝ)

@[simp]
theorem slack_self (a b : ℝ) (i : ℕ) : slack a b i i = 0 := by
  simp [slack]

theorem slack_succ_left (a b : ℝ) (i : ℕ) : slack a b (i + 1) i = a := by
  have h₁ : i + 1 - i = 1 := by omega
  have h₂ : i - (i + 1) = 0 := by omega
  simp [slack, h₁, h₂]

theorem slack_succ_right (a b : ℝ) (i : ℕ) : slack a b i (i + 1) = b := by
  have h₁ : i - (i + 1) = 0 := by omega
  have h₂ : i + 1 - i = 1 := by omega
  simp [slack, h₁, h₂]

/-- The cost is subadditive along a detour: going from `k` to `i` directly is never dearer
than going through `j`. This is what makes the construction below a genuine shortest path
value. -/
theorem slack_trans (ha : 0 ≤ a) (hb : 0 ≤ b) (i j k : ℕ) :
    slack a b i k ≤ slack a b i j + slack a b j k := by
  have h₁ : (i - k : ℕ) ≤ (i - j) + (j - k) := by omega
  have h₂ : (k - i : ℕ) ≤ (k - j) + (j - i) := by omega
  have h₁' : ((i - k : ℕ) : ℝ) ≤ ((i - j : ℕ) : ℝ) + ((j - k : ℕ) : ℝ) := by exact_mod_cast h₁
  have h₂' : ((k - i : ℕ) : ℝ) ≤ ((k - j : ℕ) : ℝ) + ((j - i : ℕ) : ℝ) := by exact_mod_cast h₂
  have ha' := mul_le_mul_of_nonneg_left h₁' ha
  have hb' := mul_le_mul_of_nonneg_left h₂' hb
  simp only [slack]
  nlinarith [ha', hb']

/-- A sequence that rises by at most `a` and falls by at most `b` at each step. -/
def StepBounded (a b : ℝ) (v : ℕ → ℝ) : Prop :=
  ∀ i, v (i + 1) ≤ v i + a ∧ v i ≤ v (i + 1) + b

theorem StepBounded.le_add_mul_up (hv : StepBounded a b v) (j d : ℕ) :
    v (j + d) ≤ v j + a * d := by
  induction d with
  | zero => simp
  | succ e ih =>
      have h := (hv (j + e)).1
      have hcast : ((e + 1 : ℕ) : ℝ) = (e : ℝ) + 1 := by push_cast; ring
      have hstep : v (j + (e + 1)) = v (j + e + 1) := by rw [← Nat.add_assoc]
      rw [hstep, hcast]
      linarith

theorem StepBounded.le_add_mul_down (hv : StepBounded a b v) (j d : ℕ) :
    v j ≤ v (j + d) + b * d := by
  induction d with
  | zero => simp
  | succ e ih =>
      have h := (hv (j + e)).2
      have hcast : ((e + 1 : ℕ) : ℝ) = (e : ℝ) + 1 := by push_cast; ring
      have hstep : v (j + (e + 1)) = v (j + e + 1) := by rw [← Nat.add_assoc]
      rw [hstep, hcast]
      linarith

/-- Every step bounded sequence is controlled at `i` by its value at any other index `j`,
with the asymmetric cost paid once. This is the bound the minorant makes sharp. -/
theorem StepBounded.le_add_slack (hv : StepBounded a b v) (i j : ℕ) :
    v i ≤ v j + slack a b i j := by
  rcases le_total j i with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd : slack a b (j + d) j = a * d := by
      have h₁ : j + d - j = d := by omega
      have h₂ : j - (j + d) = 0 := by omega
      simp [slack, h₁, h₂]
    rw [hd]
    exact hv.le_add_mul_up j d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd : slack a b i (i + d) = b * d := by
      have h₁ : i - (i + d) = 0 := by omega
      have h₂ : i + d - i = d := by omega
      simp [slack, h₁, h₂]
    rw [hd]
    exact hv.le_add_mul_down i d

/-- The candidate greatest step bounded sequence below the ceiling `L`, where the ceiling
is imposed only at the indices of the nonempty finite set `s`. -/
noncomputable def minorant (a b : ℝ) (L : ℕ → ℝ) (s : Finset ℕ) (hs : s.Nonempty) (i : ℕ) :
    ℝ :=
  s.inf' hs fun j => L j + slack a b i j

theorem minorant_le_ceiling (a b : ℝ) (L : ℕ → ℝ) (hs : s.Nonempty) {i : ℕ} (hi : i ∈ s) :
    minorant a b L s hs i ≤ L i :=
  Finset.inf'_le_of_le _ hi (by simp)

/-- The minorant is admissible: it satisfies the increment bounds everywhere, including
outside the constrained set. -/
theorem minorant_stepBounded (ha : 0 ≤ a) (hb : 0 ≤ b) (L : ℕ → ℝ) (hs : s.Nonempty) :
    StepBounded a b (minorant a b L s hs) := by
  intro i
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_inf' hs fun j => L j + slack a b i j
  obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_inf' hs fun j => L j + slack a b (i + 1) j
  have hp' : minorant a b L s hs i = L p + slack a b i p := hpe
  have hq' : minorant a b L s hs (i + 1) = L q + slack a b (i + 1) q := hqe
  have hup : minorant a b L s hs (i + 1) ≤ L p + slack a b (i + 1) p := Finset.inf'_le _ hp
  have hdown : minorant a b L s hs i ≤ L q + slack a b i q := Finset.inf'_le _ hq
  have h₁ := slack_trans ha hb (i + 1) i p
  have h₂ := slack_trans ha hb i (i + 1) q
  rw [slack_succ_left] at h₁
  rw [slack_succ_right] at h₂
  exact ⟨by linarith, by linarith⟩

/-- The minorant is the greatest admissible sequence: any step bounded competitor that
respects the ceiling on `s` lies below it at every index. -/
theorem le_minorant (hs : s.Nonempty) (hv : StepBounded a b v) (hL : ∀ j ∈ s, v j ≤ L j)
    (i : ℕ) : v i ≤ minorant a b L s hs i := by
  simp only [minorant]
  refine Finset.le_inf' _ _ ?_
  intro j hj
  have h₁ := hv.le_add_slack i j
  have h₂ := hL j hj
  linarith

/-- A ceiling that already satisfies the increment bounds is left untouched on `s`. -/
theorem minorant_eq_ceiling_of_stepBounded (hs : s.Nonempty) (hL : StepBounded a b L)
    {i : ℕ} (hi : i ∈ s) : minorant a b L s hs i = L i :=
  le_antisymm (minorant_le_ceiling a b L hs hi) (le_minorant hs hL (fun _ _ => le_rfl) i)

theorem minorant_mono (hs : s.Nonempty) (h : ∀ j ∈ s, L j ≤ M j) (i : ℕ) :
    minorant a b L s hs i ≤ minorant a b M s hs i := by
  simp only [minorant]
  refine Finset.le_inf' _ _ ?_
  intro j hj
  exact Finset.inf'_le_of_le _ hj (by have := h j hj; linarith)

/-- Lowering a ceiling to its minorant changes nothing the second time round. -/
theorem minorant_idem (ha : 0 ≤ a) (hb : 0 ≤ b) (L : ℕ → ℝ) (hs : s.Nonempty) (i : ℕ) :
    minorant a b (minorant a b L s hs) s hs i = minorant a b L s hs i := by
  refine le_antisymm ?_
    (le_minorant hs (minorant_stepBounded ha hb L hs) (fun _ _ => le_rfl) i)
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_inf' hs fun j => L j + slack a b i j
  have hp' : minorant a b L s hs i = L p + slack a b i p := hpe
  have h₁ : minorant a b (minorant a b L s hs) s hs i
      ≤ minorant a b L s hs p + slack a b i p := Finset.inf'_le _ hp
  have h₂ : minorant a b L s hs p ≤ L p := minorant_le_ceiling a b L hs hp
  linarith

end LeanFrontier.BoundedSlope
