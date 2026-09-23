import LeanFrontier.Combinatorics.CaroWei
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Turán's average-degree bound from Caro-Wei

The accepted Caro-Wei theorem gives an independent set whose size is at least

`∑ v, 1 / (degree v + 1)`.

This module packages the classical coarser consequence depending only on the
number of vertices and edges:

`|I| ≥ |V|² / (2 |E| + |V|)`.

The proof uses the finite reciprocal-sum (Engel/Cauchy-Schwarz) inequality

`n² / ∑ aᵢ ≤ ∑ 1 / aᵢ`

for positive rational weights, then rewrites the denominator with Mathlib's
degree-sum formula `∑ degree = 2 |E|`.  Thus both the accepted Caro-Wei
theorem and Mathlib's graph-counting API do substantive work.
-/

open scoped BigOperators

namespace LeanFrontier.GraphTheory

variable {V : Type*} [Fintype V]

private theorem card_sq_div_sum_le_sum_inv
    {α : Type*} (s : Finset α) (a : α → ℚ)
    (ha : ∀ x ∈ s, 0 < a x) :
    ((s.card : ℚ) ^ 2) / (∑ x ∈ s, a x) ≤
      ∑ x ∈ s, (1 : ℚ) / a x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x s hx ih =>
      have hax : 0 < a x := ha x (by simp)
      have has : ∀ y ∈ s, 0 < a y := by
        intro y hy
        exact ha y (by simp [hy])
      by_cases hs : s = ∅
      · subst s
        simp [hax.ne']
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        have hsum_pos : 0 < ∑ y ∈ s, a y :=
          Finset.sum_pos (fun y hy => has y hy) hsne
        let A : ℚ := ∑ y ∈ s, a y
        let n : ℚ := s.card
        have hA : 0 < A := by
          simpa [A] using hsum_pos
        have hsum_nonzero : A ≠ 0 := ne_of_gt hA
        have hax_nonzero : a x ≠ 0 := ne_of_gt hax
        have hAax_nonzero : A + a x ≠ 0 := ne_of_gt (add_pos hA hax)
        have hid :
            n ^ 2 / A + 1 / a x - (n + 1) ^ 2 / (A + a x)
              = (a x * n - A) ^ 2 / (A * a x * (A + a x)) := by
          field_simp [hsum_nonzero, hax_nonzero, hAax_nonzero]
          ring
        have hcombine :
            (n + 1) ^ 2 / (A + a x) ≤ n ^ 2 / A + 1 / a x := by
          have hden_pos : 0 < A * a x * (A + a x) := by
            positivity
          have hnonneg :
              0 ≤ n ^ 2 / A + 1 / a x - (n + 1) ^ 2 / (A + a x) := by
            rw [hid]
            positivity
          linarith
        calc
          (((insert x s).card : ℚ) ^ 2) / (∑ y ∈ insert x s, a y)
              = (n + 1) ^ 2 / (A + a x) := by
                  simp [Finset.card_insert_of_notMem hx, Finset.sum_insert hx, n, A]
          _ ≤ n ^ 2 / A + 1 / a x := hcombine
          _ ≤ (∑ y ∈ s, (1 : ℚ) / a y) + 1 / a x := by
                exact add_le_add_right (by simpa [n, A] using ih has) _
          _ = ∑ y ∈ insert x s, (1 : ℚ) / a y := by
                rw [Finset.sum_insert hx]
                ring

/-- **Turán's average-degree lower bound for independent sets**, obtained as a
corollary of Caro-Wei.

Every finite simple graph has an independent finset `I` satisfying

`|V|² / (2 |E| + |V|) ≤ |I|`.

The statement is over `ℚ`, avoiding floor/ceiling noise. For the empty graph
both numerator and denominator vanish, and Lean's field convention makes the
left-hand side zero. -/
theorem caroWei_implies_turan_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ I : Finset V,
      G.IsIndepSet (I : Set V) ∧
      ((Fintype.card V : ℚ) ^ 2) /
          (2 * (G.edgeFinset.card : ℚ) + (Fintype.card V : ℚ))
        ≤ (I.card : ℚ) := by
  classical
  obtain ⟨I, hI, hCW⟩ := caroWei G
  refine ⟨I, hI, ?_⟩

  have hpos :
      ∀ v ∈ (Finset.univ : Finset V), 0 < ((G.degree v : ℚ) + 1) := by
    intro v hv
    positivity

  have hrecip :=
    card_sq_div_sum_le_sum_inv (Finset.univ : Finset V)
      (fun v => (G.degree v : ℚ) + 1) hpos

  have hdegree :
      (∑ v : V, (G.degree v : ℚ)) =
        2 * (G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges

  have hden :
      (∑ v : V, ((G.degree v : ℚ) + 1)) =
        2 * (G.edgeFinset.card : ℚ) + (Fintype.card V : ℚ) := by
    rw [Finset.sum_add_distrib, hdegree]
    simp

  rw [hden] at hrecip
  simpa using hrecip.trans hCW

end LeanFrontier.GraphTheory
