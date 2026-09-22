import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

/-!
# The Caro-Wei bound

For a finite simple graph, the Caro-Wei theorem gives a lower bound for the size of an
independent set in terms of the vertex degrees:

`∑ v, 1 / (degree v + 1) ≤ α(G)`.

Rather than introducing a separate independence-number definition, this module proves the
constructive existence form: there is an independent finset whose cardinality is at least the
Caro-Wei sum.

The proof is deterministic.  On an arbitrary finite vertex subset `s`, choose a vertex of
minimum degree inside `s`, delete its closed neighborhood, and recurse.  The deleted closed
neighborhood contributes at most one to the reciprocal-degree sum, while deleting vertices can
only decrease the remaining local degrees, hence can only increase their reciprocal weights.
-/

open scoped BigOperators

namespace LeanFrontier.GraphTheory

variable {V : Type*} [Fintype V]

private theorem exists_indepSet_caroWei_on (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (s : Finset V) :
    ∃ I : Finset V,
      I ⊆ s ∧
      G.IsIndepSet (I : Set V) ∧
      (∑ v ∈ s, (1 : ℚ) / (((G.neighborFinset v ∩ s).card : ℚ) + 1)) ≤ (I.card : ℚ) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hs : s = ∅
      · subst s
        exact ⟨∅, by simp, by simp, by simp⟩
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨v, hvs, hvmin⟩ :=
          s.exists_min_image (fun x => (G.neighborFinset x ∩ s).card) hsne

        let N : Finset V := G.neighborFinset v ∩ s
        let C : Finset V := insert v N
        let r : Finset V := s \ C

        have hCsub : C ⊆ s := by
          intro x hx
          simp only [C, Finset.mem_insert, N, Finset.mem_inter] at hx
          rcases hx with rfl | hx
          · exact hvs
          · exact hx.2

        have hCne : C.Nonempty := ⟨v, by simp [C]⟩
        have hrss : r ⊂ s := by
          simpa [r] using Finset.sdiff_ssubset hCsub hCne

        obtain ⟨I, hIsub, hIind, hIbound⟩ := ih r hrss

        have hvnotI : v ∉ I := by
          intro hvI
          have hvr : v ∈ r := hIsub hvI
          exact (Finset.mem_sdiff.mp hvr).2 (by simp [C])

        have hIind_insert : G.IsIndepSet ((insert v I : Finset V) : Set V) := by
          rw [SimpleGraph.isIndepSet_iff]
          intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
          rcases hx with rfl | hxI
          · rcases hy with rfl | hyI
            · exact (hxy rfl).elim
            · intro hadj
              have hyr : y ∈ r := hIsub hyI
              have hys : y ∈ s := (Finset.mem_sdiff.mp hyr).1
              have hyCnot : y ∉ C := (Finset.mem_sdiff.mp hyr).2
              apply hyCnot
              simp [C, N, hys, hadj]
          · rcases hy with rfl | hyI
            · intro hadj
              have hxr : x ∈ r := hIsub hxI
              have hxs : x ∈ s := (Finset.mem_sdiff.mp hxr).1
              have hxCnot : x ∉ C := (Finset.mem_sdiff.mp hxr).2
              apply hxCnot
              simp [C, N, hxs, (G.adj_comm x v).mp hadj]
            · exact hIind (by simpa using hxI) (by simpa using hyI) hxy

        have hcardC : C.card = N.card + 1 := by
          simp [C, N]

        have hCsum :
            (∑ x ∈ C, (1 : ℚ) / (((G.neighborFinset x ∩ s).card : ℚ) + 1)) ≤ 1 := by
          calc
            (∑ x ∈ C, (1 : ℚ) / (((G.neighborFinset x ∩ s).card : ℚ) + 1))
                ≤ ∑ _x ∈ C, (1 : ℚ) / ((N.card : ℚ) + 1) := by
                  apply Finset.sum_le_sum
                  intro x hx
                  have hxs : x ∈ s := hCsub hx
                  have hmin : N.card ≤ (G.neighborFinset x ∩ s).card := by
                    simpa [N] using hvmin x hxs
                  apply one_div_le_one_div_of_le
                  · positivity
                  · exact_mod_cast Nat.add_le_add_right hmin 1
            _ = (C.card : ℚ) * ((1 : ℚ) / ((N.card : ℚ) + 1)) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
            _ = 1 := by
                  rw [hcardC]
                  norm_num
                  field_simp

        have hrs' : r ⊆ s := by
          intro x hx
          exact (Finset.mem_sdiff.mp hx).1

        have hRsum :
            (∑ x ∈ r, (1 : ℚ) / (((G.neighborFinset x ∩ s).card : ℚ) + 1)) ≤
              ∑ x ∈ r, (1 : ℚ) / (((G.neighborFinset x ∩ r).card : ℚ) + 1) := by
          apply Finset.sum_le_sum
          intro x hx
          have hsubset :
              G.neighborFinset x ∩ r ⊆ G.neighborFinset x ∩ s := by
            intro y hy
            exact Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hy).1, hrs' (Finset.mem_inter.mp hy).2⟩
          have hdeg :
              (G.neighborFinset x ∩ r).card ≤ (G.neighborFinset x ∩ s).card :=
            Finset.card_le_card hsubset
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast Nat.add_le_add_right hdeg 1

        have hdisj : Disjoint C r := by
          refine Finset.disjoint_left.2 ?_
          intro x hxC hxr
          exact (Finset.mem_sdiff.mp hxr).2 hxC

        have hunion : C ∪ r = s := by
          simpa [r] using Finset.union_sdiff_of_subset hCsub

        refine ⟨insert v I, ?_, hIind_insert, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hxI
          · exact hvs
          · exact hrs' (hIsub hxI)
        · calc
            (∑ x ∈ s, (1 : ℚ) / (((G.neighborFinset x ∩ s).card : ℚ) + 1))
                = (∑ x ∈ C, (1 : ℚ) / (((G.neighborFinset x ∩ s).card : ℚ) + 1)) +
                    ∑ x ∈ r, (1 : ℚ) / (((G.neighborFinset x ∩ s).card : ℚ) + 1) := by
                      rw [← hunion, Finset.sum_union hdisj]
            _ ≤ 1 + ∑ x ∈ r, (1 : ℚ) / (((G.neighborFinset x ∩ r).card : ℚ) + 1) :=
              add_le_add hCsum hRsum
            _ ≤ 1 + (I.card : ℚ) := add_le_add_left hIbound 1
            _ = ((insert v I).card : ℚ) := by
              rw [Finset.card_insert_of_notMem hvnotI]
              norm_num

/-- **Caro-Wei theorem.**

Every finite simple graph has an independent set whose cardinality is at least

`∑ v, 1 / (degree v + 1)`.

The bound is stated over `ℚ`, so no rounding or floor operation obscures the sharp
degree-dependent estimate. -/
theorem caroWei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ I : Finset V,
      G.IsIndepSet (I : Set V) ∧
      (∑ v : V, (1 : ℚ) / ((G.degree v : ℚ) + 1)) ≤ (I.card : ℚ) := by
  classical
  obtain ⟨I, _, hI, hbound⟩ := exists_indepSet_caroWei_on G Finset.univ
  refine ⟨I, hI, ?_⟩
  simpa [SimpleGraph.card_neighborFinset_eq_degree] using hbound

end LeanFrontier.GraphTheory
