module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The clique–coclique bound

In a finite vertex-transitive simple graph, the product of the sizes of a clique and an
independent set is at most the number of vertices.

See Theorem 3.1 of C. Godsil and K. Meagher, *An algebraic proof of the Erdős–Ko–Rado theorem
for intersecting families of perfect matchings*, https://arxiv.org/abs/1506.08770.
-/

public section

open scoped SimpleGraph

namespace LeanFrontier.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Finite V]

/-- The product of the sizes of a clique and an independent set in a finite vertex-transitive
graph is at most the number of vertices. -/
theorem IsClique.ncard_mul_ncard_le_of_vertex_transitive {C I : Set V}
    (hC : G.IsClique C) (hI : G.IsIndepSet I)
    (htrans : ∀ u v : V, ∃ e : G ≃g G, e u = v) : C.ncard * I.ncard ≤ Nat.card V := by
  have : Finite (G ≃g G) :=
    Finite.of_injective (fun e : G ≃g G ↦ (e : V → V)) fun _ _ h ↦ RelIso.ext (congrFun h)
  have : Nonempty (G ≃g G) := ⟨SimpleGraph.Iso.refl⟩
  let move (u v : V) : G ≃g G := (htrans u v).choose
  have move_apply (u v : V) : move u v u = v := (htrans u v).choose_spec
  -- Record the image of the clique vertex before moving it into the independent set.
  let encode : C × I × (G ≃g G) → V × (G ≃g G) :=
    fun ⟨c, i, e⟩ ↦ (e c, (move (e c) i).comp e)
  have hinj : Function.Injective encode := by
    rintro ⟨c, i, e⟩ ⟨c', i', e'⟩ heq
    have hvertex : e c = e' c' := congrArg Prod.fst heq
    have haut : (move (e c) i).comp e = (move (e' c') i').comp e' := congrArg Prod.snd heq
    let f : G ≃g G := (move (e c) i).comp e
    have hci : f c = (i : V) := move_apply (e c) i
    have hci' : f c' = (i' : V) := by
      change ((move (e c) i).comp e) c' = (i' : V)
      rw [haut]
      exact move_apply (e' c') i'
    have hc : c = c' := by
      apply Subtype.ext
      by_contra hne
      have hadj := f.map_adj_iff.mpr (hC c.property c'.property hne)
      rw [hci, hci'] at hadj
      exact hI i.property i'.property hadj.ne hadj
    subst c'
    have hi : i = i' := Subtype.ext (hci.symm.trans hci')
    subst i'
    rw [← hvertex] at haut
    have he : e = e' := by
      apply RelIso.ext
      intro v
      exact (move (e c) i).injective (congrArg (fun g : G ≃g G ↦ g v) haut)
    subst e'
    rfl
  have hcard := Nat.card_le_card_of_injective encode hinj
  simp only [Nat.card_prod, Nat.card_coe_set_eq, ← Nat.mul_assoc] at hcard
  exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos

/-- The clique number times the independence number of a finite vertex-transitive graph is at
most the number of vertices. -/
theorem cliqueNum_mul_indepNum_le_natCard_of_vertex_transitive
    (htrans : ∀ u v : V, ∃ e : G ≃g G, e u = v) :
    G.cliqueNum * G.indepNum ≤ Nat.card V := by
  obtain ⟨C, hC⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  rw [← hC.card_eq, ← hI.card_eq]
  simpa only [Set.ncard_coe_finset] using
    IsClique.ncard_mul_ncard_le_of_vertex_transitive hC.isClique hI.isIndepSet htrans

end LeanFrontier.SimpleGraph
