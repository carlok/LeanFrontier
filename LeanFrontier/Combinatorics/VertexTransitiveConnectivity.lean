module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Vertex deletion in finite vertex-transitive graphs

Deleting any one vertex from a finite connected vertex-transitive graph with at least two
vertices leaves a connected graph. See Lemma 3.3 of <https://arxiv.org/abs/2006.06387>.
-/

public section

open scoped SimpleGraph

namespace LeanFrontier.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Finite V] [Nontrivial V]

/-- A finite connected vertex-transitive graph with at least two vertices remains connected
after deleting any one vertex. -/
theorem Connected.induce_compl_singleton_of_vertex_transitive (hconn : G.Connected)
    (htrans : ∀ v w : V, ∃ e : G ≃g G, e v = w) (a : V) :
    (G.induce ({a}ᶜ : Set V)).Connected := by
  obtain ⟨z, hz⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  obtain ⟨e, he⟩ := htrans z a
  have himage : e '' ({z}ᶜ : Set V) = ({a}ᶜ : Set V) := by
    rw [Set.image_compl_eq e.bijective, Set.image_singleton, he]
  have hbij : Set.BijOn e {z}ᶜ {a}ᶜ := himage ▸ e.injective.bijOn_image
  exact (e.induce hbij).connected_iff.mp hz

end LeanFrontier.SimpleGraph
