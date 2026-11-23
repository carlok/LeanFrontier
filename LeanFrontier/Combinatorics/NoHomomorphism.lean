module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The no-homomorphism lemma

If a finite graph has a homomorphism to a finite vertex-transitive graph, its independence
ratio is at least that of the target. The statement uses cross multiplication.

See M. O. Albertson and K. L. Collins, *Homomorphisms of 3-chromatic graphs* (1985), <https://doi.org/10.1016/0012-365X(85)90073-1>,
and *Handbook of Product Graphs*, Lemma 2.13.
-/

public section

open scoped BigOperators

open scoped SimpleGraph

namespace LeanFrontier.SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} [Finite V] [Finite W]

/-- The no-homomorphism lemma of Albertson and Collins, in cross-multiplied form. -/
theorem Hom.natCard_mul_indepNum_le_of_vertex_transitive (f : G →g H)
    (htrans : ∀ u v : W, ∃ e : H ≃g H, e u = v) :
    Nat.card V * H.indepNum ≤ Nat.card W * G.indepNum := by
  classical
  have : Finite (H ≃g H) :=
    Finite.of_injective (fun e : H ≃g H ↦ (e : W → W)) fun _ _ h ↦ RelIso.ext (congrFun h)
  have : Nonempty (H ≃g H) := ⟨SimpleGraph.Iso.refl⟩
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (H ≃g H) := Fintype.ofFinite (H ≃g H)
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  let preimage (e : H ≃g H) : Finset V := Finset.univ.filter fun v ↦ e (f v) ∈ I
  have mem_preimage {e : H ≃g H} {v : V} : v ∈ preimage e ↔ e (f v) ∈ I := by
    simp [preimage]
  have hbound (e : H ≃g H) : Nat.card (preimage e) ≤ G.indepNum := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro u hu v hv _ hadj
    have hadj' := e.map_adj_iff.mpr (f.map_adj hadj)
    exact hI.isIndepSet (mem_preimage.mp hu) (mem_preimage.mp hv) hadj'.ne hadj'
  let move (x y : W) : H ≃g H := (htrans x y).choose
  have move_apply (x y : W) : move x y x = y := (htrans x y).choose_spec
  -- Record the old image of the vertex and the automorphism that now sends its image into I.
  let encode : V × I × (H ≃g H) → W × (Σ e : H ≃g H, ↥(preimage e)) :=
    fun ⟨v, i, e⟩ ↦
      (e (f v), ⟨(move (e (f v)) i).comp e, ⟨v, mem_preimage.mpr (by
        change move (e (f v)) i (e (f v)) ∈ I
        rw [move_apply]
        exact i.property)⟩⟩)
  have hinj : Function.Injective encode := by
    rintro ⟨v, i, e⟩ ⟨v', i', e'⟩ h
    have hv : v = v' := congrArg (fun p : W × (Σ a : H ≃g H, ↥(preimage a)) ↦ p.2.2.val) h
    subst v'
    have hx : e (f v) = e' (f v) := congrArg Prod.fst h
    have heq : (move (e (f v)) i).comp e = (move (e' (f v)) i').comp e' :=
      congrArg (fun p : W × (Σ a : H ≃g H, ↥(preimage a)) ↦ p.2.1) h
    have hi : i = i' := Subtype.ext <| calc
      (i : W) = ((move (e (f v)) i).comp e) (f v) := (move_apply _ _).symm
      _ = ((move (e' (f v)) i').comp e') (f v) := by rw [heq]
      _ = i' := move_apply _ _
    subst i'
    rw [← hx] at heq
    have he : e = e' := RelIso.ext fun w ↦
      (move (e (f v)) i).injective (congrArg (fun a : H ≃g H ↦ a w) heq)
    subst e'
    rfl
  have hIcard : Nat.card I = H.indepNum := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hI.card_eq
  have hcount := Nat.card_le_card_of_injective encode hinj
  simp only [Nat.card_prod, Nat.card_sigma, hIcard, ← Nat.mul_assoc] at hcount
  have hsum : (∑ e : H ≃g H, Nat.card (preimage e)) ≤ Nat.card (H ≃g H) * G.indepNum := by
    calc
      _ ≤ ∑ _e : H ≃g H, G.indepNum := Finset.sum_le_sum fun e _ ↦ hbound e
      _ = _ := by simp [Nat.card_eq_fintype_card]
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := H ≃g H))
  calc
    _ ≤ Nat.card W * ∑ e : H ≃g H, Nat.card (preimage e) := hcount
    _ ≤ Nat.card W * (Nat.card (H ≃g H) * G.indepNum) := Nat.mul_le_mul_left _ hsum
    _ = _ := by ac_rfl

end LeanFrontier.SimpleGraph
