import Mathlib.Dynamics.Transitive
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Sensitive dependence in discrete dynamical systems

This module develops the metric ingredient of the theorem of Banks, Brooks,
Cairns, Davis and Stacey: topological transitivity together with dense periodic
points forces sensitivity on an infinite metric space.

The first result isolates an essential uniform-separation step. If two forward
orbits stay a fixed positive distance apart, then every point is uniformly
distant from at least one of the two entire forward orbits. For periodic
orbits the separation hypothesis follows from disjointness, because each orbit
is finite. The remaining dynamical argument uses continuity and transitivity
to visit a neighborhood of the orbit that stays far away.
-/

namespace LeanFrontier.Dynamics

/-- A self-map on a metric space has sensitive dependence on initial conditions
if some positive separation can be witnessed from every point, within every
positive starting radius, after finitely many iterations. -/
def HasSensitiveDependence {X : Type*} [PseudoMetricSpace X] (f : X → (X)) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ x : X, ∀ ε : ℝ, 0 < ε →
      ∃ y : X, dist x y < ε ∧
        ∃ n : ℕ, δ < dist (f^[n] x) (f^[n] y)

/-- For two uniformly separated forward orbits, every point stays a uniform
distance away from at least one of the two orbits. This is the separation
lemma used in the Banks sensitivity argument. -/
theorem separated_orbits_uniformly_avoid
    {X : Type*} [PseudoMetricSpace X] (f : X → (X))
    (p q : X) {δ : ℝ} (_hδ : 0 < δ)
    (hsep : ∀ m n : ℕ, 2 * δ ≤ dist (f^[m] p) (f^[n] q)) :
    ∀ x : X,
      (∀ m : ℕ, δ ≤ dist x (f^[m] p)) ∨
      (∀ n : ℕ, δ ≤ dist x (f^[n] q)) := by
  intro x
  by_cases h : ∃ m : ℕ, dist x (f^[m] p) < δ
  · right
    obtain ⟨m, hm⟩ := h
    intro n
    have htri := dist_triangle (f^[m] p) x (f^[n] q)
    rw [dist_comm (f^[m] p) x] at htri
    have hs := hsep m n
    linarith
  · left
    intro m
    exact le_of_not_gt (fun hm => h ⟨m, hm⟩)


/-- Disjoint finite periodic orbits are separated by one positive metric
constant, uniformly over all (not necessarily reduced) iterate indices. -/
theorem disjoint_periodic_orbits_separated
    {X : Type*} [MetricSpace X] (f : X → (X))
    (p q : X) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hp : Function.IsPeriodicPt f m p)
    (hq : Function.IsPeriodicPt f n q)
    (hdisjoint : ∀ i j : ℕ, f^[i] p ≠ f^[j] q) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ i j : ℕ, 2 * δ ≤ dist (f^[i] p) (f^[j] q) := by
  classical
  let indices : Finset (ℕ × ℕ) := (Finset.range m).product (Finset.range n)
  have hi : indices.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [indices, hm, hn]
  let distances : Finset ℝ :=
    indices.image (fun ij => dist (f^[ij.1] p) (f^[ij.2] q))
  have hd : distances.Nonempty := hi.image _
  let d : ℝ := distances.min' hd
  have hdpos : 0 < d := by
    change 0 < distances.min' hd
    rw [Finset.lt_min'_iff]
    intro t ht
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp ht
    exact dist_pos.mpr (hdisjoint i j)
  refine ⟨d / 2, by positivity, ?_⟩
  intro i j
  have hk : (i % m, j % n) ∈ indices := by
    change (i % m, j % n) ∈ (Finset.range m).product (Finset.range n)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt i hm),
       Finset.mem_range.mpr (Nat.mod_lt j hn)⟩
  have hdist :
      dist (f^[i % m] p) (f^[j % n] q) ∈ distances := by
    apply Finset.mem_image.mpr
    exact ⟨(i % m, j % n), hk, rfl⟩
  have hle :
      d ≤ dist (f^[i % m] p) (f^[j % n] q) := by
    exact Finset.min'_le distances _ hdist
  rw [hp.iterate_mod_apply i, hq.iterate_mod_apply j] at hle
  linarith

/-- Two disjoint periodic orbits supply a single positive avoidance radius
valid at every point of the ambient metric space. -/
theorem disjoint_periodic_orbits_uniformly_avoid
    {X : Type*} [MetricSpace X] (f : X → (X))
    (p q : X) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hp : Function.IsPeriodicPt f m p)
    (hq : Function.IsPeriodicPt f n q)
    (hdisjoint : ∀ i j : ℕ, f^[i] p ≠ f^[j] q) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : X,
        (∀ i : ℕ, δ ≤ dist x (f^[i] p)) ∨
        (∀ j : ℕ, δ ≤ dist x (f^[j] q)) := by
  obtain ⟨δ, hδ, hsep⟩ :=
    disjoint_periodic_orbits_separated f p q hm hn hp hq hdisjoint
  exact ⟨δ, hδ, separated_orbits_uniformly_avoid f p q hδ hsep⟩


/-- In an infinite metric space with dense periodic points, there exist two
periodic points whose full forward orbits are disjoint. This turns density
into the two-orbit hypothesis of the uniform-separation lemmas. -/
theorem exists_disjoint_periodic_orbits_of_dense
    {X : Type*} [MetricSpace X] [Infinite X] [Nonempty X]
    (f : X → (X)) (hdense : Dense (Function.periodicPts f)) :
    ∃ (p q : X) (m n : ℕ), 0 < m ∧ 0 < n ∧
      Function.IsPeriodicPt f m p ∧
      Function.IsPeriodicPt f n q ∧
      (∀ i j : ℕ, f^[i] p ≠ f^[j] q) := by
  classical
  obtain ⟨p, hp, _⟩ :=
    hdense.exists_mem_open isOpen_univ (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
  let s : Set X :=
    Set.range (fun k : Fin (Function.minimalPeriod f p) => f^[k.val] p)
  have hsfin : s.Finite := Set.finite_range _
  have hsne : (sᶜ).Nonempty := by
    by_contra h
    have hall : ∀ x : X, x ∈ s := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    have hunivsub : (Set.univ : Set X) ⊆ s := fun x _ => hall x
    have hfinite : Finite X :=
      Set.finite_univ_iff.mp (hsfin.subset hunivsub)
    exact not_finite X
  obtain ⟨q, hq, hqout⟩ :=
    hdense.exists_mem_open hsfin.isClosed.isOpen_compl hsne
  have hpIter (i : ℕ) : f^[i] p ∈ s := by
    refine ⟨⟨i % Function.minimalPeriod f p,
      Nat.mod_lt i (Function.minimalPeriod_pos_of_mem_periodicPts hp)⟩, ?_⟩
    exact Function.iterate_mod_minimalPeriod_eq
  have hdisjoint (i j : ℕ) : f^[i] p ≠ f^[j] q := by
    intro heq
    have hpe : Function.periodicOrbit f (f^[i] p) = Function.periodicOrbit f p :=
      Function.periodicOrbit_apply_iterate_eq hp i
    have hqe : Function.periodicOrbit f (f^[j] q) = Function.periodicOrbit f q :=
      Function.periodicOrbit_apply_iterate_eq hq j
    have heqOrbit : Function.periodicOrbit f p = Function.periodicOrbit f q := by
      calc
        Function.periodicOrbit f p = Function.periodicOrbit f (f^[i] p) := hpe.symm
        _ = Function.periodicOrbit f (f^[j] q) := by rw [heq]
        _ = Function.periodicOrbit f q := hqe
    have hqmem : q ∈ Function.periodicOrbit f p := by
      rw [heqOrbit]
      exact Function.self_mem_periodicOrbit hq
    obtain ⟨k, hk⟩ := (Function.mem_periodicOrbit_iff hp).mp hqmem
    exact hqout (by
      rw [← hk]
      exact hpIter k)
  obtain ⟨m, hm, hpm⟩ := hp
  obtain ⟨n, hn, hqn⟩ := hq
  exact ⟨p, q, m, n, hm, hn, hpm, hqn, hdisjoint⟩

/-- Density of periodic points on an infinite metric space supplies a fixed
positive orbit-separation constant and two corresponding periodic points. -/
theorem exists_separated_periodic_orbits_of_dense
    {X : Type*} [MetricSpace X] [Infinite X] [Nonempty X]
    (f : X → (X)) (hdense : Dense (Function.periodicPts f)) :
    ∃ (p q : X) (δ : ℝ), 0 < δ ∧
      ∀ i j : ℕ, 2 * δ ≤ dist (f^[i] p) (f^[j] q) := by
  obtain ⟨p, q, m, n, hm, hn, hp, hq, hdisjoint⟩ :=
    exists_disjoint_periodic_orbits_of_dense f hdense
  obtain ⟨δ, hδ, hsep⟩ :=
    disjoint_periodic_orbits_separated f p q hm hn hp hq hdisjoint
  exact ⟨p, q, δ, hδ, hsep⟩


/-- A single positive distance threshold works uniformly over all starting
points: each point has some periodic orbit that stays at least that far away.
The choice of orbit may depend on the point, but the threshold does not. -/
theorem exists_uniformly_avoided_periodic_orbit_of_dense
    {X : Type*} [MetricSpace X] [Infinite X] [Nonempty X]
    (f : X → (X)) (hdense : Dense (Function.periodicPts f)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : X, ∃ z : X, z ∈ Function.periodicPts f ∧
        ∀ i : ℕ, δ ≤ dist x (f^[i] z) := by
  obtain ⟨p, q, m, n, hm, hn, hp, hq, hdisjoint⟩ :=
    exists_disjoint_periodic_orbits_of_dense f hdense
  obtain ⟨δ, hδ, hsep⟩ :=
    disjoint_periodic_orbits_separated f p q hm hn hp hq hdisjoint
  refine ⟨δ, hδ, ?_⟩
  intro x
  rcases separated_orbits_uniformly_avoid f p q hδ hsep x with h | h
  · exact ⟨p, Function.mk_mem_periodicPts hm hp, h⟩
  · exact ⟨q, Function.mk_mem_periodicPts hn hq, h⟩

end LeanFrontier.Dynamics
