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
    (p q : X) {δ : ℝ} (hδ : 0 < δ)
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

end LeanFrontier.Dynamics
