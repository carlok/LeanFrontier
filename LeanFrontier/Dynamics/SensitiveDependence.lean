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

end LeanFrontier.Dynamics
