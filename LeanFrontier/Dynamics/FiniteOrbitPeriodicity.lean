import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic

/-!
# Eventual periodicity of finite deterministic dynamical systems

Every orbit of a self-map of a finite set consists of a transient prefix followed
by a cycle. The pigeonhole principle proves the stronger quantitative statement
that the transient length plus one positive cycle period is at most the number
of states.

The eventual-cycle theorem gives two important consequences:

* the orbit reaches a periodic point within fewer than `card α` steps;
* **uniform synchronization:** for every map `f : α → α`, the iterates
  `f^[card α]` and `f^[card α + (card α)!]` coincide as functions.
  The factorial is a common multiple of all possible cycle lengths.

This is a theorem about arbitrary finite transformations, with no injectivity
or surjectivity hypothesis. It complements Mathlib's theory of periodic points
of injective finite maps.
-/

namespace LeanFrontier.Dynamics

/-- Every orbit in a finite deterministic system has a transient part of
length `μ` and a positive period `p`, with `μ+p` at most the number
of states. Every position after the transient is periodic modulo `p`. -/
theorem finite_orbit_eventually_periodic
    {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ μ p : ℕ, 0 < p ∧ μ + p ≤ Fintype.card α ∧
      ∀ t : ℕ, f^[μ + t + p] x = f^[μ + t] x := by
  let g : Fin (Fintype.card α + 1) → α := fun i => f^[i.val] x
  have hg : Fintype.card α <
      Fintype.card (Fin (Fintype.card α + 1)) := by simp
  obtain ⟨a, b, hab, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt g hg
  have hneq : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have hcore : ∀ u v : Fin (Fintype.card α + 1),
      u.val < v.val → f^[u.val] x = f^[v.val] x →
      ∃ μ p : ℕ, 0 < p ∧ μ + p ≤ Fintype.card α ∧
        ∀ t : ℕ, f^[μ + t + p] x = f^[μ + t] x := by
    intro u v huv heq'
    refine ⟨u.val, v.val - u.val, by omega, by omega, ?_⟩
    intro t
    have hnum : u.val + t + (v.val - u.val) = t + v.val := by omega
    have hnum' : t + u.val = u.val + t := by omega
    calc
      f^[u.val + t + (v.val - u.val)] x =
          f^[t + v.val] x := by rw [hnum]
      _ = f^[t] (f^[v.val] x) :=
          Function.iterate_add_apply f t v.val x
      _ = f^[t] (f^[u.val] x) := by rw [← heq']
      _ = f^[t + u.val] x :=
          (Function.iterate_add_apply f t u.val x).symm
      _ = f^[u.val + t] x := by rw [hnum']
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact hcore a b hlt heq
  · exact hcore b a hgt heq.symm

/-- Each orbit of a finite self-map reaches a genuinely periodic point in
fewer than `card α` iterations, with positive period at most `card α`. -/
theorem finite_orbit_reaches_periodic_point
    {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ μ p : ℕ, μ < Fintype.card α ∧ 0 < p ∧
      Function.IsPeriodicPt f p (f^[μ] x) := by
  obtain ⟨μ, p, hp, hbound, htail⟩ :=
    finite_orbit_eventually_periodic f x
  refine ⟨μ, p, by omega, hp, ?_⟩
  change f^[p] (f^[μ] x) = f^[μ] x
  calc
    f^[p] (f^[μ] x) = f^[p + μ] x :=
      (Function.iterate_add_apply f p μ x).symm
    _ = f^[μ + 0 + p] x := by
      congr 1
      omega
    _ = f^[μ + 0] x := htail 0
    _ = f^[μ] x := by simp

/-- **Uniform eventual-periodicity exponent for the full finite
transformation monoid.** If a finite set has `N` elements, every self-map
satisfies `f^(N+N!) = f^N`. The exponent `N!` simultaneously absorbs all
possible cycle periods and the first `N` steps absorb every transient. -/
theorem finite_map_iterate_card_add_factorial
    {α : Type*} [Fintype α] (f : α → α) :
    f^[Fintype.card α + Nat.factorial (Fintype.card α)] =
      f^[Fintype.card α] := by
  funext x
  obtain ⟨μ, p, hp, hbound, htail⟩ :=
    finite_orbit_eventually_periodic f x
  have hdiv : p ∣ Nat.factorial (Fintype.card α) :=
    Nat.dvd_factorial hp (by omega)
  obtain ⟨q, hq⟩ := hdiv
  have hmultiple : ∀ (t q : ℕ),
      f^[μ + t + p * q] x = f^[μ + t] x := by
    intro t q
    induction q with
    | zero =>
        simp
    | succ q ih =>
        calc
          f^[μ + t + p * (q + 1)] x =
              f^[μ + (t + p * q) + p] x := by
                congr 1
                omega
          _ = f^[μ + (t + p * q)] x := htail (t + p * q)
          _ = f^[μ + t + p * q] x := by
                congr 1
                omega
          _ = f^[μ + t] x := ih
  let t := Fintype.card α - μ
  have ht : μ + t = Fintype.card α := by
    dsimp [t]
    omega
  have hexp :
      Fintype.card α + Nat.factorial (Fintype.card α) = μ + t + p * q := by
    omega
  calc
    f^[Fintype.card α + Nat.factorial (Fintype.card α)] x =
        f^[μ + t + p * q] x := by rw [hexp]
    _ = f^[μ + t] x := hmultiple t q
    _ = f^[Fintype.card α] x := by rw [ht]

end LeanFrontier.Dynamics
