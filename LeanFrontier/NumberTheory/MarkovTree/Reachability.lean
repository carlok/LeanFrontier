import LeanFrontier.NumberTheory.MarkovTree.Paths
import Mathlib.Tactic.NormNum

/-!
# Reachability of positive Markov triples from the root

The accepted local descent theorem says that, after ordering a positive Markov triple,
jumping its largest coordinate stays positive and strictly lowers that coordinate.
The accepted path module packages the three coordinate jumps as `Move` and proves that
finite walks preserve the Markov equation and reverse exactly.

This module combines those ingredients into the global representation theorem needed before
a Markov/Farey correspondence can be built:

every positive integer Markov solution is reachable from `(1,1,1)` by a finite list of
coordinate Vieta moves.

No uniqueness of paths or numerical Markov labels is asserted.
-/

namespace LeanFrontier.MarkovTree

private def Positive (s : State) : Prop :=
  0 < s.x ∧ 0 < s.y ∧ 0 < s.z

private def weight (s : State) : ℕ :=
  Int.toNat (s.x + s.y + s.z)

private theorem permuted_isSolution
    {x y z a b c : ℤ}
    (h : MarkovEquation.IsSolution x y z)
    (hp : a = x ∧ b = y ∧ c = z ∨
          a = x ∧ b = z ∧ c = y ∨
          a = y ∧ b = x ∧ c = z ∨
          a = y ∧ b = z ∧ c = x ∨
          a = z ∧ b = x ∧ c = y ∨
          a = z ∧ b = y ∧ c = x) :
    MarkovEquation.IsSolution a b c := by
  rcases hp with hxyz | hxzy | hyxz | hyzx | hzxy | hzyx
  all_goals
    rcases ‹_ ∧ _ ∧ _› with ⟨rfl, rfl, rfl⟩
    unfold MarkovEquation.IsSolution at h ⊢
    nlinarith

private theorem exists_descending_move
    {s : State}
    (hpos : Positive s)
    (hsol : s.IsSolution)
    (hne : s ≠ ⟨1, 1, 1⟩) :
    ∃ m : Move,
      Positive (move m s) ∧
      (move m s).IsSolution ∧
      (move m s).x + (move m s).y + (move m s).z < s.x + s.y + s.z := by
  rcases s with ⟨x, y, z⟩
  change 0 < x ∧ 0 < y ∧ 0 < z at hpos
  rcases hpos with ⟨hx, hy, hz⟩
  change MarkovEquation.IsSolution x y z at hsol
  have hne' : ¬ (x = 1 ∧ y = 1 ∧ z = 1) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact hne rfl

  by_cases hxy : x ≤ y
  · by_cases hyz : y ≤ z
    · have hj :=
        jump_descends_ordered_positive hx hxy hyz hsol hne'
      refine ⟨.third, ?_, move_isSolution .third hsol, ?_⟩
      · simpa [Positive, move] using And.intro hx (And.intro hy hj.1)
      · simp only [move]
        linarith [hj.2.2]
    · have hzy : z < y := lt_of_not_ge hyz
      by_cases hxz : x ≤ z
      · have hperm : MarkovEquation.IsSolution x z y :=
          permuted_isSolution hsol (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
        have hj :=
          jump_descends_ordered_positive hx hxz (le_of_lt hzy) hperm (by
            rintro ⟨hx1, hz1, hy1⟩
            exact hne' ⟨hx1, hy1, hz1⟩)
        refine ⟨.second, ?_, move_isSolution .second hsol, ?_⟩
        · simpa [Positive, move] using And.intro hx (And.intro hj.1 hz)
        · simp only [move]
          linarith [hj.2.2]
      · have hzx : z < x := lt_of_not_ge hxz
        have hperm : MarkovEquation.IsSolution z x y :=
          permuted_isSolution hsol (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
        have hj :=
          jump_descends_ordered_positive hz (le_of_lt hzx) (le_trans (le_of_lt hzx) hxy)
            hperm (by
              rintro ⟨hz1, hx1, hy1⟩
              exact hne' ⟨hx1, hy1, hz1⟩)
        have hswap :
            MarkovEquation.jump z x y = MarkovEquation.jump x z y := by
          unfold MarkovEquation.jump
          ring
        have hjpos : 0 < MarkovEquation.jump x z y := by
          rw [← hswap]
          exact hj.1
        have hjlt : MarkovEquation.jump x z y < y := by
          rw [← hswap]
          exact hj.2.2
        refine ⟨.second, ?_, move_isSolution .second hsol, ?_⟩
        · simpa [Positive, move] using And.intro hx (And.intro hjpos hz)
        · simp only [move]
          linarith
  · have hyx : y < x := lt_of_not_ge hxy
    by_cases hxz : x ≤ z
    · have hperm : MarkovEquation.IsSolution y x z :=
        permuted_isSolution hsol (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      have hj :=
        jump_descends_ordered_positive hy (le_of_lt hyx) hxz hperm (by
          rintro ⟨hy1, hx1, hz1⟩
          exact hne' ⟨hx1, hy1, hz1⟩)
      have hswap :
          MarkovEquation.jump y x z = MarkovEquation.jump x y z := by
        unfold MarkovEquation.jump
        ring
      have hjpos : 0 < MarkovEquation.jump x y z := by
        rw [← hswap]
        exact hj.1
      have hjlt : MarkovEquation.jump x y z < z := by
        rw [← hswap]
        exact hj.2.2
      refine ⟨.third, ?_, move_isSolution .third hsol, ?_⟩
      · simpa [Positive, move] using And.intro hx (And.intro hy hjpos)
      · simp only [move]
        linarith
    · have hzx : z < x := lt_of_not_ge hxz
      by_cases hyz : y ≤ z
      · have hperm : MarkovEquation.IsSolution y z x :=
          permuted_isSolution hsol (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
        have hj :=
          jump_descends_ordered_positive hy hyz (le_of_lt hzx) hperm (by
            rintro ⟨hy1, hz1, hx1⟩
            exact hne' ⟨hx1, hy1, hz1⟩)
        have hjpos : 0 < MarkovEquation.jump y z x := hj.1
        have hjlt : MarkovEquation.jump y z x < x := hj.2.2
        refine ⟨.first, ?_, move_isSolution .first hsol, ?_⟩
        · simpa [Positive, move] using And.intro hjpos (And.intro hy hz)
        · simp only [move]
          linarith
      · have hzy : z < y := lt_of_not_ge hyz
        have hperm : MarkovEquation.IsSolution z y x :=
          permuted_isSolution hsol (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))
        have hj :=
          jump_descends_ordered_positive hz (le_of_lt hzy)
            (le_trans (le_of_lt hzy) (le_of_lt hyx)) hperm (by
              rintro ⟨hz1, hy1, hx1⟩
              exact hne' ⟨hx1, hy1, hz1⟩)
        have hswap :
            MarkovEquation.jump z y x = MarkovEquation.jump y z x := by
          unfold MarkovEquation.jump
          ring
        have hjpos : 0 < MarkovEquation.jump y z x := by
          rw [← hswap]
          exact hj.1
        have hjlt : MarkovEquation.jump y z x < x := by
          rw [← hswap]
          exact hj.2.2
        refine ⟨.first, ?_, move_isSolution .first hsol, ?_⟩
        · simpa [Positive, move] using And.intro hjpos (And.intro hy hz)
        · simp only [move]
          linarith

private theorem exists_walk_to_root_aux :
    ∀ N : ℕ, ∀ s : State,
      weight s = N →
      (Positive s ∧ s.IsSolution) →
      ∃ path : List Move, walk path s = ⟨1, 1, 1⟩ := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro s hweight hs
      rcases hs with ⟨hpos, hsol⟩
      by_cases hroot : s = ⟨1, 1, 1⟩
      · subst s
        exact ⟨[], rfl⟩
      · obtain ⟨m, hpos', hsol', hsum⟩ :=
          exists_descending_move hpos hsol hroot
        let s' := move m s
        have hsum_pos : 0 < s.x + s.y + s.z := by
          rcases hpos with ⟨hx, hy, hz⟩
          linarith
        have hweight_lt : weight s' < weight s := by
          unfold weight
          exact (Int.toNat_lt_toNat hsum_pos).2 hsum
        have hN' : weight s' < N := by
          simpa [hweight] using hweight_lt
        obtain ⟨path, hpath⟩ :=
          ih (weight s') hN' s' rfl ⟨hpos', hsol'⟩
        refine ⟨m :: path, ?_⟩
        simpa [walk, s'] using hpath

/-- Every positive integer solution of the Markov equation is reachable from the root
`(1,1,1)` by a finite sequence of coordinate Vieta moves.

This is an existence/normalization theorem only: it does not assert uniqueness of the path,
nor injectivity of any coordinate or Markov-number label. -/
theorem exists_walk_from_root_of_positive_solution
    (s : State)
    (hx : 0 < s.x) (hy : 0 < s.y) (hz : 0 < s.z)
    (hsol : s.IsSolution) :
    ∃ path : List Move, walk path ⟨1, 1, 1⟩ = s := by
  obtain ⟨path, hpath⟩ :=
    exists_walk_to_root_aux (weight s) s rfl ⟨⟨hx, hy, hz⟩, hsol⟩
  refine ⟨path.reverse, ?_⟩
  have hrev := walk_reverse path s
  rw [hpath] at hrev
  exact hrev

end LeanFrontier.MarkovTree
