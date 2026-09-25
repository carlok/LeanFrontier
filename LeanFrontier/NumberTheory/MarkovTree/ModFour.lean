import LeanFrontier.NumberTheory.MarkovTree.Reachability
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Modulo-four pattern of positive Markov triples

Every positive Markov triple is reached from `(1,1,1)` by Vieta moves.  Modulo four, those
moves preserve a very small set of residue patterns:

* `(1,1,1)`;
* `(2,1,1)`;
* `(1,2,1)`;
* `(1,1,2)`.

Thus every coordinate is congruent to either one or two modulo four, and at most one coordinate
has residue two.  In particular, if a specified coordinate is even, then that coordinate is
`2 mod 4` and the other two are `1 mod 4`.

This elementary invariant is useful in the even part of classical partial Markov-uniqueness
arguments.
-/

namespace LeanFrontier.MarkovTree

private theorem modFourPattern_move (m : Move) {s : State}
    (h :
      (((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 1) ∨
       ((s.x : ZMod 4) = 2 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 1) ∨
       ((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 2 ∧ (s.z : ZMod 4) = 1) ∨
       ((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 2))) :
    ((((move m s).x : ZMod 4) = 1 ∧
        ((move m s).y : ZMod 4) = 1 ∧
        ((move m s).z : ZMod 4) = 1) ∨
     (((move m s).x : ZMod 4) = 2 ∧
        ((move m s).y : ZMod 4) = 1 ∧
        ((move m s).z : ZMod 4) = 1) ∨
     (((move m s).x : ZMod 4) = 1 ∧
        ((move m s).y : ZMod 4) = 2 ∧
        ((move m s).z : ZMod 4) = 1) ∨
     (((move m s).x : ZMod 4) = 1 ∧
        ((move m s).y : ZMod 4) = 1 ∧
        ((move m s).z : ZMod 4) = 2) := by
  rcases s with ⟨x, y, z⟩
  rcases h with h | h | h | h <;>
    rcases h with ⟨hx, hy, hz⟩ <;>
    cases m <;>
    simp [move, MarkovEquation.jump, hx, hy, hz] <;>
    norm_num

private theorem modFourPattern_walk (path : List Move) {s : State}
    (h :
      (((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 1) ∨
       ((s.x : ZMod 4) = 2 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 1) ∨
       ((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 2 ∧ (s.z : ZMod 4) = 1) ∨
       ((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 2))) :
    ((((walk path s).x : ZMod 4) = 1 ∧
        ((walk path s).y : ZMod 4) = 1 ∧
        ((walk path s).z : ZMod 4) = 1) ∨
     (((walk path s).x : ZMod 4) = 2 ∧
        ((walk path s).y : ZMod 4) = 1 ∧
        ((walk path s).z : ZMod 4) = 1) ∨
     (((walk path s).x : ZMod 4) = 1 ∧
        ((walk path s).y : ZMod 4) = 2 ∧
        ((walk path s).z : ZMod 4) = 1) ∨
     (((walk path s).x : ZMod 4) = 1 ∧
        ((walk path s).y : ZMod 4) = 1 ∧
        ((walk path s).z : ZMod 4) = 2) := by
  induction path generalizing s with
  | nil =>
      simpa [walk] using h
  | cons m path ih =>
      simp only [walk]
      exact ih (modFourPattern_move m h)

/-- Every positive integer Markov triple has, modulo four, either residue pattern
`(1,1,1)` or a permutation of `(2,1,1)`. -/
theorem modFourPattern_of_positive_solution
    (s : State)
    (hx : 0 < s.x) (hy : 0 < s.y) (hz : 0 < s.z)
    (hsol : s.IsSolution) :
    (((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 1) ∨
     ((s.x : ZMod 4) = 2 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 1) ∨
     ((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 2 ∧ (s.z : ZMod 4) = 1) ∨
     ((s.x : ZMod 4) = 1 ∧ (s.y : ZMod 4) = 1 ∧ (s.z : ZMod 4) = 2) := by
  obtain ⟨path, hpath⟩ :=
    exists_walk_from_root_of_positive_solution s hx hy hz hsol
  have hroot :
      ((((State.mk 1 1 1).x : ZMod 4) = 1 ∧
          ((State.mk 1 1 1).y : ZMod 4) = 1 ∧
          ((State.mk 1 1 1).z : ZMod 4) = 1) ∨
       (((State.mk 1 1 1).x : ZMod 4) = 2 ∧
          ((State.mk 1 1 1).y : ZMod 4) = 1 ∧
          ((State.mk 1 1 1).z : ZMod 4) = 1) ∨
       (((State.mk 1 1 1).x : ZMod 4) = 1 ∧
          ((State.mk 1 1 1).y : ZMod 4) = 2 ∧
          ((State.mk 1 1 1).z : ZMod 4) = 1) ∨
       (((State.mk 1 1 1).x : ZMod 4) = 1 ∧
          ((State.mk 1 1 1).y : ZMod 4) = 1 ∧
          ((State.mk 1 1 1).z : ZMod 4) = 2) := by
    norm_num
  have hwalk := modFourPattern_walk path hroot
  rw [hpath] at hwalk
  exact hwalk

/-- If the third coordinate of a positive Markov triple is even, then it is `2 mod 4`, while
the other two coordinates are both `1 mod 4`. -/
theorem modFour_of_even_third_coordinate
    {x y z : ℤ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsol : MarkovEquation.IsSolution x y z)
    (heven : (2 : ℤ) ∣ z) :
    (x : ZMod 4) = 1 ∧ (y : ZMod 4) = 1 ∧ (z : ZMod 4) = 2 := by
  have hpattern :=
    modFourPattern_of_positive_solution
      (State.mk x y z) hx hy hz (by
        simpa [State.IsSolution] using hsol)
  have hz0 : (z : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact heven
  have hz_ne_one : (z : ZMod 4) ≠ 1 := by
    intro hz1
    have hmap :=
      congrArg (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)) hz1
    simpa [hz0] using hmap
  rcases hpattern with h | h | h | h
  · exact (hz_ne_one h.2.2).elim
  · exact (hz_ne_one h.2.2).elim
  · exact (hz_ne_one h.2.2).elim
  · exact h

end LeanFrontier.MarkovTree
