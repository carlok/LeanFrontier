import LeanFrontier.NumberTheory.MarkovTree.Reachability
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-!
# Pairwise coprimality of positive Markov triples

Every positive integer Markov triple is pairwise coprime.  Rather than prove this
by a separate prime-divisibility argument, this module uses the accepted global
Markov-tree structure.

The root `(1,1,1)` is pairwise coprime.  A coordinate Vieta move replaces one
coordinate by `3xy - z`, and elementary coprimality identities show that this
replacement preserves the gcd with each untouched coordinate.  Hence pairwise
coprimality is invariant under every finite Markov-tree walk.

The accepted reachability theorem then transports the invariant from the root
to every positive Markov solution.
-/

namespace LeanFrontier.MarkovTree

/-- The three coordinates of a bundled Markov state are pairwise coprime. -/
def State.PairwiseCoprime (s : State) : Prop :=
  IsCoprime s.x s.y ∧ IsCoprime s.x s.z ∧ IsCoprime s.y s.z

/-- A single Vieta coordinate move preserves pairwise coprimality.

This statement is purely algebraic and does not require the Markov equation:
replacing one coordinate by `3` times the product of the other two minus that
coordinate leaves its gcd with either untouched coordinate unchanged. -/
theorem pairwiseCoprime_move (m : Move) {s : State}
    (h : s.PairwiseCoprime) :
    (move m s).PairwiseCoprime := by
  rcases s with ⟨x, y, z⟩
  rcases h with ⟨hxy, hxz, hyz⟩
  cases m with
  | first =>
      change
        IsCoprime (MarkovEquation.jump y z x) y ∧
          IsCoprime (MarkovEquation.jump y z x) z ∧
          IsCoprime y z
      refine ⟨?_, ?_, hyz⟩
      · have hcop :
            IsCoprime ((3 * z) * y - x) y :=
          (IsCoprime.mul_sub_right_left_iff).2 hxy
        simpa [MarkovEquation.jump, mul_assoc, mul_comm, mul_left_comm] using hcop
      · have hcop :
            IsCoprime ((3 * y) * z - x) z :=
          (IsCoprime.mul_sub_right_left_iff).2 hxz
        simpa [MarkovEquation.jump, mul_assoc, mul_comm, mul_left_comm] using hcop
  | second =>
      change
        IsCoprime x (MarkovEquation.jump x z y) ∧
          IsCoprime x z ∧
          IsCoprime (MarkovEquation.jump x z y) z
      refine ⟨?_, hxz, ?_⟩
      · have hcop :
            IsCoprime x ((3 * z) * x - y) :=
          (IsCoprime.mul_sub_right_right_iff).2 hxy
        simpa [MarkovEquation.jump, mul_assoc, mul_comm, mul_left_comm] using hcop
      · have hcop :
            IsCoprime ((3 * x) * z - y) z :=
          (IsCoprime.mul_sub_right_left_iff).2 hyz
        simpa [MarkovEquation.jump, mul_assoc, mul_comm, mul_left_comm] using hcop
  | third =>
      change
        IsCoprime x y ∧
          IsCoprime x (MarkovEquation.jump x y z) ∧
          IsCoprime y (MarkovEquation.jump x y z)
      refine ⟨hxy, ?_, ?_⟩
      · have hcop :
            IsCoprime x ((3 * y) * x - z) :=
          (IsCoprime.mul_sub_right_right_iff).2 hxz
        simpa [MarkovEquation.jump, mul_assoc, mul_comm, mul_left_comm] using hcop
      · have hcop :
            IsCoprime y ((3 * x) * y - z) :=
          (IsCoprime.mul_sub_right_right_iff).2 hyz
        simpa [MarkovEquation.jump, mul_assoc, mul_comm, mul_left_comm] using hcop

/-- Pairwise coprimality is preserved by every finite Markov-tree walk. -/
theorem pairwiseCoprime_walk (path : List Move) {s : State}
    (h : s.PairwiseCoprime) :
    (walk path s).PairwiseCoprime := by
  induction path generalizing s with
  | nil =>
      simpa [walk] using h
  | cons m path ih =>
      simp only [walk]
      exact ih (pairwiseCoprime_move m h)

/-- Every positive integer solution of the Markov equation has pairwise coprime
coordinates. -/
theorem pairwiseCoprime_of_positive_solution
    (s : State)
    (hx : 0 < s.x) (hy : 0 < s.y) (hz : 0 < s.z)
    (hsol : s.IsSolution) :
    s.PairwiseCoprime := by
  obtain ⟨path, hpath⟩ :=
    exists_walk_from_root_of_positive_solution s hx hy hz hsol
  have hroot : (State.mk 1 1 1).PairwiseCoprime := by
    norm_num [State.PairwiseCoprime]
  have hwalk :=
    pairwiseCoprime_walk path hroot
  rw [hpath] at hwalk
  exact hwalk

/-- In particular, every accepted oriented Markov node has pairwise coprime
coordinates. -/
theorem OrientedNode.pairwiseCoprime (n : OrientedNode) :
    n.state.PairwiseCoprime := by
  exact pairwiseCoprime_of_positive_solution
    n.state n.positive.1 n.positive.2.1 n.positive.2.2 n.solution

end LeanFrontier.MarkovTree
