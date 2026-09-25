import LeanFrontier.NumberTheory.MarkovTree.Injectivity
import Mathlib.Tactic

/-!
# Markov-number labels on the oriented Markov tree

The accepted oriented Markov tree stores, at every node, a distinguished coordinate move
`back` which strictly decreases the sum of the coordinates.  For uniqueness questions this
contains more information than has previously been exposed: the coordinate selected by `back`
is in fact the unique largest coordinate of the Markov triple.

This module packages that fact as the numerical label of an oriented node.

* `State.coordinate` reads the coordinate selected by a `Move`.
* `OrientedNode.markovNumber` is the coordinate selected by the descending back edge.
* `markovNumber_eq_max` proves that this label is exactly the maximum coordinate.
* `markovNumber_lt_child` proves that it strictly increases along either forward edge.
* `sternMarkovNumber` transports the label to the canonical Stern-Brocot-indexed branch.

The final depth bound is intentionally coarse, but useful: a path of length `d` has Markov
number at least `d + 2`.  Consequently any search for a collision below a fixed Markov number
only needs finitely many tree levels.

These results are structural machinery only.  Strict growth along ancestor chains does not rule
out equal labels on incomparable branches, which is precisely where the Frobenius/Markov
uniqueness problem remains.
-/

namespace LeanFrontier.MarkovTree

/-- Read the coordinate of a bundled Markov state selected by a coordinate move. -/
def State.coordinate (s : State) : Move → ℤ
  | .first => s.x
  | .second => s.y
  | .third => s.z

/-- The Markov-number label of an oriented node: its coordinate on the descending back edge. -/
def OrientedNode.markovNumber (n : OrientedNode) : ℤ :=
  n.state.coordinate n.back

private theorem descending_jump_coordinate_is_largest
    {a b c : ℤ}
    (hb : 0 < b) (hc : 0 < c)
    (hdesc : MarkovEquation.jump b c a < a) :
    b < a ∧ c < a := by
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  have hbc_b : b ≤ b * c := by
    have h := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hc1)
    nlinarith
  have hbc_c : c ≤ b * c := by
    have h := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hb1)
    nlinarith
  unfold MarkovEquation.jump at hdesc
  constructor <;> nlinarith

/-- Moving one coordinate leaves each of the other two coordinates unchanged. -/
theorem coordinate_move_of_ne (s : State) {changed observed : Move}
    (hne : observed ≠ changed) :
    (move changed s).coordinate observed = s.coordinate observed := by
  rcases s with ⟨x, y, z⟩
  cases changed <;> cases observed <;>
    simp [State.coordinate, move] at hne ⊢

/-- At an oriented Markov node, the coordinate selected by any move other than `back` is
strictly smaller than the Markov-number coordinate selected by `back`.

Thus the orientation invariant already singles out a unique largest coordinate. -/
theorem coordinate_lt_markovNumber_of_ne_back
    (n : OrientedNode) {m : Move} (hne : m ≠ n.back) :
    n.state.coordinate m < n.markovNumber := by
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  rcases hpos with ⟨hx, hy, hz⟩
  cases back with
  | first =>
      have hj : MarkovEquation.jump y z x < x := by
        simp only [State.mass, move] at hdesc
        linarith
      have hlarge := descending_jump_coordinate_is_largest hy hz hj
      cases m with
      | first =>
          exact (hne rfl).elim
      | second =>
          simpa [State.coordinate, OrientedNode.markovNumber] using hlarge.1
      | third =>
          simpa [State.coordinate, OrientedNode.markovNumber] using hlarge.2
  | second =>
      have hj : MarkovEquation.jump x z y < y := by
        simp only [State.mass, move] at hdesc
        linarith
      have hlarge := descending_jump_coordinate_is_largest hx hz hj
      cases m with
      | first =>
          simpa [State.coordinate, OrientedNode.markovNumber] using hlarge.1
      | second =>
          exact (hne rfl).elim
      | third =>
          simpa [State.coordinate, OrientedNode.markovNumber] using hlarge.2
  | third =>
      have hj : MarkovEquation.jump x y z < z := by
        simp only [State.mass, move] at hdesc
        linarith
      have hlarge := descending_jump_coordinate_is_largest hx hy hj
      cases m with
      | first =>
          simpa [State.coordinate, OrientedNode.markovNumber] using hlarge.1
      | second =>
          simpa [State.coordinate, OrientedNode.markovNumber] using hlarge.2
      | third =>
          exact (hne rfl).elim

/-- The oriented-node Markov-number label is exactly the maximum of its three coordinates.

In particular, the `back` field does not introduce an arbitrary choice of numerical label: its
coordinate is forced by the underlying positive Markov state. -/
theorem markovNumber_eq_max (n : OrientedNode) :
    n.markovNumber = max n.state.x (max n.state.y n.state.z) := by
  have hle (m : Move) : n.state.coordinate m ≤ n.markovNumber := by
    by_cases hm : m = n.back
    · subst m
      rfl
    · exact le_of_lt (coordinate_lt_markovNumber_of_ne_back n hm)
  apply le_antisymm
  · cases hback : n.back with
    | first =>
        simp only [OrientedNode.markovNumber, hback, State.coordinate]
        exact le_max_left _ _
    | second =>
        simp only [OrientedNode.markovNumber, hback, State.coordinate]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
    | third =>
        simp only [OrientedNode.markovNumber, hback, State.coordinate]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
  · apply max_le
    · simpa [State.coordinate] using hle .first
    · apply max_le
      · simpa [State.coordinate] using hle .second
      · simpa [State.coordinate] using hle .third

/-- The Markov-number label strictly increases along either forward edge of the oriented tree.

This proves ancestor-chain injectivity of the numerical label.  Possible collisions are therefore
confined to incomparable branches. -/
theorem markovNumber_lt_child (n : OrientedNode) (dir : Bool) :
    n.markovNumber < (child n dir).markovNumber := by
  have hforward : n.back ≠ forwardMove n.back dir := by
    cases hback : n.back <;> cases dir <;>
      simp [forwardMove, hback]
  have hne : n.back ≠ (child n dir).back := by
    simpa [child] using hforward
  have hcoord :
      (child n dir).state.coordinate n.back = n.state.coordinate n.back := by
    change
      (move (forwardMove n.back dir) n.state).coordinate n.back =
        n.state.coordinate n.back
    exact coordinate_move_of_ne n.state hforward
  have hdom :=
    coordinate_lt_markovNumber_of_ne_back (child n dir) hne
  rw [hcoord] at hdom
  simpa [OrientedNode.markovNumber] using hdom

/-- The Markov-number label on the canonical Stern-Brocot-indexed branch. -/
def sternMarkovNumber (path : List Bool) : ℤ :=
  (sternNode path).markovNumber

/-- Prepending either Stern-Brocot direction moves to a child with strictly larger Markov number. -/
theorem sternMarkovNumber_lt_cons (dir : Bool) (path : List Bool) :
    sternMarkovNumber path < sternMarkovNumber (dir :: path) := by
  change
    (sternNode path).markovNumber <
      (sternNode (dir :: path)).markovNumber
  rw [sternNode_cons]
  exact markovNumber_lt_child (sternNode path) dir

/-- A canonical path of length `d` has Markov number at least `d + 2`.

The bound is deliberately elementary; its useful consequence is finiteness of the tree depth
that must be inspected below any fixed candidate Markov number. -/
theorem pathLength_add_two_le_sternMarkovNumber (path : List Bool) :
    (path.length : ℤ) + 2 ≤ sternMarkovNumber path := by
  induction path with
  | nil =>
      norm_num [sternMarkovNumber, sternNode, follow, orientedRoot,
        OrientedNode.markovNumber, State.coordinate]
  | cons dir path ih =>
      have hstep := sternMarkovNumber_lt_cons dir path
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

end LeanFrontier.MarkovTree
