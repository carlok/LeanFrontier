import LeanFrontier.NumberTheory.MarkovTree.Paths
import Mathlib.Tactic

/-!
# An oriented binary Markov tree

The accepted Markov path API presents the positive Markov graph through three involutive
coordinate moves.  As an undirected graph this is the right local picture, but it is not yet the
right interface for comparison with binary rational trees such as Stern-Brocot: after an edge has
been chosen, one of the three moves is the edge back to the parent and the other two are the
forward choices.

This module records exactly that orientation.

An `OrientedNode` is a positive Markov solution together with a distinguished Vieta move
`back` whose application strictly lowers the sum of the coordinates.  The binary root is
`(1,1,2)`, with the third-coordinate move pointing back to `(1,1,1)`.

For every oriented node, the two moves different from `back` strictly increase the coordinate
sum.  Applying either one therefore produces a new oriented node whose distinguished back move is
the move just taken.  Boolean paths consequently encode non-backtracking walks in the accepted
three-move Markov graph.

This is representation infrastructure only.  In particular, it does not claim that two different
Boolean paths reach different numerical Markov triples, and it makes no injectivity claim about
Markov-number labels.
-/

namespace LeanFrontier.MarkovTree

/-- All three coordinates of a bundled Markov state are positive. -/
def State.Positive (s : State) : Prop :=
  0 < s.x ∧ 0 < s.y ∧ 0 < s.z

/-- The integer sum of the three coordinates of a Markov state. -/
def State.mass (s : State) : ℤ :=
  s.x + s.y + s.z

/-- A positive Markov state together with the coordinate move pointing toward its parent.

The invariant says that applying `back` strictly lowers the coordinate sum. -/
structure OrientedNode where
  state : State
  back : Move
  positive : state.Positive
  solution : state.IsSolution
  back_descends : (move back state).mass < state.mass

/-- The two forward choices at a node: exactly the two coordinate moves other than `back`. -/
def forwardMove : Move → Bool → Move
  | .first, false => .second
  | .first, true => .third
  | .second, false => .first
  | .second, true => .third
  | .third, false => .first
  | .third, true => .second

private theorem forwardMove_ne_back (back : Move) (dir : Bool) :
    forwardMove back dir ≠ back := by
  cases back <;> cases dir <;> simp [forwardMove]

private theorem forwardMove_injective (back : Move) :
    Function.Injective (forwardMove back) := by
  intro a b h
  cases back <;> cases a <;> cases b <;> simp [forwardMove] at h ⊢

/-- Every Vieta coordinate move preserves positivity of a positive Markov solution. -/
private theorem move_positive (m : Move) {s : State}
    (hpos : s.Positive) (hsol : s.IsSolution) :
    (move m s).Positive := by
  rcases s with ⟨x, y, z⟩
  rcases hpos with ⟨hx, hy, hz⟩
  change MarkovEquation.IsSolution x y z at hsol
  cases m with
  | first =>
      have hp : MarkovEquation.IsSolution y z x := by
        unfold MarkovEquation.IsSolution at hsol ⊢
        nlinarith
      change 0 < MarkovEquation.jump y z x ∧ 0 < y ∧ 0 < z
      exact ⟨MarkovEquation.jump_pos hy hx hp, hy, hz⟩
  | second =>
      have hp : MarkovEquation.IsSolution x z y := by
        unfold MarkovEquation.IsSolution at hsol ⊢
        nlinarith
      change 0 < x ∧ 0 < MarkovEquation.jump x z y ∧ 0 < z
      exact ⟨hx, MarkovEquation.jump_pos hx hy hp, hz⟩
  | third =>
      change 0 < x ∧ 0 < y ∧ 0 < MarkovEquation.jump x y z
      exact ⟨hx, hy, MarkovEquation.jump_pos hx hz hsol⟩

/-- If jumping coordinate `a` decreases it in a positive triple, then jumping either of the
other two coordinates strictly increases that coordinate. -/
private theorem other_jumps_ascend
    {a b c : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdesc : MarkovEquation.jump b c a < a) :
    b < MarkovEquation.jump a c b ∧
      c < MarkovEquation.jump a b c := by
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  have ha1 : 1 ≤ a := by omega

  have hbc_b : b ≤ b * c := by
    have h := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hc1)
    nlinarith
  have hbc_c : c ≤ b * c := by
    have h := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hb1)
    nlinarith

  have hb_lt_a : b < a := by
    unfold MarkovEquation.jump at hdesc
    nlinarith
  have hc_lt_a : c < a := by
    unfold MarkovEquation.jump at hdesc
    nlinarith

  have hac_a : a ≤ a * c := by
    have h := mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hc1)
    nlinarith
  have hab_a : a ≤ a * b := by
    have h := mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hb1)
    nlinarith

  constructor <;> unfold MarkovEquation.jump <;> nlinarith

/-- At an oriented node, either of the two non-backtracking moves strictly increases the
coordinate sum. -/
private theorem forwardMove_ascends (n : OrientedNode) (dir : Bool) :
    n.state.mass < (move (forwardMove n.back dir) n.state).mass := by
  rcases n with ⟨⟨x, y, z⟩, back, hpos, hsol, hdesc⟩
  rcases hpos with ⟨hx, hy, hz⟩
  cases back with
  | first =>
      have hj : MarkovEquation.jump y z x < x := by
        simp only [State.mass, move] at hdesc
        linarith
      have h := other_jumps_ascend hx hy hz hj
      cases dir with
      | false =>
          simp only [forwardMove, State.mass, move]
          linarith [h.1]
      | true =>
          simp only [forwardMove, State.mass, move]
          linarith [h.2]
  | second =>
      have hj : MarkovEquation.jump x z y < y := by
        simp only [State.mass, move] at hdesc
        linarith
      have h := other_jumps_ascend hy hx hz hj
      have hzasc : z < MarkovEquation.jump x y z := by
        simpa [MarkovEquation.jump, mul_comm] using h.2
      cases dir with
      | false =>
          simp only [forwardMove, State.mass, move]
          linarith [h.1]
      | true =>
          simp only [forwardMove, State.mass, move]
          linarith [hzasc]
  | third =>
      have hj : MarkovEquation.jump x y z < z := by
        simp only [State.mass, move] at hdesc
        linarith
      have h := other_jumps_ascend hz hx hy hj
      have hxasc : x < MarkovEquation.jump y z x := by
        simpa [MarkovEquation.jump, mul_comm] using h.1
      have hyasc : y < MarkovEquation.jump x z y := by
        simpa [MarkovEquation.jump, mul_comm] using h.2
      cases dir with
      | false =>
          simp only [forwardMove, State.mass, move]
          linarith [hxasc]
      | true =>
          simp only [forwardMove, State.mass, move]
          linarith [hyasc]

/-- The binary root: `(1,1,2)`, oriented toward the exceptional Markov root `(1,1,1)`. -/
def orientedRoot : OrientedNode where
  state := ⟨1, 1, 2⟩
  back := .third
  positive := by
    norm_num [State.Positive]
  solution := by
    unfold State.IsSolution MarkovEquation.IsSolution
    norm_num
  back_descends := by
    norm_num [State.mass, move, MarkovEquation.jump]

/-- Follow one of the two forward edges of an oriented Markov node. -/
def child (n : OrientedNode) (dir : Bool) : OrientedNode :=
  let m := forwardMove n.back dir
  { state := move m n.state
    back := m
    positive := move_positive m n.positive n.solution
    solution := move_isSolution m n.solution
    back_descends := by
      have hinc := forwardMove_ascends n dir
      change (move m (move m n.state)).mass < (move m n.state).mass
      rw [move_involutive]
      exact hinc }

/-- A move list is non-backtracking relative to an incoming edge when its first move is not that
edge and every subsequent move differs from the move immediately before it. -/
def NonBacktrackingFrom : Move → List Move → Prop
  | _, [] => True
  | back, m :: path => m ≠ back ∧ NonBacktrackingFrom m path

/-- Follow a Boolean path through the oriented binary Markov tree. -/
def follow (n : OrientedNode) : List Bool → OrientedNode
  | [] => n
  | dir :: path => follow (child n dir) path

/-- Erase a Boolean oriented path to the corresponding list of accepted coordinate `Move`s. -/
def pathMoves (n : OrientedNode) : List Bool → List Move
  | [] => []
  | dir :: path =>
      forwardMove n.back dir :: pathMoves (child n dir) path

/-- Boolean paths erase to non-backtracking move lists in the accepted three-move Markov graph. -/
theorem pathMoves_nonBacktracking (n : OrientedNode) (path : List Bool) :
    NonBacktrackingFrom n.back (pathMoves n path) := by
  induction path generalizing n with
  | nil =>
      simp [pathMoves, NonBacktrackingFrom]
  | cons dir path ih =>
      constructor
      · exact forwardMove_ne_back n.back dir
      · simpa [pathMoves, child] using ih (n := child n dir)

/-- The state reached by the oriented binary path is exactly the state reached by erasing it to
the accepted `MarkovTree.walk` representation. -/
theorem follow_state_eq_walk (n : OrientedNode) (path : List Bool) :
    (follow n path).state = walk (pathMoves n path) n.state := by
  induction path generalizing n with
  | nil =>
      rfl
  | cons dir path ih =>
      simp only [follow, pathMoves, walk]
      simpa [child] using ih (n := child n dir)

/-- Distinct Boolean paths have distinct erased move sequences.

This is injectivity of the *path representation*, not injectivity of the resulting Markov state
or of any numerical Markov label. -/
theorem pathMoves_injective (n : OrientedNode) :
    Function.Injective (pathMoves n) := by
  intro p
  induction p generalizing n with
  | nil =>
      intro q h
      cases q with
      | nil => rfl
      | cons dir q =>
          simp [pathMoves] at h
  | cons dir p ih =>
      intro q h
      cases q with
      | nil =>
          simp [pathMoves] at h
      | cons dir' q =>
          simp only [pathMoves] at h
          have hhead : forwardMove n.back dir = forwardMove n.back dir' :=
            (List.cons.inj h).1
          have hdir : dir = dir' := forwardMove_injective n.back hhead
          subst dir'
          have htail :
              pathMoves (child n dir) p = pathMoves (child n dir) q :=
            (List.cons.inj h).2
          have hpq : p = q := ih (n := child n dir) htail
          subst q
          rfl

end LeanFrontier.MarkovTree
