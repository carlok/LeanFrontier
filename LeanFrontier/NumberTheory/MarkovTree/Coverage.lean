import LeanFrontier.NumberTheory.MarkovTree.Reachability
import LeanFrontier.NumberTheory.MarkovTree.SternBrocot
import Mathlib.Tactic

/-!
# Coverage of positive Markov solutions by the three oriented root branches

The accepted oriented Markov tree chooses the state `(1,1,2)`, whose third-coordinate move
points back to the exceptional root `(1,1,1)`.  This gives one binary branch of the labelled
three-coordinate Markov graph and, through the accepted Stern-Brocot bridge, one copy of the
Stern-Brocot path tree.

For global coverage of labelled positive Markov triples there are three symmetric first moves
out of `(1,1,1)`.  This module packages those three oriented root branches and proves that every
positive Markov solution other than the exceptional root occurs in one of them.

The proof has two independent pieces.

* Every non-backtracking list of coordinate moves from an oriented node has a unique Boolean
  path encoding.  This is the converse to the accepted
  `pathMoves_nonBacktracking` / `pathMoves_injective` results.
* An arbitrary root-to-solution walk supplied by the accepted global reachability theorem can
  be reduced by cancelling adjacent equal involutive moves.  The resulting reduced walk is
  non-backtracking.  Its first move selects one of the three oriented root branches; the
  remaining moves decode uniquely to Boolean choices.

This is an existence/representation theorem for labelled states.  It does not assert uniqueness
of the branch representation, does not identify coordinate-permuted branches, and makes no
injectivity claim about numerical Markov labels.
-/

namespace LeanFrontier.MarkovTree

private theorem exists_forwardDir
    {back m : Move} (hne : m ≠ back) :
    ∃ dir : Bool, forwardMove back dir = m := by
  cases back <;> cases m <;> simp [forwardMove] at hne ⊢

/-- Every non-backtracking coordinate-move list from an oriented node has a unique Boolean path
encoding. -/
theorem existsUnique_pathMoves_of_nonBacktracking
    (n : OrientedNode) {moves : List Move}
    (h : NonBacktrackingFrom n.back moves) :
    ∃! path : List Bool, pathMoves n path = moves := by
  have hexists : ∃ path : List Bool, pathMoves n path = moves := by
    induction moves generalizing n with
    | nil =>
        exact ⟨[], rfl⟩
    | cons m moves ih =>
        rcases h with ⟨hm, htail⟩
        obtain ⟨dir, hdir⟩ := exists_forwardDir hm
        have hchild :
            NonBacktrackingFrom (child n dir).back moves := by
          simpa [child, hdir] using htail
        obtain ⟨path, hpath⟩ := ih (n := child n dir) hchild
        refine ⟨dir :: path, ?_⟩
        simp [pathMoves, hdir, hpath]
  obtain ⟨path, hpath⟩ := hexists
  refine ⟨path, hpath, ?_⟩
  intro other hother
  exact pathMoves_injective n (hother.trans hpath.symm)

/-- The oriented node reached by taking one of the three possible first coordinate moves out of
the exceptional Markov root. -/
def rootBranch : Move → OrientedNode
  | .first =>
      { state := ⟨2, 1, 1⟩
        back := .first
        positive := by
          norm_num [State.Positive]
        solution := by
          norm_num [State.IsSolution, MarkovEquation.IsSolution]
        back_descends := by
          norm_num [State.mass, move, MarkovEquation.jump] }
  | .second =>
      { state := ⟨1, 2, 1⟩
        back := .second
        positive := by
          norm_num [State.Positive]
        solution := by
          norm_num [State.IsSolution, MarkovEquation.IsSolution]
        back_descends := by
          norm_num [State.mass, move, MarkovEquation.jump] }
  | .third => orientedRoot

/-- The state of the branch selected by `m` is exactly the result of applying `m` once to the
exceptional root. -/
theorem rootBranch_state (m : Move) :
    (rootBranch m).state = move m ⟨1, 1, 1⟩ := by
  cases m <;> norm_num [rootBranch, orientedRoot, move, MarkovEquation.jump]

/-- The distinguished back edge of the branch selected by `m` is precisely that first move. -/
theorem rootBranch_back (m : Move) :
    (rootBranch m).back = m := by
  cases m <;> rfl

/-- A node in one of the three labelled root branches, using the accepted Stern-Brocot list
convention: prepending a direction descends one level in the binary tree. -/
def branchNode (initial : Move) (path : List Bool) : OrientedNode :=
  follow (rootBranch initial) path.reverse

/-- The third labelled root branch is exactly the accepted `sternNode` representation. -/
theorem branchNode_third (path : List Bool) :
    branchNode .third path = sternNode path := by
  rfl

private def Reduced : List Move → Prop
  | [] => True
  | m :: moves => NonBacktrackingFrom m moves

private def reduceMoves : List Move → List Move
  | [] => []
  | m :: moves =>
      match reduceMoves moves with
      | [] => [m]
      | n :: rest => if m = n then rest else m :: n :: rest

private theorem reduced_of_nonBacktracking
    {back : Move} {moves : List Move}
    (h : NonBacktrackingFrom back moves) :
    Reduced moves := by
  cases moves with
  | nil =>
      trivial
  | cons m moves =>
      exact h.2

private theorem reduceMoves_reduced (moves : List Move) :
    Reduced (reduceMoves moves) := by
  induction moves with
  | nil =>
      trivial
  | cons m moves ih =>
      cases hred : reduceMoves moves with
      | nil =>
          simp [reduceMoves, hred, Reduced, NonBacktrackingFrom]
      | cons n rest =>
          have ih' : Reduced (n :: rest) := by
            simpa [hred] using ih
          have hnb : NonBacktrackingFrom n rest := ih'
          by_cases hmn : m = n
          · have hrest : Reduced rest :=
              reduced_of_nonBacktracking hnb
            simpa [reduceMoves, hred, hmn] using hrest
          · have hnm : n ≠ m := by
              intro h
              exact hmn h.symm
            simp [reduceMoves, hred, hmn, Reduced, NonBacktrackingFrom, hnm, hnb]

private theorem walk_reduceMoves (moves : List Move) (s : State) :
    walk (reduceMoves moves) s = walk moves s := by
  induction moves generalizing s with
  | nil =>
      rfl
  | cons m moves ih =>
      cases hred : reduceMoves moves with
      | nil =>
          have h := ih (s := move m s)
          simpa [reduceMoves, hred, walk] using h
      | cons n rest =>
          by_cases hmn : m = n
          · subst n
            have h := ih (s := move m s)
            simpa [reduceMoves, hred, walk, move_involutive] using h
          · have h := ih (s := move m s)
            simpa [reduceMoves, hred, hmn, walk] using h

/-- Every positive Markov solution other than `(1,1,1)` belongs to one of the three oriented
binary branches obtained by choosing its first coordinate move from the root.

The Boolean path is written in the same convention as the accepted Stern-Brocot representation.
No uniqueness of `first` or of the resulting numerical state representation is asserted. -/
theorem exists_branchNode_state_of_positive_solution
    (s : State)
    (hx : 0 < s.x) (hy : 0 < s.y) (hz : 0 < s.z)
    (hsol : s.IsSolution)
    (hne : s ≠ ⟨1, 1, 1⟩) :
    ∃ initial : Move, ∃ path : List Bool, (branchNode initial path).state = s := by
  obtain ⟨raw, hraw⟩ :=
    exists_walk_from_root_of_positive_solution s hx hy hz hsol
  have hwalk :=
    walk_reduceMoves raw (⟨1, 1, 1⟩ : State)
  cases hred : reduceMoves raw with
  | nil =>
      have hs : (⟨1, 1, 1⟩ : State) = s := by
        simpa [hred, walk, hraw] using hwalk
      exact (hne hs.symm).elim
  | cons initial moves =>
      have hReduced : Reduced (initial :: moves) := by
        rw [← hred]
        exact reduceMoves_reduced raw
      have hnb : NonBacktrackingFrom (rootBranch initial).back moves := by
        rw [rootBranch_back]
        exact hReduced
      obtain ⟨forwardPath, hpath, _⟩ :=
        existsUnique_pathMoves_of_nonBacktracking (rootBranch initial) hnb
      refine ⟨initial, forwardPath.reverse, ?_⟩
      unfold branchNode
      simp only [List.reverse_reverse]
      calc
        (follow (rootBranch initial) forwardPath).state =
            walk (pathMoves (rootBranch initial) forwardPath) (rootBranch initial).state :=
          follow_state_eq_walk (rootBranch initial) forwardPath
        _ = walk moves (rootBranch initial).state := by rw [hpath]
        _ = walk moves (move initial ⟨1, 1, 1⟩) := by rw [rootBranch_state]
        _ = walk (initial :: moves) ⟨1, 1, 1⟩ := rfl
        _ = walk (reduceMoves raw) ⟨1, 1, 1⟩ := by rw [hred]
        _ = walk raw ⟨1, 1, 1⟩ := hwalk
        _ = s := hraw

end LeanFrontier.MarkovTree
