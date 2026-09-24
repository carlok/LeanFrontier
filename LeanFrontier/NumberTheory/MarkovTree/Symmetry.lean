import LeanFrontier.NumberTheory.MarkovTree.Coverage

/-!
# Cyclic coordinate symmetry of the oriented Markov branches

The accepted coverage theorem presents every non-root positive labelled Markov solution in one of
three oriented binary branches, according to the first coordinate Vieta move taken from
`(1,1,1)`.  The accepted Stern-Brocot bridge is the third-coordinate branch.

Those three labelled branches differ only by cyclic permutation of the three coordinates.  This
module makes that symmetry explicit.

For each possible first move `initial`, `branchPermState initial` is the cyclic coordinate
permutation carrying the canonical third branch to the branch selected by `initial`, and
`branchPermMove initial` is the corresponding permutation of coordinate moves.  The two
permutations commute with a Vieta move and hence with a finite walk.

Rather than trying to transport Boolean left/right directions directly (whose concrete Boolean
encoding depends on the distinguished back edge), we transport the accepted erased move sequence.
Non-backtracking is preserved by the move permutation, and the accepted unique decoder from
`Coverage` then reconstructs a canonical Boolean path.

The final theorem says that every positive Markov solution other than `(1,1,1)` is a cyclic
coordinate permutation of the state attached to some Stern-Brocot path.  This is a representation
theorem modulo coordinate symmetry only.  It makes no injectivity claim about numerical Markov
triples or Markov-number labels.
-/

namespace LeanFrontier.MarkovTree

/-- The cyclic coordinate permutation carrying the canonical third branch to the branch selected
by `initial`.

* `.third` is the identity;
* `.first` sends `(x,y,z)` to `(z,x,y)`;
* `.second` sends `(x,y,z)` to `(y,z,x)`. -/
def branchPermState : Move → State → State
  | .first, s => ⟨s.z, s.x, s.y⟩
  | .second, s => ⟨s.y, s.z, s.x⟩
  | .third, s => s

/-- The corresponding cyclic permutation of coordinate Vieta moves. -/
def branchPermMove : Move → Move → Move
  | .first, .first => .second
  | .first, .second => .third
  | .first, .third => .first
  | .second, .first => .third
  | .second, .second => .first
  | .second, .third => .second
  | .third, m => m

/-- The branch index giving the inverse cyclic coordinate permutation. -/
def inverseBranch : Move → Move
  | .first => .second
  | .second => .first
  | .third => .third

/-- Cyclic permutation of coordinate moves is injective. -/
theorem branchPermMove_injective (initial : Move) :
    Function.Injective (branchPermMove initial) := by
  intro a b h
  cases initial <;> cases a <;> cases b <;> simp [branchPermMove] at h ⊢

/-- Applying the inverse branch move permutation first, then the original one, is the identity. -/
theorem branchPermMove_inverse_left (initial m : Move) :
    branchPermMove initial (branchPermMove (inverseBranch initial) m) = m := by
  cases initial <;> cases m <;> rfl

/-- Applying a branch move permutation first, then its inverse, is the identity. -/
theorem branchPermMove_inverse_right (initial m : Move) :
    branchPermMove (inverseBranch initial) (branchPermMove initial m) = m := by
  cases initial <;> cases m <;> rfl

/-- The inverse branch permutation sends the selected first move back to the canonical third
move. -/
theorem inverseBranch_sends_initial_to_third (initial : Move) :
    branchPermMove (inverseBranch initial) initial = .third := by
  cases initial <;> rfl

/-- The selected branch permutation sends the canonical third move to the selected first move. -/
theorem branchPermMove_third (initial : Move) :
    branchPermMove initial .third = initial := by
  cases initial <;> rfl

/-- The cyclic coordinate permutation commutes with the corresponding permutation of a single
Vieta coordinate move. -/
theorem branchPermState_move (initial m : Move) (s : State) :
    branchPermState initial (move m s) =
      move (branchPermMove initial m) (branchPermState initial s) := by
  rcases s with ⟨x, y, z⟩
  cases initial <;> cases m <;>
    simp [branchPermState, branchPermMove, move, MarkovEquation.jump] <;>
    ring

/-- Cyclic state permutations are mutually inverse under `inverseBranch`. -/
theorem branchPermState_inverse_left (initial : Move) (s : State) :
    branchPermState initial (branchPermState (inverseBranch initial) s) = s := by
  rcases s with ⟨x, y, z⟩
  cases initial <;> rfl

/-- Cyclic state permutations are mutually inverse in the other order as well. -/
theorem branchPermState_inverse_right (initial : Move) (s : State) :
    branchPermState (inverseBranch initial) (branchPermState initial s) = s := by
  rcases s with ⟨x, y, z⟩
  cases initial <;> rfl

/-- The cyclic permutation indexed by `initial` carries the canonical oriented root
`(1,1,2)` to the corresponding labelled root branch. -/
theorem branchPermState_orientedRoot (initial : Move) :
    branchPermState initial orientedRoot.state = (rootBranch initial).state := by
  cases initial <;>
    norm_num [branchPermState, orientedRoot, rootBranch]

/-- Cyclic coordinate symmetry commutes with a finite Markov-tree walk. -/
theorem branchPermState_walk (initial : Move) (moves : List Move) (s : State) :
    branchPermState initial (walk moves s) =
      walk (moves.map (branchPermMove initial)) (branchPermState initial s) := by
  induction moves generalizing s with
  | nil =>
      rfl
  | cons m moves ih =>
      simp only [walk, List.map_cons]
      rw [ih, branchPermState_move]

/-- Permuting every coordinate move in a non-backtracking word preserves non-backtracking. -/
theorem nonBacktracking_map_branchPerm
    (initial back : Move) {moves : List Move}
    (h : NonBacktrackingFrom back moves) :
    NonBacktrackingFrom (branchPermMove initial back)
      (moves.map (branchPermMove initial)) := by
  induction moves generalizing back with
  | nil =>
      trivial
  | cons m moves ih =>
      rcases h with ⟨hne, htail⟩
      simp only [List.map_cons, NonBacktrackingFrom]
      constructor
      · intro heq
        exact hne (branchPermMove_injective initial heq)
      · exact ih (back := m) htail

/-- Every node in any of the three labelled oriented branches is a cyclic coordinate permutation
of a node in the canonical third branch, hence of a `sternNode`.

The Boolean path on the canonical branch is reconstructed by transporting the erased
non-backtracking move word through the inverse coordinate permutation and invoking the accepted
unique decoder. -/
theorem exists_permuted_sternNode_of_branchNode
    (initial : Move) (path : List Bool) :
    ∃ sternPath : List Bool,
      branchPermState initial (sternNode sternPath).state =
        (branchNode initial path).state := by
  let moves := pathMoves (rootBranch initial) path.reverse
  have hnb : NonBacktrackingFrom initial moves := by
    dsimp [moves]
    simpa [rootBranch_back] using
      pathMoves_nonBacktracking (rootBranch initial) path.reverse
  let canonicalMoves := moves.map (branchPermMove (inverseBranch initial))
  have hcanonical :
      NonBacktrackingFrom orientedRoot.back canonicalMoves := by
    have hmap :=
      nonBacktracking_map_branchPerm (inverseBranch initial) initial hnb
    simpa [canonicalMoves, orientedRoot, inverseBranch_sends_initial_to_third] using hmap
  obtain ⟨forwardPath, hencode, _⟩ :=
    existsUnique_pathMoves_of_nonBacktracking orientedRoot hcanonical
  refine ⟨forwardPath.reverse, ?_⟩
  calc
    branchPermState initial (sternNode forwardPath.reverse).state =
        branchPermState initial (follow orientedRoot forwardPath).state := by
          simp [sternNode]
    _ = branchPermState initial
          (walk (pathMoves orientedRoot forwardPath) orientedRoot.state) := by
          rw [follow_state_eq_walk]
    _ = branchPermState initial (walk canonicalMoves orientedRoot.state) := by
          rw [hencode]
    _ = walk (canonicalMoves.map (branchPermMove initial))
          (branchPermState initial orientedRoot.state) :=
          branchPermState_walk initial canonicalMoves orientedRoot.state
    _ = walk moves (rootBranch initial).state := by
          rw [branchPermState_orientedRoot]
          congr 1
          simp [canonicalMoves, List.map_map, Function.comp_def,
            branchPermMove_inverse_left]
    _ = (branchNode initial path).state := by
          symm
          simpa [branchNode, moves] using
            follow_state_eq_walk (rootBranch initial) path.reverse

/-- Every positive integer Markov solution other than the exceptional root is a cyclic coordinate
permutation of the Markov state attached to some Stern-Brocot path.

This collapses the accepted three-branch labelled coverage theorem to the single canonical
Stern-Brocot branch modulo cyclic coordinate symmetry.  It remains purely a representation
statement: no uniqueness of the Stern-Brocot path after forgetting coordinate order, and no
injectivity of any numerical Markov label, is asserted. -/
theorem exists_permuted_sternNode_of_positive_solution
    (s : State)
    (hx : 0 < s.x) (hy : 0 < s.y) (hz : 0 < s.z)
    (hsol : s.IsSolution)
    (hne : s ≠ ⟨1, 1, 1⟩) :
    ∃ initial : Move, ∃ path : List Bool,
      branchPermState initial (sternNode path).state = s := by
  obtain ⟨initial, branchPath, hbranch⟩ :=
    exists_branchNode_state_of_positive_solution s hx hy hz hsol hne
  obtain ⟨sternPath, hperm⟩ :=
    exists_permuted_sternNode_of_branchNode initial branchPath
  exact ⟨initial, sternPath, hperm.trans hbranch⟩

end LeanFrontier.MarkovTree
