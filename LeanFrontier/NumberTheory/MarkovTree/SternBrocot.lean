import LeanFrontier.NumberTheory.MarkovTree.Oriented
import LeanFrontier.NumberTheory.SternBrocot

/-!
# The oriented Markov tree in Stern-Brocot path convention

The accepted oriented Markov tree executes a Boolean path from left to right: the head of the
list is the first forward child step.  The accepted Stern-Brocot representation uses the dual
recursive convention: prepending a Boolean direction creates a child of the node represented by
the tail.

Reversing the Stern-Brocot path therefore aligns the two rooted binary recursions exactly.  This
module packages that alignment at the tree-position level.  It deliberately compares path
positions and non-backtracking Vieta-move encodings, not numerical Markov labels.

For a Stern-Brocot path `p`, `sternNode p` is the oriented Markov node reached by following
`p.reverse`, and `sternMoves p` is its erased list of accepted coordinate moves.  Prepending
one Stern-Brocot direction becomes one forward Markov child step, and the corresponding move is
appended to the erased non-backtracking walk.

The final theorem identifies equality of Stern-Brocot nodes with equality of these oriented
Markov move encodings.  This is the intended combinatorial tree-level correspondence; it makes
no claim that different paths have different numerical Markov triples, and no claim about
injectivity of Markov-number labels.
-/

namespace LeanFrontier.MarkovTree

private theorem follow_append (n : OrientedNode) (p q : List Bool) :
    follow n (p ++ q) = follow (follow n p) q := by
  induction p generalizing n with
  | nil =>
      rfl
  | cons dir p ih =>
      simp only [List.cons_append, follow]
      exact ih (n := child n dir)

private theorem pathMoves_append (n : OrientedNode) (p q : List Bool) :
    pathMoves n (p ++ q) =
      pathMoves n p ++ pathMoves (follow n p) q := by
  induction p generalizing n with
  | nil =>
      rfl
  | cons dir p ih =>
      simp only [List.cons_append, pathMoves, follow]
      rw [ih (n := child n dir)]

/-- The oriented Markov node corresponding to a Stern-Brocot path.

The reversal converts the accepted Stern-Brocot prepend-recursion convention into the accepted
oriented Markov walk convention. -/
def sternNode (path : List Bool) : OrientedNode :=
  follow orientedRoot path.reverse

/-- The non-backtracking Vieta-move encoding of a Stern-Brocot path. -/
def sternMoves (path : List Bool) : List Move :=
  pathMoves orientedRoot path.reverse

/-- Prepending a Stern-Brocot direction is exactly one forward child step in the oriented Markov
tree.  Thus the two accepted path representations have the same rooted binary recursion after
the path-convention reversal. -/
theorem sternNode_cons (dir : Bool) (path : List Bool) :
    sternNode (dir :: path) = child (sternNode path) dir := by
  simp [sternNode, follow_append, follow]

/-- Under the same path convention, prepending a Stern-Brocot direction appends exactly the
corresponding forward coordinate move to the non-backtracking Markov walk. -/
theorem sternMoves_cons (dir : Bool) (path : List Bool) :
    sternMoves (dir :: path) =
      sternMoves path ++ [forwardMove (sternNode path).back dir] := by
  simp [sternMoves, sternNode, pathMoves_append, pathMoves]

/-- Every Stern-Brocot path gives a non-backtracking Vieta-move walk from the oriented Markov
root. -/
theorem sternMoves_nonBacktracking (path : List Bool) :
    NonBacktrackingFrom orientedRoot.back (sternMoves path) := by
  simpa [sternMoves] using pathMoves_nonBacktracking orientedRoot path.reverse

/-- Different Stern-Brocot path positions have different oriented Markov move encodings.

This remains a statement about tree positions / move sequences, not about equality of the
numerical Markov states reached by those sequences. -/
theorem sternMoves_injective : Function.Injective sternMoves := by
  intro p q h
  have hrev : p.reverse = q.reverse := by
    apply pathMoves_injective orientedRoot
    simpa [sternMoves] using h
  simpa using congrArg List.reverse hrev

/-- The oriented Markov node attached to a Stern-Brocot path is reached by exactly its
non-backtracking move encoding in the accepted `walk` interface. -/
theorem sternNode_state_eq_walk (path : List Bool) :
    (sternNode path).state = walk (sternMoves path) orientedRoot.state := by
  simpa [sternNode, sternMoves] using follow_state_eq_walk orientedRoot path.reverse

private theorem sternBrocot_pair_injective :
    Function.Injective SternBrocot.pair := by
  intro p q hpq
  have hp := SternBrocot.pair_positive_coprime p
  obtain ⟨w, hw, huniq⟩ :=
    SternBrocot.existsUnique_pair_of_coprime hp.1 hp.2.1 hp.2.2
  have hpw : p = w := huniq p rfl
  have hqw : q = w := huniq q hpq.symm
  exact hpw.trans hqw.symm

/-- Two Stern-Brocot nodes are equal exactly when their corresponding oriented Markov
non-backtracking move encodings are equal.

This is the tree-position correspondence between the accepted Stern-Brocot and oriented Markov
representations.  It intentionally stops before any assertion about injectivity of numerical
Markov triples or Markov-number labels. -/
theorem sternBrocot_pair_eq_iff_sternMoves_eq (p q : List Bool) :
    SternBrocot.pair p = SternBrocot.pair q ↔ sternMoves p = sternMoves q := by
  constructor
  · intro hpq
    exact congrArg sternMoves (sternBrocot_pair_injective hpq)
  · intro hmoves
    exact congrArg SternBrocot.pair (sternMoves_injective hmoves)

end LeanFrontier.MarkovTree
