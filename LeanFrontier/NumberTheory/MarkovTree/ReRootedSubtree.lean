import LeanFrontier.NumberTheory.MarkovTree.MarkovNumber
import Mathlib.Tactic

/-!
# Re-rooted subtrees of the oriented Markov tree

The canonical `sternNode` API indexes the whole oriented Markov tree from the global root.
Local uniqueness arguments, however, naturally start at an arbitrary canonical node and reason
inside one of its descendant subtrees.

LeanFrontier's Stern-Brocot path convention prepends a direction when moving to a child.  Hence a
descendant path has the form `tail ++ base`, and the directions in `tail` act from right to
left.  The recursion `descendFrom` packages exactly that local convention.

The main bridge proves

`sternNode (tail ++ base) = descendFrom (sternNode base) tail`.

This gives later work a root-independent subtree API.  Markov-number monotonicity and full-state
injectivity are then transported to every canonical re-rooted subtree.
-/

namespace LeanFrontier.MarkovTree

/-- Descend from an arbitrary oriented Markov node using Stern-Brocot's prepend convention.

The head of the list is the final child step; equivalently, directions are executed from the
right end of the list toward the left. -/
def descendFrom (n : OrientedNode) : List Bool → OrientedNode
  | [] => n
  | dir :: tail => child (descendFrom n tail) dir

/-- Appending a local descendant tail to a canonical base path is exactly the same as re-rooting
at `sternNode base` and applying `descendFrom`. -/
theorem sternNode_append_eq_descendFrom (tail base : List Bool) :
    sternNode (tail ++ base) = descendFrom (sternNode base) tail := by
  induction tail with
  | nil =>
      rfl
  | cons dir tail ih =>
      simp only [List.cons_append, sternNode_cons, descendFrom]
      rw [ih]

/-- A descendant of the immediate `dir` child of `base` can be computed entirely inside the
re-rooted subtree at that child. -/
theorem sternNode_childSubtree_eq_descendFrom
    (base tail : List Bool) (dir : Bool) :
    sternNode (tail ++ dir :: base) =
      descendFrom (child (sternNode base) dir) tail := by
  calc
    sternNode (tail ++ dir :: base) =
        descendFrom (sternNode (dir :: base)) tail :=
      sternNode_append_eq_descendFrom tail (dir :: base)
    _ = descendFrom (child (sternNode base) dir) tail := by
      rw [sternNode_cons]

/-- The canonical Markov-number label of an appended descendant path is the local label obtained
by re-rooting at the base node. -/
theorem sternMarkovNumber_append_eq_descendFrom
    (tail base : List Bool) :
    sternMarkovNumber (tail ++ base) =
      (descendFrom (sternNode base) tail).markovNumber := by
  unfold sternMarkovNumber
  rw [sternNode_append_eq_descendFrom]

/-- Re-rooted descent never decreases the Markov-number label. -/
theorem markovNumber_le_descendFrom
    (n : OrientedNode) (tail : List Bool) :
    n.markovNumber ≤ (descendFrom n tail).markovNumber := by
  induction tail with
  | nil =>
      rfl
  | cons dir tail ih =>
      have hstep := markovNumber_lt_child (descendFrom n tail) dir
      simpa [descendFrom] using le_trans ih (le_of_lt hstep)

/-- Every nontrivial re-rooted descent strictly increases the Markov-number label. -/
theorem markovNumber_lt_descendFrom_of_ne_nil
    (n : OrientedNode) {tail : List Bool} (hne : tail ≠ []) :
    n.markovNumber < (descendFrom n tail).markovNumber := by
  cases tail with
  | nil =>
      exact (hne rfl).elim
  | cons dir tail =>
      have hle := markovNumber_le_descendFrom n tail
      have hstep := markovNumber_lt_child (descendFrom n tail) dir
      simpa [descendFrom] using lt_of_le_of_lt hle hstep

/-- Within a subtree re-rooted at a canonical `sternNode`, the full labelled Markov state still
determines the local descendant tail.

Thus re-rooting does not create any collisions in the already-proved full-state tree embedding. -/
theorem descendFrom_sternNode_state_injective (base : List Bool) :
    Function.Injective
      (fun tail : List Bool => (descendFrom (sternNode base) tail).state) := by
  intro p q hstate
  have hglobal :
      (sternNode (p ++ base)).state =
        (sternNode (q ++ base)).state := by
    calc
      (sternNode (p ++ base)).state =
          (descendFrom (sternNode base) p).state :=
        congrArg OrientedNode.state
          (sternNode_append_eq_descendFrom p base)
      _ = (descendFrom (sternNode base) q).state := hstate
      _ = (sternNode (q ++ base)).state :=
        congrArg OrientedNode.state
          (sternNode_append_eq_descendFrom q base).symm
  have hpaths : p ++ base = q ++ base :=
    sternNode_state_injective hglobal
  exact List.append_left_injective base hpaths

end LeanFrontier.MarkovTree
