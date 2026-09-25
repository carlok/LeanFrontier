import LeanFrontier.NumberTheory.MarkovTree.SternBrocot
import Mathlib.Tactic

/-!
# Injectivity of the oriented Markov state tree

The accepted oriented Markov development already gives a binary non-backtracking path
representation and identifies its path shape with the Stern-Brocot tree.  Its injectivity
statement, however, is deliberately only about the erased coordinate-move word.

This module proves the next structural fact: the full labelled Markov state reached in the
canonical oriented branch also determines the tree position.

The key observation is local.  At an oriented node the distinguished back move strictly lowers
the coordinate mass, while either forward child has strictly larger mass.  Hence two oriented
nodes with the same state must have the same distinguished back move.  A child state therefore
determines its parent by applying that back move once.  Induction from the oriented root then
shows that different Stern-Brocot paths cannot merge in the labelled Markov graph.

This remains safely below the Frobenius/Markov uniqueness boundary.  It proves injectivity of
the *full triples* attached to tree positions; it does not assert that the maximum coordinate
alone determines a triple.
-/

namespace LeanFrontier.MarkovTree

private theorem forwardMove_injective' (back : Move) :
    Function.Injective (forwardMove back) := by
  intro a b h
  cases back <;> cases a <;> cases b <;> simp [forwardMove] at h ⊢

private theorem exists_forwardDir_of_ne
    {back m : Move} (hne : m ≠ back) :
    ∃ dir : Bool, forwardMove back dir = m := by
  cases back <;> cases m <;> simp [forwardMove] at hne ⊢

/-- Moving to either forward child strictly increases coordinate mass. -/
theorem state_mass_lt_child (n : OrientedNode) (dir : Bool) :
    n.state.mass < (child n dir).state.mass := by
  have h := (child n dir).back_descends
  dsimp [child] at h
  rw [move_involutive] at h
  exact h

private theorem back_eq_of_state_eq
    {a b : OrientedNode} (hstate : a.state = b.state) :
    a.back = b.back := by
  by_contra hback
  obtain ⟨dir, hdir⟩ := exists_forwardDir_of_ne (Ne.symm hback)
  have hinc := state_mass_lt_child a dir
  dsimp [child] at hinc
  rw [hdir] at hinc
  have hdec := b.back_descends
  rw [← hstate] at hdec
  omega

/-- The underlying labelled Markov state uniquely determines an oriented node.

In particular, the descending parent edge is not extra ambiguity: it is forced by the state. -/
theorem orientedNode_eq_of_state_eq
    {a b : OrientedNode} (hstate : a.state = b.state) :
    a = b := by
  have hback := back_eq_of_state_eq hstate
  cases a with
  | mk aState aBack aPos aSol aDesc =>
      cases b with
      | mk bState bBack bPos bSol bDesc =>
          dsimp at hstate hback
          subst bState
          subst bBack
          rfl

private theorem child_parent_state (n : OrientedNode) (dir : Bool) :
    move (child n dir).back (child n dir).state = n.state := by
  dsimp [child]
  exact move_involutive _ _

private theorem orientedRoot_mass_le_sternNode (path : List Bool) :
    orientedRoot.state.mass ≤ (sternNode path).state.mass := by
  induction path with
  | nil =>
      simp [sternNode, follow]
  | cons dir path ih =>
      rw [sternNode_cons]
      exact le_trans ih (le_of_lt (state_mass_lt_child (sternNode path) dir))

/-- Distinct Stern-Brocot path positions reach distinct full labelled Markov states in the
canonical oriented branch.

This is injectivity of the complete triple-valued tree embedding, not injectivity of the
maximum-coordinate Markov-number label. -/
theorem sternNode_state_injective :
    Function.Injective (fun path : List Bool => (sternNode path).state) := by
  intro p
  induction p with
  | nil =>
      intro q h
      cases q with
      | nil =>
          rfl
      | cons dir q =>
          change orientedRoot.state = (sternNode (dir :: q)).state at h
          rw [sternNode_cons] at h
          have hmass := congrArg State.mass h
          have hrootle := orientedRoot_mass_le_sternNode q
          have hstep := state_mass_lt_child (sternNode q) dir
          omega
  | cons dir p ih =>
      intro q h
      cases q with
      | nil =>
          change (sternNode (dir :: p)).state = orientedRoot.state at h
          rw [sternNode_cons] at h
          have hmass := congrArg State.mass h
          have hrootle := orientedRoot_mass_le_sternNode p
          have hstep := state_mass_lt_child (sternNode p) dir
          omega
      | cons dir' q =>
          change
            (sternNode (dir :: p)).state =
              (sternNode (dir' :: q)).state at h
          rw [sternNode_cons, sternNode_cons] at h
          have hchildren :
              child (sternNode p) dir = child (sternNode q) dir' :=
            orientedNode_eq_of_state_eq h
          have hparentState :
              (sternNode p).state = (sternNode q).state := by
            calc
              (sternNode p).state =
                  move (child (sternNode p) dir).back
                    (child (sternNode p) dir).state :=
                (child_parent_state (sternNode p) dir).symm
              _ =
                  move (child (sternNode q) dir').back
                    (child (sternNode q) dir').state := by
                rw [hchildren]
              _ = (sternNode q).state :=
                child_parent_state (sternNode q) dir'
          have hpq : p = q := ih hparentState
          subst q
          have hback := congrArg OrientedNode.back hchildren
          have hdir : dir = dir' := by
            apply forwardMove_injective' (sternNode p).back
            simpa [child] using hback
          subst dir'
          rfl

/-- Equality of Stern-Brocot nodes is equivalent to equality of the full labelled Markov states
attached to the same path positions.

This upgrades the accepted move-word correspondence to the actual triple-valued tree embedding,
without making any claim about injectivity of a single Markov-number coordinate. -/
theorem sternBrocot_pair_eq_iff_sternNode_state_eq (p q : List Bool) :
    SternBrocot.pair p = SternBrocot.pair q ↔
      (sternNode p).state = (sternNode q).state := by
  constructor
  · intro hpq
    have hpath : p = q := by
      apply sternMoves_injective
      exact (sternBrocot_pair_eq_iff_sternMoves_eq p q).1 hpq
    subst q
    rfl
  · intro hstate
    have hpath : p = q := sternNode_state_injective hstate
    subst q
    rfl

end LeanFrontier.MarkovTree
