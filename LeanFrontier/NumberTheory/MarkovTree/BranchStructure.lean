import LeanFrontier.NumberTheory.MarkovTree.SternBrocot
import Mathlib.Data.List.Infix
import Mathlib.Tactic

/-!
# Common ancestors in the canonical Markov/Stern-Brocot tree

LeanFrontier's accepted `sternNode` convention stores a path in reverse traversal order:
prepending a Boolean direction moves one edge farther from the root.  Consequently a path `p`
is an ancestor of a path `q` exactly when `p` is a suffix of `q`.

For later uniqueness arguments it is useful to have a canonical greatest common ancestor rather
than repeatedly unpacking suffix witnesses.  This module builds it in two stages.

First, `commonPrefix` is the ordinary longest common prefix of two Boolean lists and is
characterized by its universal property: it is a prefix of both lists, and every common prefix
is a prefix of it.  Reversing turns that into `commonAncestor`, the greatest common suffix in
the Stern-Brocot path convention.

The resulting API is purely combinatorial, but it is tailored to the accepted Markov tree:
`commonAncestor p q` is exactly the path of the deepest canonical node lying on both root-to-node
chains.

No Markov-number uniqueness statement is used or proved here.
-/

namespace LeanFrontier.MarkovTree

/-- The longest common prefix of two Boolean paths. -/
def commonPrefix : List Bool → List Bool → List Bool
  | a :: p, b :: q =>
      if a = b then a :: commonPrefix p q else []
  | _, _ => []

/-- The longest common prefix is a prefix of its left input. -/
theorem commonPrefix_isPrefix_left (p q : List Bool) :
    commonPrefix p q <+: p := by
  induction p generalizing q with
  | nil =>
      simp [commonPrefix]
  | cons a p ih =>
      cases q with
      | nil =>
          simp [commonPrefix]
      | cons b q =>
          by_cases hab : a = b
          · subst b
            simp [commonPrefix, ih]
          · simp [commonPrefix, hab]

/-- The longest common prefix is a prefix of its right input. -/
theorem commonPrefix_isPrefix_right (p q : List Bool) :
    commonPrefix p q <+: q := by
  induction p generalizing q with
  | nil =>
      simp [commonPrefix]
  | cons a p ih =>
      cases q with
      | nil =>
          simp [commonPrefix]
      | cons b q =>
          by_cases hab : a = b
          · subst b
            simp [commonPrefix, ih]
          · simp [commonPrefix, hab]

/-- Universal property of `commonPrefix`: every list which is a prefix of both inputs is itself
a prefix of their longest common prefix. -/
theorem isPrefix_commonPrefix {r p q : List Bool}
    (hp : r <+: p) (hq : r <+: q) :
    r <+: commonPrefix p q := by
  induction p generalizing q r with
  | nil =>
      have hr : r = [] := List.prefix_nil.mp hp
      subst r
      simp
  | cons a p ih =>
      cases q with
      | nil =>
          have hr : r = [] := List.prefix_nil.mp hq
          subst r
          simp
      | cons b q =>
          by_cases hab : a = b
          · subst b
            cases r with
            | nil =>
                simp
            | cons c r =>
                obtain ⟨hca, hrp⟩ := List.cons_prefix_cons.mp hp
                obtain ⟨hca', hrq⟩ := List.cons_prefix_cons.mp hq
                subst c
                have htail := ih hrp hrq
                rcases htail with ⟨rest, hrest⟩
                refine ⟨rest, ?_⟩
                simpa [commonPrefix] using congrArg (List.cons a) hrest
          · cases r with
            | nil =>
                simp [commonPrefix, hab]
            | cons c r =>
                obtain ⟨hca, _⟩ := List.cons_prefix_cons.mp hp
                obtain ⟨hcb, _⟩ := List.cons_prefix_cons.mp hq
                exfalso
                apply hab
                exact hca.symm.trans hcb

/-- Reversal exchanges the ordinary prefix order with the suffix order. -/
private theorem reverse_prefix_iff_suffix (p q : List Bool) :
    p.reverse <+: q.reverse ↔ p <:+ q := by
  constructor
  · rintro ⟨r, h⟩
    refine ⟨r.reverse, ?_⟩
    have hr := congrArg List.reverse h
    simpa using hr
  · rintro ⟨r, h⟩
    refine ⟨r.reverse, ?_⟩
    have hr := congrArg List.reverse h
    simpa using hr

/-- The deepest common ancestor of two canonical Stern-Brocot paths.

Because `sternNode` moves away from the root by prepending directions, ancestors are suffixes.
We therefore reverse, take the ordinary longest common prefix, and reverse back. -/
def commonAncestor (p q : List Bool) : List Bool :=
  (commonPrefix p.reverse q.reverse).reverse

/-- The common ancestor lies on the ancestor chain of the left path. -/
theorem commonAncestor_isSuffix_left (p q : List Bool) :
    commonAncestor p q <:+ p := by
  apply (reverse_prefix_iff_suffix (commonAncestor p q) p).1
  simpa [commonAncestor] using
    commonPrefix_isPrefix_left p.reverse q.reverse

/-- The common ancestor lies on the ancestor chain of the right path. -/
theorem commonAncestor_isSuffix_right (p q : List Bool) :
    commonAncestor p q <:+ q := by
  apply (reverse_prefix_iff_suffix (commonAncestor p q) q).1
  simpa [commonAncestor] using
    commonPrefix_isPrefix_right p.reverse q.reverse

/-- Universal property of the canonical common ancestor: every path which is an ancestor of
both `p` and `q` is itself an ancestor of `commonAncestor p q`.

Thus `commonAncestor p q` is the greatest common ancestor in the tree order. -/
theorem isSuffix_commonAncestor {r p q : List Bool}
    (hp : r <:+ p) (hq : r <:+ q) :
    r <:+ commonAncestor p q := by
  apply (reverse_prefix_iff_suffix r (commonAncestor p q)).1
  have hp' : r.reverse <+: p.reverse :=
    (reverse_prefix_iff_suffix r p).2 hp
  have hq' : r.reverse <+: q.reverse :=
    (reverse_prefix_iff_suffix r q).2 hq
  simpa [commonAncestor] using
    isPrefix_commonPrefix hp' hq'

/-- A path is its own common ancestor with `q` exactly when it is an ancestor of `q`. -/
theorem commonAncestor_eq_left_iff (p q : List Bool) :
    commonAncestor p q = p ↔ p <:+ q := by
  constructor
  · intro h
    rw [← h]
    exact commonAncestor_isSuffix_right p q
  · intro hpq
    have hca : commonAncestor p q <:+ p :=
      commonAncestor_isSuffix_left p q
    have hpca : p <:+ commonAncestor p q :=
      isSuffix_commonAncestor (List.suffix_refl p) hpq
    exact hca.eq_of_length (hca.length_le.antisymm hpca.length_le)

/-- Symmetrically, a path is its own common ancestor with `p` exactly when it is an ancestor
of `p`. -/
theorem commonAncestor_eq_right_iff (p q : List Bool) :
    commonAncestor p q = q ↔ q <:+ p := by
  constructor
  · intro h
    rw [← h]
    exact commonAncestor_isSuffix_left p q
  · intro hqp
    have hca : commonAncestor p q <:+ q :=
      commonAncestor_isSuffix_right p q
    have hqca : q <:+ commonAncestor p q :=
      isSuffix_commonAncestor hqp (List.suffix_refl q)
    exact hca.eq_of_length (hca.length_le.antisymm hqca.length_le)

/-- The canonical common ancestor is symmetric in its two arguments. -/
theorem commonAncestor_comm (p q : List Bool) :
    commonAncestor p q = commonAncestor q p := by
  have hpq : commonAncestor p q <:+ commonAncestor q p :=
    isSuffix_commonAncestor
      (commonAncestor_isSuffix_right p q)
      (commonAncestor_isSuffix_left p q)
  have hqp : commonAncestor q p <:+ commonAncestor p q :=
    isSuffix_commonAncestor
      (commonAncestor_isSuffix_right q p)
      (commonAncestor_isSuffix_left q p)
  exact hpq.eq_of_length (hpq.length_le.antisymm hqp.length_le)

end LeanFrontier.MarkovTree
