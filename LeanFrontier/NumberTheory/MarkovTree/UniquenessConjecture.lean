import LeanFrontier.NumberTheory.MarkovTree.Symmetry
import Mathlib.Tactic

/-!
# The Markov uniqueness conjecture and a Stern-Brocot reduction

A classical Markov triple is a positive integer solution of

`x^2 + y^2 + z^2 = 3xyz`.

The Frobenius/Markov uniqueness conjecture says that the largest coordinate determines the
triple up to permutation.  The accepted LeanFrontier development deliberately stopped short of
that boundary: it proves reachability of every positive solution, constructs a canonical
Stern-Brocot branch, proves injectivity of the full labelled states on that branch, and reduces
all positive solutions modulo cyclic coordinate symmetry to that branch.

This module states the open uniqueness problem against those accepted definitions and then proves
a reduction: the global conjecture is equivalent to checking the same maximum-coordinate
condition only for pairs of canonical `sternNode` states.  Thus future attacks can work entirely
inside the accepted binary path model without losing the meaning of the original conjecture.

No claim is made here that the conjecture is proved.
-/

namespace LeanFrontier.MarkovTree

/-- The largest coordinate of a bundled Markov state. -/
def State.maxCoord (s : State) : ℤ :=
  max s.x (max s.y s.z)

/-- The unordered multiset of the three coordinates of a bundled Markov state. -/
def State.coordMultiset (s : State) : Multiset ℤ :=
  ({s.x} : Multiset ℤ) + {s.y} + {s.z}

/-- Two bundled states agree up to a permutation of their three coordinates. -/
def State.Permutes (s t : State) : Prop :=
  s.coordMultiset = t.coordMultiset

/-- **Frobenius/Markov uniqueness conjecture.**

Among positive integer solutions of the Markov equation, equality of the largest coordinate
forces equality of the coordinate multisets.  Equivalently, a Markov number determines its
Markov triple up to permutation.

This is an open problem; the definition asserts no theorem. -/
def UniquenessConjecture : Prop :=
  ∀ s t : State,
    s.Positive → t.Positive →
    s.IsSolution → t.IsSolution →
    s.maxCoord = t.maxCoord →
    s.Permutes t

private theorem maxCoord_branchPermState (initial : Move) (s : State) :
    (branchPermState initial s).maxCoord = s.maxCoord := by
  rcases s with ⟨x, y, z⟩
  cases initial <;>
    simp [branchPermState, State.maxCoord, max_comm, max_left_comm]

private theorem coordMultiset_branchPermState (initial : Move) (s : State) :
    (branchPermState initial s).coordMultiset = s.coordMultiset := by
  rcases s with ⟨x, y, z⟩
  cases initial with
  | first =>
      change ({z} : Multiset ℤ) + {x} + {y} = {x} + {y} + {z}
      ac_rfl
  | second =>
      change ({y} : Multiset ℤ) + {z} + {x} = {x} + {y} + {z}
      ac_rfl
  | third =>
      rfl

private theorem eq_root_of_positive_maxCoord_eq_one
    {s : State} (hpos : s.Positive) (hmax : s.maxCoord = 1) :
    s = ⟨1, 1, 1⟩ := by
  rcases s with ⟨x, y, z⟩
  change 0 < x ∧ 0 < y ∧ 0 < z at hpos
  change max x (max y z) = 1 at hmax
  have hxle : x ≤ 1 := by
    have hx : x ≤ max x (max y z) := le_max_left _ _
    omega
  have hyle : y ≤ 1 := by
    have hy₁ : y ≤ max y z := le_max_left _ _
    have hy₂ : max y z ≤ max x (max y z) := le_max_right _ _
    omega
  have hzle : z ≤ 1 := by
    have hz₁ : z ≤ max y z := le_max_right _ _
    have hz₂ : max y z ≤ max x (max y z) := le_max_right _ _
    omega
  rcases hpos with ⟨hxpos, hypos, hzpos⟩
  congr <;> omega

/-- The classical global Markov uniqueness conjecture is equivalent to its restriction to the
accepted canonical Stern-Brocot branch.

The forward direction is immediate because every `sternNode` is a positive Markov solution.
For the converse, the accepted cyclic-symmetry coverage theorem writes every non-root positive
solution as a cyclic coordinate permutation of some `sternNode`.  Cyclic permutation preserves
both the maximum coordinate and the unordered coordinate multiset, so a canonical-branch
uniqueness statement transports back to arbitrary positive Markov triples.  The exceptional
root `(1,1,1)` is handled directly from positivity and maximum coordinate one. -/
theorem uniquenessConjecture_iff_sternNode :
    UniquenessConjecture ↔
      ∀ p q : List Bool,
        (sternNode p).state.maxCoord = (sternNode q).state.maxCoord →
          (sternNode p).state.Permutes (sternNode q).state := by
  constructor
  · intro h p q hmax
    exact h
      (sternNode p).state
      (sternNode q).state
      (sternNode p).positive
      (sternNode q).positive
      (sternNode p).solution
      (sternNode q).solution
      hmax
  · intro hcanonical
    intro s t hspos htpos hssol htsol hmax
    by_cases hsroot : s = ⟨1, 1, 1⟩
    · subst s
      have htmax : t.maxCoord = 1 := by
        simpa [State.maxCoord] using hmax.symm
      have htroot := eq_root_of_positive_maxCoord_eq_one htpos htmax
      subst t
      rfl
    · by_cases htroot : t = ⟨1, 1, 1⟩
      · subst t
        have hsmax : s.maxCoord = 1 := by
          simpa [State.maxCoord] using hmax
        have hsroot' := eq_root_of_positive_maxCoord_eq_one hspos hsmax
        exact (hsroot hsroot').elim
      · obtain ⟨initialS, p, hp⟩ :=
          exists_permuted_sternNode_of_positive_solution
            s hspos.1 hspos.2.1 hspos.2.2 hssol hsroot
        obtain ⟨initialT, q, hq⟩ :=
          exists_permuted_sternNode_of_positive_solution
            t htpos.1 htpos.2.1 htpos.2.2 htsol htroot
        have hpmax :
            (sternNode p).state.maxCoord = s.maxCoord := by
          exact
            (maxCoord_branchPermState initialS (sternNode p).state).symm.trans
              (congrArg State.maxCoord hp)
        have hqmax :
            (sternNode q).state.maxCoord = t.maxCoord := by
          exact
            (maxCoord_branchPermState initialT (sternNode q).state).symm.trans
              (congrArg State.maxCoord hq)
        have hcanonMax :
            (sternNode p).state.maxCoord = (sternNode q).state.maxCoord := by
          calc
            (sternNode p).state.maxCoord = s.maxCoord := hpmax
            _ = t.maxCoord := hmax
            _ = (sternNode q).state.maxCoord := hqmax.symm
        have hcanon := hcanonical p q hcanonMax
        change s.coordMultiset = t.coordMultiset
        change (sternNode p).state.coordMultiset =
          (sternNode q).state.coordMultiset at hcanon
        calc
          s.coordMultiset =
              (branchPermState initialS (sternNode p).state).coordMultiset :=
            congrArg State.coordMultiset hp.symm
          _ = (sternNode p).state.coordMultiset :=
            coordMultiset_branchPermState initialS (sternNode p).state
          _ = (sternNode q).state.coordMultiset := hcanon
          _ = (branchPermState initialT (sternNode q).state).coordMultiset :=
            (coordMultiset_branchPermState initialT (sternNode q).state).symm
          _ = t.coordMultiset :=
            congrArg State.coordMultiset hq

end LeanFrontier.MarkovTree
