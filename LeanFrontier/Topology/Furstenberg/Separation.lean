import LeanFrontier.Topology.Furstenberg
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic

/-!
# Separation properties of the Furstenberg topology

The accepted Furstenberg-topology development proves that every nonzero-step arithmetic
progression is clopen and that every nonempty open set is infinite.

This module extracts two global consequences.

* Any two distinct integers are separated by a clopen arithmetic progression, so the
  Furstenberg topology is totally separated (hence Hausdorff and totally disconnected).
* No singleton is open, so despite that strong separation property the topology is not
  discrete.

For distinct `x` and `y`, the separator used below is the progression through `x`
with step `2 * (y - x)`.  The point `y` cannot lie in it: that would say
`2 * (y - x)` divides `y - x`, impossible when `y - x ≠ 0`.
-/

namespace LeanFrontier.Int

open Set Topology TopologicalSpace

/-- The Furstenberg topology on the integers is totally separated: any two distinct
integers can be separated by a clopen arithmetic progression. -/
theorem totallySeparatedSpace_furstenberg :
    @TotallySeparatedSpace ℤ furstenbergTopology := by
  letI : TopologicalSpace ℤ := furstenbergTopology
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  let d : ℤ := y - x
  let b : ℤ := 2 * d
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr (Ne.symm hxy)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact mul_ne_zero (by norm_num) hd
  have hy : y ∉ arithProgression x b := by
    intro hmem
    rcases hmem with ⟨k, hk⟩
    have hk' : d = (2 * d) * k := by
      simpa [d, b] using hk
    have hmul : d * (1 - 2 * k) = 0 := by
      calc
        d * (1 - 2 * k) = d - (2 * d) * k := by ring
        _ = 0 := by rw [← hk']; ring
    rcases mul_eq_zero.mp hmul with hzero | hparity
    · exact hd hzero
    · omega
  refine ⟨arithProgression x b, ?_, self_mem_arithProgression x b, ?_⟩
  · exact ⟨isClosed_arithProgression x hb, isOpen_arithProgression x b hb⟩
  · simpa only [Set.mem_compl_iff] using hy

/-- No point is isolated in the Furstenberg topology: a singleton cannot be open because every
nonempty open set is infinite. In particular, the Furstenberg topology is not discrete. -/
theorem not_isOpen_singleton_furstenberg (x : ℤ) :
    ¬ IsOpen[furstenbergTopology] ({x} : Set ℤ) := by
  intro hopen
  exact infinite_of_isOpen hopen ⟨x, by simp⟩ (Set.finite_singleton x)

end LeanFrontier.Int
