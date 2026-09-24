import LeanFrontier.Topology.Furstenberg
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Order

/-!
# Furstenberg topology from finite cyclic quotients

The evenly spaced topology on the integers can be described through the family of reduction maps

`ℤ → ZMod n`

for nonzero moduli `n`, with each finite quotient equipped with the discrete topology.

This module makes that description explicit without replacing the ordinary global topology
instances on either `ℤ` or `ZMod n`.

First, an arithmetic progression of step `n` is identified with a fiber of the reduction map.
That makes every nonzero reduction map continuous from the Furstenberg topology to the discrete
quotient.  Finally, taking the infimum of the induced discrete quotient topologies recovers
`furstenbergTopology` exactly.

The zero modulus is deliberately excluded from the quotient family: `ZMod 0` is essentially
`ℤ`, and the corresponding map to the discrete topology would force singleton opens, which the
Furstenberg topology does not have.
-/

namespace LeanFrontier.Int

open Set Topology TopologicalSpace

/-- Reduction of an integer modulo `n`, kept as a plain function so no topology instance is
installed on either side. -/
def zmodReduction (n : ℕ) (x : ℤ) : ZMod n :=
  x

/-- An arithmetic progression with natural step `n` is exactly a fiber of reduction modulo
`n`.  This identity also holds at `n = 0`. -/
theorem arithProgression_eq_zmodReduction_fiber (a : ℤ) (n : ℕ) :
    arithProgression a (n : ℤ) =
      zmodReduction n ⁻¹' ({zmodReduction n a} : Set (ZMod n)) := by
  ext x
  simp only [mem_arithProgression, mem_preimage, mem_singleton_iff]
  change ((n : ℤ) ∣ x - a) ↔ (x : ZMod n) = (a : ZMod n)
  rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]

/-- Every nonzero reduction map is continuous from the Furstenberg topology to the discrete
topology on the finite cyclic quotient. -/
theorem continuous_zmodReduction {n : ℕ} (hn : n ≠ 0) :
    Continuous[furstenbergTopology, (⊥ : TopologicalSpace (ZMod n))]
      (zmodReduction n) := by
  letI : NeZero n := ⟨hn⟩
  rw [continuous_def]
  intro s _hs
  have hpre :
      zmodReduction n ⁻¹' s =
        ⋃ y ∈ s, arithProgression (y.val : ℤ) (n : ℤ) := by
    ext x
    simp only [mem_preimage, mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨zmodReduction n x, hx, ?_⟩
      rw [mem_arithProgression]
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simpa [zmodReduction] using ZMod.natCast_zmod_val (zmodReduction n x)
    · rintro ⟨y, hy, hxy⟩
      rw [mem_arithProgression, ← ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
      have hred : zmodReduction n x = y := by
        calc
          zmodReduction n x = (x : ZMod n) := rfl
          _ = (y.val : ZMod n) := hxy.symm
          _ = y := ZMod.natCast_zmod_val y
      rwa [hred]
  rw [hpre]
  exact isOpen_biUnion fun y _ =>
    isOpen_arithProgression (y.val : ℤ) (n : ℤ)
      (Int.natCast_ne_zero.mpr hn)

/-- The topology obtained by observing all nonzero finite cyclic quotients discretely. -/
def finiteQuotientTopology : TopologicalSpace ℤ :=
  ⨅ n : {n : ℕ // n ≠ 0},
    (⊥ : TopologicalSpace (ZMod n.1)).induced (zmodReduction n.1)

/-- The Furstenberg topology is exactly the topology induced jointly by all nonzero reduction
maps `ℤ → ZMod n` when the finite quotients are discrete.

Thus the clopen arithmetic-progressions basis is precisely the finite-congruence quotient
topology. -/
theorem furstenbergTopology_eq_finiteQuotientTopology :
    furstenbergTopology = finiteQuotientTopology := by
  apply le_antisymm
  · rw [finiteQuotientTopology]
    refine le_iInf fun n => ?_
    exact Continuous.le_induced (continuous_zmodReduction n.property)
  · rw [finiteQuotientTopology, furstenbergTopology]
    apply le_generateFrom
    rintro _ ⟨a, b, hb, rfl⟩
    let n : {n : ℕ // n ≠ 0} :=
      ⟨b.natAbs, Int.natAbs_ne_zero.mpr hb⟩
    have hle :
        (⨅ n : {n : ℕ // n ≠ 0},
          (⊥ : TopologicalSpace (ZMod n.1)).induced (zmodReduction n.1)) ≤
          (⊥ : TopologicalSpace (ZMod n.1)).induced (zmodReduction n.1) :=
      iInf_le _ n
    apply TopologicalSpace.le_def.1 hle
    have hstep :
        arithProgression a b =
          arithProgression a (b.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using
        (Set.ext fun x => (abs_dvd b (x - a)).symm)
    rw [hstep, arithProgression_eq_zmodReduction_fiber]
    exact isOpen_induced (by simp)

end LeanFrontier.Int
