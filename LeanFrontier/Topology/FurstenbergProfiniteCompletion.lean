import LeanFrontier.Topology.FurstenbergProfiniteTopology
import LeanFrontier.Topology.Furstenberg.Separation
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.DenseEmbedding

/-!
# Furstenberg integers inside the additive profinite completion

The accepted finite-quotient comparison identifies the Furstenberg topology with the topology
jointly induced by all generic finite-index additive quotients of `ℤ`. Mathlib defines the
additive profinite completion as the projective limit of exactly those quotients.

This module identifies the canonical map into that completion with the Furstenberg topology itself.
It then combines Mathlib's dense-range theorem with LeanFrontier's accepted total-separation theorem
to show that the canonical map is a dense embedding.

The result closes the topology/completion interface promised by the Furstenberg roadmap: the
Furstenberg integers occur as a dense topological subspace of Mathlib's additive profinite
completion of `ℤ`.
-/

namespace LeanFrontier.Int

open Topology TopologicalSpace

private abbrev intProfiniteDiagram :=
  ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)

/-- The additive profinite completion of the integers, using Mathlib's canonical construction. -/
abbrev intProfiniteCompletion :=
  ProfiniteAddGrp.ProfiniteCompletion.completion (AddGrpCat.of ℤ)

/-- Mathlib's canonical map from the integers into their additive profinite completion. -/
def furstenbergProfiniteMap : ℤ → intProfiniteCompletion :=
  ProfiniteAddGrp.ProfiniteCompletion.etaFn (AddGrpCat.of ℤ)

set_option linter.style.haveILetI false in
private theorem diagramObj_topology_eq_bot
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    ((intProfiniteDiagram.obj H).toProfinite.toTop.str) =
      (⊥ : TopologicalSpace (intProfiniteDiagram.obj H)) := by
  haveI : Finite (intProfiniteDiagram.obj H) := by
    change Finite (ℤ ⧸ H.toAddSubgroup)
    infer_instance
  exact DiscreteTopology.eq_bot

/-- The `H`-coordinate projection from Mathlib's explicit profinite limit. -/
private def intProfiniteProjection
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    intProfiniteCompletion → intProfiniteDiagram.obj H :=
  fun x => (ProfiniteAddGrp.limitCone intProfiniteDiagram).π.app H x

private theorem continuous_intProfiniteProjection
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    Continuous (intProfiniteProjection H) := by
  exact
    ((ProfiniteAddGrp.limitCone intProfiniteDiagram).π.app H).hom.continuous_toFun

private theorem continuous_intProfiniteProjection_discrete
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    @Continuous
      intProfiniteCompletion
      (ℤ ⧸ H.toAddSubgroup)
      (inferInstance : TopologicalSpace intProfiniteCompletion)
      (⊥ : TopologicalSpace (ℤ ⧸ H.toAddSubgroup))
      (fun x => (intProfiniteProjection H x : ℤ ⧸ H.toAddSubgroup)) := by
  have hp := continuous_intProfiniteProjection H
  rw [diagramObj_topology_eq_bot H] at hp
  exact hp

@[simp] private theorem intProfiniteProjection_furstenbergProfiniteMap
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) (x : ℤ) :
    intProfiniteProjection H (furstenbergProfiniteMap x) =
      (QuotientAddGroup.mk x : ℤ ⧸ H.toAddSubgroup) := by
  rfl

private theorem induced_furstenbergProfiniteMap_eq_genericFiniteQuotientTopology :
    TopologicalSpace.induced furstenbergProfiniteMap
        (inferInstance : TopologicalSpace intProfiniteCompletion) =
      genericFiniteQuotientTopology := by
  apply le_antisymm
  · rw [genericFiniteQuotientTopology]
    refine le_iInf fun H => ?_
    have heta :
        @Continuous
          ℤ
          intProfiniteCompletion
          (TopologicalSpace.induced furstenbergProfiniteMap
            (inferInstance : TopologicalSpace intProfiniteCompletion))
          (inferInstance : TopologicalSpace intProfiniteCompletion)
          furstenbergProfiniteMap :=
      continuous_induced_dom
    have hq :
        @Continuous
          ℤ
          (ℤ ⧸ H.toAddSubgroup)
          (TopologicalSpace.induced furstenbergProfiniteMap
            (inferInstance : TopologicalSpace intProfiniteCompletion))
          (⊥ : TopologicalSpace (ℤ ⧸ H.toAddSubgroup))
          (fun x : ℤ => (QuotientAddGroup.mk x : ℤ ⧸ H.toAddSubgroup)) := by
      have hcomp :
          @Continuous
            ℤ
            (ℤ ⧸ H.toAddSubgroup)
            (TopologicalSpace.induced furstenbergProfiniteMap
              (inferInstance : TopologicalSpace intProfiniteCompletion))
            (⊥ : TopologicalSpace (ℤ ⧸ H.toAddSubgroup))
            (fun x => intProfiniteProjection H (furstenbergProfiniteMap x)) :=
        (continuous_intProfiniteProjection_discrete H).comp heta
      simpa using hcomp
    exact hq.le_induced
  · have hmap :
        @Continuous
          ℤ
          intProfiniteCompletion
          genericFiniteQuotientTopology
          (inferInstance : TopologicalSpace intProfiniteCompletion)
          furstenbergProfiniteMap := by
      apply continuous_induced_rng.mpr
      exact continuous_pi fun H => by
        have hq :
            @Continuous
              ℤ
              (ℤ ⧸ H.toAddSubgroup)
              genericFiniteQuotientTopology
              (⊥ : TopologicalSpace (ℤ ⧸ H.toAddSubgroup))
              (fun x : ℤ => (QuotientAddGroup.mk x : ℤ ⧸ H.toAddSubgroup)) :=
          continuous_iff_le_induced.mpr (iInf_le _ H)
        have hqObj :
            @Continuous
              ℤ
              (intProfiniteDiagram.obj H)
              genericFiniteQuotientTopology
              ((intProfiniteDiagram.obj H).toProfinite.toTop.str)
              (fun x : ℤ => (QuotientAddGroup.mk x : intProfiniteDiagram.obj H)) := by
          rw [diagramObj_topology_eq_bot H]
          exact hq
        simpa [
          furstenbergProfiniteMap,
          ProfiniteAddGrp.ProfiniteCompletion.etaFn,
          Function.comp_def
        ] using hqObj
    exact hmap.le_induced

/-- The topology induced on `ℤ` by Mathlib's canonical map into its additive profinite
completion is exactly the Furstenberg topology. -/
theorem furstenbergTopology_eq_induced_profiniteCompletion :
    furstenbergTopology =
      TopologicalSpace.induced furstenbergProfiniteMap
        (inferInstance : TopologicalSpace intProfiniteCompletion) := by
  rw [induced_furstenbergProfiniteMap_eq_genericFiniteQuotientTopology]
  exact furstenbergTopology_eq_genericFiniteQuotientTopology

/-- The canonical map from the Furstenberg integers into Mathlib's additive profinite completion
is a dense topological embedding. -/
set_option linter.style.haveILetI false in
theorem isDenseEmbedding_furstenbergProfiniteMap :
    @IsDenseEmbedding
      ℤ
      intProfiniteCompletion
      furstenbergTopology
      (inferInstance : TopologicalSpace intProfiniteCompletion)
      furstenbergProfiniteMap := by
  letI : TopologicalSpace ℤ := furstenbergTopology
  letI : TotallySeparatedSpace ℤ := totallySeparatedSpace_furstenberg
  have hind : IsInducing furstenbergProfiniteMap :=
    ⟨furstenbergTopology_eq_induced_profiniteCompletion⟩
  have hdense : DenseRange furstenbergProfiniteMap := by
    simpa [furstenbergProfiniteMap] using
      (ProfiniteAddGrp.ProfiniteCompletion.denseRange (G := AddGrpCat.of ℤ))
  exact {
    toIsDenseInducing := ⟨hind, hdense⟩
    injective := hind.injective
  }

end LeanFrontier.Int
