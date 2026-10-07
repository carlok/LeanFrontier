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

/-- The additive profinite completion of the integers, using Mathlib's explicit limit
construction for its finite-quotient diagram. -/
abbrev intProfiniteCompletion :=
  ProfiniteAddGrp.limit intProfiniteDiagram

/-- The canonical map from the integers into their additive profinite completion, written in the
coordinate form used by Mathlib's `ProfiniteAddGrp.ProfiniteCompletion.etaFn`. -/
def furstenbergProfiniteMap (x : ℤ) : intProfiniteCompletion :=
  ⟨fun _ => QuotientAddGroup.mk x, fun _ _ _ => rfl⟩

set_option linter.style.haveILetI false in
private theorem diagramObj_topology_eq_bot
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    ((intProfiniteDiagram.obj H).toProfinite.toTop.str) =
      (⊥ : TopologicalSpace (intProfiniteDiagram.obj H)) := by
  haveI : Finite (intProfiniteDiagram.obj H) := by
    change Finite (ℤ ⧸ H.toAddSubgroup)
    infer_instance
  exact DiscreteTopology.eq_bot

/-- Identity on the underlying finite quotient, viewed from Mathlib's wrapped profinite topology
to the explicit discrete topology used by `genericFiniteQuotientTopology`. -/
private theorem continuous_diagramObj_toQuotient
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    @Continuous
      (intProfiniteDiagram.obj H)
      (ℤ ⧸ H.toAddSubgroup)
      ((intProfiniteDiagram.obj H).toProfinite.toTop.str)
      (⊥ : TopologicalSpace (ℤ ⧸ H.toAddSubgroup))
      (fun q => q) := by
  rw [diagramObj_topology_eq_bot H]
  exact continuous_id

/-- Identity on the underlying finite quotient in the opposite topological direction. -/
private theorem continuous_quotient_toDiagramObj
    (H : FiniteIndexNormalAddSubgroup (AddGrpCat.of ℤ)) :
    @Continuous
      (ℤ ⧸ H.toAddSubgroup)
      (intProfiniteDiagram.obj H)
      (⊥ : TopologicalSpace (ℤ ⧸ H.toAddSubgroup))
      ((intProfiniteDiagram.obj H).toProfinite.toTop.str)
      (fun q => q) := by
  rw [diagramObj_topology_eq_bot H]
  exact continuous_id

set_option linter.style.haveILetI false in
private theorem induced_furstenbergProfiniteMap_eq_genericFiniteQuotientTopology :
    TopologicalSpace.induced furstenbergProfiniteMap
        (inferInstance : TopologicalSpace intProfiniteCompletion) =
      genericFiniteQuotientTopology := by
  apply le_antisymm
  · rw [genericFiniteQuotientTopology]
    refine le_iInf fun H => ?_
    letI : TopologicalSpace ℤ :=
      TopologicalSpace.induced furstenbergProfiniteMap
        (inferInstance : TopologicalSpace intProfiniteCompletion)
    have heta : Continuous furstenbergProfiniteMap :=
      continuous_induced_dom
    have hcoord :
        Continuous (fun x : ℤ => (furstenbergProfiniteMap x).1 H) :=
      (continuous_apply H).comp (continuous_subtype_val.comp heta)
    have htransported :=
      (continuous_diagramObj_toQuotient H).comp hcoord
    apply Continuous.le_induced
    simpa [Function.comp_def, furstenbergProfiniteMap] using htransported
  · apply Continuous.le_induced
    letI : TopologicalSpace ℤ := genericFiniteQuotientTopology
    change Continuous furstenbergProfiniteMap
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
      have htransported :=
        (continuous_quotient_toDiagramObj H).comp hq
      simpa [Function.comp_def, furstenbergProfiniteMap] using htransported

/-- The topology induced on `ℤ` by the canonical map into Mathlib's additive profinite
completion is exactly the Furstenberg topology. -/
theorem furstenbergTopology_eq_induced_profiniteCompletion :
    furstenbergTopology =
      TopologicalSpace.induced furstenbergProfiniteMap
        (inferInstance : TopologicalSpace intProfiniteCompletion) := by
  rw [induced_furstenbergProfiniteMap_eq_genericFiniteQuotientTopology]
  exact furstenbergTopology_eq_genericFiniteQuotientTopology

/-- The canonical map from the Furstenberg integers into the additive profinite completion has
dense range and induces exactly the Furstenberg topology. -/
theorem isDenseInducing_furstenbergProfiniteMap :
    @IsDenseInducing
      ℤ
      intProfiniteCompletion
      furstenbergTopology
      (inferInstance : TopologicalSpace intProfiniteCompletion)
      furstenbergProfiniteMap := by
  have hind :
      @IsInducing
        ℤ
        intProfiniteCompletion
        furstenbergTopology
        (inferInstance : TopologicalSpace intProfiniteCompletion)
        furstenbergProfiniteMap :=
    ⟨furstenbergTopology_eq_induced_profiniteCompletion⟩
  have hdense : DenseRange furstenbergProfiniteMap := by
    simpa [
      furstenbergProfiniteMap,
      intProfiniteCompletion,
      intProfiniteDiagram,
      ProfiniteAddGrp.ProfiniteCompletion.completion,
      ProfiniteAddGrp.ProfiniteCompletion.etaFn
    ] using
      (ProfiniteAddGrp.ProfiniteCompletion.denseRange (G := AddGrpCat.of ℤ))
  exact ⟨hind, hdense⟩

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
  have hd :
      IsDenseInducing furstenbergProfiniteMap :=
    isDenseInducing_furstenbergProfiniteMap
  exact ⟨hd, hd.isInducing.injective⟩

end LeanFrontier.Int
