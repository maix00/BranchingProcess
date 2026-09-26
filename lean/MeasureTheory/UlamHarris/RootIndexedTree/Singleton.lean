import MeasureTheory.UlamHarris.RootIndexedTree.Measurability
import MeasureTheory.UlamHarris.RootIndexedTree.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The single-root case of a root-indexed tree

`RootIndexedTree Root α` is an indexed family of `Tree α`, one tree per initial
ancestor (`Basic.lean`), so a family over a one-element index type *is* a tree.
This file makes that specialization explicit. For `[Unique Root]`,
`equivOfUnique` identifies `RootIndexedTree Root α` with `Tree α`; in
particular `Tree α` is `RootIndexedTree Unit α`, `RootIndexedTree PUnit α`, and
`RootIndexedTree (Fin 1) α`. The identification preserves

* the tree distance (`treeDist_apply`), so the sup metric of the family is the
  tree metric of its only member;
* the measurable space (`measurableSpace_eq_comap`), so the product σ-algebra
  is the cylinder σ-algebra;
* the pointwise topology (`pointwiseTopology_eq_induced`);
* the truncation, uniform, and metric topologies
  (`productTruncationTopology_eq_induced`, `uniformTopology_eq_induced`,
  `metricTopology_eq_induced`);
* the Borel σ-algebra of the uniform topology
  (`borel_uniformTopology_eq_comap`).

The dependency direction is the one already fixed in `Basic.lean`:
`RootIndexedTree` is defined from `Tree`, so the single-root case is a
specialization of the multi-root object, not the other way around.
-/

open MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

namespace MeasureTheory

namespace UlamHarris

namespace RootIndexedTree

variable {Root α : Type*} [LT α]

section Unique

variable [Unique Root]

/-- A root-indexed tree over a single initial ancestor is a tree. -/
def equivOfUnique : RootIndexedTree Root α ≃ Tree α :=
  Equiv.funUnique Root (Tree α)

@[simp]
theorem equivOfUnique_apply (T : RootIndexedTree Root α) :
    equivOfUnique (Root := Root) (α := α) T = T default :=
  rfl

@[simp]
theorem equivOfUnique_symm_apply (T : Tree α) :
    (equivOfUnique (Root := Root) (α := α)).symm T = fun _ => T :=
  rfl

/-- The sup tree distance of a single-root family is the tree distance of its
only initial ancestor. -/
theorem treeDist_apply (T T' : RootIndexedTree Root α) :
    treeDist T T' = Tree.treeDist (T default) (T' default) := by
  haveI : Nonempty Root := ⟨default⟩
  rw [treeDist]
  exact le_antisymm (ciSup_le fun r => by rw [Unique.eq_default r])
    (le_ciSup (treeDist_bddAbove T T') default)

/-- The uniform balls of a single-root family are the truncation balls of its
only initial ancestor. -/
theorem preimage_truncationBall_eq_uniformBall (T : RootIndexedTree Root α) (n : ℕ) :
    equivOfUnique (Root := Root) (α := α) ⁻¹'
        Tree.truncationBall (equivOfUnique (Root := Root) (α := α) T) n =
      uniformBall T n := by
  ext S
  rw [Set.mem_preimage, Tree.mem_truncationBall, mem_uniformBall,
    equivOfUnique_apply, equivOfUnique_apply]
  constructor
  · intro h r
    rw [Unique.eq_default r]
    exact h
  · intro h
    exact h default

/-- The measurable space of a single-root family is the tree σ-algebra of its
only initial ancestor. -/
theorem measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (RootIndexedTree Root α)) =
      (inferInstance : MeasurableSpace (Tree α)).comap
        (equivOfUnique (Root := Root) (α := α)) := by
  rw [measurableSpace_eq_iSup, iSup_unique]
  rfl

/-- The default topology of a single-root family is the pointwise topology of
its only initial ancestor. -/
theorem pointwiseTopology_eq_induced :
    (inferInstance : TopologicalSpace (RootIndexedTree Root α)) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        Tree.treePointwiseTopology := by
  rw [pointwiseTopology_eq_iInf, iInf_unique]
  rfl

/-- The product of the truncation topologies of a single-root family is the
truncation topology of its only initial ancestor. -/
theorem productTruncationTopology_eq_induced :
    productTruncationTopology (Root := Root) (α := α) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        Tree.treeTruncationTopology := by
  rw [productTruncationTopology, iInf_unique]
  rfl

/-- The uniform topology of a single-root family is the truncation topology of
its only initial ancestor. -/
theorem uniformTopology_eq_induced :
    uniformTopology (Root := Root) (α := α) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        Tree.treeTruncationTopology := by
  have hgen : {s : Set (RootIndexedTree Root α) | ∃ T n, s = uniformBall T n} =
      Set.preimage (equivOfUnique (Root := Root) (α := α)) ''
        {s : Set (Tree α) | ∃ T n, s = Tree.truncationBall T n} := by
    ext s
    constructor
    · rintro ⟨T, n, rfl⟩
      exact ⟨Tree.truncationBall (equivOfUnique (Root := Root) (α := α) T) n,
        ⟨equivOfUnique (Root := Root) (α := α) T, n, rfl⟩,
        preimage_truncationBall_eq_uniformBall T n⟩
    · rintro ⟨V, ⟨U, n, rfl⟩, hUV⟩
      refine ⟨(equivOfUnique (Root := Root) (α := α)).symm U, n, ?_⟩
      rw [← hUV]
      simpa using preimage_truncationBall_eq_uniformBall
        (Root := Root) (α := α) ((equivOfUnique (Root := Root) (α := α)).symm U) n
  rw [uniformTopology, Tree.treeTruncationTopology, induced_generateFrom_eq, hgen]

/-- The sup tree metric of a single-root family induces the metric topology of
its only initial ancestor. -/
theorem metricTopology_eq_induced :
    metricTopology (Root := Root) (α := α) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        (Tree.treeMetricTopology α) := by
  haveI : Nonempty Root := ⟨default⟩
  rw [metricTopology_eq_uniformTopology, uniformTopology_eq_induced,
    Tree.treeMetricTopology_eq_truncationTopology]

/-- The Borel σ-algebra of the uniform topology of a single-root family is the
Borel σ-algebra of the truncation topology of its only initial ancestor. -/
theorem borel_uniformTopology_eq_comap :
    @borel (RootIndexedTree Root α) (uniformTopology (Root := Root) (α := α)) =
      (@borel (Tree α) Tree.treeTruncationTopology).comap
        (equivOfUnique (Root := Root) (α := α)) := by
  rw [uniformTopology_eq_induced, borel_comap]

end Unique

end RootIndexedTree

end UlamHarris

end MeasureTheory
