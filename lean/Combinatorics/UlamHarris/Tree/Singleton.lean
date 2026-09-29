module

public import Combinatorics.UlamHarris.Tree.Borel
public import Combinatorics.UlamHarris.Tree.Metric

/-!
# The single-root specialization of root-indexed trees

`RootIndexed.Tree Root α` is an indexed family of `UlamHarris.Tree α`.  For a
unique root the family is identified with its only coordinate.  The family
definition and its topology, metric, and measurable-space interfaces are in
the corresponding `Tree/` modules; this file records only the specialization.
-/

open MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

section Unique

variable [Unique Root]

def equivOfUnique : RootIndexed.Tree Root α ≃ UlamHarris.Tree α :=
  Equiv.funUnique Root (UlamHarris.Tree α)

@[simp]
theorem equivOfUnique_apply (T : RootIndexed.Tree Root α) :
    equivOfUnique (Root := Root) (α := α) T = T default :=
  rfl

@[simp]
theorem equivOfUnique_symm_apply (T : UlamHarris.Tree α) :
    (equivOfUnique (Root := Root) (α := α)).symm T = fun _ => T :=
  rfl

theorem treeDist_apply (T T' : RootIndexed.Tree Root α) :
    treeDist T T' = UlamHarris.Tree.treeDist (T default) (T' default) := by
  haveI : Nonempty Root := ⟨default⟩
  rw [treeDist]
  exact le_antisymm (ciSup_le fun r => by rw [Unique.eq_default r])
    (le_ciSup (treeDist_bddAbove T T') default)

theorem preimage_truncationBall_eq_uniformBall (T : RootIndexed.Tree Root α) (n : ℕ) :
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

theorem measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (RootIndexed.Tree Root α)) =
      (inferInstance : MeasurableSpace (UlamHarris.Tree α)).comap
        (equivOfUnique (Root := Root) (α := α)) := by
  rw [measurableSpace_eq_iSup, iSup_unique]
  rfl

theorem pointwiseTopology_eq_induced :
    (inferInstance : TopologicalSpace (RootIndexed.Tree Root α)) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        Tree.treePointwiseTopology := by
  rw [pointwiseTopology_eq_iInf, iInf_unique]
  rfl

theorem productTruncationTopology_eq_induced :
    productTruncationTopology (Root := Root) (α := α) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        Tree.treeTruncationTopology := by
  rw [productTruncationTopology, iInf_unique]
  rfl

theorem uniformTopology_eq_induced :
    uniformTopology (Root := Root) (α := α) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        Tree.treeTruncationTopology := by
  have hgen : {s : Set (RootIndexed.Tree Root α) | ∃ T n, s = uniformBall T n} =
      Set.preimage (equivOfUnique (Root := Root) (α := α)) ''
        {s : Set (UlamHarris.Tree α) | ∃ T n, s = Tree.truncationBall T n} := by
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
        (Root := Root) (α := α)
        ((equivOfUnique (Root := Root) (α := α)).symm U) n
  rw [uniformTopology, Tree.treeTruncationTopology, induced_generateFrom_eq, hgen]

theorem metricTopology_eq_induced :
    metricTopology (Root := Root) (α := α) =
      TopologicalSpace.induced (equivOfUnique (Root := Root) (α := α))
        (Tree.treeMetricTopology α) := by
  haveI : Nonempty Root := ⟨default⟩
  rw [metricTopology_eq_uniformTopology, uniformTopology_eq_induced,
    Tree.treeMetricTopology_eq_truncationTopology]

theorem borel_uniformTopology_eq_comap :
    @borel (RootIndexed.Tree Root α) (uniformTopology (Root := Root) (α := α)) =
      (@borel (UlamHarris.Tree α) Tree.treeTruncationTopology).comap
        (equivOfUnique (Root := Root) (α := α)) := by
  rw [uniformTopology_eq_induced, borel_comap]

end Unique

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end
