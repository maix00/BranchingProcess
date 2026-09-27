import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtree
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtreeVector

/-!
# Cells of a stopped root family

The stopping cell records the stopping generation and an arbitrarily indexed
root family simultaneously, and is measurable at that generation whenever
the corresponding root-family fiber is measurable.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


def abstractStoppedVectorCell {κ α X : Type*}
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (A : Set (TreeNode α → Step α X))
    (p : ℕ × (κ → TreeNode α)) :
    Set (TreeNode α → Step α X) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | roots ω = p.2}

theorem abstractStoppedVectorCell_measurable
    {κ α X : Type*} [MeasurableSpace X]
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step α X)) τ)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (A : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × (κ → TreeNode α))
    (hrootSet : MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = p.2}) :
    MeasurableSet[generationFiltration (M := Step α X) p.1]
      (abstractStoppedVectorCell τ roots A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable
      (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hrootEq := (hτ.measurableSet_inter_eq_iff
    {ω | roots ω = p.2} p.1).1
      (hrootSet.inter (hτ.measurable
        (measurableSet_singleton (p.1 : WithTop ℕ))))
  have heq : abstractStoppedVectorCell τ roots A p =
      (A ∩ {ω | τ ω = p.1}) ∩
        ({ω | roots ω = p.2} ∩ {ω | τ ω = p.1}) := by
    ext ω
    simp [abstractStoppedVectorCell, and_left_comm, and_assoc, and_comm]
  rw [heq]
  exact hAeq.inter hrootEq

end ProbabilityTheory.BranchingRandomWalk
