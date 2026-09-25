import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtree
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtreeVector

/-!
# Cells of a stopped measurable root vector

The fixed-cardinality stopping cell records the stopping generation and the
root vector simultaneously, and is measurable at that generation.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingStep MeasureTheory


def abstractStoppedVectorCell {X : Type*} {k : ℕ}
    (τ : (𝕍 → Step ℕ X) → WithTop ℕ)
    (roots : (𝕍 → Step ℕ X) → Fin k → 𝕍)
    (A : Set (𝕍 → Step ℕ X))
    (p : ℕ × (Fin k → 𝕍)) :
    Set (𝕍 → Step ℕ X) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | roots ω = p.2}

theorem abstractStoppedVectorCell_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (τ : (𝕍 → Step ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step ℕ X)) τ)
    (roots : (𝕍 → Step ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (A : Set (𝕍 → Step ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × (Fin k → 𝕍)) :
    MeasurableSet[generationFiltration (M := Step ℕ X) p.1]
      (abstractStoppedVectorCell τ roots A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable
      (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hrootSet : MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = p.2} := hroots (measurableSet_singleton p.2)
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
