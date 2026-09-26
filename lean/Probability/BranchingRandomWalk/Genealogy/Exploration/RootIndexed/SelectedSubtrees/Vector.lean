import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Independence

/-!
# Selected subtree step fields of a multi-root field

Selection uses the joint generation domain flow of every root, so the chosen
nodes may belong to different initial roots. This layer defines the selected
subtree vector and proves it is measurable once the selection is.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


def selectedMultiRootSubtreeStepFieldVector
    {m k : ℕ} {X : Type*}
    (chosen : FiniteRootStepField m X → Fin k → Fin m × 𝕍)
    (step : FiniteRootStepField m X) :
    Fin k → 𝕍 → Step ℕ X :=
  multiRootSubtreeStepFieldVector (chosen step) step

theorem selectedMultiRootSubtreeStepFieldVector_measurable
    {m k n : ℕ} {X : Type*} [MeasurableSpace X]
    (chosen : FiniteRootStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen) :
    Measurable (selectedMultiRootSubtreeStepFieldVector chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono (multiRootStepFiltration (m := m) (X := X) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : (Fin k → Fin m × 𝕍) × FiniteRootStepField m X =>
        multiRootSubtreeStepFieldVector p.1 p.2) :=
    measurable_from_prod_countable_right
      multiRootSubtreeStepFieldVector_measurable
  exact hjoint.comp (hselect.prodMk measurable_id)

end ProbabilityTheory.BranchingRandomWalk
