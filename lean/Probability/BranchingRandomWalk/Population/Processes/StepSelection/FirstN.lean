import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.Infinite
import Probability.BranchingRandomWalk.Selection.NSelection.ByValue

/-!
# Measurable first-N step rules

The intrinsic first-`N` selection of an unordered branching step is
measurable when slot labels are countable and its dynamic comparison keys
are measurable.  Countability is confined to this labelled realization; the
underlying `Step.FiniteSelection` and its recursive population do not require
it.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.StepSelection

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- Measurability of an intrinsic first-`N` rule on branching steps. -/
theorem firstNBy_measurable
    {α X Value : Type*} [Countable α]
    [MeasurableSpace X] [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ))
    (hkey : ∀ p q : α, Measurable fun ξ : Step α X =>
      valueKey (value ξ) q < valueKey (value ξ) p) :
    Measurable (Step.FiniteSelection.firstNBy N value hadmits).select := by
  apply Selection.NSelection.measurable_selectFirstNFromSet
    N value (fun ξ : Step α X => support ξ) hadmits
  · rw [measurable_set_iff]
    intro i
    exact measurableSet_setOfPred.mp (survive_measurableSet i)
  · exact hkey

/-- The first-`N` rule ordered by a measurable real potential is measurable.
No ordering of the branching law is assumed. -/
theorem firstNByPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X)
    (hadmits : ∀ ξ : Step α X, AdmitsFirstNBy N
      (fun i => ξ.potentialValue' φ i) (support ξ)) :
    Measurable
      (Step.FiniteSelection.firstNByPotential N φ hadmits).select := by
  apply firstNBy_measurable N
    (fun (ξ : Step α X) i => ξ.potentialValue' φ i) hadmits
  intro p q
  exact Selection.NSelection.measurable_valueKey_lt
    (fun (ξ : Step α X) i => ξ.potentialValue' φ i)
    (fun i => Step.potentialValue'_measurable φ i) p q

end ProbabilityTheory.BranchingRandomWalk.StepSelection
