import Probability.BranchingRandomWalk.Selection.NSelection.Law.CausalPopulation
import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition

/-!
# Coupling a restarted killed population to first-N selection

The killed source is constructed from relative-position windows on the left
half of one common pre-sampled field.  Rank installation then produces a
second field with the original product law, on which first-`N` selection is
run.  The result is a measure-level coupling with both marginals verified.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The canonical product-law coupling for a restarted real-valued killed
population.  Spatial domination is a separate pathwise theorem about this
coupling; it is not built into the definition of a coupling. -/
noncomputable def RootIndexed.restartedRealPositionCoupling
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition d id
          (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (n : ℕ) :
    ProbabilityTheory.Coupling
      (RootIndexed.stepFieldLaw (Root := Root) μ)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let killed := RootIndexed.CausalFinitePopulation.ofRestartedRealPositionSets
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
  let source := killed.pullback RootIndexed.StepField.left
    (fun k => RootIndexed.StepField.reindex_filtration_measurable Sum.inl k)
    (by rfl)
  exact RootIndexed.causalPopulationCoupling μ N roots initialPosition d hd
    id measurable_id hadmits source n

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
