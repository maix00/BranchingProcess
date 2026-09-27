import Probability.BranchingRandomWalk.Selection.NSelection.Law.SelectedPopulation
import Probability.BranchingRandomWalk.Selection.Process

/-!
# Product law for a causal selected source

This file connects recursive equal-rank matching to the general causal
finite-selection interface.  The source rule may depend on the whole
generation domain and may vary with time.  In particular, it need not be a
time-homogeneous rule applied separately to each branching step.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- Equal-rank installation couples any causal finite selected source to the
concrete first-`N` target while preserving the target product-field law.

The candidate process may itself be recursively generated.  Its adaptation
is the only measurability premise needed here; the causal mechanism then
supplies adaptation of the retained source population. -/
theorem RootIndexed.rankInstalledField_causalSelection_law
    {Root α Mark Position Value : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (R : CausalFiniteMechanism ℕ
      (RootIndexed.StepField (Root ⊕ Root) α Mark)
      (RootIndexed.TreeNode Root α)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark)))
    (candidates : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (hcandidates : ∀ k, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) k] (candidates k))
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (hsourceDepth : ∀ k field p,
      p ∈ R.population candidates k field → p.2.length = k)
    (hsourceKey : ∀ k p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) k]
      fun field => valueKey (sourceValue k field) q <
        valueKey (sourceValue k field) p) :
    let targetValue := fun k
        (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
        (field : RootIndexed.StepField Root α Mark) =>
      RootIndexed.observedPositionAtGeneration initial d φ k field
    let target := fun k
        (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
        (field : RootIndexed.StepField Root α Mark) =>
      RootIndexed.selectedPopulation N roots initial d φ hadmits k field
    ∀ n,
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
          (RootIndexed.rankInstalledField sourceValue targetValue
            (R.population candidates) target RootIndexed.StepField.left
            RootIndexed.StepField.right n) =
        RootIndexed.stepFieldLaw (Root := Root) μ := by
  dsimp only
  have hsourceFiber : ∀ k s,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k]
        {field | R.population candidates k field = s} := by
    intro k s
    exact (R.measurable_population candidates hcandidates k)
      (measurableSet_singleton s)
  have hsourceRange : ∀ k,
      (Set.range (R.population candidates k)).Countable :=
    fun _ => Set.to_countable _
  exact fun n =>
    (RootIndexed.rankInstalledField_selectedPopulation_measurable_law
      μ N roots initial d hd φ hφ hadmits sourceValue
      (R.population candidates) hsourceDepth hsourceFiber hsourceRange
      hsourceKey n).2

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
