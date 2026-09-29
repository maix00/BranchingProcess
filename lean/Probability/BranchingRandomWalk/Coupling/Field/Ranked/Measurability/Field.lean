import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Past

/-!
# Filtration measurability of the recursive matched field

The stagewise matched field is measurable for its generation domain flow.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- The stage-`n` matched field is causal using only coordinate-map
predictability at stages below `n`. -/
theorem RootIndexed.rankInstalledField_filtration_measurable_of_lt
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ n field p, p ∈ source n field → p.2.length = n)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target k)).Countable)
    (hfiber : ∀ k, k < n → ∀ roots,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) k]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target k field = roots}) :
    @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α X)
      (RootIndexed.StepField Root α X)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) n)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n)
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n) := by
  let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α X) :=
    RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n
  exact (RootIndexed.StepField.measurable_stepFiltration_iff_past n _).2
    (RootIndexed.rankInstalledField_past_measurable_of_lt sourceValue targetValue
      source target hsourceDepth n hcount hfiber)

/-- Each recursive stage is a causal endomorphism of the corresponding
generation domain. -/
theorem RootIndexed.rankInstalledField_filtration_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ n field p, p ∈ source n field → p.2.length = n)
    (hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
        source target n field = roots}) :
    ∀ n, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α X)
      (RootIndexed.StepField Root α X)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) n)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n)
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n) := by
  intro n
  let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α X) :=
    RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n
  exact (RootIndexed.StepField.measurable_stepFiltration_iff_past n _).2
    (RootIndexed.rankInstalledField_past_measurable sourceValue targetValue source
      target hsourceDepth hcount hfiber n)

end ProbabilityTheory.BranchingRandomWalk.Coupling
