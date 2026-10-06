/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Field

/-!
# Measurable observables of the recursive matched field

Concrete first-`N` populations and observed positions are measurable after the
matched field has been shown filtration-measurable.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- The totalized selected population evaluated on a stage-`n` matched field
is measurable using only the measurable lower-finite selector. -/
theorem RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
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
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ k field p, p ∈ source k field → p.2.length = k)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target k)).Countable)
    (hfiber : ∀ k, k < n → ∀ choices,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target k field = choices}) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      (fun field => RootIndexed.selectedPopulationTotalized N roots initial d φ n
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) := by
  have hprior := RootIndexed.rankInstalledField_filtration_measurable_of_lt
    sourceValue targetValue source target hsourceDepth n hcount hfiber
  have hselected := RootIndexed.selectedPopulationTotalized_adapted
    (Root := Root) (α := α) (Mark := Mark) (Position := Position)
    (Value := Value) N roots initial d hd φ hφ n
  exact hselected.comp hprior

/-- An observed generation position in the stage-`n` matched field is
measurable from predictability of the strictly earlier matching stages. -/
theorem RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
    {Root α Mark Position Value : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ k field p, p ∈ source k field → p.2.length = k)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target k)).Countable)
    (hfiber : ∀ k, k < n → ∀ choices,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target k field = choices})
    (p : RootIndexed.TreeNode Root α) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      (fun field => RootIndexed.observedPositionAtGeneration initial d φ n
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) p) := by
  have hprior := RootIndexed.rankInstalledField_filtration_measurable_of_lt
    sourceValue targetValue source target hsourceDepth n hcount hfiber
  exact hφ.comp ((RootIndexed.positionAtGeneration_measurable
    initial d hd n p.1 p.2).comp hprior)

end ProbabilityTheory.BranchingRandomWalk.Coupling
