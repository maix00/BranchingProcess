/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Combinatorics.UlamHarris.Basic
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Basic
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration
public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Core
import all Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Lemmas.Past

/-!
# Generation-domain measurability of the recursive matched field

The stagewise matched field is measurable for its generation domain flow.

## Public declarations

Writing `F_n` for the installed field and `𝒟_n` for the generation domain flow,
both declarations assert

\[
  \operatorname{Measurable}_{𝒟_n}(F_n).
\]
The first derives this statement from coordinate-map hypotheses at each
`k < n`; the second assembles it for every generation.

* `RootIndexed.rankInstalledField_domainFlow_measurable_of_lt` derives the
  stage-`n` map from hypotheses for each earlier generation `k < n`.
* `RootIndexed.rankInstalledField_domainFlow_measurable` assembles the
  stagewise domain-flow measurability statement for every `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The stage-`n` matched field is causal using only coordinate-map
predictability at stages below `n`. -/
theorem RootIndexed.rankInstalledField_domainFlow_measurable_of_lt
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hselectedBRWPopulationDepth : ∀ n field p, p ∈ selectedBRWPopulation n field → p.2.length = n)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation k)).Countable)
    (hfiber : ∀ k, k < n → ∀ roots,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) k]
        {field | RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
          selectedBRWPopulation nSelectedBRWPopulation k field = roots}) :
    @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α X)
      (RootIndexed.StepField Root α X)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) n)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n)
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n) := by
  let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α X) :=
    RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n
  exact (RootIndexed.StepField.measurable_stepFiltration_iff_past n _).2
    (RootIndexed.rankInstalledField_past_measurable_of_lt selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
      selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth n hcount hfiber)

/-- Each recursive stage is a causal endomorphism of the corresponding
generation domain. -/
theorem RootIndexed.rankInstalledField_domainFlow_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hselectedBRWPopulationDepth : ∀ n field p, p ∈ selectedBRWPopulation n field → p.2.length = n)
    (hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
        selectedBRWPopulation nSelectedBRWPopulation n field = roots}) :
    ∀ n, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α X)
      (RootIndexed.StepField Root α X)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) n)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n)
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n) := by
  intro n
  let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α X) :=
    RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n
  exact (RootIndexed.StepField.measurable_stepFiltration_iff_past n _).2
    (RootIndexed.rankInstalledField_past_measurable selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation
      nSelectedBRWPopulation hselectedBRWPopulationDepth hcount hfiber n)

end ProbabilityTheory.BranchingRandomWalk.Coupling
