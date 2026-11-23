/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Basic

/-!
# First-N specifications on installed stages

## Internal proof declarations

- `installedFirstN_spec_ae` proves that almost surely the slice of each
  installed successor field is the first $N$ of its candidate children.
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- Lower finiteness on the original field transfers to the installed field,
which has the same law. -/
lemma installedFirstN_spec_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (admissible : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ, ∀ k,
      IsLowerFiniteBy
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1) field)
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k field) field))
    (selectedBRWPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left)
    (hselectedBRWPopulationFiniteSlices : selectedBRWPopulation.FiniteSlices) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ, ∀ k,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1)
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k
            (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
              (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (RootIndexed.selectedPopulationTotalized N roots initialPosition id id
          (k + 1) (RootIndexed.restartedRealPositionNSelectedBRWField N roots
            initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field)) := by
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  have hspec : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ, ∀ k,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1) field)
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k field) field)
        (RootIndexed.selectedPopulationTotalized N roots initialPosition id id (k + 1) field) := by
    filter_upwards [admissible] with field hfield
    exact fun k => RootIndexed.selectedPopulationTotalized_succ_spec
      N roots initialPosition id id k field (hfield k)
  apply ae_all_iff.2
  intro k
  let nSelectedBRWField := RootIndexed.restartedRealPositionNSelectedBRWField N roots
    initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1)
  have hleft : RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α ℝ →
          RootIndexed.StepField Root α ℝ) := rfl
  have hnSelectedBRWFieldLaw : Measurable nSelectedBRWField ∧
      P.map nSelectedBRWField = RootIndexed.stepFieldLaw (Root := Root) μ := by
    change Measurable
        (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
          (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1)) ∧
      P.map (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
        (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1)) = RootIndexed.stepFieldLaw (Root := Root) μ
    simpa only [P, RootIndexed.restartedRealPositionNSelectedBRWField, hleft] using
      (RootIndexed.rankInstalledField_causalPopulation_measurable_law
        μ N roots initialPosition id measurable_id id measurable_id selectedBRWPopulation
        hselectedBRWPopulationFiniteSlices (k + 1))
  have hspecMap : ∀ᵐ sample ∂P.map nSelectedBRWField,
      ∀ j, IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (j + 1) sample)
        (Combinatorics.Branching.Population.childrenAtGeneration j
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id j sample)
          sample)
        (RootIndexed.selectedPopulationTotalized N roots initialPosition id id
          (j + 1) sample) := by
    rw [hnSelectedBRWFieldLaw.2]
    exact hspec
  have hspecFieldAtStage :=
    MeasureTheory.ae_of_ae_map hnSelectedBRWFieldLaw.1.aemeasurable hspecMap
  filter_upwards [hspecFieldAtStage] with field hstage
  exact hstage k


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
