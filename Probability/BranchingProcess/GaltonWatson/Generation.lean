/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Basic.GenerationSize
public import Probability.BranchingProcess.Offspring.Count
public import Probability.BranchingProcess.GaltonWatson.Law

/-!
# Galton--Watson generation sizes

Generation sizes reuse the `ℕ∞`-valued observation on presampled branching
configurations, so infinite populations remain representable.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

open MeasureTheory

/-- The first-generation size under the presampled Galton--Watson law has the
offspring-count law of the one-step configuration. This includes zero and
infinite offspring counts. -/
theorem generationSize_one_law {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) :
    (law μ).map (fun β : Combinatorics.Branching.Process ι =>
      β.generationSize 1) = μ.childCountLaw := by
  have hpair : Measurable
      (fun β : Combinatorics.Branching.Process ι => (β.step, β.initial)) :=
    Measurable.of_comap_le le_rfl
  have hstepField : Measurable
      (fun β : Combinatorics.Branching.Process ι => β.step PUnit.unit) :=
    (measurable_pi_apply PUnit.unit).comp (measurable_fst.comp hpair)
  have hstep : Measurable
      (fun β : Combinatorics.Branching.Process ι =>
        (β.step PUnit.unit) ([] : Combinatorics.UlamHarris.TreeNode ι)) :=
    (measurable_pi_apply ([] : Combinatorics.UlamHarris.TreeNode ι)).comp hstepField
  have hgeneration : Measurable
      (fun β : Combinatorics.Branching.Process ι => β.generationSize 1) := by
    have hcountStep : Measurable
        (Combinatorics.Branching.Step.childCount :
          Combinatorics.Branching.Step ι PUnit.{1} → ℕ∞) :=
      Combinatorics.Branching.Step.childCount_measurable
    have hcount : Measurable
        (fun β : Combinatorics.Branching.Process ι =>
          Combinatorics.Branching.Step.childCount
            ((β.step PUnit.unit) ([] : Combinatorics.UlamHarris.TreeNode ι))) :=
      hcountStep.comp hstep
    have heq : (fun β : Combinatorics.Branching.Process ι =>
        β.generationSize 1) = fun β =>
          Combinatorics.Branching.Step.childCount
            ((β.step PUnit.unit) ([] : Combinatorics.UlamHarris.TreeNode ι)) := by
      funext β
      exact Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount β
    rw [heq]
    exact hcount
  have hfield : Measurable
      (Combinatorics.Branching.branchingOfStepField (α := ι)) :=
    Combinatorics.Branching.measurable_branchingOfStepField
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, law,
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_toMeasure]
  rw [Measure.map_map hgeneration hfield]
  have hcompose :
      (fun β : Combinatorics.Branching.Process ι => β.generationSize 1) ∘
        Combinatorics.Branching.branchingOfStepField =
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        Combinatorics.Branching.Step.childCount (field ([] :
          Combinatorics.UlamHarris.TreeNode ι))) := by
    funext field
    exact Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount
      (Combinatorics.Branching.branchingOfStepField field)
  have hchildCount : Measurable
      (Combinatorics.Branching.Step.childCount :
        Combinatorics.Branching.Step ι PUnit.{1} → ℕ∞) :=
    Combinatorics.Branching.Step.childCount_measurable
  have heval : Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        field ([] : Combinatorics.UlamHarris.TreeNode ι)) :=
    measurable_pi_apply ([] : Combinatorics.UlamHarris.TreeNode ι)
  rw [hcompose]
  calc
    _ = (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})).map
      (Combinatorics.Branching.Step.childCount ∘
          (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
            field ([] : Combinatorics.UlamHarris.TreeNode ι))) := by
      congr 1
    _ = ((μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})).map
          (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
            field ([] : Combinatorics.UlamHarris.TreeNode ι))).map
          Combinatorics.Branching.Step.childCount :=
      (Measure.map_map hchildCount heval).symm
    _ = ((μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})).map
          Combinatorics.Branching.Step.childCount) := by
      rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_coordinate
        μ ([] : Combinatorics.UlamHarris.TreeNode ι)]

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
