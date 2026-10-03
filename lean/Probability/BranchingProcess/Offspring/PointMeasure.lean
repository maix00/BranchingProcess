/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Step.PointMeasure
public import Probability.BranchingProcess.Offspring.Map

/-!
# Point-measure laws of offspring configurations

The law of the point-measure observation is a pushforward of the complete
slot-configuration law. This projection forgets slot labels but retains
multiplicity. It does not assert local finiteness; that must be supplied for
the chosen family of sets when a locally finite point process is needed.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

open MeasureTheory

/-- The law of the unordered point measure of a random offspring
configuration. -/
noncomputable def pointMeasureLaw {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure (Measure Mark) :=
  μ.map Combinatorics.Branching.stepPointMeasure

@[simp] theorem pointMeasureLaw_toMeasure {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    (μ.pointMeasureLaw : Measure (Measure Mark)) =
      (μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        Combinatorics.Branching.stepPointMeasure := rfl

/-- Mapping child marks before taking the unordered point-measure law agrees
with pushing that law forward by the induced map on measures. -/
theorem pointMeasureLaw_mapMarks {ι Mark Mark' : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).pointMeasureLaw =
      μ.pointMeasureLaw.map (Measure.map f) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, pointMeasureLaw_toMeasure,
    mapMarks_toMeasure]
  calc
    _ = ((μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        (fun ξ => Combinatorics.Branching.stepPointMeasure (ξ.map f))) := by
      rw [Measure.map_map Combinatorics.Branching.stepPointMeasure_measurable
        (Combinatorics.Branching.Step.map_measurable hf)]
      congr 1
    _ = ((μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        (fun ξ => (Combinatorics.Branching.stepPointMeasure ξ).map f)) := by
      congr 1
      funext ξ
      exact Combinatorics.Branching.stepPointMeasure_map f hf ξ
    _ = (((μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        Combinatorics.Branching.stepPointMeasure).map (Measure.map f)) := by
      rw [Measure.map_map (Measure.measurable_map f hf)
        Combinatorics.Branching.stepPointMeasure_measurable]
      congr 1

end ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

end
