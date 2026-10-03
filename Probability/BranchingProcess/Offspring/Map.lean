module

public import Combinatorics.BranchingWalk.Basic.Map
public import Probability.BranchingProcess.Offspring.Law

/-!
# Mark maps of offspring configuration laws

A measurable transformation of child marks acts slotwise on a configuration
law. Independent sampling at every address commutes with this projection, by
Mathlib's `Measure.infinitePi_map_pi` theorem.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

open MeasureTheory

/-- Push an offspring configuration law forward by a measurable map of child
marks. Slot labels and the presence or absence of each child are preserved. -/
noncomputable def mapMarks {ι Mark Mark' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (_hf : Measurable f) :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark' :=
  μ.map (Combinatorics.Branching.Step.map f)

@[simp] theorem mapMarks_toMeasure {ι Mark Mark' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf : Measure (Combinatorics.Branching.Step ι Mark')) =
      (μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        (Combinatorics.Branching.Step.map f) := rfl

/-- Mapping all marks in an offspring configuration law commutes with
independently sampling the configuration at every Ulam--Harris address. -/
theorem fieldLaw_mapMarks {ι Mark Mark' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).fieldLaw =
      (μ.fieldLaw).map (Combinatorics.Branching.StepField.map f) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (μ.mapMarks f hf : Measure (Combinatorics.Branching.Step ι Mark')) =
    (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (μ : Measure (Combinatorics.Branching.Step ι Mark))).map
      (Combinatorics.Branching.StepField.map f)
  rw [mapMarks_toMeasure]
  unfold ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
  rw [← Measure.infinitePi_map_pi (f := fun _ =>
    Combinatorics.Branching.Step.map f) (μ := fun _ :
      Combinatorics.UlamHarris.TreeNode ι =>
        (μ : Measure (Combinatorics.Branching.Step ι Mark)))
      (hf := fun _ =>
      Combinatorics.Branching.Step.map_measurable hf)]
  rfl

end ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

end
