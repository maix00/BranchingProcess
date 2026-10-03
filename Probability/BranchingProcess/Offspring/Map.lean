module

public import Combinatorics.BranchingWalk.Step.Map
public import Probability.BranchingProcess.Offspring.Law

/-!
# Mark maps of single offspring configurations

A measurable transformation of child marks acts slotwise on a configuration
law. Compatibility with the independently sampled configuration field is
proved in `Offspring/FieldLaw.lean`.
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

end ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

end
