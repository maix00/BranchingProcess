module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Offspring configuration laws

A configuration law is a probability measure on complete optional child-slot
configurations. The mark type is a parameter: `PUnit` gives an unmarked slot
configuration, while a spatial mark type retains the marks attached to
children. Optional slots allow a configuration with no children and preserve
slot labels.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingProcess

/-- A probability law for one complete offspring configuration, retaining its
slot labels and the marks of present children. -/
abbrev OffspringConfigurationLaw (ι Mark : Type*) [MeasurableSpace Mark] :=
  ProbabilityMeasure (Combinatorics.Branching.Step ι Mark)

end ProbabilityTheory.BranchingProcess

end
