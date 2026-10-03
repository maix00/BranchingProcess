module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Probability.BranchingRandomWalk.Step.Law

/-!
# Offspring configuration laws

A configuration law is a probability measure on complete optional child-slot
configurations. The mark type is a parameter: `PUnit` gives an unmarked
genealogy, while a spatial mark type retains the marks attached to children.
Optional slots allow a configuration with no children and preserve slot labels.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingProcess

/-- A probability law for one complete offspring configuration, retaining its
slot labels and the marks of present children. -/
abbrev OffspringConfigurationLaw (ι Mark : Type*) [MeasurableSpace Mark] :=
  ProbabilityMeasure (Combinatorics.Branching.Step ι Mark)

namespace OffspringConfigurationLaw

/-- Independently sample one offspring configuration at every Ulam--Harris
address. -/
noncomputable def fieldLaw {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure (Combinatorics.Branching.StepField ι Mark) :=
  ⟨ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
    (α := ι) (X := Mark)
    (μ : Measure (Combinatorics.Branching.Step ι Mark)), inferInstance⟩

@[simp] theorem fieldLaw_toMeasure {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : OffspringConfigurationLaw ι Mark) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι Mark)) =
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := ι) (X := Mark)
        (μ : Measure (Combinatorics.Branching.Step ι Mark)) := rfl

/-- The configuration at each address has the specified offspring law. -/
theorem fieldLaw_coordinate {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : OffspringConfigurationLaw ι Mark)
    (u : Combinatorics.UlamHarris.TreeNode ι) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι Mark)).map
      (fun field => field u) = (μ : Measure (Combinatorics.Branching.Step ι Mark)) := by
  rw [fieldLaw_toMeasure]
  exact ProbabilityTheory.BranchingRandomWalk.stepFieldLaw_coordinate
    (α := ι) (X := Mark)
    (μ : Measure (Combinatorics.Branching.Step ι Mark)) u

end OffspringConfigurationLaw

end ProbabilityTheory.BranchingProcess

end
