module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Probability.BranchingRandomWalk.Step.Law

/-!
# Offspring configuration laws

An offspring law is a probability measure on a complete optional child-slot
configuration. Since a configuration is `ι → Option PUnit`, it permits zero
children and keeps the slot labels of distinct children.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingProcess

/-- A probability law for one complete, unmarked offspring configuration. -/
abbrev OffspringLaw (ι : Type*) :=
  ProbabilityMeasure (Combinatorics.Branching.Step ι PUnit.{1})

namespace OffspringLaw

/-- Independently sample one offspring configuration at every Ulam--Harris
address. -/
noncomputable def fieldLaw {ι : Type*} (μ : OffspringLaw ι) :
    ProbabilityMeasure (Combinatorics.Branching.StepField ι PUnit.{1}) :=
  ⟨ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
    (α := ι) (X := PUnit.{1})
    (μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})), inferInstance⟩

@[simp] theorem fieldLaw_toMeasure {ι : Type*} (μ : OffspringLaw ι) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) =
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := ι) (X := PUnit.{1})
        (μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})) := rfl

/-- The configuration at each address has the specified offspring law. -/
theorem fieldLaw_coordinate {ι : Type*} (μ : OffspringLaw ι)
    (u : Combinatorics.UlamHarris.TreeNode ι) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})).map
      (fun field => field u) = (μ : Measure _) := by
  rw [fieldLaw_toMeasure]
  exact ProbabilityTheory.BranchingRandomWalk.stepFieldLaw_coordinate
    (α := ι) (X := PUnit.{1})
    (μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})) u

end OffspringLaw

end ProbabilityTheory.BranchingProcess

end
