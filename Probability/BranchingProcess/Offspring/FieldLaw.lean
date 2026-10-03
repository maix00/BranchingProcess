module

public import Combinatorics.BranchingWalk.StepField
public import Mathlib.Probability.Independence.InfinitePi
public import Probability.BranchingProcess.Offspring.Map

/-!
# Independent fields of offspring configurations

The generic branching-process construction samples one complete child-slot
configuration independently at every Ulam--Harris address. It is independent
of spatial positions and applies to marked and unmarked configurations alike.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingProcess

/-- The law of an independently sampled offspring configuration at every
Ulam--Harris address. -/
noncomputable def offspringFieldLaw {α Mark : Type*} [MeasurableSpace Mark]
    (μ : Measure (Combinatorics.Branching.Step α Mark)) :
    Measure (Combinatorics.Branching.StepField α Mark) :=
  Measure.infinitePi (fun _ : Combinatorics.UlamHarris.TreeNode α => μ)

instance offspringFieldLaw.isProbabilityMeasure {α Mark : Type*}
    [MeasurableSpace Mark] (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (offspringFieldLaw μ) := by
  unfold offspringFieldLaw
  infer_instance

/-- Every address has the prescribed offspring-configuration marginal. -/
theorem offspringFieldLaw_coordinate {α Mark : Type*} [MeasurableSpace Mark]
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ] (u : Combinatorics.UlamHarris.TreeNode α) :
    (offspringFieldLaw μ).map (fun field => field u) = μ := by
  unfold offspringFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : Combinatorics.UlamHarris.TreeNode α => μ) u

/-- Configurations sampled at distinct addresses are mutually independent. -/
theorem offspringFieldLaw_independent {α Mark : Type*}
    [MeasurableSpace Mark]
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ] :
    iIndepFun
      (fun u (field : Combinatorics.Branching.StepField α Mark) => field u)
      (offspringFieldLaw μ) := by
  unfold offspringFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Combinatorics.UlamHarris.TreeNode α => μ)
    (X := fun _ => id) (fun _ => measurable_id))

/-- Mapping child marks commutes with the independent product construction. -/
theorem offspringFieldLaw_mapMarks {α Mark Mark' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ] (f : Mark → Mark') (hf : Measurable f) :
    (offspringFieldLaw μ).map (Combinatorics.Branching.StepField.map f) =
      offspringFieldLaw (μ.map (Combinatorics.Branching.Step.map f)) := by
  unfold offspringFieldLaw
  rw [← Measure.infinitePi_map_pi
    (μ := fun _ : Combinatorics.UlamHarris.TreeNode α => μ)
    (f := fun _ => Combinatorics.Branching.Step.map f)
    (hf := fun _ => Combinatorics.Branching.Step.map_measurable hf)]
  rfl

namespace OffspringConfigurationLaw

/-- Independently sample one offspring configuration at every Ulam--Harris
address. -/
noncomputable def fieldLaw {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure (Combinatorics.Branching.StepField ι Mark) :=
  ⟨ProbabilityTheory.BranchingProcess.offspringFieldLaw
    (μ : Measure (Combinatorics.Branching.Step ι Mark)), inferInstance⟩

@[simp] theorem fieldLaw_toMeasure {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι Mark)) =
      ProbabilityTheory.BranchingProcess.offspringFieldLaw
        (μ : Measure (Combinatorics.Branching.Step ι Mark)) := rfl

/-- The configuration at every address has the prescribed offspring law. -/
theorem fieldLaw_coordinate {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (u : Combinatorics.UlamHarris.TreeNode ι) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι Mark)).map
      (fun field => field u) =
        (μ : Measure (Combinatorics.Branching.Step ι Mark)) := by
  rw [fieldLaw_toMeasure]
  exact ProbabilityTheory.BranchingProcess.offspringFieldLaw_coordinate
    (μ : Measure (Combinatorics.Branching.Step ι Mark)) u

/-- Mapping child marks commutes with the independent configuration-field
construction. -/
theorem fieldLaw_mapMarks {ι Mark Mark' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).fieldLaw =
      (μ.fieldLaw).map (Combinatorics.Branching.StepField.map f) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ProbabilityTheory.BranchingProcess.offspringFieldLaw
      (μ.mapMarks f hf : Measure (Combinatorics.Branching.Step ι Mark')) =
    (ProbabilityTheory.BranchingProcess.offspringFieldLaw
      (μ : Measure (Combinatorics.Branching.Step ι Mark))).map
      (Combinatorics.Branching.StepField.map f)
  rw [mapMarks_toMeasure]
  exact (ProbabilityTheory.BranchingProcess.offspringFieldLaw_mapMarks
    (μ : Measure (Combinatorics.Branching.Step ι Mark)) f hf).symm

end OffspringConfigurationLaw

end ProbabilityTheory.BranchingProcess

end
