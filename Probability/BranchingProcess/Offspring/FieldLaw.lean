module

public import Combinatorics.BranchingWalk.Basic.Map
public import Mathlib.Probability.Independence.InfinitePi

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

end ProbabilityTheory.BranchingProcess

end
