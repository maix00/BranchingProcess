import Probability.BranchingRandomWalk.Step.Basic
import Combinatorics.BranchingWalk.Basic.Core

/-!
# Random branching-step fields

A random step is indexed by child slots. A random step field adds one further
index, the Ulam--Harris address at which reproduction occurs. Evaluation at a
sample assembles the corresponding deterministic step field.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris

/-- A random branching-step field: one random step at every tree address. -/
abbrev StepField (Ω α X : Type*) [MeasurableSpace Ω] [MeasurableSpace X] :=
  TreeNode α → Step Ω α X

/-- Evaluate every random coordinate of a step field at one sample. -/
def StepField.realize
    {Ω α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepField Ω α X) (ω : Ω) :
    Combinatorics.Branching.StepField α X :=
  fun u => S u ω

/-- Realization of a random step field is measurable into the product space of
deterministic fields. -/
theorem StepField.measurable_realize
    {Ω α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepField Ω α X) : Measurable S.realize := by
  rw [measurable_pi_iff]
  intro u
  exact (S u).measurable_toFun

@[simp] theorem StepField.realize_apply
    {Ω α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepField Ω α X) (ω : Ω) (u : TreeNode α) (i : α) :
    S.realize ω u i =
      if (S u).present i ω then some ((S u).displace i ω) else none := rfl

end ProbabilityTheory.BranchingRandomWalk
