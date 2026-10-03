module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.BranchingProcess.Offspring.FieldLaw
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Product laws on branching step fields

`stepFieldLaw μ` is the product law of an i.i.d. family of branching
steps, one at every address; `RootIndexed.stepFieldLaw` is the product
of one such field over every initial root. The file also records the
coordinate marginals and the independence statements that the restart and
multi-root arguments consume.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



noncomputable def stepFieldLaw {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) :
    Measure (StepField α X) :=
  ProbabilityTheory.BranchingProcess.offspringFieldLaw μ

instance stepFieldLaw.isProbabilityMeasure
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (stepFieldLaw μ) := by
  unfold stepFieldLaw
  infer_instance

theorem stepFieldLaw_coordinate
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] (u : TreeNode α) :
    (stepFieldLaw μ).map (fun ω => ω u) = μ := by
  exact ProbabilityTheory.BranchingProcess.offspringFieldLaw_coordinate μ u

theorem stepFieldLaw_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    iIndepFun (fun u (ω : StepField α X) => ω u)
      (stepFieldLaw μ) := by
  exact ProbabilityTheory.BranchingProcess.offspringFieldLaw_independent μ

theorem stepFieldLaw_injective_coordinates_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode α) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : StepField α X) => ω (f i))
      (stepFieldLaw μ) := by
  exact (stepFieldLaw_independent μ).precomp hf

theorem stepFieldLaw_injective_coordinates_comp_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode α) (hf : Function.Injective f)
    (g : ∀ i, Step α X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : StepField α X) =>
      g i (ω (f i))) (stepFieldLaw μ) := by
  exact (stepFieldLaw_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

end ProbabilityTheory.BranchingRandomWalk
